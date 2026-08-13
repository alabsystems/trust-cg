// trust-cg-verify/neon_lowering_proofs.rs - NEON SIMD lowering verification proofs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Proof obligations verifying that trust_ir vector operations lower correctly
// to AArch64 NEON instructions. Each proof pairs a trust_ir-side semantic
// encoding (lane-wise scalar operation on bitvector vectors) with the
// corresponding NEON semantic encoding from `neon_semantics.rs`.
//
// The trust_ir side encodes vector operations as per-lane scalar ops applied
// to a flat bitvector, which is the canonical trust_ir vector semantics.
// The NEON side uses the instruction-specific encoders. The proof shows
// these are semantically equivalent for all inputs.
//
// 128-bit vectors are represented as pairs of 64-bit symbolic variables
// (`{name}_lo`, `{name}_hi`) concatenated via `hi.concat(lo)`. This is
// required because the mock evaluator uses u64 concrete values.
//
// Reference: designs/2026-04-13-verification-architecture.md
// Reference: ARM Architecture Reference Manual (DDI 0487), Sections C7.2

//! NEON SIMD lowering verification proofs.
//!
//! Provides [`ProofObligation`]s that verify trust_ir vector operations lower
//! correctly to AArch64 NEON instructions. Each proof covers both a 64-bit
//! and a 128-bit vector arrangement.
//!
//! Verified operations:
//! - Arithmetic: vector add, sub, mul, neg, mla (multiply-accumulate)
//! - Bitwise: and, or (orr), xor (eor), bit clear (bic)
//! - Shifts: shl, ushr (logical shift right), sshr (arithmetic shift right)
//! - Min/max: smin, umin, smax, umax
//! - Comparisons: cmgt (signed greater-than), cmge (signed greater-or-equal)

use crate::lowering_proof::ProofObligation;
use crate::neon_semantics::{
    encode_neon_abs, encode_neon_add, encode_neon_and, encode_neon_bic, encode_neon_bit,
    encode_neon_cmeq, encode_neon_cmge, encode_neon_cmgt, encode_neon_cmhi, encode_neon_cmhs,
    encode_neon_cnt, encode_neon_eor, encode_neon_ext, encode_neon_mla, encode_neon_mul,
    encode_neon_neg, encode_neon_not, encode_neon_orr, encode_neon_rbit_16b, encode_neon_rev64_4s,
    encode_neon_saddlp, encode_neon_saddw, encode_neon_shl, encode_neon_smax, encode_neon_smin,
    encode_neon_smlal, encode_neon_sshr, encode_neon_sub, encode_neon_uadalp, encode_neon_uaddlp,
    encode_neon_uaddw, encode_neon_udot, encode_neon_umax, encode_neon_umin, encode_neon_ushr,
};
use crate::smt::{
    SmtExpr, VectorArrangement, concat_lanes, lane_concat, lane_extract, map_lanes_binary,
    map_lanes_binary_imm, map_lanes_unary,
};

// ---------------------------------------------------------------------------
// Helper: build symbolic vector inputs
// ---------------------------------------------------------------------------

/// Build a 128-bit symbolic vector from two 64-bit halves.
///
/// Returns `hi.concat(lo)` where `lo = {prefix}_lo` (bits [63:0]) and
/// `hi = {prefix}_hi` (bits [127:64]).
fn var_128(prefix: &str) -> SmtExpr {
    let lo = SmtExpr::var(format!("{}_lo", prefix), 64);
    let hi = SmtExpr::var(format!("{}_hi", prefix), 64);
    hi.concat(lo)
}

/// Build a symbolic vector at the given arrangement's total width.
///
/// For 64-bit arrangements, returns a single 64-bit variable.
/// For 128-bit arrangements, returns `hi.concat(lo)` (two 64-bit halves).
fn symbolic_vector(name: &str, arrangement: VectorArrangement) -> SmtExpr {
    let w = arrangement.total_bits();
    if w <= 64 {
        SmtExpr::var(name, w)
    } else {
        var_128(name)
    }
}

/// Build input descriptors for a symbolic vector variable.
///
/// For 64-bit: `[(name, 64)]`.
/// For 128-bit: `[(name_lo, 64), (name_hi, 64)]`.
fn vector_inputs(name: &str, arrangement: VectorArrangement) -> Vec<(String, u32)> {
    let w = arrangement.total_bits();
    if w <= 64 {
        vec![(name.to_string(), w)]
    } else {
        vec![(format!("{}_lo", name), 64), (format!("{}_hi", name), 64)]
    }
}

/// Build input descriptors for a bitwise op at the given full width.
fn bitwise_inputs(width: u32) -> Vec<(String, u32)> {
    if width <= 64 {
        vec![("vn".to_string(), width), ("vm".to_string(), width)]
    } else {
        vec![
            ("vn_lo".to_string(), 64),
            ("vn_hi".to_string(), 64),
            ("vm_lo".to_string(), 64),
            ("vm_hi".to_string(), 64),
        ]
    }
}

/// Build a symbolic bitvector at the given width (splits at 128).
fn symbolic_bv(name: &str, width: u32) -> SmtExpr {
    if width <= 64 {
        SmtExpr::var(name, width)
    } else {
        var_128(name)
    }
}

// ---------------------------------------------------------------------------
// Vector ADD proofs
// ---------------------------------------------------------------------------

/// Proof: trust_ir vector_add -> NEON ADD at the specified arrangement.
///
/// trust_ir semantics: per-lane `bvadd`.
/// NEON semantics: `encode_neon_add`.
fn proof_vector_add(arrangement: VectorArrangement, label: &str) -> ProofObligation {
    let vn = symbolic_vector("vn", arrangement);
    let vm = symbolic_vector("vm", arrangement);
    let trust_ir_expr = map_lanes_binary(&vn, &vm, arrangement, |a, b| a.bvadd(b));
    let neon_expr = encode_neon_add(arrangement, &vn, &vm);

    let mut inputs = vector_inputs("vn", arrangement);
    inputs.extend(vector_inputs("vm", arrangement));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("VectorAdd -> NEON ADD.{}", label),
        trust_ir_expr,
        aarch64_expr: neon_expr,
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// Proof: trust_ir vector_add -> NEON ADD.2S (64-bit, 2x32-bit lanes).
pub fn proof_vector_add_2s() -> ProofObligation {
    proof_vector_add(VectorArrangement::S2, "2S")
}

/// Proof: trust_ir vector_add -> NEON ADD.4S (128-bit, 4x32-bit lanes).
pub fn proof_vector_add_4s() -> ProofObligation {
    proof_vector_add(VectorArrangement::S4, "4S")
}

// ---------------------------------------------------------------------------
// Vector SUB proofs
// ---------------------------------------------------------------------------

/// Proof: trust_ir vector_sub -> NEON SUB at the specified arrangement.
fn proof_vector_sub(arrangement: VectorArrangement, label: &str) -> ProofObligation {
    let vn = symbolic_vector("vn", arrangement);
    let vm = symbolic_vector("vm", arrangement);
    let trust_ir_expr = map_lanes_binary(&vn, &vm, arrangement, |a, b| a.bvsub(b));
    let neon_expr = encode_neon_sub(arrangement, &vn, &vm);

    let mut inputs = vector_inputs("vn", arrangement);
    inputs.extend(vector_inputs("vm", arrangement));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("VectorSub -> NEON SUB.{}", label),
        trust_ir_expr,
        aarch64_expr: neon_expr,
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// Proof: trust_ir vector_sub -> NEON SUB.4H (64-bit, 4x16-bit lanes).
pub fn proof_vector_sub_4h() -> ProofObligation {
    proof_vector_sub(VectorArrangement::H4, "4H")
}

/// Proof: trust_ir vector_sub -> NEON SUB.8H (128-bit, 8x16-bit lanes).
pub fn proof_vector_sub_8h() -> ProofObligation {
    proof_vector_sub(VectorArrangement::H8, "8H")
}

// ---------------------------------------------------------------------------
// Vector MUL proofs
// ---------------------------------------------------------------------------

/// Proof: trust_ir vector_mul -> NEON MUL at the specified arrangement.
///
/// Note: NEON MUL does not support D2 (64-bit lane) arrangement.
fn proof_vector_mul(arrangement: VectorArrangement, label: &str) -> ProofObligation {
    let vn = symbolic_vector("vn", arrangement);
    let vm = symbolic_vector("vm", arrangement);
    let trust_ir_expr = map_lanes_binary(&vn, &vm, arrangement, |a, b| a.bvmul(b));
    let neon_expr = encode_neon_mul(arrangement, &vn, &vm);

    let mut inputs = vector_inputs("vn", arrangement);
    inputs.extend(vector_inputs("vm", arrangement));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("VectorMul -> NEON MUL.{}", label),
        trust_ir_expr,
        aarch64_expr: neon_expr,
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// Proof: trust_ir vector_mul -> NEON MUL.8B (64-bit, 8x8-bit lanes).
pub fn proof_vector_mul_8b() -> ProofObligation {
    proof_vector_mul(VectorArrangement::B8, "8B")
}

/// Proof: trust_ir vector_mul -> NEON MUL.16B (128-bit, 16x8-bit lanes).
pub fn proof_vector_mul_16b() -> ProofObligation {
    proof_vector_mul(VectorArrangement::B16, "16B")
}

// ---------------------------------------------------------------------------
// Vector NEG proofs
// ---------------------------------------------------------------------------

/// Proof: trust_ir vector_neg -> NEON NEG at the specified arrangement.
fn proof_vector_neg(arrangement: VectorArrangement, label: &str) -> ProofObligation {
    let vn = symbolic_vector("vn", arrangement);
    let trust_ir_expr = map_lanes_unary(&vn, arrangement, |a| a.bvneg());
    let neon_expr = encode_neon_neg(arrangement, &vn);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("VectorNeg -> NEON NEG.{}", label),
        trust_ir_expr,
        aarch64_expr: neon_expr,
        inputs: vector_inputs("vn", arrangement),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// Proof: trust_ir vector_neg -> NEON NEG.2S (64-bit, 2x32-bit lanes).
pub fn proof_vector_neg_2s() -> ProofObligation {
    proof_vector_neg(VectorArrangement::S2, "2S")
}

/// Proof: trust_ir vector_neg -> NEON NEG.2D (128-bit, 2x64-bit lanes).
pub fn proof_vector_neg_2d() -> ProofObligation {
    proof_vector_neg(VectorArrangement::D2, "2D")
}

// ---------------------------------------------------------------------------
// Vector AND proofs
// ---------------------------------------------------------------------------

/// Proof: trust_ir vector_and -> NEON AND at the specified bit-width.
///
/// Bitwise AND is width-agnostic (no lane decomposition).
/// trust_ir: `bvand(vn, vm)`. NEON: `encode_neon_and(vn, vm)`.
fn proof_vector_and(width: u32, label: &str) -> ProofObligation {
    let vn = symbolic_bv("vn", width);
    let vm = symbolic_bv("vm", width);
    let trust_ir_expr = vn.clone().bvand(vm.clone());
    let neon_expr = encode_neon_and(&vn, &vm);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("VectorAnd -> NEON AND.{}", label),
        trust_ir_expr,
        aarch64_expr: neon_expr,
        inputs: bitwise_inputs(width),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// Proof: trust_ir vector_and -> NEON AND.8B (64-bit).
pub fn proof_vector_and_8b() -> ProofObligation {
    proof_vector_and(64, "8B")
}

/// Proof: trust_ir vector_and -> NEON AND.16B (128-bit).
pub fn proof_vector_and_16b() -> ProofObligation {
    proof_vector_and(128, "16B")
}

// ---------------------------------------------------------------------------
// Vector ORR proofs
// ---------------------------------------------------------------------------

/// Proof: trust_ir vector_or -> NEON ORR at the specified bit-width.
fn proof_vector_orr(width: u32, label: &str) -> ProofObligation {
    let vn = symbolic_bv("vn", width);
    let vm = symbolic_bv("vm", width);
    let trust_ir_expr = vn.clone().bvor(vm.clone());
    let neon_expr = encode_neon_orr(&vn, &vm);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("VectorOr -> NEON ORR.{}", label),
        trust_ir_expr,
        aarch64_expr: neon_expr,
        inputs: bitwise_inputs(width),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// Proof: trust_ir vector_or -> NEON ORR.8B (64-bit).
pub fn proof_vector_orr_8b() -> ProofObligation {
    proof_vector_orr(64, "8B")
}

/// Proof: trust_ir vector_or -> NEON ORR.16B (128-bit).
pub fn proof_vector_orr_16b() -> ProofObligation {
    proof_vector_orr(128, "16B")
}

// ---------------------------------------------------------------------------
// Vector EOR proofs
// ---------------------------------------------------------------------------

/// Proof: trust_ir vector_xor -> NEON EOR at the specified bit-width.
fn proof_vector_eor(width: u32, label: &str) -> ProofObligation {
    let vn = symbolic_bv("vn", width);
    let vm = symbolic_bv("vm", width);
    let trust_ir_expr = vn.clone().bvxor(vm.clone());
    let neon_expr = encode_neon_eor(&vn, &vm);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("VectorXor -> NEON EOR.{}", label),
        trust_ir_expr,
        aarch64_expr: neon_expr,
        inputs: bitwise_inputs(width),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// Proof: trust_ir vector_xor -> NEON EOR.8B (64-bit).
pub fn proof_vector_eor_8b() -> ProofObligation {
    proof_vector_eor(64, "8B")
}

/// Proof: trust_ir vector_xor -> NEON EOR.16B (128-bit).
pub fn proof_vector_eor_16b() -> ProofObligation {
    proof_vector_eor(128, "16B")
}

// ---------------------------------------------------------------------------
// Vector BIC proofs
// ---------------------------------------------------------------------------

/// Proof: trust_ir vector_bic (and-not) -> NEON BIC at the specified bit-width.
///
/// trust_ir: `bvand(vn, bvnot(vm))` where bvnot is `bvxor(vm, all_ones)`.
/// NEON: `encode_neon_bic(vn, vm)`.
fn proof_vector_bic(width: u32, label: &str) -> ProofObligation {
    let vn = symbolic_bv("vn", width);
    let vm = symbolic_bv("vm", width);

    // trust_ir BIC semantics: AND with complement of second operand.
    // Build NOT(vm) as XOR with all-ones, then AND with vn.
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
    let trust_ir_expr = vn.clone().bvand(vm.clone().bvxor(all_ones));
    let neon_expr = encode_neon_bic(&vn, &vm);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("VectorBic -> NEON BIC.{}", label),
        trust_ir_expr,
        aarch64_expr: neon_expr,
        inputs: bitwise_inputs(width),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// Proof: trust_ir vector_bic -> NEON BIC.8B (64-bit).
pub fn proof_vector_bic_8b() -> ProofObligation {
    proof_vector_bic(64, "8B")
}

/// Proof: trust_ir vector_bic -> NEON BIC.16B (128-bit).
pub fn proof_vector_bic_16b() -> ProofObligation {
    proof_vector_bic(128, "16B")
}

// ---------------------------------------------------------------------------
// FAITHFUL per-LANE-intent == whole-register NEON bitwise proofs
// ---------------------------------------------------------------------------
//
// SOUNDNESS — these are the obligations the per-compile coverage gate CREDITS
// for NeonAndV/NeonOrrV/NeonEorV/NeonBicV/NeonNotV. The OLDER
// `proof_vector_{and,orr,eor,bic}_*` above pair the trust_ir side with the
// SAME-SHAPE whole-register `encode_neon_*`, so both sides are the IDENTICAL
// `SmtExpr` — a DEGENERATE X==X that `is_genuinely_proven()` rejects and that no
// wrong machine op could ever refute. They prove nothing about the lowering and
// the gate does NOT count them (purely model-consistency / documented debt).
//
// Instead, model the trust_ir INTENT as the genuine per-LANE vector op and
// compare it to the whole-128-bit-register op the lowerer actually emits:
//
//   * SOURCE (trust_ir) = split the two 128-bit inputs into the 16 byte lanes of
//     the emitted `.16B` arrangement, apply the LANE bitwise op, and concat the
//     lanes back (`map_lanes_binary`/`map_lanes_unary` over `lane_extract`).
//   * MACHINE = the single whole-128-bit-register op (`encode_neon_*`): AND =
//     `vn & vm`, ORR = `vn | vm`, EOR = `vn ^ vm`, BIC = `vn & ~vm`, NOT = `~vn`
//     (complement realized as XOR with all-ones, matching `encode_neon_bic/not`,
//     since `SmtExpr` has no bitvector-NOT primitive).
//
// The two sides are STRUCTURALLY DISTINCT (`is_genuinely_proven`, NOT X==X): the
// source is a 16-lane concat tree of per-byte ops over `lane_extract` slices;
// the machine is one op over the full register. They are provably EQUAL because
// bitwise ops are lane-width-INDEPENDENT over the 128-bit register — which is
// ALSO why ONE 128-bit obligation per opcode suffices and is arrangement-
// agnostic (we pick `.16B` to match the actual encoding). A WRONG machine op
// (ORR where the source is AND, or BIC without the `~vm` complement) makes the
// two sides differ on some input and REFUTES.
//
// Emission: the isel emits these on `Type::V128` (isel.rs `select_logic` ~7799
// for AND/ORR/EOR/BIC; the `Mvn` arm ~4303 for NOT); the encoder's `q=1` selects
// the `.16B` whole-register form (encode.rs `NeonAndV`/etc. ~2390+), which is
// exactly what the whole-register machine side models. ARM DDI 0487 C7.2.9 AND /
// C7.2.215 ORR / C7.2.71 EOR / C7.2.15 BIC / C7.2.210 NOT (vector).

/// `.16B` — the byte arrangement the `Type::V128` bitwise ops actually encode to
/// (encoder `q=1`). Used to express the per-LANE intent of the SOURCE side.
const NEON_BITWISE_ARR: VectorArrangement = VectorArrangement::B16;

/// FAITHFUL: trust_ir per-LANE AND (`.16B`) == whole-register NEON `AND.16B`.
///
/// SOURCE = 16-lane concat tree of per-byte `bvand`; MACHINE = single
/// whole-register `vn & vm`. STRUCTURALLY DISTINCT (NOT X==X); a wrong machine
/// op (e.g. `bvor`) REFUTES.
pub fn proof_neon_andv_lanewise_16b() -> ProofObligation {
    let vn = var_128("vn");
    let vm = var_128("vm");
    let source = map_lanes_binary(&vn, &vm, NEON_BITWISE_ARR, |a, b| a.bvand(b));
    let machine = encode_neon_and(&vn, &vm);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "NEON AndV.16B lanewise-intent == whole-register bvand (faithful)".to_string(),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: bitwise_inputs(128),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// FAITHFUL: trust_ir per-LANE OR (`.16B`) == whole-register NEON `ORR.16B`.
pub fn proof_neon_orrv_lanewise_16b() -> ProofObligation {
    let vn = var_128("vn");
    let vm = var_128("vm");
    let source = map_lanes_binary(&vn, &vm, NEON_BITWISE_ARR, |a, b| a.bvor(b));
    let machine = encode_neon_orr(&vn, &vm);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "NEON OrrV.16B lanewise-intent == whole-register bvor (faithful)".to_string(),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: bitwise_inputs(128),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// FAITHFUL: trust_ir per-LANE XOR (`.16B`) == whole-register NEON `EOR.16B`.
pub fn proof_neon_eorv_lanewise_16b() -> ProofObligation {
    let vn = var_128("vn");
    let vm = var_128("vm");
    let source = map_lanes_binary(&vn, &vm, NEON_BITWISE_ARR, |a, b| a.bvxor(b));
    let machine = encode_neon_eor(&vn, &vm);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "NEON EorV.16B lanewise-intent == whole-register bvxor (faithful)".to_string(),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: bitwise_inputs(128),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// FAITHFUL: trust_ir per-LANE BIC (`.16B`, `a & ~b`) == whole-register NEON
/// `BIC.16B`. The per-byte complement is `b ^ 0xFF` (matching `encode_neon_bic`,
/// which has no bitvector-NOT primitive). Omitting the complement on the machine
/// side (modelling plain AND) makes the sides differ and REFUTES.
pub fn proof_neon_bicv_lanewise_16b() -> ProofObligation {
    let vn = var_128("vn");
    let vm = var_128("vm");
    // SOURCE: per-byte `a & ~b` with `~b = b ^ 0xFF` (8-bit lane all-ones).
    let source = map_lanes_binary(&vn, &vm, NEON_BITWISE_ARR, |a, b| {
        a.bvand(b.bvxor(SmtExpr::bv_const(0xFF, 8)))
    });
    let machine = encode_neon_bic(&vn, &vm);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "NEON BicV.16B lanewise-intent (a & ~b) == whole-register bvand-not (faithful)"
            .to_string(),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: bitwise_inputs(128),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// FAITHFUL: trust_ir per-LANE NOT (`.16B`, `~a`) == whole-register NEON
/// `NOT.16B`. Unary; the per-byte complement is `a ^ 0xFF` (matching
/// `encode_neon_not`). MACHINE is the single whole-register `vn ^ all-ones`.
pub fn proof_neon_notv_lanewise_16b() -> ProofObligation {
    let vn = var_128("vn");
    // SOURCE: per-byte `~a` with `~a = a ^ 0xFF` (8-bit lane all-ones).
    let source = map_lanes_unary(&vn, NEON_BITWISE_ARR, |a| {
        a.bvxor(SmtExpr::bv_const(0xFF, 8))
    });
    let machine = encode_neon_not(&vn);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "NEON NotV.16B lanewise-intent (~a) == whole-register bvnot (faithful)".to_string(),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: vec![("vn_lo".to_string(), 64), ("vn_hi".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

// ---------------------------------------------------------------------------
// FAITHFUL per-LANE NEON COMPUTE proofs (D-register-pair decomposition)
// ---------------------------------------------------------------------------
//
// SOUNDNESS — these are the obligations the per-compile coverage gate CREDITS for
// the LANE-WISE integer compute ops (NeonAddV/SubV/MulV, the compares
// CmeqV/CmgeV/CmgtV/CmhiV/CmhsV, the immediate shifts ShlVImm/UshrVImm/SshrVImm,
// and the lane-wise min/max SmaxV/SminV/UmaxV/UminV). Just like the OLDER
// `proof_vector_*` builders (VectorAdd/Sub/Mul/Cmp/Min/Max/Shift), the ACTUAL NEON
// encoders (`encode_neon_add` etc.) are ONE call to `map_lanes_binary` — so
// pairing the trust_ir side with the SAME `map_lanes_binary` call produces the
// IDENTICAL `SmtExpr`, a DEGENERATE X==X that `is_genuinely_proven()` rejects (no
// wrong opcode could refute both-sides-are-the-same-tree). That is exactly why the
// static `proof_vector_*` obligations prove nothing and the gate never counted
// them.
//
// UNLIKE the NEON BITWISE ops above, a lane-wise ADD/CMP/SHIFT has NO whole-
// register single-primitive form (carries and lane masks are blocked at the
// element boundary), and — UNLIKE the i128 ADDS;ADC carry chain — there is NO
// cross-lane carry to reconstruct (NEON lanes are independent). So the faithful
// obligation cannot borrow either of those two structural distinctions.
//
// Instead we model the SOURCE (trust_ir per-lane intent) over the ARM D-REGISTER-
// PAIR view of the 128-bit Q register: a Q register IS architecturally two 64-bit
// D halves `{ Dlo = bits[63:0], Dhi = bits[127:64] }`, and for EVERY 128-bit
// arrangement the lane width divides 64, so each lane lies WHOLLY within one half
// (lanes `[0, 64/lane_bits)` in `Dlo`, the rest in `Dhi`). The SOURCE therefore
// slices lane `i` DIRECTLY from the raw half `Var` (`Extract(Var(vn_lo|vn_hi), …)`)
// and applies the per-lane op; the MACHINE is the real `encode_neon_*` encoder
// operating on the reassembled `Concat(hi, lo)` register
// (`Extract(Concat(vn_hi, vn_lo), …)`). The two sides are STRUCTURALLY DISTINCT
// (raw-half `Var` leaf vs an `Extract`-of-`Concat`), so `is_genuinely_proven()`
// holds and the gate credits them; they are provably EQUAL because slicing a lane
// from its D-half equals slicing the same bit-field from the packed Q register.
//
// WHAT THIS CERTIFIES (honest scope). The obligation pins that the emitted NEON
// instruction computes, in EACH lane, exactly the trust_ir per-lane vector op — so
// a WRONG instruction REFUTES: a wrong operation (SUB for ADD, MUL for ADD), wrong
// SIGNEDNESS (SMAX for UMAX, CMGT for CMHI, USHR for SSHR), wrong COMPARE DIRECTION
// (CMGE for CMGT), or a wrong LANE WIDTH (a different arrangement repacks the
// element boundaries) all make the two sides diverge on some input. This is the
// same guarantee the gate certifies for every other opcode (the lowerer selected
// the RIGHT instruction); it does NOT — and structurally CANNOT — add cross-lane
// reconstruction content, because the lanes are independent. One representative
// `.4S` obligation per opcode suffices: `.4S` (4×32) is the arrangement the
// reduction / vectorization passes actually emit, and the D-pair decomposition is
// arrangement-parametric. The `*_wrong_*_refutes` negative controls +
// `neon_lanewise_compute_proofs_are_non_degenerate` test discharge the refutation
// obligation. Reference: ARM DDI 0487 C7.2 (ADD/SUB/MUL/CMEQ/CMGT/CMGE/CMHI/CMHS/
// SMAX/SMIN/UMAX/UMIN/SHL/USHR/SSHR vector) + B1.2 (Q = {Dlo, Dhi} register view).

/// The 128-bit arrangement the lane-wise reduction / vectorization passes emit for
/// the i32x4 shapes (`neon_arrangement` default `.4S`; the `<4 x i32>` right-shift
/// lowerings emit `NeonUshrVImm`/`NeonSshrVImm` at `.4S`).
const NEON_LANEWISE_ARR: VectorArrangement = VectorArrangement::S4;

/// Slice lane `idx` of a 128-bit vector DIRECTLY from its two 64-bit D-halves
/// (`lo` = bits [63:0], `hi` = bits [127:64]). For every 128-bit arrangement the
/// lane width divides 64, so lane `idx` lies wholly in `lo` (when
/// `idx < 64/lane_bits`) or `hi`. STRUCTURALLY DISTINCT from the machine encoder's
/// `Extract(Concat(hi, lo), …)` (a raw-half `Var` leaf vs an `Extract`-of-`Concat`),
/// which is what makes the paired obligation NON-degenerate.
fn lane_from_halves(
    lo: &SmtExpr,
    hi: &SmtExpr,
    arrangement: VectorArrangement,
    idx: u32,
) -> SmtExpr {
    let lane_bits = arrangement.lane_bits();
    debug_assert!(
        arrangement.total_bits() == 128,
        "D-pair lane slicing is defined for 128-bit arrangements only"
    );
    let lanes_per_half = 64 / lane_bits;
    let (half, local) = if idx < lanes_per_half {
        (lo, idx)
    } else {
        (hi, idx - lanes_per_half)
    };
    let low = local * lane_bits;
    let high = low + lane_bits - 1;
    half.clone().extract(high, low)
}

/// SOURCE side for a binary lane-wise op: slice each lane from the raw D-halves of
/// `vn`/`vm`, apply `op`, reassemble. Independent of the machine encoder's
/// whole-register `Concat` threading.
fn neon_source_binary_from_halves<F>(arrangement: VectorArrangement, op: F) -> SmtExpr
where
    F: Fn(SmtExpr, SmtExpr) -> SmtExpr,
{
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let vm_lo = SmtExpr::var("vm_lo", 64);
    let vm_hi = SmtExpr::var("vm_hi", 64);
    let lanes: Vec<SmtExpr> = (0..arrangement.lane_count())
        .map(|i| {
            let a = lane_from_halves(&vn_lo, &vn_hi, arrangement, i);
            let b = lane_from_halves(&vm_lo, &vm_hi, arrangement, i);
            op(a, b)
        })
        .collect();
    concat_lanes(&lanes, arrangement)
}

/// SOURCE side for an immediate-shift lane-wise op: slice each lane from the raw
/// D-halves of `vn`, apply `op(lane, imm_const)`, reassemble.
fn neon_source_shift_from_halves<F>(arrangement: VectorArrangement, imm: u32, op: F) -> SmtExpr
where
    F: Fn(SmtExpr, SmtExpr) -> SmtExpr,
{
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let lane_bits = arrangement.lane_bits();
    let lanes: Vec<SmtExpr> = (0..arrangement.lane_count())
        .map(|i| {
            let a = lane_from_halves(&vn_lo, &vn_hi, arrangement, i);
            let b = SmtExpr::bv_const(imm as u64, lane_bits);
            op(a, b)
        })
        .collect();
    concat_lanes(&lanes, arrangement)
}

/// Per-lane all-ones / zero mask constants for the given arrangement (the NEON
/// compare-mask convention).
fn lane_mask_consts(arrangement: VectorArrangement) -> (SmtExpr, SmtExpr) {
    let lane_bits = arrangement.lane_bits();
    let all_ones = SmtExpr::bv_const(
        if lane_bits >= 64 {
            u64::MAX
        } else {
            (1u64 << lane_bits) - 1
        },
        lane_bits,
    );
    (all_ones, SmtExpr::bv_const(0, lane_bits))
}

/// Build a per-lane COMPARE-MASK source op from a boolean lane predicate.
fn cmp_mask_op<C>(arrangement: VectorArrangement, cmp: C) -> impl Fn(SmtExpr, SmtExpr) -> SmtExpr
where
    C: Fn(SmtExpr, SmtExpr) -> SmtExpr,
{
    let (all_ones, zero) = lane_mask_consts(arrangement);
    move |a, b| SmtExpr::ite(cmp(a, b), all_ones.clone(), zero.clone())
}

/// Assemble a faithful lane-wise BINARY obligation: D-pair SOURCE vs the real NEON
/// `machine` encoder over the reassembled `Concat(hi, lo)` register.
fn neon_lanewise_binary_obligation<S, M>(
    name: &str,
    arrangement: VectorArrangement,
    source_op: S,
    machine: M,
) -> ProofObligation
where
    S: Fn(SmtExpr, SmtExpr) -> SmtExpr,
    M: Fn(VectorArrangement, &SmtExpr, &SmtExpr) -> SmtExpr,
{
    let vn = var_128("vn");
    let vm = var_128("vm");
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: neon_source_binary_from_halves(arrangement, source_op),
        aarch64_expr: machine(arrangement, &vn, &vm),
        inputs: bitwise_inputs(128),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// Assemble a faithful lane-wise immediate-SHIFT obligation.
fn neon_lanewise_shift_obligation<S, M>(
    name: &str,
    arrangement: VectorArrangement,
    imm: u32,
    source_op: S,
    machine: M,
) -> ProofObligation
where
    S: Fn(SmtExpr, SmtExpr) -> SmtExpr,
    M: Fn(VectorArrangement, &SmtExpr, u32) -> SmtExpr,
{
    let vn = var_128("vn");
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: neon_source_shift_from_halves(arrangement, imm, source_op),
        aarch64_expr: machine(arrangement, &vn, imm),
        inputs: vec![("vn_lo".to_string(), 64), ("vn_hi".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

// -- Arithmetic (ADD / SUB / MUL) -------------------------------------------

/// FAITHFUL: trust_ir per-lane `<4 x i32>` ADD (D-pair) == NEON `ADD.4S`.
pub fn proof_neon_addv_lanewise_4s() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON AddV.4S lanewise-intent == D-pair per-lane bvadd (faithful)",
        NEON_LANEWISE_ARR,
        |a, b| a.bvadd(b),
        encode_neon_add,
    )
}

/// FAITHFUL: trust_ir per-lane `<4 x i32>` SUB (D-pair) == NEON `SUB.4S`.
pub fn proof_neon_subv_lanewise_4s() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON SubV.4S lanewise-intent == D-pair per-lane bvsub (faithful)",
        NEON_LANEWISE_ARR,
        |a, b| a.bvsub(b),
        encode_neon_sub,
    )
}

/// FAITHFUL: trust_ir per-lane `<4 x i32>` MUL (D-pair) == NEON `MUL.4S`.
pub fn proof_neon_mulv_lanewise_4s() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON MulV.4S lanewise-intent == D-pair per-lane bvmul (faithful)",
        NEON_LANEWISE_ARR,
        |a, b| a.bvmul(b),
        encode_neon_mul,
    )
}

// -- Compares (CMEQ / CMGE / CMGT / CMHI / CMHS) ----------------------------

/// FAITHFUL: trust_ir per-lane `<4 x i32>` EQ-mask (D-pair) == NEON `CMEQ.4S`.
pub fn proof_neon_cmeqv_lanewise_4s() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON CmeqV.4S lanewise-intent == D-pair per-lane eq-mask (faithful)",
        NEON_LANEWISE_ARR,
        cmp_mask_op(NEON_LANEWISE_ARR, |a, b| a.eq_expr(b)),
        encode_neon_cmeq,
    )
}

/// FAITHFUL: trust_ir per-lane `<16 x i8>` EQ-mask (D-pair) == NEON `CMEQ.16B`.
///
/// The BYTE-lane sibling of [`proof_neon_cmeqv_lanewise_4s`]. This is the exact
/// obligation the `neon-bytesum` count-if(`==0`) kernel needs: it emits
/// `CMEQ.16B qs[k], vzero` (0xFF per byte lane where the byte `== 0`), so the
/// per-byte-lane EQ mask must be faithful. `encode_neon_cmeq` is
/// arrangement-generic; instantiating it at `.16B` gives 16 independent 8-bit
/// lane comparisons. A wrong per-lane op (e.g. CMGT) or a wrong lane width (a
/// `.4S`/`.8H` re-pack of the byte boundaries) REFUTES (negative control:
/// `WRONG: CmeqV.16B encoded as CMGT.16B must REFUTE`).
pub fn proof_neon_cmeqv_lanewise_16b() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON CmeqV.16B lanewise-intent == D-pair per-lane eq-mask (faithful)",
        VectorArrangement::B16,
        cmp_mask_op(VectorArrangement::B16, |a, b| a.eq_expr(b)),
        encode_neon_cmeq,
    )
}

/// FAITHFUL: trust_ir per-lane `<4 x i32>` signed >= mask (D-pair) == NEON `CMGE.4S`.
pub fn proof_neon_cmgev_lanewise_4s() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON CmgeV.4S lanewise-intent == D-pair per-lane sge-mask (faithful)",
        NEON_LANEWISE_ARR,
        cmp_mask_op(NEON_LANEWISE_ARR, |a, b| a.bvsge(b)),
        encode_neon_cmge,
    )
}

/// FAITHFUL: trust_ir per-lane `<4 x i32>` signed > mask (D-pair) == NEON `CMGT.4S`.
pub fn proof_neon_cmgtv_lanewise_4s() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON CmgtV.4S lanewise-intent == D-pair per-lane sgt-mask (faithful)",
        NEON_LANEWISE_ARR,
        cmp_mask_op(NEON_LANEWISE_ARR, |a, b| a.bvsgt(b)),
        encode_neon_cmgt,
    )
}

/// FAITHFUL: trust_ir per-lane `<4 x i32>` unsigned > mask (D-pair) == NEON `CMHI.4S`.
pub fn proof_neon_cmhiv_lanewise_4s() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON CmhiV.4S lanewise-intent == D-pair per-lane ugt-mask (faithful)",
        NEON_LANEWISE_ARR,
        cmp_mask_op(NEON_LANEWISE_ARR, |a, b| a.bvugt(b)),
        encode_neon_cmhi,
    )
}

/// FAITHFUL: trust_ir per-lane `<4 x i32>` unsigned >= mask (D-pair) == NEON `CMHS.4S`.
pub fn proof_neon_cmhsv_lanewise_4s() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON CmhsV.4S lanewise-intent == D-pair per-lane uge-mask (faithful)",
        NEON_LANEWISE_ARR,
        cmp_mask_op(NEON_LANEWISE_ARR, |a, b| a.bvuge(b)),
        encode_neon_cmhs,
    )
}

// -- Min / Max (SMAX / SMIN / UMAX / UMIN) ----------------------------------

/// FAITHFUL: trust_ir per-lane `<4 x i32>` signed max (D-pair) == NEON `SMAX.4S`.
pub fn proof_neon_smaxv_lanewise_4s() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON SmaxV.4S lanewise-intent == D-pair per-lane smax (faithful)",
        NEON_LANEWISE_ARR,
        |a, b| SmtExpr::ite(a.clone().bvsgt(b.clone()), a, b),
        encode_neon_smax,
    )
}

/// FAITHFUL: trust_ir per-lane `<4 x i32>` signed min (D-pair) == NEON `SMIN.4S`.
pub fn proof_neon_sminv_lanewise_4s() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON SminV.4S lanewise-intent == D-pair per-lane smin (faithful)",
        NEON_LANEWISE_ARR,
        |a, b| SmtExpr::ite(a.clone().bvslt(b.clone()), a, b),
        encode_neon_smin,
    )
}

/// FAITHFUL: trust_ir per-lane `<4 x i32>` unsigned max (D-pair) == NEON `UMAX.4S`.
pub fn proof_neon_umaxv_lanewise_4s() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON UmaxV.4S lanewise-intent == D-pair per-lane umax (faithful)",
        NEON_LANEWISE_ARR,
        |a, b| SmtExpr::ite(a.clone().bvugt(b.clone()), a, b),
        encode_neon_umax,
    )
}

/// FAITHFUL: trust_ir per-lane `<4 x i32>` unsigned min (D-pair) == NEON `UMIN.4S`.
pub fn proof_neon_uminv_lanewise_4s() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON UminV.4S lanewise-intent == D-pair per-lane umin (faithful)",
        NEON_LANEWISE_ARR,
        |a, b| SmtExpr::ite(a.clone().bvult(b.clone()), a, b),
        encode_neon_umin,
    )
}

// -- Immediate shifts (SHL / USHR / SSHR) -----------------------------------

/// Representative in-range shift amounts for the `.4S` (32-bit lane) proofs.
const NEON_SHL_IMM_4S: u32 = 3;
const NEON_USHR_IMM_4S: u32 = 5;
const NEON_SSHR_IMM_4S: u32 = 7;

/// FAITHFUL: trust_ir per-lane `<4 x i32>` left shift (D-pair) == NEON `SHL.4S #3`.
pub fn proof_neon_shlv_lanewise_4s() -> ProofObligation {
    neon_lanewise_shift_obligation(
        "NEON ShlVImm.4S #3 lanewise-intent == D-pair per-lane bvshl (faithful)",
        NEON_LANEWISE_ARR,
        NEON_SHL_IMM_4S,
        |a, b| a.bvshl(b),
        encode_neon_shl,
    )
}

/// FAITHFUL: trust_ir per-lane `<4 x i32>` logical right shift (D-pair) == NEON `USHR.4S #5`.
pub fn proof_neon_ushrv_lanewise_4s() -> ProofObligation {
    neon_lanewise_shift_obligation(
        "NEON UshrVImm.4S #5 lanewise-intent == D-pair per-lane bvlshr (faithful)",
        NEON_LANEWISE_ARR,
        NEON_USHR_IMM_4S,
        |a, b| a.bvlshr(b),
        encode_neon_ushr,
    )
}

/// FAITHFUL: trust_ir per-lane `<4 x i32>` arithmetic right shift (D-pair) == NEON `SSHR.4S #7`.
pub fn proof_neon_sshrv_lanewise_4s() -> ProofObligation {
    neon_lanewise_shift_obligation(
        "NEON SshrVImm.4S #7 lanewise-intent == D-pair per-lane bvashr (faithful)",
        NEON_LANEWISE_ARR,
        NEON_SSHR_IMM_4S,
        |a, b| a.bvashr(b),
        encode_neon_sshr,
    )
}

/// FAITHFUL: trust_ir per-lane `<16 x i8>` logical right shift (D-pair) == NEON
/// `USHR.16B #imm`.
///
/// The BYTE-lane sibling of [`proof_neon_ushrv_lanewise_4s`]. This is the exact
/// obligation the `neon-bytesum` HEX-NIBBLE-sum kernel needs: it emits
/// `USHR.16B qs[k], #4` to isolate each byte's HIGH nibble (`b >> 4`), so the
/// per-byte-lane logical right shift must be faithful. `encode_neon_ushr` is
/// arrangement-generic; instantiating it at `.16B` gives 16 independent 8-bit
/// logical shifts. A wrong per-lane op (SSHR — arithmetic, differs on bytes
/// `>= 0x80`) or a wrong lane width (a `.4S`/`.8H` re-pack that shifts across byte
/// boundaries) REFUTES (negative control:
/// `WRONG: UshrVImm.16B #4 encoded as SSHR.16B must REFUTE`).
pub fn proof_neon_ushrv_lanewise_16b(imm: u32) -> ProofObligation {
    neon_lanewise_shift_obligation(
        &format!("NEON UshrVImm.16B #{imm} lanewise-intent == D-pair per-lane bvlshr (faithful)"),
        VectorArrangement::B16,
        imm,
        |a, b| a.bvlshr(b),
        encode_neon_ushr,
    )
}

/// FAITHFUL: trust_ir per-lane `<16 x i8>` unsigned `>=` mask (D-pair) == NEON
/// `CMHS.16B`.
///
/// The BYTE-lane sibling of [`proof_neon_cmhsv_lanewise_4s`]. The `neon-bytesum`
/// HEX-NIBBLE-sum kernel emits `CMHS.16B nibble, #10`-broadcast (0xFF per byte
/// lane where a nibble `>= 10`, i.e. is a hex letter `a..f`), so the per-byte-lane
/// UNSIGNED `>=` mask must be faithful. `encode_neon_cmhs` is arrangement-generic;
/// instantiating it at `.16B` gives 16 independent 8-bit UNSIGNED comparisons. A
/// wrong per-lane op (CMGE — SIGNED, differs on bytes `>= 0x80`) or a wrong lane
/// width REFUTES (negative control:
/// `WRONG: CmhsV.16B (unsigned) encoded as CMGE.16B (signed) must REFUTE`).
pub fn proof_neon_cmhsv_lanewise_16b() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON CmhsV.16B lanewise-intent == D-pair per-lane uge-mask (faithful)",
        VectorArrangement::B16,
        cmp_mask_op(VectorArrangement::B16, |a, b| a.bvuge(b)),
        encode_neon_cmhs,
    )
}

/// NEGATIVE CONTROLS: for each credited lane-wise opcode, an obligation that keeps
/// the correct D-pair SOURCE but pairs it with a WRONG NEON `machine` encoder (the
/// discriminating mutation per op — wrong operation / signedness / direction).
/// Verifying any of these MUST refute (Invalid / SAT counterexample), proving the
/// faithful obligations genuinely pin the emitted instruction. Shared by the mock
/// (`neon_lanewise_compute_wrong_encodings_refute`) and the real-solver
/// (`ay_bridge::…test_ay_batch_verify_neon_lanewise_compute_proofs`) tests.
pub fn neon_lanewise_wrong_encoding_controls() -> Vec<ProofObligation> {
    let a = NEON_LANEWISE_ARR;
    vec![
        // ADD encoded as SUB, SUB as ADD, MUL as ADD.
        neon_lanewise_binary_obligation(
            "WRONG: AddV.4S encoded as SUB.4S must REFUTE",
            a,
            |x, y| x.bvadd(y),
            encode_neon_sub,
        ),
        neon_lanewise_binary_obligation(
            "WRONG: SubV.4S encoded as ADD.4S must REFUTE",
            a,
            |x, y| x.bvsub(y),
            encode_neon_add,
        ),
        neon_lanewise_binary_obligation(
            "WRONG: MulV.4S encoded as ADD.4S must REFUTE",
            a,
            |x, y| x.bvmul(y),
            encode_neon_add,
        ),
        // CMEQ as CMGT; CMGE as CMGT (>= vs >); CMGT as CMGE.
        neon_lanewise_binary_obligation(
            "WRONG: CmeqV.4S encoded as CMGT.4S must REFUTE",
            a,
            cmp_mask_op(a, |x, y| x.eq_expr(y)),
            encode_neon_cmgt,
        ),
        // The `.16B` byte-lane CMEQ (the count-if kernel's mask op): a wrong
        // per-lane op (CMGT) or wrong lane width must refute.
        neon_lanewise_binary_obligation(
            "WRONG: CmeqV.16B encoded as CMGT.16B must REFUTE",
            VectorArrangement::B16,
            cmp_mask_op(VectorArrangement::B16, |x, y| x.eq_expr(y)),
            encode_neon_cmgt,
        ),
        neon_lanewise_binary_obligation(
            "WRONG: CmgeV.4S encoded as CMGT.4S must REFUTE",
            a,
            cmp_mask_op(a, |x, y| x.bvsge(y)),
            encode_neon_cmgt,
        ),
        neon_lanewise_binary_obligation(
            "WRONG: CmgtV.4S encoded as CMGE.4S must REFUTE",
            a,
            cmp_mask_op(a, |x, y| x.bvsgt(y)),
            encode_neon_cmge,
        ),
        // CMHI (unsigned >) as CMGT (signed >); CMHS (unsigned >=) as CMGE.
        neon_lanewise_binary_obligation(
            "WRONG: CmhiV.4S (unsigned) encoded as CMGT.4S (signed) must REFUTE",
            a,
            cmp_mask_op(a, |x, y| x.bvugt(y)),
            encode_neon_cmgt,
        ),
        neon_lanewise_binary_obligation(
            "WRONG: CmhsV.4S (unsigned) encoded as CMGE.4S (signed) must REFUTE",
            a,
            cmp_mask_op(a, |x, y| x.bvuge(y)),
            encode_neon_cmge,
        ),
        // SMAX as SMIN; SMIN as SMAX; UMAX (unsigned) as SMAX (signed); UMIN as UMAX.
        neon_lanewise_binary_obligation(
            "WRONG: SmaxV.4S encoded as SMIN.4S must REFUTE",
            a,
            |x, y| SmtExpr::ite(x.clone().bvsgt(y.clone()), x, y),
            encode_neon_smin,
        ),
        neon_lanewise_binary_obligation(
            "WRONG: SminV.4S encoded as SMAX.4S must REFUTE",
            a,
            |x, y| SmtExpr::ite(x.clone().bvslt(y.clone()), x, y),
            encode_neon_smax,
        ),
        neon_lanewise_binary_obligation(
            "WRONG: UmaxV.4S (unsigned) encoded as SMAX.4S (signed) must REFUTE",
            a,
            |x, y| SmtExpr::ite(x.clone().bvugt(y.clone()), x, y),
            encode_neon_smax,
        ),
        neon_lanewise_binary_obligation(
            "WRONG: UminV.4S encoded as UMAX.4S must REFUTE",
            a,
            |x, y| SmtExpr::ite(x.clone().bvult(y.clone()), x, y),
            encode_neon_umax,
        ),
        // SHL as USHR; USHR (logical) as SSHR (arithmetic); SSHR as USHR.
        neon_lanewise_shift_obligation(
            "WRONG: ShlVImm.4S #3 encoded as USHR.4S must REFUTE",
            a,
            NEON_SHL_IMM_4S,
            |x, y| x.bvshl(y),
            encode_neon_ushr,
        ),
        neon_lanewise_shift_obligation(
            "WRONG: UshrVImm.4S #5 (logical) encoded as SSHR.4S (arithmetic) must REFUTE",
            a,
            NEON_USHR_IMM_4S,
            |x, y| x.bvlshr(y),
            encode_neon_sshr,
        ),
        neon_lanewise_shift_obligation(
            "WRONG: SshrVImm.4S #7 (arithmetic) encoded as USHR.4S (logical) must REFUTE",
            a,
            NEON_SSHR_IMM_4S,
            |x, y| x.bvashr(y),
            encode_neon_ushr,
        ),
        // The `.16B` byte-lane USHR #4 (the hex-nibble kernel's high-nibble isolate):
        // encoding it as SSHR.16B (arithmetic) diverges on bytes `>= 0x80` — must
        // REFUTE.
        neon_lanewise_shift_obligation(
            "WRONG: UshrVImm.16B #4 (logical) encoded as SSHR.16B (arithmetic) must REFUTE",
            VectorArrangement::B16,
            4,
            |x, y| x.bvlshr(y),
            encode_neon_sshr,
        ),
        // The `.16B` byte-lane CMHS #10 (the hex-nibble kernel's hex-letter mask):
        // encoding the UNSIGNED `>=` as the SIGNED CMGE.16B diverges on bytes
        // `>= 0x80` — must REFUTE.
        neon_lanewise_binary_obligation(
            "WRONG: CmhsV.16B (unsigned) encoded as CMGE.16B (signed) must REFUTE",
            VectorArrangement::B16,
            cmp_mask_op(VectorArrangement::B16, |x, y| x.bvuge(y)),
            encode_neon_cmge,
        ),
    ]
}

/// All 18 FAITHFUL lane-wise-compute obligations the coverage gate CREDITS for the
/// NEON arith / compare / min-max / shift opcodes. One representative `.4S`
/// obligation per opcode, PLUS the `.16B` byte-lane `CMEQ` the `neon-bytesum`
/// count-if(`==0`) kernel emits (a second arrangement of `NeonCmeqV`).
pub fn all_neon_lanewise_compute_proofs() -> Vec<ProofObligation> {
    vec![
        proof_neon_addv_lanewise_4s(),
        proof_neon_subv_lanewise_4s(),
        proof_neon_mulv_lanewise_4s(),
        proof_neon_cmeqv_lanewise_4s(),
        proof_neon_cmeqv_lanewise_16b(),
        proof_neon_cmgev_lanewise_4s(),
        proof_neon_cmgtv_lanewise_4s(),
        proof_neon_cmhiv_lanewise_4s(),
        proof_neon_cmhsv_lanewise_4s(),
        proof_neon_smaxv_lanewise_4s(),
        proof_neon_sminv_lanewise_4s(),
        proof_neon_umaxv_lanewise_4s(),
        proof_neon_uminv_lanewise_4s(),
        proof_neon_shlv_lanewise_4s(),
        proof_neon_ushrv_lanewise_4s(),
        proof_neon_sshrv_lanewise_4s(),
        // The `.16B` byte-lane USHR #4 (high-nibble isolate) and CMHS #10 (hex-letter
        // mask) the `neon-bytesum` HEX-NIBBLE-sum kernel emits — a second arrangement
        // of `NeonUshrVImm` / `NeonCmhsV`.
        proof_neon_ushrv_lanewise_16b(4),
        proof_neon_cmhsv_lanewise_16b(),
    ]
}

// ---------------------------------------------------------------------------
// FAITHFUL per-LANE NEON BIT (bitwise insert if true) proof
// ---------------------------------------------------------------------------
//
// SOUNDNESS — credits the coverage gate for `NeonBitV`, the tied-destination
// bitwise select the i64 (`.2D`) min/max reduction pairs with `CMGT/CMHI.2D`
// (clang's exact shape — no `.2D` SMAX/SMIN/UMAX/UMIN exists). Like the other
// NEON bitwise ops, BIT is lane-width-INDEPENDENT, so ONE `.16B` per-lane
// obligation suffices: the SOURCE applies the per-BYTE insert
// `d ^ ((d ^ n) & m)` over the 16 byte lanes (Extract-of-Concat slices); the
// MACHINE is the single whole-register `encode_neon_bit`. STRUCTURALLY
// DISTINCT, so `is_genuinely_proven()` holds. The negative controls pin the
// three confusable mutations in the BSL/BIT/BIF family (the `size` field is
// the operand-WIRING selector there): BIT-as-BIF (inverted mask polarity —
// inserts where the mask is 0), BIT-as-BSL (the mask is Vd, not Vm), and
// BIT-as-AND (no insert at all). Each REFUTES.
// Reference: ARM DDI 0487 C7.2.16 BIT, C7.2.15 BIF, C7.2.18 BSL.

/// Inputs for the 3-operand BIT obligation (Vd tied + Vn + Vm, 128-bit each).
fn bit_inputs() -> Vec<(String, u32)> {
    vec![
        ("vd_lo".to_string(), 64),
        ("vd_hi".to_string(), 64),
        ("vn_lo".to_string(), 64),
        ("vn_hi".to_string(), 64),
        ("vm_lo".to_string(), 64),
        ("vm_hi".to_string(), 64),
    ]
}

/// SOURCE side for BIT: per-byte `d ^ ((d ^ n) & m)` over the `.16B` lanes.
fn bit_source_lanewise_16b() -> SmtExpr {
    let vd = var_128("vd");
    let vn = var_128("vn");
    let vm = var_128("vm");
    let arr = VectorArrangement::B16;
    let lanes: Vec<SmtExpr> = (0..arr.lane_count())
        .map(|i| {
            let d = lane_extract(&vd, arr, i);
            let n = lane_extract(&vn, arr, i);
            let m = lane_extract(&vm, arr, i);
            d.clone().bvxor(d.bvxor(n).bvand(m))
        })
        .collect();
    concat_lanes(&lanes, arr)
}

/// FAITHFUL: per-BYTE `.16B` insert-if-true == whole-register NEON `BIT.16B`.
pub fn proof_neon_bitv_lanewise_16b() -> ProofObligation {
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "NEON BitV.16B lanewise-intent == whole-register d^((d^n)&m) (faithful)".to_string(),
        trust_ir_expr: bit_source_lanewise_16b(),
        aarch64_expr: encode_neon_bit(&var_128("vd"), &var_128("vn"), &var_128("vm")),
        inputs: bit_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// NEGATIVE CONTROLS for `NeonBitV`: correct per-byte SOURCE paired with the
/// WRONG whole-register op. Each MUST refute:
///   * BIT-as-BIF: inverted mask polarity (`d ^ ((d ^ n) & ~m)`) — inserts
///     where the mask is 0 instead of 1 (the min-vs-max flip).
///   * BIT-as-BSL: wrong operand wiring (`(n & d) | (m & ~d)` — Vd is the
///     mask in BSL, not the kept value).
///   * BIT-as-AND: no insert at all (`n & m`).
pub fn neon_bit_wrong_encoding_controls() -> Vec<ProofObligation> {
    let vd = var_128("vd");
    let vn = var_128("vn");
    let vm = var_128("vm");
    let all_ones = SmtExpr::bv_const(u64::MAX, 64).concat(SmtExpr::bv_const(u64::MAX, 64));
    let wrong_bif = vd.clone().bvxor(
        vd.clone()
            .bvxor(vn.clone())
            .bvand(vm.clone().bvxor(all_ones.clone())),
    );
    let wrong_bsl = vn
        .clone()
        .bvand(vd.clone())
        .bvor(vm.clone().bvand(vd.clone().bvxor(all_ones)));
    let wrong_and = vn.clone().bvand(vm.clone());
    let mk = |name: &str, machine: SmtExpr| ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: bit_source_lanewise_16b(),
        aarch64_expr: machine,
        inputs: bit_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    };
    vec![
        mk(
            "WRONG: BitV.16B encoded as BIF (inverted mask) must REFUTE",
            wrong_bif,
        ),
        mk(
            "WRONG: BitV.16B encoded as BSL (Vd-as-mask wiring) must REFUTE",
            wrong_bsl,
        ),
        mk("WRONG: BitV.16B encoded as AND must REFUTE", wrong_and),
    ]
}

/// The 1 FAITHFUL BIT obligation the coverage gate CREDITS for `NeonBitV`.
pub fn all_neon_bit_proofs() -> Vec<ProofObligation> {
    vec![proof_neon_bitv_lanewise_16b()]
}

// ---------------------------------------------------------------------------
// FAITHFUL per-LANE NEON COMPUTE proofs at `.2D` (2 x i64 lanes)
// ---------------------------------------------------------------------------
//
// SOUNDNESS — the i64 (`.2D`) vectorizer paths (neon_array's i64 sum, and the
// width-parameterized neon_predsum / neon_minmax / neon_map i64 paths) emit the
// SAME lane-wise opcodes at the `.2D` arrangement (arrangement imm code 6):
// ADD/SUB, the five compares CMEQ/CMGT/CMGE/CMHI/CMHS, and the immediate shifts
// SHL/USHR/SSHR. Every one of these opcodes ALLOCATES a 64-bit-lane form in the
// ISA (ARM DDI 0487 "Advanced SIMD three same"/"shift by immediate", size==11 /
// immh=1xxx) — unlike MUL/SMAX/SMIN/UMAX/UMIN, whose `.2D` forms are RESERVED
// and which the encoder now REJECTS fail-closed (`encode_int_vec3_same`).
//
// The `.4S` obligations above pin the right OPERATION but a `.2D` emission also
// depends on the right LANE WIDTH: a 64-bit-lane add has carries crossing bit 31
// within each D half, and a 64-bit compare masks the WHOLE half. So each op the
// i64 paths emit gets its own D-pair obligation at `.2D` — the identical
// D-register-pair construction (`lane_from_halves` degenerates to lane0 = the
// raw `vn_lo` Var, lane1 = `vn_hi`; the MACHINE side extracts the same fields
// from `Concat(vn_hi, vn_lo)`) — STRUCTURALLY DISTINCT, hence genuinely proven,
// and REFUTABLE: the negative controls below include the per-op discriminating
// mutation AND a WRONG-ARRANGEMENT control (`.2D` source vs `.4S` machine),
// which diverges whenever a carry crosses a 32-bit lane boundary.

/// The `.2D` (2 x i64) arrangement the i64 vectorizer paths emit.
const NEON_LANEWISE_ARR_2D: VectorArrangement = VectorArrangement::D2;

/// FAITHFUL: per-lane `<2 x i64>` ADD (D-pair) == NEON `ADD.2D`.
pub fn proof_neon_addv_lanewise_2d() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON AddV.2D lanewise-intent == D-pair per-lane bvadd (faithful)",
        NEON_LANEWISE_ARR_2D,
        |a, b| a.bvadd(b),
        encode_neon_add,
    )
}

/// FAITHFUL: per-lane `<2 x i64>` SUB (D-pair) == NEON `SUB.2D`.
pub fn proof_neon_subv_lanewise_2d() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON SubV.2D lanewise-intent == D-pair per-lane bvsub (faithful)",
        NEON_LANEWISE_ARR_2D,
        |a, b| a.bvsub(b),
        encode_neon_sub,
    )
}

/// FAITHFUL: per-lane `<2 x i64>` EQ-mask (D-pair) == NEON `CMEQ.2D`.
pub fn proof_neon_cmeqv_lanewise_2d() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON CmeqV.2D lanewise-intent == D-pair per-lane eq-mask (faithful)",
        NEON_LANEWISE_ARR_2D,
        cmp_mask_op(NEON_LANEWISE_ARR_2D, |a, b| a.eq_expr(b)),
        encode_neon_cmeq,
    )
}

/// FAITHFUL: per-lane `<2 x i64>` signed >= mask (D-pair) == NEON `CMGE.2D`.
pub fn proof_neon_cmgev_lanewise_2d() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON CmgeV.2D lanewise-intent == D-pair per-lane sge-mask (faithful)",
        NEON_LANEWISE_ARR_2D,
        cmp_mask_op(NEON_LANEWISE_ARR_2D, |a, b| a.bvsge(b)),
        encode_neon_cmge,
    )
}

/// FAITHFUL: per-lane `<2 x i64>` signed > mask (D-pair) == NEON `CMGT.2D`.
pub fn proof_neon_cmgtv_lanewise_2d() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON CmgtV.2D lanewise-intent == D-pair per-lane sgt-mask (faithful)",
        NEON_LANEWISE_ARR_2D,
        cmp_mask_op(NEON_LANEWISE_ARR_2D, |a, b| a.bvsgt(b)),
        encode_neon_cmgt,
    )
}

/// FAITHFUL: per-lane `<2 x i64>` unsigned > mask (D-pair) == NEON `CMHI.2D`.
pub fn proof_neon_cmhiv_lanewise_2d() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON CmhiV.2D lanewise-intent == D-pair per-lane ugt-mask (faithful)",
        NEON_LANEWISE_ARR_2D,
        cmp_mask_op(NEON_LANEWISE_ARR_2D, |a, b| a.bvugt(b)),
        encode_neon_cmhi,
    )
}

/// FAITHFUL: per-lane `<2 x i64>` unsigned >= mask (D-pair) == NEON `CMHS.2D`.
pub fn proof_neon_cmhsv_lanewise_2d() -> ProofObligation {
    neon_lanewise_binary_obligation(
        "NEON CmhsV.2D lanewise-intent == D-pair per-lane uge-mask (faithful)",
        NEON_LANEWISE_ARR_2D,
        cmp_mask_op(NEON_LANEWISE_ARR_2D, |a, b| a.bvuge(b)),
        encode_neon_cmhs,
    )
}

/// Representative in-range shift amounts for the `.2D` (64-bit lane) proofs.
/// Chosen ABOVE 31 so a 32-bit-lane (wrong-arrangement) implementation cannot
/// even represent them — the width is load-bearing, not just the operation.
const NEON_SHL_IMM_2D: u32 = 33;
const NEON_USHR_IMM_2D: u32 = 35;
const NEON_SSHR_IMM_2D: u32 = 37;

/// FAITHFUL: per-lane `<2 x i64>` left shift (D-pair) == NEON `SHL.2D #33`.
pub fn proof_neon_shlv_lanewise_2d() -> ProofObligation {
    neon_lanewise_shift_obligation(
        "NEON ShlVImm.2D #33 lanewise-intent == D-pair per-lane bvshl (faithful)",
        NEON_LANEWISE_ARR_2D,
        NEON_SHL_IMM_2D,
        |a, b| a.bvshl(b),
        encode_neon_shl,
    )
}

/// FAITHFUL: per-lane `<2 x i64>` logical right shift (D-pair) == NEON `USHR.2D #35`.
pub fn proof_neon_ushrv_lanewise_2d() -> ProofObligation {
    neon_lanewise_shift_obligation(
        "NEON UshrVImm.2D #35 lanewise-intent == D-pair per-lane bvlshr (faithful)",
        NEON_LANEWISE_ARR_2D,
        NEON_USHR_IMM_2D,
        |a, b| a.bvlshr(b),
        encode_neon_ushr,
    )
}

/// FAITHFUL: per-lane `<2 x i64>` arithmetic right shift (D-pair) == NEON `SSHR.2D #37`.
pub fn proof_neon_sshrv_lanewise_2d() -> ProofObligation {
    neon_lanewise_shift_obligation(
        "NEON SshrVImm.2D #37 lanewise-intent == D-pair per-lane bvashr (faithful)",
        NEON_LANEWISE_ARR_2D,
        NEON_SSHR_IMM_2D,
        |a, b| a.bvashr(b),
        encode_neon_sshr,
    )
}

/// All 10 FAITHFUL `.2D` lane-wise-compute obligations — one per op the i64
/// (`.2D`) vectorizer paths emit. MUL/SMAX/SMIN/UMAX/UMIN have NO `.2D` form in
/// the ISA (encoder-rejected fail-closed), so there is nothing to prove for
/// them: the passes BAIL instead of emitting.
pub fn all_neon_lanewise_compute_proofs_2d() -> Vec<ProofObligation> {
    vec![
        proof_neon_addv_lanewise_2d(),
        proof_neon_subv_lanewise_2d(),
        proof_neon_cmeqv_lanewise_2d(),
        proof_neon_cmgev_lanewise_2d(),
        proof_neon_cmgtv_lanewise_2d(),
        proof_neon_cmhiv_lanewise_2d(),
        proof_neon_cmhsv_lanewise_2d(),
        proof_neon_shlv_lanewise_2d(),
        proof_neon_ushrv_lanewise_2d(),
        proof_neon_sshrv_lanewise_2d(),
    ]
}

/// NEGATIVE CONTROLS for the `.2D` obligations: correct D-pair SOURCE paired
/// with a WRONG NEON `machine` encoder. 10 per-op discriminating mutations
/// (wrong operation / signedness / direction — the same axes as the `.4S`
/// controls) PLUS one WRONG-ARRANGEMENT control (`.2D` source vs `.4S` machine),
/// which diverges whenever a carry/borrow crosses a 32-bit lane boundary —
/// pinning that the LANE WIDTH itself is load-bearing. Each MUST refute.
pub fn neon_lanewise_wrong_encoding_controls_2d() -> Vec<ProofObligation> {
    let a = NEON_LANEWISE_ARR_2D;
    // Wrong-arrangement machine: the encoder invoked at `.4S` instead of `.2D`.
    let add_4s_machine = |_arr: VectorArrangement, vn: &SmtExpr, vm: &SmtExpr| -> SmtExpr {
        encode_neon_add(VectorArrangement::S4, vn, vm)
    };
    vec![
        neon_lanewise_binary_obligation(
            "WRONG: AddV.2D encoded as SUB.2D must REFUTE",
            a,
            |x, y| x.bvadd(y),
            encode_neon_sub,
        ),
        neon_lanewise_binary_obligation(
            "WRONG: SubV.2D encoded as ADD.2D must REFUTE",
            a,
            |x, y| x.bvsub(y),
            encode_neon_add,
        ),
        neon_lanewise_binary_obligation(
            "WRONG: CmeqV.2D encoded as CMGT.2D must REFUTE",
            a,
            cmp_mask_op(a, |x, y| x.eq_expr(y)),
            encode_neon_cmgt,
        ),
        neon_lanewise_binary_obligation(
            "WRONG: CmgeV.2D encoded as CMGT.2D must REFUTE",
            a,
            cmp_mask_op(a, |x, y| x.bvsge(y)),
            encode_neon_cmgt,
        ),
        neon_lanewise_binary_obligation(
            "WRONG: CmgtV.2D encoded as CMGE.2D must REFUTE",
            a,
            cmp_mask_op(a, |x, y| x.bvsgt(y)),
            encode_neon_cmge,
        ),
        neon_lanewise_binary_obligation(
            "WRONG: CmhiV.2D (unsigned) encoded as CMGT.2D (signed) must REFUTE",
            a,
            cmp_mask_op(a, |x, y| x.bvugt(y)),
            encode_neon_cmgt,
        ),
        neon_lanewise_binary_obligation(
            "WRONG: CmhsV.2D (unsigned) encoded as CMGE.2D (signed) must REFUTE",
            a,
            cmp_mask_op(a, |x, y| x.bvuge(y)),
            encode_neon_cmge,
        ),
        neon_lanewise_shift_obligation(
            "WRONG: ShlVImm.2D #33 encoded as USHR.2D must REFUTE",
            a,
            NEON_SHL_IMM_2D,
            |x, y| x.bvshl(y),
            encode_neon_ushr,
        ),
        neon_lanewise_shift_obligation(
            "WRONG: UshrVImm.2D #35 (logical) encoded as SSHR.2D (arithmetic) must REFUTE",
            a,
            NEON_USHR_IMM_2D,
            |x, y| x.bvlshr(y),
            encode_neon_sshr,
        ),
        neon_lanewise_shift_obligation(
            "WRONG: SshrVImm.2D #37 (arithmetic) encoded as USHR.2D (logical) must REFUTE",
            a,
            NEON_SSHR_IMM_2D,
            |x, y| x.bvashr(y),
            encode_neon_ushr,
        ),
        neon_lanewise_binary_obligation(
            "WRONG-ARRANGEMENT: AddV.2D encoded as ADD.4S must REFUTE",
            a,
            |x, y| x.bvadd(y),
            add_4s_machine,
        ),
    ]
}

// ---------------------------------------------------------------------------
// FAITHFUL per-LANE NEON POPCOUNT-FOLD proofs (CNT + UADDLP)
// ---------------------------------------------------------------------------
//
// SOUNDNESS — these credit the coverage gate for the two population-count-fold
// ops the ctpop-reduction lowering emits: `NeonCntV` (per-byte popcount) and
// `NeonUaddlpV` (unsigned add long pairwise, the widening `.16B→.8H` and
// `.8H→.4S` collapses). Chained, they compute the per-i32-lane popcount:
// `CNT.16B` gives 16 byte-popcounts, then two `UADDLP` collapse each 4-byte
// group into one 32-bit count.
//
// Same D-REGISTER-PAIR faithful obligation as the lane-wise compute proofs: the
// SOURCE slices each INPUT lane DIRECTLY from the two 64-bit D-halves of the Q
// register (`Extract(Var(vn_lo|vn_hi), …)`) and applies the per-lane
// popcount/pairwise-widen; the MACHINE is the real `encode_neon_cnt` /
// `encode_neon_uaddlp` encoder over the reassembled whole register
// (`Extract(Concat(hi, lo), …)`). STRUCTURALLY DISTINCT (raw-half `Var` leaf vs
// an `Extract`-of-`Concat`), so `is_genuinely_proven()` holds; provably EQUAL
// because slicing a lane from its D-half equals slicing the same bit-field from
// the packed register. A WRONG encoding REFUTES (see
// `neon_popcount_wrong_encoding_controls`): CNT-as-identity (a passthrough that
// is not counting bits), and UADDLP-as-pairwise-SUBTRACT (wrong pairwise op).
//
// HONEST SCOPE: byte popcount and pairwise-adjacent widening add are BOTH
// lane-local within each output lane's contributing input lanes (no cross-Q
// carry beyond the modeled pair), so the D-pair obligation is exact — CNT's byte
// lanes lie wholly in one half, and each UADDLP output lane is the widened sum
// of two adjacent input lanes that lie in the same half for the arrangements we
// emit (`.16B→.8H`: bytes 2k/2k+1 share a half; `.8H→.4S`: halfwords 2k/2k+1
// share a half). Reference: ARM DDI 0487 C7.2.34 CNT, C7.2.351 UADDLP.

/// The byte arrangement `CNT.16B` operates on (the popcount-fold's first step).
const NEON_CNT_ARR: VectorArrangement = VectorArrangement::B16;

/// SOURCE side for `CNT.16B`: slice each byte lane from the raw D-halves of `vn`
/// and apply the per-byte popcount, then reassemble. Independent of the machine
/// encoder's whole-register `Concat` threading (so the obligation is
/// non-degenerate).
fn neon_source_cnt_from_halves(arrangement: VectorArrangement) -> SmtExpr {
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let lanes: Vec<SmtExpr> = (0..arrangement.lane_count())
        .map(|i| {
            let byte = lane_from_halves(&vn_lo, &vn_hi, arrangement, i);
            source_popcount_lane(&byte, arrangement.lane_bits())
        })
        .collect();
    concat_lanes(&lanes, arrangement)
}

/// Per-lane popcount for the SOURCE side (identical formula to the machine
/// encoder's private `popcount_lane`, so the two sides differ ONLY in the sliced
/// leaf — the D-half `Var` vs the `Concat`-of-halves — which is exactly the
/// non-degeneracy distinction).
fn source_popcount_lane(a: &SmtExpr, bits: u32) -> SmtExpr {
    let bit = |k: u32| a.clone().extract(k, k).zero_ext(bits - 1);
    let mut acc = bit(0);
    for k in 1..bits {
        acc = acc.bvadd(bit(k));
    }
    acc
}

/// SOURCE side for `UADDLP` (widening pairwise add): slice each INPUT lane from
/// the raw D-halves of `vn`, sum adjacent pairs zero-extended to double width,
/// reassemble the (half-count, double-width) output.
fn neon_source_uaddlp_from_halves(in_arr: VectorArrangement) -> SmtExpr {
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let in_bits = in_arr.lane_bits();
    let out_count = in_arr.lane_count() / 2;
    let lanes: Vec<SmtExpr> = (0..out_count)
        .map(|k| {
            let lo = lane_from_halves(&vn_lo, &vn_hi, in_arr, 2 * k).zero_ext(in_bits);
            let hi = lane_from_halves(&vn_lo, &vn_hi, in_arr, 2 * k + 1).zero_ext(in_bits);
            lo.bvadd(hi)
        })
        .collect();
    lane_concat(&lanes)
}

/// Assemble a faithful lane-wise UNARY obligation: D-pair SOURCE vs the real NEON
/// `machine` encoder over the reassembled `Concat(hi, lo)` register.
fn neon_unary_obligation(name: &str, source: SmtExpr, machine: SmtExpr) -> ProofObligation {
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: vec![("vn_lo".to_string(), 64), ("vn_hi".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// FAITHFUL: trust_ir per-byte `.16B` popcount (D-pair) == NEON `CNT.16B`.
pub fn proof_neon_cntv_lanewise_16b() -> ProofObligation {
    neon_unary_obligation(
        "NEON CntV.16B lanewise-intent == D-pair per-byte popcount (faithful)",
        neon_source_cnt_from_halves(NEON_CNT_ARR),
        encode_neon_cnt(NEON_CNT_ARR, &var_128("vn")),
    )
}

/// FAITHFUL: trust_ir pairwise-widening add `.16B->.8H` (D-pair) == NEON `UADDLP.8H`.
pub fn proof_neon_uaddlpv_16b_8h() -> ProofObligation {
    neon_unary_obligation(
        "NEON UaddlpV.16B->.8H lanewise-intent == D-pair pairwise zext-add (faithful)",
        neon_source_uaddlp_from_halves(VectorArrangement::B16),
        encode_neon_uaddlp(VectorArrangement::B16, &var_128("vn")),
    )
}

/// FAITHFUL: trust_ir pairwise-widening add `.8H->.4S` (D-pair) == NEON `UADDLP.4S`.
pub fn proof_neon_uaddlpv_8h_4s() -> ProofObligation {
    neon_unary_obligation(
        "NEON UaddlpV.8H->.4S lanewise-intent == D-pair pairwise zext-add (faithful)",
        neon_source_uaddlp_from_halves(VectorArrangement::H8),
        encode_neon_uaddlp(VectorArrangement::H8, &var_128("vn")),
    )
}

/// NEGATIVE CONTROLS for the popcount-fold ops: correct D-pair SOURCE paired with
/// a WRONG NEON `machine` encoder. Each MUST refute (SAT counterexample):
///   * CNT.16B as IDENTITY (a passthrough that does not count bits).
///   * UADDLP as pairwise SUBTRACT (wrong pairwise op — differs whenever the two
///     paired lanes are unequal).
pub fn neon_popcount_wrong_encoding_controls() -> Vec<ProofObligation> {
    // Wrong CNT: identity (each output byte = the input byte, uncounted).
    let wrong_cnt_identity =
        |arr: VectorArrangement, vn: &SmtExpr| -> SmtExpr { map_lanes_unary(vn, arr, |a| a) };
    // Wrong UADDLP: pairwise widening SUBTRACT instead of ADD.
    let wrong_uaddlp_sub = |in_arr: VectorArrangement, vn: &SmtExpr| -> SmtExpr {
        let in_bits = in_arr.lane_bits();
        let out_count = in_arr.lane_count() / 2;
        let lanes: Vec<SmtExpr> = (0..out_count)
            .map(|k| {
                let lo = lane_extract(vn, in_arr, 2 * k).zero_ext(in_bits);
                let hi = lane_extract(vn, in_arr, 2 * k + 1).zero_ext(in_bits);
                lo.bvsub(hi)
            })
            .collect();
        lane_concat(&lanes)
    };
    vec![
        neon_unary_obligation(
            "WRONG: CntV.16B encoded as IDENTITY must REFUTE",
            neon_source_cnt_from_halves(NEON_CNT_ARR),
            wrong_cnt_identity(NEON_CNT_ARR, &var_128("vn")),
        ),
        neon_unary_obligation(
            "WRONG: UaddlpV.16B->.8H encoded as pairwise SUB must REFUTE",
            neon_source_uaddlp_from_halves(VectorArrangement::B16),
            wrong_uaddlp_sub(VectorArrangement::B16, &var_128("vn")),
        ),
        neon_unary_obligation(
            "WRONG: UaddlpV.8H->.4S encoded as pairwise SUB must REFUTE",
            neon_source_uaddlp_from_halves(VectorArrangement::H8),
            wrong_uaddlp_sub(VectorArrangement::H8, &var_128("vn")),
        ),
    ]
}

/// The 3 FAITHFUL popcount-fold obligations the coverage gate CREDITS for
/// `NeonCntV` and `NeonUaddlpV` (`.16B->.8H` and `.8H->.4S`).
pub fn all_neon_popcount_proofs() -> Vec<ProofObligation> {
    vec![
        proof_neon_cntv_lanewise_16b(),
        proof_neon_uaddlpv_16b_8h(),
        proof_neon_uaddlpv_8h_4s(),
    ]
}

// ---------------------------------------------------------------------------
// FAITHFUL per-LANE NEON SIGNED add-long-pairwise proofs (SADDLP)
// ---------------------------------------------------------------------------
//
// SOUNDNESS — these credit the coverage gate for `NeonSaddlpV`, the SIGNED
// sibling of `NeonUaddlpV`, emitted by the widening `sext(i8/i16) -> i32`
// array-reduction lowering (`.16B->.8H` then `.8H->.4S` for i8; `.8H->.4S`
// alone for i16). Same D-REGISTER-PAIR faithful obligation as the UADDLP
// proofs, with the pairwise add SIGN-extending each input lane: the SOURCE
// slices each INPUT lane DIRECTLY from the two 64-bit D-halves and computes
// `sext(in[2k]) + sext(in[2k+1])`; the MACHINE is the real
// `encode_neon_saddlp` over the reassembled `Concat(hi, lo)` register.
// STRUCTURALLY DISTINCT (raw-half `Var` leaf vs `Extract`-of-`Concat`), so
// `is_genuinely_proven()` holds; provably EQUAL because each output lane's two
// contributing input lanes share a D-half (`.16B->.8H`: bytes 2k/2k+1;
// `.8H->.4S`: halfwords 2k/2k+1 — no cross-half pair).
//
// SIGNEDNESS is the classic trap in widening reductions, so the negative
// controls include the SIGN-CONFUSION mutation explicitly: SADDLP encoded as
// UADDLP (zero- instead of sign-extending) REFUTES — the sides diverge on any
// input lane with the sign bit set (e.g. byte 0x80: sext -> 0xFF80, zext ->
// 0x0080). A pairwise-SUB mutation refutes the operation axis, as for UADDLP.
// Reference: ARM DDI 0487, C7.2.252 SADDLP.

/// SOURCE side for `SADDLP` (SIGNED widening pairwise add): slice each INPUT
/// lane from the raw D-halves of `vn`, sum adjacent pairs SIGN-extended to
/// double width, reassemble the (half-count, double-width) output.
fn neon_source_saddlp_from_halves(in_arr: VectorArrangement) -> SmtExpr {
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let in_bits = in_arr.lane_bits();
    let out_count = in_arr.lane_count() / 2;
    let lanes: Vec<SmtExpr> = (0..out_count)
        .map(|k| {
            let lo = lane_from_halves(&vn_lo, &vn_hi, in_arr, 2 * k).sign_ext(in_bits);
            let hi = lane_from_halves(&vn_lo, &vn_hi, in_arr, 2 * k + 1).sign_ext(in_bits);
            lo.bvadd(hi)
        })
        .collect();
    lane_concat(&lanes)
}

/// FAITHFUL: pairwise-widening SIGNED add `.16B->.8H` (D-pair) == NEON `SADDLP.8H`.
pub fn proof_neon_saddlpv_16b_8h() -> ProofObligation {
    neon_unary_obligation(
        "NEON SaddlpV.16B->.8H lanewise-intent == D-pair pairwise sext-add (faithful)",
        neon_source_saddlp_from_halves(VectorArrangement::B16),
        encode_neon_saddlp(VectorArrangement::B16, &var_128("vn")),
    )
}

/// FAITHFUL: pairwise-widening SIGNED add `.8H->.4S` (D-pair) == NEON `SADDLP.4S`.
pub fn proof_neon_saddlpv_8h_4s() -> ProofObligation {
    neon_unary_obligation(
        "NEON SaddlpV.8H->.4S lanewise-intent == D-pair pairwise sext-add (faithful)",
        neon_source_saddlp_from_halves(VectorArrangement::H8),
        encode_neon_saddlp(VectorArrangement::H8, &var_128("vn")),
    )
}

/// NEGATIVE CONTROLS for `NeonSaddlpV`: correct D-pair SOURCE paired with a
/// WRONG NEON `machine` encoder. Each MUST refute (SAT counterexample):
///   * SIGN CONFUSION: SADDLP encoded as UADDLP (zero-extend instead of
///     sign-extend) — diverges on any negative input lane (0x80 / 0x8000
///     edges), at BOTH arrangements. THE discriminating control for a widening
///     signed reduction.
///   * SADDLP as pairwise widening SUBTRACT (wrong pairwise op).
pub fn neon_saddlp_wrong_encoding_controls() -> Vec<ProofObligation> {
    // Wrong SADDLP: pairwise widening SIGNED subtract instead of add.
    let wrong_saddlp_sub = |in_arr: VectorArrangement, vn: &SmtExpr| -> SmtExpr {
        let in_bits = in_arr.lane_bits();
        let out_count = in_arr.lane_count() / 2;
        let lanes: Vec<SmtExpr> = (0..out_count)
            .map(|k| {
                let lo = lane_extract(vn, in_arr, 2 * k).sign_ext(in_bits);
                let hi = lane_extract(vn, in_arr, 2 * k + 1).sign_ext(in_bits);
                lo.bvsub(hi)
            })
            .collect();
        lane_concat(&lanes)
    };
    vec![
        neon_unary_obligation(
            "WRONG-SIGN: SaddlpV.16B->.8H encoded as UADDLP (zext) must REFUTE",
            neon_source_saddlp_from_halves(VectorArrangement::B16),
            encode_neon_uaddlp(VectorArrangement::B16, &var_128("vn")),
        ),
        neon_unary_obligation(
            "WRONG-SIGN: SaddlpV.8H->.4S encoded as UADDLP (zext) must REFUTE",
            neon_source_saddlp_from_halves(VectorArrangement::H8),
            encode_neon_uaddlp(VectorArrangement::H8, &var_128("vn")),
        ),
        neon_unary_obligation(
            "WRONG: SaddlpV.16B->.8H encoded as pairwise SUB must REFUTE",
            neon_source_saddlp_from_halves(VectorArrangement::B16),
            wrong_saddlp_sub(VectorArrangement::B16, &var_128("vn")),
        ),
        neon_unary_obligation(
            "WRONG: SaddlpV.8H->.4S encoded as pairwise SUB must REFUTE",
            neon_source_saddlp_from_halves(VectorArrangement::H8),
            wrong_saddlp_sub(VectorArrangement::H8, &var_128("vn")),
        ),
    ]
}

/// The 2 FAITHFUL SADDLP obligations the coverage gate CREDITS for
/// `NeonSaddlpV` (`.16B->.8H` and `.8H->.4S`).
pub fn all_neon_saddlp_proofs() -> Vec<ProofObligation> {
    vec![proof_neon_saddlpv_16b_8h(), proof_neon_saddlpv_8h_4s()]
}

// ---------------------------------------------------------------------------
// FAITHFUL per-LANE NEON SIGNED-ABS proof (ABS.4S)
// ---------------------------------------------------------------------------
//
// SOUNDNESS — credits the coverage gate for `NeonAbsV` (`ABS.4S`), the single op
// the abs-sum reduction lowering emits in place of the negating `SUB` + `SMAX`
// pair. Same D-REGISTER-PAIR faithful obligation as the lane-wise compute proofs:
// the SOURCE slices each 32-bit lane DIRECTLY from the two 64-bit D-halves of the
// Q register (`Extract(Var(vn_lo|vn_hi), …)`) and applies the reference per-lane
// signed abs; the MACHINE is the real `encode_neon_abs` encoder over the
// reassembled whole register (`Extract(Concat(hi, lo), …)`). STRUCTURALLY DISTINCT
// (raw-half `Var` leaf vs an `Extract`-of-`Concat`), so `is_genuinely_proven()`
// holds; provably EQUAL because slicing a lane from its D-half equals slicing the
// same bit-field from the packed register. Signed abs is lane-local (no cross-lane
// carry), so the D-pair obligation is EXACT: each `.4S` lane lies wholly in one
// half (lanes 0,1 in `lo`; lanes 2,3 in `hi`).
//
// abs(INT_MIN) == INT_MIN: `0 - INT_MIN` wraps to INT_MIN in two's complement, so
// the reference (`bvneg`) and the machine encoder agree — matching clang and the
// SUB+SMAX path. A WRONG encoding REFUTES (see `neon_abs_wrong_encoding_controls`):
// abs-as-IDENTITY (leaves negatives unchanged) and abs-as-NEGATE-ALWAYS (flips the
// sign of positives). Reference: ARM DDI 0487 C7.2.1 ABS (vector).

/// The 128-bit arrangement `ABS.4S` operates on (the abs-sum lowering emits `.4S`).
const NEON_ABS_ARR: VectorArrangement = VectorArrangement::S4;

/// Per-lane signed abs for the SOURCE side (identical formula to the machine
/// encoder's private `abs_lane`, so the two sides differ ONLY in the sliced leaf —
/// the D-half `Var` vs the `Concat`-of-halves — which is exactly the non-degeneracy
/// distinction). `if a <s 0 then 0 - a else a` (two's complement).
fn source_abs_lane(a: &SmtExpr, bits: u32) -> SmtExpr {
    let zero = SmtExpr::bv_const(0, bits);
    SmtExpr::ite(a.clone().bvslt(zero), a.clone().bvneg(), a.clone())
}

/// SOURCE side for `ABS`: slice each lane from the raw D-halves of `vn` and apply
/// the per-lane signed abs, then reassemble. Independent of the machine encoder's
/// whole-register `Concat` threading (so the obligation is non-degenerate).
fn neon_source_abs_from_halves(arrangement: VectorArrangement) -> SmtExpr {
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let lanes: Vec<SmtExpr> = (0..arrangement.lane_count())
        .map(|i| {
            let lane = lane_from_halves(&vn_lo, &vn_hi, arrangement, i);
            source_abs_lane(&lane, arrangement.lane_bits())
        })
        .collect();
    concat_lanes(&lanes, arrangement)
}

/// FAITHFUL: trust_ir per-lane `<4 x i32>` signed abs (D-pair) == NEON `ABS.4S`.
pub fn proof_neon_absv_lanewise_4s() -> ProofObligation {
    neon_unary_obligation(
        "NEON AbsV.4S lanewise-intent == D-pair per-lane signed abs (faithful)",
        neon_source_abs_from_halves(NEON_ABS_ARR),
        encode_neon_abs(NEON_ABS_ARR, &var_128("vn")),
    )
}

/// NEGATIVE CONTROLS for `NeonAbsV`: correct D-pair SOURCE paired with a WRONG NEON
/// `machine` encoder. Each MUST refute (SAT counterexample):
///   * ABS as IDENTITY (leaves negative lanes unchanged).
///   * ABS as NEGATE-ALWAYS (`0 - a` for every lane — flips the sign of positives).
pub fn neon_abs_wrong_encoding_controls() -> Vec<ProofObligation> {
    // Wrong ABS: identity (passthrough — negatives are NOT made positive).
    let wrong_abs_identity =
        |arr: VectorArrangement, vn: &SmtExpr| -> SmtExpr { map_lanes_unary(vn, arr, |a| a) };
    // Wrong ABS: unconditional negate (`0 - a` for every lane).
    let wrong_abs_negate = |arr: VectorArrangement, vn: &SmtExpr| -> SmtExpr {
        map_lanes_unary(vn, arr, |a| a.bvneg())
    };
    vec![
        neon_unary_obligation(
            "WRONG: AbsV.4S encoded as IDENTITY must REFUTE",
            neon_source_abs_from_halves(NEON_ABS_ARR),
            wrong_abs_identity(NEON_ABS_ARR, &var_128("vn")),
        ),
        neon_unary_obligation(
            "WRONG: AbsV.4S encoded as NEGATE-ALWAYS must REFUTE",
            neon_source_abs_from_halves(NEON_ABS_ARR),
            wrong_abs_negate(NEON_ABS_ARR, &var_128("vn")),
        ),
    ]
}

/// The FAITHFUL signed-abs obligation the coverage gate CREDITS for `NeonAbsV`
/// (`ABS.4S`).
pub fn all_neon_abs_proofs() -> Vec<ProofObligation> {
    vec![proof_neon_absv_lanewise_4s()]
}

// ---------------------------------------------------------------------------
// FAITHFUL per-LANE NEON UNSIGNED DOT-PRODUCT-ACCUMULATE proof (UDOT.4S)
// ---------------------------------------------------------------------------
//
// SOUNDNESS — credits the coverage gate for `NeonUdotV` (`UDOT Vd.4S, Vn.16B,
// Vm.16B`, FEAT_DotProd), the accumulating dot product the ctpop-reduction
// lowering emits: `UDOT(acc, CNT.16B(x), ones.16B)` folds the four per-byte
// popcounts of each i32 lane straight into the running `.4S` accumulator,
// replacing the UADDLP + UADDLP + ADD chain with one instruction.
//
// Same D-REGISTER-PAIR faithful obligation as the lane-wise compute proofs,
// extended to the op's THREE register inputs (Vd is BOTH source and destination
// — the accumulate): the SOURCE slices the 4 input byte lanes of `Vn`/`Vm` AND
// the 32-bit accumulator lane of `Vd` DIRECTLY from the raw 64-bit D-halves
// (`Extract(Var(vd_lo|vd_hi|vn_lo|…), …)`) and computes
// `acc + sum_{j<4}(zext32(vn_byte_j) * zext32(vm_byte_j))`; the MACHINE is the
// real `encode_neon_udot` encoder over the reassembled whole registers
// (`Extract(Concat(hi, lo), …)`). STRUCTURALLY DISTINCT (raw-half `Var` leaf vs
// an `Extract`-of-`Concat`), so `is_genuinely_proven()` holds; provably EQUAL
// because slicing a lane from its D-half equals slicing the same bit-field from
// the packed register.
//
// HONEST SCOPE — the D-pair obligation is EXACT here, no cross-half carry:
// each output lane `i` reads ONLY byte lanes `4i..4i+3` of `Vn`/`Vm` and word
// lane `i` of `Vd`, and for `.16B`/`.4S` all of those live wholly in one
// D-half (lanes 0-1 in `lo`, 2-3 in `hi`). A WRONG encoding REFUTES (see
// `neon_udot_wrong_encoding_controls`): dot-WITHOUT-accumulate (drops the `Vd`
// addend), UDOT-as-SDOT (sign-extends the bytes — diverges for bytes >= 0x80),
// and a pair-shuffle (sums the WRONG byte group). Reference: ARM DDI 0487
// C7.2.361 UDOT (vector) + B1.2 (Q = {Dlo, Dhi} register view).

/// The INPUT byte arrangement of the `UDOT .16B -> .4S` form the ctpop-reduction
/// lowering emits.
const NEON_UDOT_IN_ARR: VectorArrangement = VectorArrangement::B16;

/// SOURCE side for `UDOT.4S`: slice the accumulator word of `vd` and the four
/// byte lanes of `vn`/`vm` per output lane DIRECTLY from the raw D-halves and
/// compute `acc + sum_j zext32(n_j) * zext32(m_j)`, then reassemble. Independent
/// of the machine encoder's whole-register `Concat` threading (so the obligation
/// is non-degenerate).
fn neon_source_udot_from_halves(in_arr: VectorArrangement) -> SmtExpr {
    debug_assert!(in_arr == VectorArrangement::B16);
    let vd_lo = SmtExpr::var("vd_lo", 64);
    let vd_hi = SmtExpr::var("vd_hi", 64);
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let vm_lo = SmtExpr::var("vm_lo", 64);
    let vm_hi = SmtExpr::var("vm_hi", 64);
    let out_arr = VectorArrangement::S4;
    let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
        .map(|i| {
            let mut acc = lane_from_halves(&vd_lo, &vd_hi, out_arr, i);
            for j in 0..4 {
                let n = lane_from_halves(&vn_lo, &vn_hi, in_arr, 4 * i + j).zero_ext(24);
                let m = lane_from_halves(&vm_lo, &vm_hi, in_arr, 4 * i + j).zero_ext(24);
                acc = acc.bvadd(n.bvmul(m));
            }
            acc
        })
        .collect();
    lane_concat(&lanes)
}

/// Assemble a faithful UDOT-shaped (accumulator + two vector inputs) obligation:
/// D-pair SOURCE vs a NEON `machine` expression over the reassembled
/// `Concat(hi, lo)` registers. Shared by the UDOT and MLA proofs — the same
/// tied-accumulator three-register input shape (`vd`/`vn`/`vm` halves); only
/// the source/machine expressions differ.
fn neon_udot_obligation(name: &str, source: SmtExpr, machine: SmtExpr) -> ProofObligation {
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: vec![
            ("vd_lo".to_string(), 64),
            ("vd_hi".to_string(), 64),
            ("vn_lo".to_string(), 64),
            ("vn_hi".to_string(), 64),
            ("vm_lo".to_string(), 64),
            ("vm_hi".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// FAITHFUL: trust_ir per-lane `<4 x i32>` unsigned byte-dot-accumulate (D-pair)
/// == NEON `UDOT.4S` (accumulating).
pub fn proof_neon_udotv_lanewise_4s() -> ProofObligation {
    neon_udot_obligation(
        "NEON UdotV.4S lanewise-intent == D-pair per-lane u8-dot-accumulate (faithful)",
        neon_source_udot_from_halves(NEON_UDOT_IN_ARR),
        encode_neon_udot(
            NEON_UDOT_IN_ARR,
            &var_128("vd"),
            &var_128("vn"),
            &var_128("vm"),
        ),
    )
}

/// NEGATIVE CONTROLS for `NeonUdotV`: correct D-pair SOURCE paired with a WRONG
/// NEON `machine` expression. Each MUST refute (SAT counterexample):
///   * dot WITHOUT accumulate — drops the `Vd` addend (diverges whenever the
///     prior accumulator lane is nonzero).
///   * UDOT as SDOT — SIGN-extends the bytes instead of zero-extending
///     (diverges for byte values >= 0x80).
///   * pair-shuffle — sums the byte group of the NEXT word lane
///     (`4*((i+1) mod 4) + j`), i.e. the right op over the WRONG bytes.
pub fn neon_udot_wrong_encoding_controls() -> Vec<ProofObligation> {
    let in_arr = NEON_UDOT_IN_ARR;
    let out_arr = VectorArrangement::S4;

    // Wrong: dot product WITHOUT the accumulator addend.
    let wrong_no_accumulate = |vd: &SmtExpr, vn: &SmtExpr, vm: &SmtExpr| -> SmtExpr {
        let _ = vd; // the addend is (wrongly) dropped
        let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
            .map(|i| {
                let mut acc = SmtExpr::bv_const(0, 32);
                for j in 0..4 {
                    let n = lane_extract(vn, in_arr, 4 * i + j).zero_ext(24);
                    let m = lane_extract(vm, in_arr, 4 * i + j).zero_ext(24);
                    acc = acc.bvadd(n.bvmul(m));
                }
                acc
            })
            .collect();
        lane_concat(&lanes)
    };
    // Wrong: SDOT — sign-extends the bytes (unsigned/signed confusion).
    let wrong_sdot = |vd: &SmtExpr, vn: &SmtExpr, vm: &SmtExpr| -> SmtExpr {
        let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
            .map(|i| {
                let mut acc = lane_extract(vd, out_arr, i);
                for j in 0..4 {
                    let n = lane_extract(vn, in_arr, 4 * i + j).sign_ext(24);
                    let m = lane_extract(vm, in_arr, 4 * i + j).sign_ext(24);
                    acc = acc.bvadd(n.bvmul(m));
                }
                acc
            })
            .collect();
        lane_concat(&lanes)
    };
    // Wrong: sums the byte group of the NEXT word lane (wrong pairing).
    let wrong_pair_shuffle = |vd: &SmtExpr, vn: &SmtExpr, vm: &SmtExpr| -> SmtExpr {
        let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
            .map(|i| {
                let mut acc = lane_extract(vd, out_arr, i);
                let shifted = (i + 1) % out_arr.lane_count();
                for j in 0..4 {
                    let n = lane_extract(vn, in_arr, 4 * shifted + j).zero_ext(24);
                    let m = lane_extract(vm, in_arr, 4 * shifted + j).zero_ext(24);
                    acc = acc.bvadd(n.bvmul(m));
                }
                acc
            })
            .collect();
        lane_concat(&lanes)
    };

    let vd = var_128("vd");
    let vn = var_128("vn");
    let vm = var_128("vm");
    vec![
        neon_udot_obligation(
            "WRONG: UdotV.4S encoded WITHOUT the accumulate must REFUTE",
            neon_source_udot_from_halves(in_arr),
            wrong_no_accumulate(&vd, &vn, &vm),
        ),
        neon_udot_obligation(
            "WRONG: UdotV.4S encoded as SDOT (sign-extending) must REFUTE",
            neon_source_udot_from_halves(in_arr),
            wrong_sdot(&vd, &vn, &vm),
        ),
        neon_udot_obligation(
            "WRONG: UdotV.4S summing the WRONG byte group must REFUTE",
            neon_source_udot_from_halves(in_arr),
            wrong_pair_shuffle(&vd, &vn, &vm),
        ),
    ]
}

/// The FAITHFUL unsigned dot-product-accumulate obligation the coverage gate
/// CREDITS for `NeonUdotV` (`UDOT.4S`).
pub fn all_neon_udot_proofs() -> Vec<ProofObligation> {
    vec![proof_neon_udotv_lanewise_4s()]
}

// ---------------------------------------------------------------------------
// FAITHFUL widening multiply-ACCUMULATE-LONG proofs (SMLAL/SMLAL2/UMLAL/UMLAL2)
// ---------------------------------------------------------------------------
//
// SOUNDNESS — credits the coverage gate for `NeonSmlalV`/`NeonSmlal2V`/
// `NeonUmlalV`/`NeonUmlal2V` (SMLAL/SMLAL2/UMLAL/UMLAL2 `.4S -> .2D`), the
// widening multiply-accumulate the neon_array widening-dot vectorizer emits for
// `s(i64) += (a_i32[i] as i64) * (b_i32[i] as i64)` (signed) or the u32->u64
// unsigned dot.
//
// Same D-REGISTER-PAIR faithful ACCUMULATE obligation as UDOT (`Vd` is
// source+dest): one WHOLE-REGISTER obligation per opcode whose SOURCE
// CONCATENATES BOTH `.2D` output lanes — so a single-lane miswire refutes. Per
// output lane `j` in {0,1}, with source `.4S` lane `s = j` (LOW, SMLAL/UMLAL) or
// `s = 2+j` (HIGH, SMLAL2/UMLAL2), the SOURCE slices the `.2D` accumulator lane
// of `Vd` and the two `.4S` operand lanes of `Vn`/`Vm` DIRECTLY from the raw
// 64-bit D-halves (`vd_lo/vd_hi/vn_lo/vn_hi/vm_lo/vm_hi`) and computes
// `acc_j + EXT64(n_s) * EXT64(m_s)` (EXT64 = sign_ext(32) for SMLAL /
// zero_ext(32) for UMLAL — the EXACT i32xi32->i64 product, no truncation), then
// reassembles; the MACHINE is the real `encode_neon_smlal` over the reassembled
// whole registers (`Extract(Concat(hi, lo), …)`). STRUCTURALLY DISTINCT (raw-half
// `Var` leaf vs an `Extract`-of-`Concat`), so `is_genuinely_proven()` holds; pure
// QF_BV over 6x64-bit vars.
//
// HONEST SCOPE — the D-pair obligation is EXACT here, no cross-half carry: each
// `.2D` output lane `j` reads ONLY `.2D` lane `j` of `Vd` and `.4S` lanes `s` of
// `Vn`/`Vm`, and for `.4S` lanes {0,1} live in `lo`, {2,3} in `hi` — wholly in
// one D-half. A WRONG encoding REFUTES (see `neon_smlal_wrong_encoding_controls`):
// SMLAL-as-UMLAL (zero-extends instead of sign-extending — diverges when a lane
// has bit 31 set), dot-WITHOUT-accumulate (drops the `Vd` addend), low-as-high
// (wrong `.4S` half select), and truncating-32-bit-mul (i32xi32 truncated to 32
// then re-extended instead of widened). Reference: ARM DDI 0487 C7.2.267
// SMLAL/SMLAL2 + C7.2.352 UMLAL/UMLAL2 + B1.2 (Q = {Dlo, Dhi} register view).

/// The INPUT `.4S` arrangement of the `SMLAL/UMLAL .4S -> .2D` form the
/// widening-dot vectorizer emits.
const NEON_SMLAL_IN_ARR: VectorArrangement = VectorArrangement::S4;

/// SOURCE side for `SMLAL/UMLAL.2D`: slice the two `.2D` accumulator lanes of
/// `vd` and the corresponding `.4S` operand lanes of `vn`/`vm` per output lane
/// DIRECTLY from the raw D-halves and compute `acc_j + EXT64(n_s)*EXT64(m_s)`
/// (`s = j` low / `s = 2+j` high; EXT64 = sign/zero extend), then reassemble.
/// Independent of the machine encoder's whole-register `Concat` threading (so the
/// obligation is non-degenerate).
fn neon_source_smlal_from_halves(high: bool, signed: bool) -> SmtExpr {
    let vd_lo = SmtExpr::var("vd_lo", 64);
    let vd_hi = SmtExpr::var("vd_hi", 64);
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let vm_lo = SmtExpr::var("vm_lo", 64);
    let vm_hi = SmtExpr::var("vm_hi", 64);
    let in_arr = NEON_SMLAL_IN_ARR;
    let out_arr = VectorArrangement::D2;
    let base = if high { 2 } else { 0 };
    let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
        .map(|j| {
            let acc = lane_from_halves(&vd_lo, &vd_hi, out_arr, j);
            let n = lane_from_halves(&vn_lo, &vn_hi, in_arr, base + j);
            let m = lane_from_halves(&vm_lo, &vm_hi, in_arr, base + j);
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

/// Assemble a faithful SMLAL-shaped (accumulator + two vector inputs) obligation:
/// D-pair SOURCE vs a NEON `machine` expression over the reassembled
/// `Concat(hi, lo)` registers.
fn neon_smlal_obligation(name: &str, source: SmtExpr, machine: SmtExpr) -> ProofObligation {
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: vec![
            ("vd_lo".to_string(), 64),
            ("vd_hi".to_string(), 64),
            ("vn_lo".to_string(), 64),
            ("vn_hi".to_string(), 64),
            ("vm_lo".to_string(), 64),
            ("vm_hi".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// FAITHFUL: trust_ir per-lane `<2 x i64>` SIGNED widening (i32->i64) MAC over the
/// LOW `.4S` half (D-pair) == NEON `SMLAL.2D` (accumulating).
pub fn proof_neon_smlalv_2d() -> ProofObligation {
    neon_smlal_obligation(
        "NEON SmlalV.2D low widening-mac-intent == D-pair per-lane i32->i64 signed MAC (faithful)",
        neon_source_smlal_from_halves(false, true),
        encode_neon_smlal(
            NEON_SMLAL_IN_ARR,
            false,
            true,
            &var_128("vd"),
            &var_128("vn"),
            &var_128("vm"),
        ),
    )
}

/// FAITHFUL: SIGNED widening MAC over the HIGH `.4S` half == NEON `SMLAL2.2D`.
pub fn proof_neon_smlal2v_2d() -> ProofObligation {
    neon_smlal_obligation(
        "NEON Smlal2V.2D high widening-mac-intent == D-pair per-lane i32->i64 signed MAC (faithful)",
        neon_source_smlal_from_halves(true, true),
        encode_neon_smlal(
            NEON_SMLAL_IN_ARR,
            true,
            true,
            &var_128("vd"),
            &var_128("vn"),
            &var_128("vm"),
        ),
    )
}

/// FAITHFUL: UNSIGNED widening (u32->u64) MAC over the LOW `.4S` half == NEON
/// `UMLAL.2D`.
pub fn proof_neon_umlalv_2d() -> ProofObligation {
    neon_smlal_obligation(
        "NEON UmlalV.2D low widening-mac-intent == D-pair per-lane u32->u64 unsigned MAC (faithful)",
        neon_source_smlal_from_halves(false, false),
        encode_neon_smlal(
            NEON_SMLAL_IN_ARR,
            false,
            false,
            &var_128("vd"),
            &var_128("vn"),
            &var_128("vm"),
        ),
    )
}

/// FAITHFUL: UNSIGNED widening MAC over the HIGH `.4S` half == NEON `UMLAL2.2D`.
pub fn proof_neon_umlal2v_2d() -> ProofObligation {
    neon_smlal_obligation(
        "NEON Umlal2V.2D high widening-mac-intent == D-pair per-lane u32->u64 unsigned MAC (faithful)",
        neon_source_smlal_from_halves(true, false),
        encode_neon_smlal(
            NEON_SMLAL_IN_ARR,
            true,
            false,
            &var_128("vd"),
            &var_128("vn"),
            &var_128("vm"),
        ),
    )
}

/// NEGATIVE CONTROLS for the widening MAC: correct SIGNED-LOW (`SMLAL`) D-pair
/// SOURCE paired with a WRONG NEON `machine` expression. Each MUST refute (SAT
/// counterexample):
///   * SMLAL as UMLAL — ZERO-extends the source lanes instead of sign-extending
///     (signed/unsigned confusion; diverges whenever a source lane has bit 31
///     set).
///   * dot WITHOUT accumulate — drops the `Vd` addend (diverges whenever the
///     prior accumulator lane is nonzero).
///   * low as high — reads the HIGH `.4S` half `{2,3}` instead of the LOW `{0,1}`
///     (the silent SMLAL/SMLAL2 lane-select miscompile).
///   * truncating 32-bit mul — truncates the i32xi32 product to 32 bits then
///     re-extends (a non-widening `MUL`+sign-extend instead of the widening MAC;
///     diverges whenever a product exceeds 32 bits).
pub fn neon_smlal_wrong_encoding_controls() -> Vec<ProofObligation> {
    let in_arr = NEON_SMLAL_IN_ARR;
    let out_arr = VectorArrangement::D2;
    let vd = var_128("vd");
    let vn = var_128("vn");
    let vm = var_128("vm");

    // Wrong: SMLAL encoded WITHOUT the accumulator addend (SMULL, drops Vd).
    let wrong_no_accumulate = |_vd: &SmtExpr, vn: &SmtExpr, vm: &SmtExpr| -> SmtExpr {
        let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
            .map(|j| {
                let n = lane_extract(vn, in_arr, j).sign_ext(32);
                let m = lane_extract(vm, in_arr, j).sign_ext(32);
                n.bvmul(m)
            })
            .collect();
        lane_concat(&lanes)
    };
    // Wrong: truncating 32-bit multiply then sign-extend (non-widening MUL).
    let wrong_truncating = |vd: &SmtExpr, vn: &SmtExpr, vm: &SmtExpr| -> SmtExpr {
        let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
            .map(|j| {
                let acc = lane_extract(vd, out_arr, j);
                let n = lane_extract(vn, in_arr, j).sign_ext(32);
                let m = lane_extract(vm, in_arr, j).sign_ext(32);
                // 64-bit product truncated to 32 bits, then sign-extended back.
                let prod32 = n.bvmul(m).extract(31, 0);
                acc.bvadd(prod32.sign_ext(32))
            })
            .collect();
        lane_concat(&lanes)
    };

    vec![
        neon_smlal_obligation(
            "WRONG: SmlalV.2D encoded as UMLAL (zero-extending, sign confusion) must REFUTE",
            neon_source_smlal_from_halves(false, true),
            encode_neon_smlal(in_arr, false, false, &vd, &vn, &vm),
        ),
        neon_smlal_obligation(
            "WRONG: SmlalV.2D encoded WITHOUT the accumulate (SMULL) must REFUTE",
            neon_source_smlal_from_halves(false, true),
            wrong_no_accumulate(&vd, &vn, &vm),
        ),
        neon_smlal_obligation(
            "WRONG: SmlalV.2D encoded as SMLAL2 (HIGH half select) must REFUTE",
            neon_source_smlal_from_halves(false, true),
            encode_neon_smlal(in_arr, true, true, &vd, &vn, &vm),
        ),
        neon_smlal_obligation(
            "WRONG: SmlalV.2D encoded as a TRUNCATING 32-bit multiply must REFUTE",
            neon_source_smlal_from_halves(false, true),
            wrong_truncating(&vd, &vn, &vm),
        ),
    ]
}

/// The FAITHFUL widening multiply-accumulate-long obligations the coverage gate
/// CREDITS for `NeonSmlalV`/`NeonSmlal2V`/`NeonUmlalV`/`NeonUmlal2V` — one whole-
/// register D-pair obligation per opcode (both `.2D` lanes concatenated).
pub fn all_neon_smlal_proofs() -> Vec<ProofObligation> {
    vec![
        proof_neon_smlalv_2d(),
        proof_neon_smlal2v_2d(),
        proof_neon_umlalv_2d(),
        proof_neon_umlal2v_2d(),
    ]
}

// ---------------------------------------------------------------------------
// FAITHFUL widening add-WIDE proofs (UADDW/UADDW2)
// ---------------------------------------------------------------------------
//
// SOUNDNESS — credits the coverage gate for `NeonUaddwV`/`NeonUaddw2V`
// (UADDW/UADDW2 `.4S -> .2D`), the unsigned widening add the neon_array
// widening abs-sum vectorizer (TRACK D) emits for
// `s(i64) += zext64(abs_bits(a_i32[i] [+ inv]))` — per lane
// `acc_j + zext64(u_s)`, replacing the UMLAL-by-ones MAC (identical per lane:
// `acc_j + zext64(u_s) * 1`) and structurally matching LLVM's
// `abs.4s + uaddw.2d/uaddw2.2d` codegen.
//
// Same D-REGISTER-PAIR faithful obligation shape as SMLAL, but the ISA's plain
// THREE-OPERAND form: the i64 addend is the SEPARATE wide source `Vn` (operand
// 1), `Vd` is a pure def whose prior value is never read. One WHOLE-REGISTER
// obligation per opcode whose SOURCE CONCATENATES BOTH `.2D` output lanes — so
// a single-lane miswire refutes. Per output lane `j` in {0,1}, with source
// `.4S` lane `s = j` (LOW, UADDW) or `s = 2+j` (HIGH, UADDW2), the SOURCE
// slices the `.2D` addend lane of `Vn` and the source `.4S` lane of `Vm`
// DIRECTLY from the raw 64-bit D-halves (`vn_lo/vn_hi/vm_lo/vm_hi`) and
// computes `addend_j + zext64(m_s)` (UNSIGNED u32->u64 extension — the scalar
// chain's `Uxtw`), then reassembles; the MACHINE is the real
// `encode_neon_uaddw` over the reassembled whole registers
// (`Extract(Concat(hi, lo), ...)`). STRUCTURALLY DISTINCT (raw-half `Var` leaf
// vs an `Extract`-of-`Concat`), so `is_genuinely_proven()` holds; pure QF_BV
// over 4x64-bit vars.
//
// HONEST SCOPE — the D-pair obligation is EXACT here, no cross-half carry:
// each `.2D` output lane `j` reads ONLY `.2D` lane `j` of `Vn` and `.4S` lane
// `s` of `Vm`, and `.4S` lanes {0,1} live in `lo`, {2,3} in `hi` — wholly in
// one D-half. A WRONG encoding REFUTES (see
// `neon_uaddw_wrong_encoding_controls`): UADDW-as-SADDW (sign-extends instead
// of zero-extending — diverges on every lane with bit 31 set, exactly the
// abs-sum's `>= 2^31` u32 bit patterns), widen-WITHOUT-addend (drops the `Vn`
// wide operand, a UXTL/USHLL#0), low-as-high (wrong `.4S` half select), and
// truncating-32-bit-add (adds in 32 bits then re-extends, dropping the addend's
// high word and the carry). Reference: ARM DDI 0487 C7.2.350 UADDW/UADDW2 +
// B1.2 (Q = [Dlo, Dhi] register view).

/// The INPUT `.4S` arrangement of the `UADDW/UADDW2 .4S -> .2D` form the
/// widening abs-sum vectorizer emits.
const NEON_UADDW_IN_ARR: VectorArrangement = VectorArrangement::S4;

/// SOURCE side for `UADDW/UADDW2.2D`: slice the two `.2D` addend lanes of `vn`
/// and the corresponding source `.4S` lanes of `vm` per output lane DIRECTLY
/// from the raw D-halves and compute `addend_j + zext64(m_s)` (`s = j` low /
/// `s = 2+j` high; UNSIGNED extension), then reassemble. Independent of the
/// machine encoder's whole-register `Concat` threading (so the obligation is
/// non-degenerate).
fn neon_source_uaddw_from_halves(high: bool) -> SmtExpr {
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let vm_lo = SmtExpr::var("vm_lo", 64);
    let vm_hi = SmtExpr::var("vm_hi", 64);
    let in_arr = NEON_UADDW_IN_ARR;
    let out_arr = VectorArrangement::D2;
    let base = if high { 2 } else { 0 };
    let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
        .map(|j| {
            let addend = lane_from_halves(&vn_lo, &vn_hi, out_arr, j);
            let m = lane_from_halves(&vm_lo, &vm_hi, in_arr, base + j);
            addend.bvadd(m.zero_ext(32))
        })
        .collect();
    lane_concat(&lanes)
}

/// Assemble a faithful xADDW-shaped (wide addend + narrow source, both plain
/// inputs) obligation: D-pair SOURCE vs a NEON `machine` expression over the
/// reassembled `Concat(hi, lo)` registers. Shared by the UNSIGNED (UADDW) and
/// SIGNED (SADDW) widening add-wide proofs — same inputs, same shape; only the
/// source/machine expressions differ.
fn neon_uaddw_obligation(name: &str, source: SmtExpr, machine: SmtExpr) -> ProofObligation {
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: vec![
            ("vn_lo".to_string(), 64),
            ("vn_hi".to_string(), 64),
            ("vm_lo".to_string(), 64),
            ("vm_hi".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// FAITHFUL: trust_ir per-lane `<2 x i64>` UNSIGNED widening (u32->u64) add over
/// the LOW `.4S` half (D-pair) == NEON `UADDW.2D` (three-operand wide add).
pub fn proof_neon_uaddwv_2d() -> ProofObligation {
    neon_uaddw_obligation(
        "NEON UaddwV.2D low widening-add-intent == D-pair per-lane u32->u64 unsigned wide add (faithful)",
        neon_source_uaddw_from_halves(false),
        encode_neon_uaddw(NEON_UADDW_IN_ARR, false, &var_128("vn"), &var_128("vm")),
    )
}

/// FAITHFUL: UNSIGNED widening add over the HIGH `.4S` half == NEON `UADDW2.2D`.
pub fn proof_neon_uaddw2v_2d() -> ProofObligation {
    neon_uaddw_obligation(
        "NEON Uaddw2V.2D high widening-add-intent == D-pair per-lane u32->u64 unsigned wide add (faithful)",
        neon_source_uaddw_from_halves(true),
        encode_neon_uaddw(NEON_UADDW_IN_ARR, true, &var_128("vn"), &var_128("vm")),
    )
}

/// NEGATIVE CONTROLS for the widening add-wide: correct UNSIGNED-LOW (`UADDW`)
/// D-pair SOURCE paired with a WRONG NEON `machine` expression. Each MUST refute
/// (SAT counterexample):
///   * UADDW as SADDW — SIGN-extends the source lanes instead of zero-extending
///     (signed/unsigned confusion; diverges whenever a source lane has bit 31
///     set — exactly the abs-sum's `unsigned_abs >= 2^31` bit patterns, i.e.
///     the `i32::MIN` lanes).
///   * widen WITHOUT the addend — drops the `Vn` wide operand (a UXTL/USHLL#0;
///     diverges whenever the addend lane is nonzero).
///   * low as high — reads the HIGH `.4S` half `[2,3]` instead of the LOW
///     `[0,1]` (the silent UADDW/UADDW2 lane-select miscompile).
///   * truncating 32-bit add — adds the source lane into the addend's LOW 32
///     bits then zero-extends (drops the addend's high word and the carry;
///     diverges whenever the addend exceeds 32 bits or the 32-bit add carries).
pub fn neon_uaddw_wrong_encoding_controls() -> Vec<ProofObligation> {
    let in_arr = NEON_UADDW_IN_ARR;
    let out_arr = VectorArrangement::D2;
    let vn = var_128("vn");
    let vm = var_128("vm");

    // Wrong: SADDW — sign-extends the `.4S` source lanes.
    let wrong_saddw = |vn: &SmtExpr, vm: &SmtExpr| -> SmtExpr {
        let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
            .map(|j| {
                let addend = lane_extract(vn, out_arr, j);
                let m = lane_extract(vm, in_arr, j).sign_ext(32);
                addend.bvadd(m)
            })
            .collect();
        lane_concat(&lanes)
    };
    // Wrong: UXTL (USHLL #0) — widens the source but DROPS the Vn addend.
    let wrong_no_addend = |_vn: &SmtExpr, vm: &SmtExpr| -> SmtExpr {
        let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
            .map(|j| lane_extract(vm, in_arr, j).zero_ext(32))
            .collect();
        lane_concat(&lanes)
    };
    // Wrong: truncating 32-bit add — adds into the addend's low 32 bits, then
    // zero-extends (drops the addend's high word and the carry out of bit 31).
    let wrong_truncating = |vn: &SmtExpr, vm: &SmtExpr| -> SmtExpr {
        let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
            .map(|j| {
                let addend32 = lane_extract(vn, out_arr, j).extract(31, 0);
                let m = lane_extract(vm, in_arr, j);
                addend32.bvadd(m).zero_ext(32)
            })
            .collect();
        lane_concat(&lanes)
    };

    vec![
        neon_uaddw_obligation(
            "WRONG: UaddwV.2D encoded as SADDW (sign-extending, sign confusion) must REFUTE",
            neon_source_uaddw_from_halves(false),
            wrong_saddw(&vn, &vm),
        ),
        neon_uaddw_obligation(
            "WRONG: UaddwV.2D encoded WITHOUT the wide addend (UXTL) must REFUTE",
            neon_source_uaddw_from_halves(false),
            wrong_no_addend(&vn, &vm),
        ),
        neon_uaddw_obligation(
            "WRONG: UaddwV.2D encoded as UADDW2 (HIGH half select) must REFUTE",
            neon_source_uaddw_from_halves(false),
            encode_neon_uaddw(in_arr, true, &vn, &vm),
        ),
        neon_uaddw_obligation(
            "WRONG: UaddwV.2D encoded as a TRUNCATING 32-bit add must REFUTE",
            neon_source_uaddw_from_halves(false),
            wrong_truncating(&vn, &vm),
        ),
    ]
}

/// The FAITHFUL widening add-wide obligations the coverage gate CREDITS for
/// `NeonUaddwV`/`NeonUaddw2V` — one whole-register D-pair obligation per opcode
/// (both `.2D` lanes concatenated).
pub fn all_neon_uaddw_proofs() -> Vec<ProofObligation> {
    vec![proof_neon_uaddwv_2d(), proof_neon_uaddw2v_2d()]
}

// ---------------------------------------------------------------------------
// FAITHFUL SIGNED widening add-WIDE proofs (SADDW/SADDW2)
// ---------------------------------------------------------------------------
//
// SOUNDNESS — credits the coverage gate for `NeonSaddwV`/`NeonSaddw2V`
// (SADDW/SADDW2 `.4S -> .2D`), the SIGNED widening add the neon_predsum
// widening i64-accumulator condsum emits for
// `s(i64) += (a_i32[iv] as i64) [if pred]` — per lane
// `acc_j + sext64(masked_s)`, replacing the SMLAL-by-ones MAC (identical per
// lane: `acc_j + sext64(masked_s) * sext64(1)`) and structurally matching
// LLVM's `cmgt.4s + and.16b + saddw.2d/saddw2.2d` codegen.
//
// The exact MIRROR of the UADDW obligations above — same D-REGISTER-PAIR
// faithful shape, same plain THREE-OPERAND form (the i64 addend is the
// SEPARATE wide source `Vn`, operand 1; `Vd` is a pure def) — with the ONE
// semantic difference on the extension axis: the source `.4S` lane is
// SIGN-extended (i32->i64), not zero-extended. One WHOLE-REGISTER obligation
// per opcode whose SOURCE CONCATENATES BOTH `.2D` output lanes — so a
// single-lane miswire refutes. Per output lane `j` in {0,1}, with source `.4S`
// lane `s = j` (LOW, SADDW) or `s = 2+j` (HIGH, SADDW2), the SOURCE slices the
// `.2D` addend lane of `Vn` and the source `.4S` lane of `Vm` DIRECTLY from
// the raw 64-bit D-halves (`vn_lo/vn_hi/vm_lo/vm_hi`) and computes
// `addend_j + sext64(m_s)` (SIGNED i32->i64 extension — the scalar chain's
// `Sxtw`), then reassembles; the MACHINE is the real `encode_neon_saddw` over
// the reassembled whole registers (`Extract(Concat(hi, lo), ...)`).
// STRUCTURALLY DISTINCT (raw-half `Var` leaf vs an `Extract`-of-`Concat`), so
// `is_genuinely_proven()` holds; pure QF_BV over 4x64-bit vars.
//
// HONEST SCOPE — the D-pair obligation is EXACT here, no cross-half carry:
// each `.2D` output lane `j` reads ONLY `.2D` lane `j` of `Vn` and `.4S` lane
// `s` of `Vm`, and `.4S` lanes {0,1} live in `lo`, {2,3} in `hi` — wholly in
// one D-half. A WRONG encoding REFUTES (see
// `neon_saddw_wrong_encoding_controls`): SADDW-as-UADDW (zero-extends instead
// of sign-extending — diverges on every NEGATIVE source lane, exactly the
// condsum's in-mask negative `a[i]` values; the mirror of the UADDW proofs'
// SADDW-confusion control, so the sign axis is refuted in BOTH directions),
// widen-WITHOUT-addend (drops the `Vn` wide operand, an SXTL/SSHLL#0),
// low-as-high (wrong `.4S` half select), and truncating-32-bit-add (adds in 32
// bits then sign-extends, dropping the addend's high word and the carry).
// Reference: ARM DDI 0487 C7.2.207 SADDW/SADDW2 + B1.2 (Q = [Dlo, Dhi]
// register view).

/// The INPUT `.4S` arrangement of the `SADDW/SADDW2 .4S -> .2D` form the
/// widening i64-acc condsum vectorizer emits.
const NEON_SADDW_IN_ARR: VectorArrangement = VectorArrangement::S4;

/// SOURCE side for `SADDW/SADDW2.2D`: slice the two `.2D` addend lanes of `vn`
/// and the corresponding source `.4S` lanes of `vm` per output lane DIRECTLY
/// from the raw D-halves and compute `addend_j + sext64(m_s)` (`s = j` low /
/// `s = 2+j` high; SIGNED extension), then reassemble. Independent of the
/// machine encoder's whole-register `Concat` threading (so the obligation is
/// non-degenerate).
fn neon_source_saddw_from_halves(high: bool) -> SmtExpr {
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let vm_lo = SmtExpr::var("vm_lo", 64);
    let vm_hi = SmtExpr::var("vm_hi", 64);
    let in_arr = NEON_SADDW_IN_ARR;
    let out_arr = VectorArrangement::D2;
    let base = if high { 2 } else { 0 };
    let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
        .map(|j| {
            let addend = lane_from_halves(&vn_lo, &vn_hi, out_arr, j);
            let m = lane_from_halves(&vm_lo, &vm_hi, in_arr, base + j);
            addend.bvadd(m.sign_ext(32))
        })
        .collect();
    lane_concat(&lanes)
}

/// FAITHFUL: trust_ir per-lane `<2 x i64>` SIGNED widening (i32->i64) add over
/// the LOW `.4S` half (D-pair) == NEON `SADDW.2D` (three-operand wide add).
pub fn proof_neon_saddwv_2d() -> ProofObligation {
    neon_uaddw_obligation(
        "NEON SaddwV.2D low widening-add-intent == D-pair per-lane i32->i64 signed wide add (faithful)",
        neon_source_saddw_from_halves(false),
        encode_neon_saddw(NEON_SADDW_IN_ARR, false, &var_128("vn"), &var_128("vm")),
    )
}

/// FAITHFUL: SIGNED widening add over the HIGH `.4S` half == NEON `SADDW2.2D`.
pub fn proof_neon_saddw2v_2d() -> ProofObligation {
    neon_uaddw_obligation(
        "NEON Saddw2V.2D high widening-add-intent == D-pair per-lane i32->i64 signed wide add (faithful)",
        neon_source_saddw_from_halves(true),
        encode_neon_saddw(NEON_SADDW_IN_ARR, true, &var_128("vn"), &var_128("vm")),
    )
}

/// NEGATIVE CONTROLS for the SIGNED widening add-wide: correct SIGNED-LOW
/// (`SADDW`) D-pair SOURCE paired with a WRONG NEON `machine` expression. Each
/// MUST refute (SAT counterexample):
///   * SADDW as UADDW — ZERO-extends the source lanes instead of
///     sign-extending (the signed/unsigned confusion in the OPPOSITE direction
///     from the UADDW proofs' SADDW control, closing the sign axis both ways;
///     diverges on every NEGATIVE source lane — exactly the condsum's in-mask
///     negative `a[i]` values). The wrong machine side is the REAL
///     `encode_neon_uaddw` model.
///   * widen WITHOUT the addend — drops the `Vn` wide operand (an SXTL/SSHLL#0;
///     diverges whenever the addend lane is nonzero).
///   * low as high — reads the HIGH `.4S` half `[2,3]` instead of the LOW
///     `[0,1]` (the silent SADDW/SADDW2 lane-select miscompile).
///   * truncating 32-bit add — adds the source lane into the addend's LOW 32
///     bits then sign-extends (drops the addend's high word and the carry;
///     diverges whenever the addend exceeds 32 bits or the 32-bit sum's bit 31
///     disagrees with the true high word).
pub fn neon_saddw_wrong_encoding_controls() -> Vec<ProofObligation> {
    let in_arr = NEON_SADDW_IN_ARR;
    let out_arr = VectorArrangement::D2;
    let vn = var_128("vn");
    let vm = var_128("vm");

    // Wrong: SXTL (SSHLL #0) — widens the source but DROPS the Vn addend.
    let wrong_no_addend = |_vn: &SmtExpr, vm: &SmtExpr| -> SmtExpr {
        let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
            .map(|j| lane_extract(vm, in_arr, j).sign_ext(32))
            .collect();
        lane_concat(&lanes)
    };
    // Wrong: truncating 32-bit add — adds into the addend's low 32 bits, then
    // sign-extends (drops the addend's high word and the carry out of bit 31).
    let wrong_truncating = |vn: &SmtExpr, vm: &SmtExpr| -> SmtExpr {
        let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
            .map(|j| {
                let addend32 = lane_extract(vn, out_arr, j).extract(31, 0);
                let m = lane_extract(vm, in_arr, j);
                addend32.bvadd(m).sign_ext(32)
            })
            .collect();
        lane_concat(&lanes)
    };

    vec![
        neon_uaddw_obligation(
            "WRONG: SaddwV.2D encoded as UADDW (zero-extending, sign confusion) must REFUTE",
            neon_source_saddw_from_halves(false),
            encode_neon_uaddw(in_arr, false, &vn, &vm),
        ),
        neon_uaddw_obligation(
            "WRONG: SaddwV.2D encoded WITHOUT the wide addend (SXTL) must REFUTE",
            neon_source_saddw_from_halves(false),
            wrong_no_addend(&vn, &vm),
        ),
        neon_uaddw_obligation(
            "WRONG: SaddwV.2D encoded as SADDW2 (HIGH half select) must REFUTE",
            neon_source_saddw_from_halves(false),
            encode_neon_saddw(in_arr, true, &vn, &vm),
        ),
        neon_uaddw_obligation(
            "WRONG: SaddwV.2D encoded as a TRUNCATING 32-bit add must REFUTE",
            neon_source_saddw_from_halves(false),
            wrong_truncating(&vn, &vm),
        ),
    ]
}

/// The FAITHFUL SIGNED widening add-wide obligations the coverage gate CREDITS
/// for `NeonSaddwV`/`NeonSaddw2V` — one whole-register D-pair obligation per
/// opcode (both `.2D` lanes concatenated).
pub fn all_neon_saddw_proofs() -> Vec<ProofObligation> {
    vec![proof_neon_saddwv_2d(), proof_neon_saddw2v_2d()]
}

// ---------------------------------------------------------------------------
// FAITHFUL vector multiply-ACCUMULATE proof (MLA.4S)
// ---------------------------------------------------------------------------
//
// SOUNDNESS — credits the coverage gate for `NeonMlaV` (`MLA Vd.4S, Vn.4S,
// Vm.4S`), the same-width integer multiply-accumulate the neon_predsum
// MLA-BY-MASK condsum accumulate emits for the `Gpr32` (`.4S`) masked-add
// `s(i32) += a_i32[iv] [if pred]`: the compare mask lane is exactly -1/0, so
// `MLA(acc, a, mask)` contributes `a * (-1) == -a mod 2^32` on TRUE lanes and
// `0` on FALSE lanes — the accumulators hold the NEGATED predicated sum,
// folded at the drain by one wrapping `SubRR` (replacing the AND + ADD.4S
// pair with ONE op per Q). The obligation covers ARBITRARY multiplier lanes,
// so the by-mask emission (like the SMLAL-by-mask precedent) needs no special
// case.
//
// Same D-REGISTER-PAIR faithful obligation shape as UDOT (the tied-accumulate
// class: `Vd` is BOTH source and destination): the SOURCE slices the 32-bit
// accumulator lane of `Vd` and the multiplicand/multiplier lanes of `Vn`/`Vm`
// DIRECTLY from the raw 64-bit D-halves (`vd_lo/vd_hi/vn_lo/vn_hi/vm_lo/
// vm_hi`) and computes `acc_i + n_i * m_i` (32-bit ops — `bvmul` keeps the
// LOW 32 bits of the product and `bvadd` wraps, both mod 2^32 — exactly the
// ISA's truncating MLA), then reassembles; the MACHINE is the real
// `encode_neon_mla` over the reassembled whole registers
// (`Extract(Concat(hi, lo), ...)`). STRUCTURALLY DISTINCT (raw-half `Var`
// leaf vs an `Extract`-of-`Concat`), so `is_genuinely_proven()` holds; pure
// QF_BV over 6x64-bit vars.
//
// HONEST SCOPE — the D-pair obligation is EXACT here, no cross-half carry:
// each `.4S` output lane `i` reads ONLY `.4S` lane `i` of `Vd`/`Vn`/`Vm`,
// wholly within one D-half (lanes {0,1} in `lo`, {2,3} in `hi`). A WRONG
// encoding REFUTES (see `neon_mla_wrong_encoding_controls`): MLA-as-MLS
// (SUBTRACTS the product — flips the sign of every contribution, the exact
// U-bit miswire one bit away in the encoding), MLA-as-MUL (drops the `Vd`
// addend — the no-accumulate miscompile that loses the running sum), and a
// lane-swap (accumulates the product of the WRONG source lane pair).
// Reference: ARM DDI 0487 C7.2.200 MLA (vector) + B1.2 (Q = [Dlo, Dhi]
// register view).

/// The `.4S` arrangement of the `MLA` form the neon_predsum MLA-by-mask
/// condsum accumulate emits.
const NEON_MLA_ARR: VectorArrangement = VectorArrangement::S4;

/// SOURCE side for `MLA.4S`: slice the accumulator lane of `vd` and the
/// multiplicand/multiplier lanes of `vn`/`vm` per output lane DIRECTLY from
/// the raw D-halves and compute `acc_i + n_i * m_i` (all 32-bit, mod 2^32),
/// then reassemble. Independent of the machine encoder's whole-register
/// `Concat` threading (so the obligation is non-degenerate).
fn neon_source_mla_from_halves() -> SmtExpr {
    let vd_lo = SmtExpr::var("vd_lo", 64);
    let vd_hi = SmtExpr::var("vd_hi", 64);
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let vm_lo = SmtExpr::var("vm_lo", 64);
    let vm_hi = SmtExpr::var("vm_hi", 64);
    let arr = NEON_MLA_ARR;
    let lanes: Vec<SmtExpr> = (0..arr.lane_count())
        .map(|i| {
            let acc = lane_from_halves(&vd_lo, &vd_hi, arr, i);
            let n = lane_from_halves(&vn_lo, &vn_hi, arr, i);
            let m = lane_from_halves(&vm_lo, &vm_hi, arr, i);
            acc.bvadd(n.bvmul(m))
        })
        .collect();
    lane_concat(&lanes)
}

/// FAITHFUL: trust_ir per-lane `<4 x i32>` multiply-accumulate (D-pair) ==
/// NEON `MLA.4S` (tied accumulator).
pub fn proof_neon_mlav_lanewise_4s() -> ProofObligation {
    neon_udot_obligation(
        "NEON MlaV.4S lanewise mul-accumulate-intent == D-pair per-lane i32 multiply-accumulate (faithful)",
        neon_source_mla_from_halves(),
        encode_neon_mla(NEON_MLA_ARR, &var_128("vd"), &var_128("vn"), &var_128("vm")),
    )
}

/// NEGATIVE CONTROLS for `NeonMlaV`: correct MLA D-pair SOURCE paired with a
/// WRONG NEON `machine` expression. Each MUST refute (SAT counterexample):
///   * MLA as MLS — SUBTRACTS the product instead of adding it (the U-bit
///     miswire; flips the sign of every nonzero contribution).
///   * MLA as MUL — drops the `Vd` addend (the no-accumulate miscompile;
///     diverges whenever the prior accumulator lane is nonzero).
///   * lane-swap — accumulates the product of the NEXT source lane pair
///     (`(i+1) mod 4`), i.e. the right op over the WRONG lanes.
pub fn neon_mla_wrong_encoding_controls() -> Vec<ProofObligation> {
    let arr = NEON_MLA_ARR;
    let vd = var_128("vd");
    let vn = var_128("vn");
    let vm = var_128("vm");

    // Wrong: MLS — subtracts the product.
    let wrong_mls = |vd: &SmtExpr, vn: &SmtExpr, vm: &SmtExpr| -> SmtExpr {
        let lanes: Vec<SmtExpr> = (0..arr.lane_count())
            .map(|i| {
                let acc = lane_extract(vd, arr, i);
                let n = lane_extract(vn, arr, i);
                let m = lane_extract(vm, arr, i);
                acc.bvsub(n.bvmul(m))
            })
            .collect();
        lane_concat(&lanes)
    };
    // Wrong: MUL — drops the accumulator addend.
    let wrong_mul = |_vd: &SmtExpr, vn: &SmtExpr, vm: &SmtExpr| -> SmtExpr {
        let lanes: Vec<SmtExpr> = (0..arr.lane_count())
            .map(|i| {
                let n = lane_extract(vn, arr, i);
                let m = lane_extract(vm, arr, i);
                n.bvmul(m)
            })
            .collect();
        lane_concat(&lanes)
    };
    // Wrong: lane-swap — accumulates the product of the NEXT lane pair.
    let wrong_lane_swap = |vd: &SmtExpr, vn: &SmtExpr, vm: &SmtExpr| -> SmtExpr {
        let lanes: Vec<SmtExpr> = (0..arr.lane_count())
            .map(|i| {
                let acc = lane_extract(vd, arr, i);
                let s = (i + 1) % arr.lane_count();
                let n = lane_extract(vn, arr, s);
                let m = lane_extract(vm, arr, s);
                acc.bvadd(n.bvmul(m))
            })
            .collect();
        lane_concat(&lanes)
    };

    vec![
        neon_udot_obligation(
            "WRONG: MlaV.4S encoded as MLS (subtracting) must REFUTE",
            neon_source_mla_from_halves(),
            wrong_mls(&vd, &vn, &vm),
        ),
        neon_udot_obligation(
            "WRONG: MlaV.4S encoded as MUL (no accumulate) must REFUTE",
            neon_source_mla_from_halves(),
            wrong_mul(&vd, &vn, &vm),
        ),
        neon_udot_obligation(
            "WRONG: MlaV.4S accumulating the WRONG lane pair must REFUTE",
            neon_source_mla_from_halves(),
            wrong_lane_swap(&vd, &vn, &vm),
        ),
    ]
}

/// The FAITHFUL multiply-accumulate obligation the coverage gate CREDITS for
/// `NeonMlaV` (`MLA.4S`) — one whole-register D-pair obligation (all four
/// `.4S` lanes concatenated).
pub fn all_neon_mla_proofs() -> Vec<ProofObligation> {
    vec![proof_neon_mlav_lanewise_4s()]
}

// ---------------------------------------------------------------------------
// FAITHFUL pairwise widening ACCUMULATE proof (UADALP .4S -> .2D)
// ---------------------------------------------------------------------------
//
// SOUNDNESS — credits the coverage gate for `NeonUadalpV` (`UADALP Vd.2D,
// Vn.4S`), the unsigned pairwise widening accumulate the neon_array widening
// abs-sum vectorizer (TRACK D) emits for
// `s(i64) += zext64(abs_bits(a_i32[i] [+ inv]))` — per output lane `j`:
// `acc_j + zext64(n_{2j}) + zext64(n_{2j+1})`, replacing the UADDW/UADDW2
// pair (2 ops per Q) with ONE op. Both forms add the SAME four `zext64(u_s)`
// terms into the two `.2D` accumulator lanes (UADDW/UADDW2 groups source
// lanes {0,2}/{1,3}, UADALP the adjacent pairs {0,1}/{2,3}); the drain sums
// BOTH `.2D` lanes into one scalar i64, so the different grouping is a pure
// REASSOCIATION of modular (mod-2^64) addition — the folded total is
// identical for every input.
//
// Same D-REGISTER-PAIR faithful obligation shape as UDOT (the tied-accumulate
// class: `Vd` is BOTH source and destination — contrast the three-operand
// UADDW, whose addend is the separate register `Vn`): the SOURCE slices the
// `.2D` accumulator lane of `Vd` and the ADJACENT `.4S` source lane pair of
// `Vn` DIRECTLY from the raw 64-bit D-halves (`vd_lo/vd_hi/vn_lo/vn_hi`) and
// computes `acc_j + zext64(n_{2j}) + zext64(n_{2j+1})` (UNSIGNED u32->u64
// extension — the scalar chain's `Uxtw`), then reassembles; the MACHINE is
// the real `encode_neon_uadalp` over the reassembled whole registers
// (`Extract(Concat(hi, lo), ...)`). STRUCTURALLY DISTINCT (raw-half `Var`
// leaf vs an `Extract`-of-`Concat`), so `is_genuinely_proven()` holds; pure
// QF_BV over 4x64-bit vars.
//
// HONEST SCOPE — the D-pair obligation is EXACT here, no cross-half carry:
// each `.2D` output lane `j` reads ONLY `.2D` lane `j` of `Vd` and `.4S`
// lanes `{2j, 2j+1}` of `Vn`, and that adjacent pair lives wholly in one
// D-half ({0,1} in `lo`, {2,3} in `hi`). A WRONG encoding REFUTES (see
// `neon_uadalp_wrong_encoding_controls`): UADALP-as-SADALP (SIGN-extends the
// source lanes — diverges on every lane with bit 31 set, exactly the
// abs-sum's `>= 2^31` u32 bit patterns, i.e. the `i32::MIN` lanes),
// UADALP-as-UADDLP (drops the `Vd` addend — the no-accumulate miscompile),
// and a wrong-pairing (sums a STRADDLING lane pair instead of the adjacent
// one). Reference: ARM DDI 0487 C7.2.346 UADALP + B1.2 (Q = [Dlo, Dhi]
// register view).

/// The INPUT `.4S` arrangement of the `UADALP .4S -> .2D` form the widening
/// abs-sum vectorizer emits.
const NEON_UADALP_IN_ARR: VectorArrangement = VectorArrangement::S4;

/// SOURCE side for `UADALP.2D`: slice the `.2D` accumulator lane of `vd` and
/// the adjacent `.4S` source lane pair of `vn` per output lane DIRECTLY from
/// the raw D-halves and compute `acc_j + zext64(n_{2j}) + zext64(n_{2j+1})`
/// (UNSIGNED extension), then reassemble. Independent of the machine
/// encoder's whole-register `Concat` threading (so the obligation is
/// non-degenerate).
fn neon_source_uadalp_from_halves() -> SmtExpr {
    let vd_lo = SmtExpr::var("vd_lo", 64);
    let vd_hi = SmtExpr::var("vd_hi", 64);
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let in_arr = NEON_UADALP_IN_ARR;
    let out_arr = VectorArrangement::D2;
    let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
        .map(|j| {
            let acc = lane_from_halves(&vd_lo, &vd_hi, out_arr, j);
            let p0 = lane_from_halves(&vn_lo, &vn_hi, in_arr, 2 * j).zero_ext(32);
            let p1 = lane_from_halves(&vn_lo, &vn_hi, in_arr, 2 * j + 1).zero_ext(32);
            acc.bvadd(p0).bvadd(p1)
        })
        .collect();
    lane_concat(&lanes)
}

/// Assemble a faithful UADALP-shaped (tied accumulator + one vector input)
/// obligation: D-pair SOURCE vs a NEON `machine` expression over the
/// reassembled `Concat(hi, lo)` registers.
fn neon_uadalp_obligation(name: &str, source: SmtExpr, machine: SmtExpr) -> ProofObligation {
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: vec![
            ("vd_lo".to_string(), 64),
            ("vd_hi".to_string(), 64),
            ("vn_lo".to_string(), 64),
            ("vn_hi".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// FAITHFUL: trust_ir per-lane `<2 x i64>` unsigned pairwise widening
/// accumulate (D-pair) == NEON `UADALP.2D` (tied accumulator).
pub fn proof_neon_uadalpv_2d() -> ProofObligation {
    neon_uadalp_obligation(
        "NEON UadalpV.2D pairwise widening-accumulate-intent == D-pair per-lane u32-pair accumulate (faithful)",
        neon_source_uadalp_from_halves(),
        encode_neon_uadalp(NEON_UADALP_IN_ARR, &var_128("vd"), &var_128("vn")),
    )
}

/// NEGATIVE CONTROLS for `NeonUadalpV`: correct UADALP D-pair SOURCE paired
/// with a WRONG NEON `machine` expression. Each MUST refute (SAT
/// counterexample):
///   * UADALP as SADALP — SIGN-extends the source lanes instead of
///     zero-extending (signed/unsigned confusion; diverges whenever a source
///     lane has bit 31 set — exactly the abs-sum's `unsigned_abs >= 2^31` bit
///     patterns, i.e. the `i32::MIN` lanes).
///   * UADALP as UADDLP — drops the `Vd` addend (the no-accumulate
///     miscompile; diverges whenever the prior accumulator lane is nonzero).
///   * wrong-pairing — sums the STRADDLING lane pair `{2j+1, (2j+2) mod 4}`
///     instead of the adjacent `{2j, 2j+1}` (the right op over the WRONG
///     source pairing).
pub fn neon_uadalp_wrong_encoding_controls() -> Vec<ProofObligation> {
    let in_arr = NEON_UADALP_IN_ARR;
    let out_arr = VectorArrangement::D2;
    let vd = var_128("vd");
    let vn = var_128("vn");

    // Wrong: SADALP — sign-extends the source lane pair.
    let wrong_sadalp = |vd: &SmtExpr, vn: &SmtExpr| -> SmtExpr {
        let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
            .map(|j| {
                let acc = lane_extract(vd, out_arr, j);
                let p0 = lane_extract(vn, in_arr, 2 * j).sign_ext(32);
                let p1 = lane_extract(vn, in_arr, 2 * j + 1).sign_ext(32);
                acc.bvadd(p0).bvadd(p1)
            })
            .collect();
        lane_concat(&lanes)
    };
    // Wrong: UADDLP — widens the pairs but DROPS the Vd accumulator.
    let wrong_uaddlp = |_vd: &SmtExpr, vn: &SmtExpr| -> SmtExpr {
        let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
            .map(|j| {
                let p0 = lane_extract(vn, in_arr, 2 * j).zero_ext(32);
                let p1 = lane_extract(vn, in_arr, 2 * j + 1).zero_ext(32);
                p0.bvadd(p1)
            })
            .collect();
        lane_concat(&lanes)
    };
    // Wrong: straddling pairing — sums lanes {2j+1, (2j+2) mod 4}.
    let wrong_pairing = |vd: &SmtExpr, vn: &SmtExpr| -> SmtExpr {
        let lanes: Vec<SmtExpr> = (0..out_arr.lane_count())
            .map(|j| {
                let acc = lane_extract(vd, out_arr, j);
                let p0 = lane_extract(vn, in_arr, 2 * j + 1).zero_ext(32);
                let p1 = lane_extract(vn, in_arr, (2 * j + 2) % 4).zero_ext(32);
                acc.bvadd(p0).bvadd(p1)
            })
            .collect();
        lane_concat(&lanes)
    };

    vec![
        neon_uadalp_obligation(
            "WRONG: UadalpV.2D encoded as SADALP (sign-extending) must REFUTE",
            neon_source_uadalp_from_halves(),
            wrong_sadalp(&vd, &vn),
        ),
        neon_uadalp_obligation(
            "WRONG: UadalpV.2D encoded as UADDLP (no accumulate) must REFUTE",
            neon_source_uadalp_from_halves(),
            wrong_uaddlp(&vd, &vn),
        ),
        neon_uadalp_obligation(
            "WRONG: UadalpV.2D summing the WRONG (straddling) lane pair must REFUTE",
            neon_source_uadalp_from_halves(),
            wrong_pairing(&vd, &vn),
        ),
    ]
}

/// The FAITHFUL pairwise widening accumulate obligation the coverage gate
/// CREDITS for `NeonUadalpV` (`UADALP.2D`) — one whole-register D-pair
/// obligation (both `.2D` lanes concatenated).
pub fn all_neon_uadalp_proofs() -> Vec<ProofObligation> {
    vec![proof_neon_uadalpv_2d()]
}

// ---------------------------------------------------------------------------
// FAITHFUL per-BYTE NEON EXTRACT/CONCATENATE proofs (EXT.16B #4/#8/#12)
// ---------------------------------------------------------------------------
//
// SOUNDNESS — credits the coverage gate for `NeonExtV` (`EXT Vd.16B, Vn.16B,
// Vm.16B, #imm`), the byte-window extract the stencil vectorizer emits to form
// a shifted stencil stream in-register (`EXT(a_block_j, a_block_j+1, #4*d)` =
// the `a[i+d..)` window) instead of a third overlapping load stream.
//
// Same D-REGISTER-PAIR faithful obligation as the lane-wise compute proofs,
// specialised to the op's defining property: the output bytes CROSS the D-half
// boundary. Unlike CNT/ABS/UDOT (where every input of an output lane lives in
// ONE half), EXT's output byte `j` comes from byte `j+imm` of the concatenation
// `Vm:Vn` — depending on `j` and `imm` that is `vn_lo`, `vn_hi`, `vm_lo`, or
// `vm_hi` (e.g. `imm=12, j=15` -> byte 27 of the concatenation = `vm` byte 11 =
// `vm_hi` byte 3) — proving that crossing EXACTLY is the point of the
// obligation. The SOURCE
// selects every output byte DIRECTLY from the raw 64-bit D-halves
// (`Extract(Var(vn_lo|vn_hi|vm_lo|vm_hi), …)`) with the half-crossing resolved
// byte-by-byte at proof-construction time; the MACHINE is the real
// `encode_neon_ext` — the ARM ARM `Vm:Vn` concatenation-extract in its exact
// 128-bit form `(Vn >> imm*8) | (Vm << (128-imm*8))` over the reassembled whole
// registers. STRUCTURALLY DISTINCT
// (per-byte raw-half `Var` extracts vs whole-register shift/OR), so
// `is_genuinely_proven()` holds; provably EQUAL because selecting byte `j+imm`
// of the concatenation equals selecting the same bit-field from the packed
// halves.
//
// One obligation PER EMITTED IMMEDIATE (`#4`, `#8`, `#12` — the whole-i32-lane
// shifts; the encoder rejects everything else fail-closed). A WRONG encoding
// REFUTES (see `neon_ext_wrong_encoding_controls`): swapped operands (`Vm:Vn`
// vs `Vn:Vm` — the classic silent-miscompile window swap), a wrong immediate
// (off by one i32 lane), and ext-as-identity (passthrough `Vn`). Reference:
// ARM DDI 0487 C7.2.116 EXT + B1.2 (Q = {Dlo, Dhi} register view).

/// The byte arrangement of the `.16B` EXT form the stencil vectorizer emits.
const NEON_EXT_ARR: VectorArrangement = VectorArrangement::B16;

/// SOURCE side for `EXT.16B #imm`: select each output byte DIRECTLY from the
/// raw D-halves of `Vn`/`Vm` — output byte `j` is byte `j+imm` of `Vm:Vn`, i.e.
/// byte `j+imm` of `Vn` when `j+imm < 16`, else byte `j+imm-16` of `Vm`; the
/// D-half crossing (`lo` holds bytes 0-7, `hi` bytes 8-15) is resolved per byte
/// at construction time. Independent of the machine encoder's whole-register
/// shift/OR threading (so the obligation is non-degenerate).
fn neon_source_ext_from_halves(imm: u32) -> SmtExpr {
    debug_assert!(matches!(imm, 1 | 4 | 8 | 12 | 15));
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let vm_lo = SmtExpr::var("vm_lo", 64);
    let vm_hi = SmtExpr::var("vm_hi", 64);
    let arr = NEON_EXT_ARR;
    let lanes: Vec<SmtExpr> = (0..arr.lane_count())
        .map(|j| {
            let p = j + imm; // byte position in the 32-byte concatenation Vm:Vn
            if p < 16 {
                lane_from_halves(&vn_lo, &vn_hi, arr, p)
            } else {
                lane_from_halves(&vm_lo, &vm_hi, arr, p - 16)
            }
        })
        .collect();
    concat_lanes(&lanes, arr)
}

/// Assemble a faithful EXT-shaped (two vector inputs, plain def) obligation:
/// D-pair SOURCE vs a NEON `machine` expression over the reassembled
/// `Concat(hi, lo)` registers.
fn neon_ext_obligation(name: &str, source: SmtExpr, machine: SmtExpr) -> ProofObligation {
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: vec![
            ("vn_lo".to_string(), 64),
            ("vn_hi".to_string(), 64),
            ("vm_lo".to_string(), 64),
            ("vm_hi".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// FAITHFUL: trust_ir per-byte `Vm:Vn` window select (D-pair, crossing the
/// D-half boundary) == NEON `EXT.16B #imm`, for one emitted immediate.
pub fn proof_neon_extv_16b(imm: u32) -> ProofObligation {
    assert!(
        matches!(imm, 1 | 4 | 8 | 12 | 15),
        "EXT proof exists only for the emitted byte shifts (#4/#8/#12 middle \
         windows + #1/#15 stencil-count-if shifted-neighbor streams)"
    );
    neon_ext_obligation(
        &format!("NEON ExtV.16B lanewise-intent #{imm} == D-pair byte-window extract (faithful)"),
        neon_source_ext_from_halves(imm),
        encode_neon_ext(imm, &var_128("vn"), &var_128("vm")),
    )
}

/// NEGATIVE CONTROLS for `NeonExtV`: correct D-pair SOURCE paired with a WRONG
/// NEON `machine` expression. Each MUST refute (SAT counterexample):
///   * swapped operands — `EXT(Vm, Vn, #4)` instead of `EXT(Vn, Vm, #4)`: the
///     complementary window (`Vn:Vm` concatenation), the classic silent
///     stencil miscompile.
///   * wrong immediate — `#8` instead of `#4`: the window shifted by one whole
///     i32 lane.
///   * ext-as-identity — passthrough `Vn`: drops the window select entirely.
pub fn neon_ext_wrong_encoding_controls() -> Vec<ProofObligation> {
    let vn = var_128("vn");
    let vm = var_128("vm");
    vec![
        neon_ext_obligation(
            "WRONG: ExtV.16B #4 encoded with SWAPPED operands (Vm, Vn) must REFUTE",
            neon_source_ext_from_halves(4),
            encode_neon_ext(4, &vm, &vn),
        ),
        neon_ext_obligation(
            "WRONG: ExtV.16B #4 encoded with immediate #8 (off by one lane) must REFUTE",
            neon_source_ext_from_halves(4),
            encode_neon_ext(8, &vn, &vm),
        ),
        neon_ext_obligation(
            "WRONG: ExtV.16B #4 encoded as IDENTITY (passthrough Vn) must REFUTE",
            neon_source_ext_from_halves(4),
            vn.clone(),
        ),
        // STENCIL-NEIGHBOR direction controls: the count-if vectorizer's #1
        // (forward, `a[iv+1]`) and #15 (backward, `a[iv-1]`) are exact opposites;
        // encoding one as the other is the classic silent neighbor-window
        // miscompile and MUST refute, as must a swap or identity.
        neon_ext_obligation(
            "WRONG: ExtV.16B #1 encoded with the OPPOSITE direction #15 must REFUTE",
            neon_source_ext_from_halves(1),
            encode_neon_ext(15, &vn, &vm),
        ),
        neon_ext_obligation(
            "WRONG: ExtV.16B #1 encoded with SWAPPED operands (Vm, Vn) must REFUTE",
            neon_source_ext_from_halves(1),
            encode_neon_ext(1, &vm, &vn),
        ),
        neon_ext_obligation(
            "WRONG: ExtV.16B #1 encoded as IDENTITY (passthrough Vn) must REFUTE",
            neon_source_ext_from_halves(1),
            vn.clone(),
        ),
        neon_ext_obligation(
            "WRONG: ExtV.16B #15 encoded with the OPPOSITE direction #1 must REFUTE",
            neon_source_ext_from_halves(15),
            encode_neon_ext(1, &vn, &vm),
        ),
        neon_ext_obligation(
            "WRONG: ExtV.16B #15 encoded with SWAPPED operands (Vm, Vn) must REFUTE",
            neon_source_ext_from_halves(15),
            encode_neon_ext(15, &vm, &vn),
        ),
    ]
}

/// The FAITHFUL byte-window extract obligations the coverage gate CREDITS for
/// `NeonExtV` (`EXT.16B`) — one per emitted immediate: the whole-i32-lane
/// middle-window shifts `#4`/`#8`/`#12` (stencil vectorizer) plus the
/// single-byte shifted-NEIGHBOR streams `#1` (`a[iv+1]`) / `#15` (`a[iv-1]`)
/// the neon-bytesum stencil count-if forms.
pub fn all_neon_ext_proofs() -> Vec<ProofObligation> {
    vec![
        proof_neon_extv_16b(1),
        proof_neon_extv_16b(4),
        proof_neon_extv_16b(8),
        proof_neon_extv_16b(12),
        proof_neon_extv_16b(15),
    ]
}

// ---------------------------------------------------------------------------
// FAITHFUL 32-bit pair-swap proofs (REV64.4S)
// ---------------------------------------------------------------------------
//
// SOUNDNESS -- credits the coverage gate for `NeonRev64V` at the `.4S`
// arrangement (`REV64 Vd.4S, Vn.4S`), the in-register complex `{rp, ip}` pair
// swap the AoS stride-2 butterfly vectorizer (`neon_butterfly`) emits to form
// `[di, dr]` from the interleaved difference `[dr, di]` before the twiddle
// multiply. (The `.8B`/`.16B` byte forms remain UNEMITTED and fail-closed.)
//
// Same D-REGISTER-PAIR faithful obligation as the EXT window proofs,
// specialised to the op's defining property: output lane `j` is input lane
// `j ^ 1` -- the swap NEVER crosses a 64-bit container. The SOURCE selects
// every output 32-bit lane DIRECTLY from the raw 64-bit D-halves
// (`Extract(Var(vn_lo|vn_hi), ...)` at the swapped index); the MACHINE is the
// real `encode_neon_rev64_4s` -- the ARM ARM within-container element reverse
// in its whole-register shift/mask form
// `((Vn << 32) & ODD) | ((Vn >> 32) & EVEN)` over the reassembled register.
// STRUCTURALLY DISTINCT (per-lane raw-half `Var` extracts vs whole-register
// shift/mask/OR), so `is_genuinely_proven()` holds; provably EQUAL because
// each masked shift routes exactly the swapped lane into each output lane.
//
// A WRONG encoding REFUTES (see `neon_rev64_wrong_encoding_controls`):
// rev64-as-identity (passthrough), a DOUBLEWORD swap (crossing the container
// boundary -- the classic wrong-granularity permute), and a wrong shift
// amount (#16, half-lane smear). Reference: ARM DDI 0487 C7.2.219 REV64
// (vector) + B1.2 (Q = {Dlo, Dhi} register view).

/// The `.4S` arrangement of the REV64 form the butterfly vectorizer emits.
const NEON_REV64_ARR: VectorArrangement = VectorArrangement::S4;

/// SOURCE side for `REV64.4S`: select each output 32-bit lane DIRECTLY from
/// the raw D-halves of `Vn` -- output lane `j` is input lane `j ^ 1` (the
/// within-doubleword swap; lanes 0/1 live in `vn_lo`, 2/3 in `vn_hi`, so the
/// swap never crosses halves). Independent of the machine encoder's
/// whole-register shift/mask threading (non-degenerate obligation).
fn neon_source_rev64_4s_from_halves() -> SmtExpr {
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let arr = NEON_REV64_ARR;
    let lanes: Vec<SmtExpr> = (0..arr.lane_count())
        .map(|j| lane_from_halves(&vn_lo, &vn_hi, arr, j ^ 1))
        .collect();
    concat_lanes(&lanes, arr)
}

/// Assemble a faithful REV64-shaped (one vector input, plain def) obligation:
/// D-pair SOURCE vs a NEON `machine` expression over the reassembled
/// `Concat(hi, lo)` register.
fn neon_rev64_obligation(name: &str, source: SmtExpr, machine: SmtExpr) -> ProofObligation {
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: vec![("vn_lo".to_string(), 64), ("vn_hi".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// FAITHFUL: trust_ir per-lane swapped-index select (D-pair, swap contained
/// within each doubleword) == NEON `REV64.4S`.
pub fn proof_neon_rev64v_4s() -> ProofObligation {
    neon_rev64_obligation(
        "NEON Rev64V.4S pair-swap-intent == D-pair within-doubleword element swap (faithful)",
        neon_source_rev64_4s_from_halves(),
        encode_neon_rev64_4s(&var_128("vn")),
    )
}

/// FAITHFUL SOURCE for `REV64.16B`: each output BYTE is sliced DIRECTLY from the
/// raw D-halves at the container-reversed index. A container holds 8 bytes, so
/// reversing within it is `j ^ 7` — the exact analogue of the `.4S` form's
/// `j ^ 1` (2 lanes per container). XOR keeps the container-selecting high bits
/// untouched, so the permutation provably NEVER crosses a 64-bit boundary.
fn neon_source_rev64_16b_from_halves() -> SmtExpr {
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let arr = VectorArrangement::B16;
    let lanes: Vec<SmtExpr> = (0..arr.lane_count())
        .map(|j| lane_from_halves(&vn_lo, &vn_hi, arr, j ^ 7))
        .collect();
    concat_lanes(&lanes, arr)
}

/// FAITHFUL: trust_ir per-BYTE container-reversed select (D-pair, reversal
/// contained within each doubleword) == NEON `REV64.16B`.
///
/// This is the arrangement the VECTORIZER emits for a `<2 x i64>` bit-reversal
/// (`rewrite_bitreverse_to_neon`, vectorize.rs: `RBIT.16B` reverses bits within
/// each byte, then this `REV64.16B` reverses the byte ORDER within each i64
/// lane). The encoder admits it (`encode_vec_byte_2reg` accepts `B8`/`B16` and
/// `S4` for Rev64), so `.4S`-only evidence would leave the EMITTED `.16B` form
/// unproven.
pub fn proof_neon_rev64v_16b() -> ProofObligation {
    neon_rev64_obligation(
        "NEON Rev64V.16B byte-reverse-intent == D-pair within-doubleword byte reversal (faithful)",
        neon_source_rev64_16b_from_halves(),
        crate::neon_semantics::encode_neon_rev64_16b(&var_128("vn")),
    )
}

/// NEGATIVE CONTROLS for `NeonRev64V`: correct D-pair SOURCE paired with a
/// WRONG NEON `machine` expression. Each MUST refute (SAT counterexample):
///   * rev64-as-identity -- passthrough `Vn`: drops the swap entirely.
///   * DOUBLEWORD swap -- `Concat(lo_dw, hi_dw)` of the 64-bit containers:
///     the wrong-granularity permute (crosses the container boundary REV64
///     never crosses).
///   * wrong shift amount -- the shift/mask form with #16 instead of #32:
///     half-lane smear, no lane receives a whole swapped element.
pub fn neon_rev64_wrong_encoding_controls() -> Vec<ProofObligation> {
    let vn = var_128("vn");
    // DOUBLEWORD swap: bits [63:0] <-> [127:64] of the reassembled register.
    let dw_swap = vn
        .clone()
        .extract(63, 0)
        .concat(vn.clone().extract(127, 64));
    let dw_swap_16b = vn
        .clone()
        .extract(63, 0)
        .concat(vn.clone().extract(127, 64));
    // Wrong shift amount (#16): same mask/OR skeleton, half-lane smear.
    let even = SmtExpr::bv_const(0x0000_0000_FFFF_FFFF, 64);
    let odd = SmtExpr::bv_const(0xFFFF_FFFF_0000_0000, 64);
    let even_lanes = even.clone().concat(even);
    let odd_lanes = odd.clone().concat(odd);
    let sh16 = SmtExpr::bv_const(16, 128);
    let wrong_shift = vn
        .clone()
        .bvshl(sh16.clone())
        .bvand(odd_lanes)
        .bvor(vn.clone().bvlshr(sh16).bvand(even_lanes));
    vec![
        neon_rev64_obligation(
            "WRONG: Rev64V.4S encoded as IDENTITY (passthrough Vn) must REFUTE",
            neon_source_rev64_4s_from_halves(),
            vn.clone(),
        ),
        neon_rev64_obligation(
            "WRONG: Rev64V.4S encoded as a DOUBLEWORD swap (wrong granularity) must REFUTE",
            neon_source_rev64_4s_from_halves(),
            dw_swap,
        ),
        neon_rev64_obligation(
            "WRONG: Rev64V.4S encoded with shift #16 (half-lane smear) must REFUTE",
            neon_source_rev64_4s_from_halves(),
            wrong_shift,
        ),
        // `.16B` controls. The GRANULARITY control is the important one: it is
        // exactly the confusion an arrangement-incomplete gate would have
        // admitted (crediting the emitted `.16B` form with `.4S` evidence).
        neon_rev64_obligation(
            "WRONG: Rev64V.16B encoded as IDENTITY (passthrough Vn) must REFUTE",
            neon_source_rev64_16b_from_halves(),
            vn.clone(),
        ),
        neon_rev64_obligation(
            "WRONG: Rev64V.16B encoded with the .4S element-reverse (wrong container \
             GRANULARITY -- 32-bit elements instead of bytes) must REFUTE",
            neon_source_rev64_16b_from_halves(),
            encode_neon_rev64_4s(&vn),
        ),
        neon_rev64_obligation(
            "WRONG: Rev64V.16B encoded as a DOUBLEWORD swap (crosses the container \
             REV64 never crosses) must REFUTE",
            neon_source_rev64_16b_from_halves(),
            dw_swap_16b,
        ),
    ]
}

// ---------------------------------------------------------------------------
// POST-INDEX BASE-REGISTER WRITEBACK obligations (PARTIAL evidence)
// ---------------------------------------------------------------------------
//
// SCOPE -- READ THIS BEFORE CREDITING ANYTHING TO THESE.
//
// `NeonLd1Post` / `NeonSt1Post` / `NeonLdpQPost` / `NeonStpQPost` do TWO things:
//   (a) transfer a vector to/from memory, and
//   (b) advance the base register by the number of bytes transferred.
//
// These obligations prove (b) ONLY. They establish nothing whatsoever about (a):
// not the address computed, not the values moved, not aliasing, not ordering.
//
// (a) is NOT expressible faithfully in this crate today, and the reason is
// structural rather than a modeling choice we could make differently:
//   * `trust-cg-verify` has no dependency on `trust-cg-codegen`, so the real
//     byte-level memory encoders are unreachable; any machine side would be a
//     transcription of the bit layout, not an independent model.
//   * `SmtExpr::Var` is BitVec-only -- there is no array-sorted variable -- so
//     "arbitrary prior memory" cannot even be written down. Memory is limited to
//     `ConstArray` plus a finite `Store` chain, and the evaluator the coverage
//     gate actually runs excludes a general array `Select`.
//   * every per-opcode load/store obligation previously built on the array
//     theory was DEGENERATE (both sides from the same hand-written builder) and
//     was RETRACTED (`memory_proofs::MEMORY_RETRACTED_DEGENERATE`).
//
// So the four rows STAY RED. Their deferral reasons are rewritten to name this
// evidence and the surviving residue, rather than being deleted. Crediting (b)
// as if it covered the instruction would be exactly the overclaim the RED row
// exists to prevent.
//
// What (b) IS worth: every vectorizer that emits these in a loop silently
// depends on the base advancing by exactly the transfer size. A wrong scale or a
// wrong field would corrupt every subsequent iteration's address.

/// Assemble a post-index writeback obligation. SOURCE advances the base by the
/// ARCHITECTURAL transfer size; MACHINE decodes the real instruction word.
fn neon_post_index_writeback_obligation(
    name: String,
    bytes_transferred: u64,
    machine: SmtExpr,
) -> ProofObligation {
    let base = SmtExpr::var("base", 64);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name,
        trust_ir_expr: base.bvadd(SmtExpr::bv_const(bytes_transferred, 64)),
        aarch64_expr: machine,
        inputs: vec![("base".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// PARTIAL evidence for the four post-index NEON memory opcodes: the base
/// register advances by EXACTLY the number of bytes the instruction transfers.
/// See the section header -- this does NOT cover the memory transfer, and the
/// opcodes deliberately remain `DeferredUnfaithfulModel` RED.
pub fn all_neon_post_index_writeback_proofs() -> Vec<ProofObligation> {
    use crate::neon_semantics::{
        encode_neon_pair_post_writeback, encode_neon_single_post_writeback, neon_ldp_q_post_word,
        neon_stp_q_post_word,
    };
    let base = SmtExpr::var("base", 64);
    // The Q-pair forms move two 128-bit registers = 32 bytes.
    let ldp_word = neon_ldp_q_post_word(32, 1, 2, 0);
    let stp_word = neon_stp_q_post_word(32, 1, 2, 0);
    // LD1/ST1 at a Q arrangement move one 128-bit register = 16 bytes; the Q bit
    // is set in the assembled word (0 | Q=1 | 0011001 | ...).
    let ld1_word: u32 = (1 << 30) | (0b0011001 << 23) | (1 << 22) | (0b11111 << 16);
    let st1_word: u32 = (1 << 30) | (0b0011001 << 23) | (0b11111 << 16);
    vec![
        neon_post_index_writeback_obligation(
            "NEON LdpQPost post-index-writeback-intent == base advances by the 32 bytes \
             transferred (decoded imm7 << 4; PARTIAL -- says nothing about the load)"
                .to_string(),
            32,
            encode_neon_pair_post_writeback(&base, ldp_word),
        ),
        neon_post_index_writeback_obligation(
            "NEON StpQPost post-index-writeback-intent == base advances by the 32 bytes \
             transferred (decoded imm7 << 4; PARTIAL -- says nothing about the store)"
                .to_string(),
            32,
            encode_neon_pair_post_writeback(&base, stp_word),
        ),
        neon_post_index_writeback_obligation(
            "NEON Ld1Post post-index-writeback-intent == base advances by the 16 bytes \
             transferred (decoded Q bit; PARTIAL -- says nothing about the load)"
                .to_string(),
            16,
            encode_neon_single_post_writeback(&base, ld1_word),
        ),
        neon_post_index_writeback_obligation(
            "NEON St1Post post-index-writeback-intent == base advances by the 16 bytes \
             transferred (decoded Q bit; PARTIAL -- says nothing about the store)"
                .to_string(),
            16,
            encode_neon_single_post_writeback(&base, st1_word),
        ),
    ]
}

/// NEGATIVE CONTROLS for the post-index writeback; each MUST refute. These are
/// the realistic scale/field bugs: a loop whose base advances by the wrong
/// amount corrupts every subsequent iteration's address.
pub fn neon_post_index_writeback_wrong_encoding_controls() -> Vec<ProofObligation> {
    use crate::neon_semantics::{
        encode_neon_pair_post_writeback, encode_neon_single_post_writeback, neon_ldp_q_post_word,
    };
    let base = SmtExpr::var("base", 64);
    vec![
        neon_post_index_writeback_obligation(
            "WRONG: LdpQPost writeback encoded with imm7 for 16 bytes (HALF the pair \
             transfer) must REFUTE"
                .to_string(),
            32,
            encode_neon_pair_post_writeback(&base, neon_ldp_q_post_word(16, 1, 2, 0)),
        ),
        neon_post_index_writeback_obligation(
            "WRONG: LdpQPost writeback encoded with a NEGATIVE imm7 (-32) must REFUTE".to_string(),
            32,
            encode_neon_pair_post_writeback(&base, neon_ldp_q_post_word(-32, 1, 2, 0)),
        ),
        neon_post_index_writeback_obligation(
            "WRONG: Ld1Post writeback encoded with Q=0 (8 bytes, the D-form transfer) \
             where the Q-form moved 16 must REFUTE"
                .to_string(),
            16,
            encode_neon_single_post_writeback(
                &base,
                (0b0011001 << 23) | (1 << 22) | (0b11111 << 16),
            ),
        ),
    ]
}

// ---------------------------------------------------------------------------
// FAITHFUL byte-replicated immediate proof (MOVI, byte form)
// ---------------------------------------------------------------------------
//
// SOUNDNESS -- credits the coverage gate for `NeonMovi`, the constant
// materialization the vectorizers emit for accumulator zeroing, all-ones masks,
// and byte thresholds.
//
// The deferral this replaces named the trap: "the registered replicated-byte
// identity is degenerate X==X". The old `neon_encoding_proofs::proof_movi_immediate`
// literally re-ran `encode_neon_movi`'s own `for .. { result = byte.concat(result) }`
// loop on the trust_ir side, so both sides were the same tree.
//
// Two changes break that:
//   * the immediate is a symbolic 8-bit `Var`, not a concrete `u8`. The old proof
//     could only ever state a fact about ONE constant; this states it for EVERY
//     byte value, which is what the emitters actually rely on (they pass 0, 1,
//     0x0F, 10, 39, 96, ...).
//   * the SOURCE expresses replication ARITHMETICALLY -- `zext(imm8) * 0x01..01`
//     per element -- while the MACHINE builds it STRUCTURALLY, as a Concat chain.
//     "Multiply by the all-ones-bytes constant" and "concatenate the byte N
//     times" are the same value by a non-trivial identity, so the solver has to
//     actually prove the replication rather than match syntax.

/// The Q=1 element views of a byte-replicated MOVI: (arrangement, label, the
/// per-element replication constant `0x01..01`).
const NEON_MOVI_REPL: &[(VectorArrangement, &str, u64)] = &[
    (VectorArrangement::B16, "16b", 0x01),
    (VectorArrangement::H8, "8h", 0x0101),
    (VectorArrangement::S4, "4s", 0x0101_0101),
    (VectorArrangement::D2, "2d", 0x0101_0101_0101_0101),
];

/// Assemble one byte-form MOVI obligation at the `src_arr` element view.
fn neon_movi_broadcast_obligation(
    name: String,
    src_arr: VectorArrangement,
    mach_q: u32,
    repl: u64,
) -> ProofObligation {
    let imm8 = SmtExpr::var("movi_imm8", 8);
    let lane_bits = src_arr.lane_bits();
    // SOURCE: each element is the byte replicated ARITHMETICALLY across it.
    let widened = if lane_bits == 8 {
        imm8.clone()
    } else {
        imm8.clone().zero_ext(lane_bits - 8)
    };
    let elem = widened.bvmul(SmtExpr::bv_const(repl, lane_bits));
    let lanes: Vec<SmtExpr> = (0..src_arr.lane_count()).map(|_| elem.clone()).collect();
    let src = concat_lanes(&lanes, src_arr);
    let mach = crate::neon_semantics::encode_neon_movi_byte_reg(mach_q, &imm8);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name,
        trust_ir_expr: src,
        aarch64_expr: mach,
        inputs: vec![("movi_imm8".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// The FAITHFUL byte-replicated-immediate obligations the coverage gate CREDITS
/// for `NeonMovi`, one per element view of the Q=1 register write. Every
/// emission site allocates an `Fpr128` destination, so Q=1 is the emitted form;
/// the `.16B`/`.8H`/`.4S`/`.2D` views all describe that same write and together
/// pin the replication at every element granularity a consumer might read it at.
pub fn all_neon_movi_proofs() -> Vec<ProofObligation> {
    NEON_MOVI_REPL
        .iter()
        .map(|(arr, label, repl)| {
            neon_movi_broadcast_obligation(
                format!(
                    "NEON Movi.{label} byte-replicated-immediate-intent == symbolic imm8 \
                     replicated across every element (faithful)"
                ),
                *arr,
                1,
                *repl,
            )
        })
        .collect()
}

/// NEGATIVE CONTROLS for `NeonMovi`; each MUST refute.
///   * Q=0 encoding where the Q=1 register write was intended -- the upper half
///     is wrongly zeroed.
///   * WRONG REPLICATION CONSTANT -- replicating into only the low byte of each
///     element (`* 1`) instead of every byte, i.e. the "forgot to broadcast" bug.
pub fn neon_movi_wrong_encoding_controls() -> Vec<ProofObligation> {
    let imm8 = SmtExpr::var("movi_imm8", 8);
    vec![
        neon_movi_broadcast_obligation(
            "WRONG: Movi.16b encoded with Q=0 (upper half wrongly zeroed) must REFUTE".to_string(),
            VectorArrangement::B16,
            0,
            0x01,
        ),
        {
            // SOURCE replicates into every byte of each .4S element; MACHINE is
            // given a register whose elements only carry the byte in bits[7:0].
            let elem = imm8.clone().zero_ext(24);
            let lanes: Vec<SmtExpr> = (0..4).map(|_| elem.clone()).collect();
            ProofObligation {
                machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
                name: "WRONG: Movi.4s encoded as a ZERO-EXTENDED byte per element (replication \
                       dropped) must REFUTE"
                    .to_string(),
                trust_ir_expr: concat_lanes(&lanes, VectorArrangement::S4),
                aarch64_expr: crate::neon_semantics::encode_neon_movi_byte_reg(1, &imm8),
                inputs: vec![("movi_imm8".to_string(), 8)],
                preconditions: vec![],
                fp_inputs: vec![],
                category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
            }
        },
    ]
}

// ---------------------------------------------------------------------------
// FAITHFUL GPR-into-selected-lane insertion proof (INS (general))
// ---------------------------------------------------------------------------
//
// SOUNDNESS -- credits the coverage gate for `NeonInsGen` (`INS Vd.<T>[lane], Rn`),
// the TIED-destination insert the iota/lane-materialization paths emit.
//
// The deferral this replaces asked for all three axes at once: "a faithful
// tied-destination, arrangement, and lane-index insertion obligation". All three
// are covered here, and the TIED axis is the one that distinguishes this from
// every other NEON obligation so far: the instruction's correctness is as much
// about the lanes it must NOT disturb as about the one it writes. Because every
// 128-bit arrangement has >= 2 lanes, at least one PRESERVED lane always appears
// in the obligation, so lane preservation is genuinely constrained rather than
// assumed.

/// The emitted `INS (general)` element sizes: (arrangement, label, GPR width).
const NEON_INS_GEN_FORMS: &[(VectorArrangement, &str, u32)] = &[
    (VectorArrangement::B16, "16b", 32),
    (VectorArrangement::H8, "8h", 32),
    (VectorArrangement::S4, "4s", 64),
    (VectorArrangement::D2, "2d", 64),
];

/// Assemble one INS-(general) obligation. `src_*` describe the lane the SOURCE
/// intends to overwrite; `mach_*` what the machine encoder is given.
fn neon_ins_gen_obligation(
    name: String,
    src_arr: VectorArrangement,
    src_lane: u32,
    mach_arr: VectorArrangement,
    mach_lane: u32,
    gpr_bits: u32,
) -> ProofObligation {
    let vd_lo = SmtExpr::var("vd_lo", 64);
    let vd_hi = SmtExpr::var("vd_hi", 64);
    let rn = SmtExpr::var("rn", gpr_bits);
    // SOURCE: splice the D-pair lanes, substituting the TRUNCATED GPR at the
    // target lane and PRESERVING every other lane, sliced from the raw halves.
    let lane_bits = src_arr.lane_bits();
    let inserted = if gpr_bits > lane_bits {
        rn.clone().extract(lane_bits - 1, 0)
    } else {
        rn.clone()
    };
    let lanes: Vec<SmtExpr> = (0..src_arr.lane_count())
        .map(|i| {
            if i == src_lane {
                inserted.clone()
            } else {
                lane_from_halves(&vd_lo, &vd_hi, src_arr, i)
            }
        })
        .collect();
    let src = concat_lanes(&lanes, src_arr);
    let mach =
        crate::neon_semantics::encode_neon_ins_general(&var_128("vd"), mach_arr, mach_lane, &rn);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name,
        trust_ir_expr: src,
        aarch64_expr: mach,
        inputs: vec![
            ("vd_lo".to_string(), 64),
            ("vd_hi".to_string(), 64),
            ("rn".to_string(), gpr_bits),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// The FAITHFUL per-(element size, lane) insertion obligations the coverage gate
/// CREDITS for `NeonInsGen`: `.16B` 16 + `.8H` 8 + `.4S` 4 + `.2D` 2 = 30.
pub fn all_neon_ins_gen_proofs() -> Vec<ProofObligation> {
    let mut proofs = Vec::new();
    for (arr, label, gpr_bits) in NEON_INS_GEN_FORMS {
        for lane in 0..arr.lane_count() {
            proofs.push(neon_ins_gen_obligation(
                format!(
                    "NEON InsGen.{label} lane{lane:02} gpr-insert-intent == D-pair lane splice, \
                     other lanes PRESERVED (faithful)"
                ),
                *arr,
                lane,
                *arr,
                lane,
                *gpr_bits,
            ));
        }
    }
    proofs
}

/// NEGATIVE CONTROLS for `NeonInsGen`; each MUST refute.
///   * WRONG LANE -- writes the right value into the wrong place AND corrupts a
///     lane that had to be preserved, so it fails on both axes at once.
///   * WRONG ELEMENT SIZE -- inserting at `.2D` where `.4S` was intended
///     overwrites 64 bits, destroying a neighbouring lane.
pub fn neon_ins_gen_wrong_encoding_controls() -> Vec<ProofObligation> {
    use VectorArrangement as VA;
    vec![
        neon_ins_gen_obligation(
            "WRONG: InsGen.4s lane0 encoded as lane1 (wrong LANE — also clobbers a \
             PRESERVED lane) must REFUTE"
                .to_string(),
            VA::S4,
            0,
            VA::S4,
            1,
            64,
        ),
        neon_ins_gen_obligation(
            "WRONG: InsGen.4s lane2 encoded as lane3 (wrong LANE) must REFUTE".to_string(),
            VA::S4,
            2,
            VA::S4,
            3,
            64,
        ),
        neon_ins_gen_obligation(
            "WRONG: InsGen.16b lane0 encoded as lane1 (wrong LANE) must REFUTE".to_string(),
            VA::B16,
            0,
            VA::B16,
            1,
            32,
        ),
        neon_ins_gen_obligation(
            "WRONG: InsGen.4s lane0 encoded at .2D (wrong element SIZE — overwrites 64 bits, \
             destroying the neighbouring lane) must REFUTE"
                .to_string(),
            VA::S4,
            0,
            VA::D2,
            0,
            64,
        ),
    ]
}

// ---------------------------------------------------------------------------
// FAITHFUL GPR-to-all-lanes broadcast proof (DUP (general))
// ---------------------------------------------------------------------------
//
// SOUNDNESS -- credits the coverage gate for `NeonDupGen` (`DUP Vd.<T>, Rn`).
//
// The deferral this replaces named the exact trap: "the registered broadcast
// identity is degenerate X==X". The old `neon_encoding_proofs::proof_dup_broadcast`
// declared its scalar AT LANE WIDTH, so `concat_lanes([scalar; n])` was LITERALLY
// the expression `encode_neon_dup` builds -- both sides the same tree.
//
// Two changes break that, and neither is cosmetic:
//   * the GPR is declared at its REAL width (64). Hardware reads `Wn = Xn[31:0]`
//     for B/H/S and truncates, so `Xn[lane_bits-1:0]` is the honest source value
//     -- and it forces `encode_neon_dup` down its TRUNCATION branch, the branch
//     the degenerate proof never exercised.
//   * the MACHINE side READS THE LANE BACK with the real `encode_neon_umov_general`
//     rather than restating the broadcast. So the obligation is "build the vector
//     with the real DUP encoder, extract lane k with the real UMOV encoder, and
//     you get the GPR's low bits back" -- a round trip through two independent
//     encoders, against a SOURCE that is a plain slice of the `Var` leaf.
//
// Every lane of every emitted element size is covered (30 obligations): a DUP
// that populated only lane 0 would satisfy a lane-0-only pin while dropping the
// broadcast entirely, which is precisely the bug worth catching.

/// The emitted `DUP (general)` element sizes: (arrangement, label, GPR width).
/// B/H/S read a 32-bit `Wn`; `.2D` reads a 64-bit `Xn`.
const NEON_DUP_GEN_FORMS: &[(VectorArrangement, &str, u32)] = &[
    (VectorArrangement::B16, "16b", 32),
    (VectorArrangement::H8, "8h", 32),
    (VectorArrangement::S4, "4s", 32),
    (VectorArrangement::D2, "2d", 64),
];

/// Assemble one DUP-(general) round-trip obligation. `src_arr` is the element
/// size the SOURCE intends; `mach_arr` what the DUP is encoded at; `read_arr` /
/// `lane` how the result is read back. Positives set all three equal.
fn neon_dup_gen_obligation(
    name: String,
    src_arr: VectorArrangement,
    mach_arr: VectorArrangement,
    read_arr: VectorArrangement,
    lane: u32,
    gpr_bits: u32,
) -> ProofObligation {
    use crate::neon_semantics::{encode_neon_dup, encode_neon_umov_general};
    let xn = SmtExpr::var("xn", 64);
    // SOURCE: a DIRECT slice of the GPR leaf -- the value the broadcast intends.
    let lb = src_arr.lane_bits();
    let src_lane = if lb < 64 {
        xn.clone().extract(lb - 1, 0)
    } else {
        xn.clone()
    };
    let src = umov_zext_to(src_lane, lb, gpr_bits);
    // MACHINE: real DUP encoder, then real UMOV read-back of lane `lane`.
    let mach = encode_neon_umov_general(&encode_neon_dup(mach_arr, &xn), read_arr, lane, gpr_bits);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name,
        trust_ir_expr: src,
        aarch64_expr: mach,
        inputs: vec![("xn".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// The FAITHFUL per-(element size, lane) broadcast obligations the coverage gate
/// CREDITS for `NeonDupGen`: `.16B` 16 + `.8H` 8 + `.4S` 4 + `.2D` 2 = 30.
pub fn all_neon_dup_gen_proofs() -> Vec<ProofObligation> {
    let mut proofs = Vec::new();
    for (arr, label, gpr_bits) in NEON_DUP_GEN_FORMS {
        for lane in 0..arr.lane_count() {
            proofs.push(neon_dup_gen_obligation(
                format!(
                    "NEON DupGen.{label} lane{lane:02} gpr-broadcast-intent == GPR low bits \
                     replicated to every lane (faithful)"
                ),
                *arr,
                *arr,
                *arr,
                lane,
                *gpr_bits,
            ));
        }
    }
    proofs
}

/// NEGATIVE CONTROLS for `NeonDupGen`; each MUST refute.
///
/// The wrong-ELEMENT-SIZE controls deliberately read back at lane >= 1. At lane 0
/// a `.2D` broadcast and a `.4S` broadcast share bits[31:0], and a `.4S` and a
/// `.16B` share bits[7:0], so a lane-0 version of these controls would be
/// VACUOUS -- it would "pass" while proving nothing.
pub fn neon_dup_gen_wrong_encoding_controls() -> Vec<ProofObligation> {
    use VectorArrangement as VA;
    vec![
        neon_dup_gen_obligation(
            "WRONG: DupGen.4s encoded at .2D (wrong element SIZE), read back at .4S lane1 \
             must REFUTE"
                .to_string(),
            VA::S4,
            VA::D2,
            VA::S4,
            1,
            32,
        ),
        neon_dup_gen_obligation(
            "WRONG: DupGen.16b encoded at .4S (wrong element SIZE), read back at .16B lane1 \
             must REFUTE"
                .to_string(),
            VA::B16,
            VA::S4,
            VA::B16,
            1,
            32,
        ),
        neon_dup_gen_obligation(
            "WRONG: DupGen.8h encoded at .16B (wrong element SIZE), read back at .8H lane1 \
             must REFUTE"
                .to_string(),
            VA::H8,
            VA::B16,
            VA::H8,
            1,
            32,
        ),
    ]
}

// ---------------------------------------------------------------------------
// FAITHFUL selected-lane broadcast proof (DUP (element))
// ---------------------------------------------------------------------------
//
// SOUNDNESS -- credits the coverage gate for `NeonDupElem`. The backend emits it
// at exactly two concrete forms, `DUP Vd.4S, Vn.S[0]` (the complex-butterfly
// twiddle broadcast) and `DUP Vd.2D, Vn.D[0]`, always with an `Fpr128`
// destination, hence always Q=1. Both arrangements are covered here at EVERY
// lane, not just the emitted lane 0: the lane index is what the permutation is
// ABOUT, so pinning only lane 0 would leave the selection axis unproven and
// would let a wrong-lane rewrite land silently if a later emitter picks lane 1.
//
// Non-degeneracy: the SOURCE replicates a lane sliced from the raw D-half `Var`s
// (`Extract(Var vn_lo | vn_hi, ..)`), the MACHINE replicates a lane sliced from
// the reassembled `Concat(vn_hi, vn_lo)`. Distinct leaves, as for the UMOV matrix
// this mirrors.

/// The Q=1 arrangements `NeonDupElem` is emitted at, with their name labels.
const NEON_DUP_ELEM_FORMS: &[(VectorArrangement, &str)] =
    &[(VectorArrangement::S4, "4s"), (VectorArrangement::D2, "2d")];

/// Assemble one DUP-(element) obligation. `src_*` describe the lane the SOURCE
/// intends to broadcast; `mach_*` what the machine encoder is actually given.
/// Positives set them equal; a control makes them differ.
fn neon_dup_elem_obligation(
    name: String,
    src_arr: VectorArrangement,
    src_lane: u32,
    mach_arr: VectorArrangement,
    mach_lane: u32,
) -> ProofObligation {
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    // SOURCE: the selected lane sliced DIRECTLY from the raw halves, replicated.
    let selected = lane_from_halves(&vn_lo, &vn_hi, src_arr, src_lane);
    let lanes: Vec<SmtExpr> = (0..src_arr.lane_count())
        .map(|_| selected.clone())
        .collect();
    let src = concat_lanes(&lanes, src_arr);
    let mach = crate::neon_semantics::encode_neon_dup_element(&var_128("vn"), mach_arr, mach_lane);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name,
        trust_ir_expr: src,
        aarch64_expr: mach,
        inputs: vec![("vn_lo".to_string(), 64), ("vn_hi".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// The FAITHFUL per-(arrangement, lane) broadcast obligations the coverage gate
/// CREDITS for `NeonDupElem`: `.4S` lanes 0..4 and `.2D` lanes 0..2 = 6.
pub fn all_neon_dup_elem_proofs() -> Vec<ProofObligation> {
    let mut proofs = Vec::new();
    for (arr, label) in NEON_DUP_ELEM_FORMS {
        for lane in 0..arr.lane_count() {
            proofs.push(neon_dup_elem_obligation(
                format!(
                    "NEON DupElem.{label} lane{lane:02} broadcast-intent == D-pair selected-lane \
                     replication (faithful)"
                ),
                *arr,
                lane,
                *arr,
                lane,
            ));
        }
    }
    proofs
}

/// NEGATIVE CONTROLS for `NeonDupElem`; each MUST refute.
///   * WRONG LANE -- the selection axis itself. Uses lane 0 vs lane 1, which
///     differ for a general register.
///   * WRONG ELEMENT SIZE -- broadcasting `.2D` lane 0 where `.4S` lane 0 was
///     intended replicates 64 bits instead of 32.
pub fn neon_dup_elem_wrong_encoding_controls() -> Vec<ProofObligation> {
    vec![
        neon_dup_elem_obligation(
            "WRONG: DupElem.4s lane0 encoded as lane1 (wrong LANE) must REFUTE".to_string(),
            VectorArrangement::S4,
            0,
            VectorArrangement::S4,
            1,
        ),
        neon_dup_elem_obligation(
            "WRONG: DupElem.4s lane1 encoded as lane0 (wrong LANE) must REFUTE".to_string(),
            VectorArrangement::S4,
            1,
            VectorArrangement::S4,
            0,
        ),
        neon_dup_elem_obligation(
            "WRONG: DupElem.2d lane0 encoded as lane1 (wrong LANE) must REFUTE".to_string(),
            VectorArrangement::D2,
            0,
            VectorArrangement::D2,
            1,
        ),
        neon_dup_elem_obligation(
            "WRONG: DupElem.4s lane0 encoded at .2D (wrong element SIZE -- replicates 64 \
             bits, not 32) must REFUTE"
                .to_string(),
            VectorArrangement::S4,
            0,
            VectorArrangement::D2,
            0,
        ),
    ]
}

// ---------------------------------------------------------------------------
// FAITHFUL cross-lane horizontal reduce proof (UMAXV.4S)
// ---------------------------------------------------------------------------
//
// SOUNDNESS -- credits the coverage gate for `NeonUmaxv`, the horizontal
// UNSIGNED maximum the vectorizer emits to collapse a `CMEQ.4S` compare mask to
// a scalar "any lane matched" answer (`vectorize.rs`
// `rewrite_horizontal_any_reduction_to_neon`). `.4S` is the ONLY emitted
// arrangement -- the rewrite bails unless the reduction is `I32EqAny` at `S4`,
// and the codegen encoder rejects every other arrangement fail-closed -- so a
// single obligation is arrangement-COMPLETE here.
//
// This is the first CROSS-LANE (as opposed to lane-wise) NEON obligation: the
// result is a scalar function of ALL lanes, not a per-lane image. Non-degeneracy
// is therefore established on TWO independent axes rather than the usual one:
//
//   * LEAVES -- the SOURCE slices each lane out of the raw 64-bit D-half `Var`s
//     (`Extract(Var vn_lo | vn_hi, ..)`), while the MACHINE folds over the
//     reassembled `Concat(vn_hi, vn_lo)` register.
//   * FOLD SHAPE -- the SOURCE is a BALANCED TREE using non-strict `bvuge`
//     selection; the MACHINE is a LINEAR LEFT fold using strict `bvugt`. Both
//     compute the unsigned maximum, but they are structurally different
//     expressions, so `is_genuinely_proven()` cannot be satisfied by accident.

/// The `.4S` arrangement -- the only one `NeonUmaxv` is emitted at.
const NEON_UMAXV_ARR: VectorArrangement = VectorArrangement::S4;

/// The four `.4S` lanes sliced DIRECTLY from the raw 64-bit D-halves.
fn neon_umaxv_source_lanes() -> Vec<SmtExpr> {
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    (0..NEON_UMAXV_ARR.lane_count())
        .map(|i| lane_from_halves(&vn_lo, &vn_hi, NEON_UMAXV_ARR, i))
        .collect()
}

/// FAITHFUL SOURCE for `UMAXV Sd, Vn.4S`: a BALANCED-TREE unsigned maximum with
/// non-strict `bvuge` selection over the D-pair lanes.
fn neon_source_umaxv_4s_from_halves() -> SmtExpr {
    let l = neon_umaxv_source_lanes();
    let umax = |a: SmtExpr, b: SmtExpr| SmtExpr::ite(a.clone().bvuge(b.clone()), a, b);
    umax(
        umax(l[0].clone(), l[1].clone()),
        umax(l[2].clone(), l[3].clone()),
    )
}

/// Assemble a UMAXV-shaped obligation: D-pair SOURCE vs a `machine` expression
/// over the reassembled register. The result is the 32-bit scalar destination.
fn neon_umaxv_obligation(name: &str, source: SmtExpr, machine: SmtExpr) -> ProofObligation {
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: vec![("vn_lo".to_string(), 64), ("vn_hi".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// FAITHFUL: trust_ir balanced-tree unsigned lane maximum == NEON `UMAXV.4S`.
pub fn proof_neon_umaxv_4s() -> ProofObligation {
    neon_umaxv_obligation(
        "NEON Umaxv.4S cross-lane-max-intent == D-pair unsigned horizontal maximum (faithful)",
        neon_source_umaxv_4s_from_halves(),
        crate::neon_semantics::encode_neon_umaxv(&var_128("vn"), VectorArrangement::S4),
    )
}

/// NEGATIVE CONTROLS for `NeonUmaxv`; each MUST refute.
///   * SIGNEDNESS confusion -- a signed maximum diverges on any MSB-set lane,
///     which is exactly the case the compare-mask reduction produces (`CMEQ`
///     writes all-ones lanes).
///   * NO REDUCTION -- lane 0 passed through: the fold is dropped entirely.
///   * WRONG ELEMENT SIZE -- the same linear fold instantiated at `.16B` and
///     `.8H`, i.e. reducing over the wrong container width.
pub fn neon_umaxv_wrong_encoding_controls() -> Vec<ProofObligation> {
    use crate::neon_semantics::encode_neon_umaxv;
    let vn = var_128("vn");
    // Signed horizontal max over the same reassembled register.
    let signed_max = {
        let mut acc = lane_extract(&vn, NEON_UMAXV_ARR, 0);
        for idx in 1..NEON_UMAXV_ARR.lane_count() {
            let lane = lane_extract(&vn, NEON_UMAXV_ARR, idx);
            acc = SmtExpr::ite(lane.clone().bvsgt(acc.clone()), lane, acc);
        }
        acc
    };
    vec![
        neon_umaxv_obligation(
            "WRONG: Umaxv.4S encoded as a SIGNED horizontal max (SMAXV) must REFUTE",
            neon_source_umaxv_4s_from_halves(),
            signed_max,
        ),
        neon_umaxv_obligation(
            "WRONG: Umaxv.4S encoded as lane0 passthrough (no cross-lane reduction) must REFUTE",
            neon_source_umaxv_4s_from_halves(),
            lane_extract(&vn, NEON_UMAXV_ARR, 0),
        ),
        neon_umaxv_obligation(
            "WRONG: Umaxv.4S encoded as a .16B byte-wise horizontal max (wrong element \
             SIZE) must REFUTE",
            neon_source_umaxv_4s_from_halves(),
            encode_neon_umaxv(&vn, VectorArrangement::B16).zero_ext(24),
        ),
        neon_umaxv_obligation(
            "WRONG: Umaxv.4S encoded as a .8H halfword-wise horizontal max (wrong element \
             SIZE) must REFUTE",
            neon_source_umaxv_4s_from_halves(),
            encode_neon_umaxv(&vn, VectorArrangement::H8).zero_ext(16),
        ),
    ]
}

/// The FAITHFUL cross-lane obligation the coverage gate CREDITS for `NeonUmaxv`.
/// `.4S` is arrangement-COMPLETE: it is the only form the vectorizer emits and
/// the only one the encoder admits.
pub fn all_neon_umaxv_proofs() -> Vec<ProofObligation> {
    vec![proof_neon_umaxv_4s()]
}

/// FAITHFUL SOURCE for `REV32.16B`: each output BYTE is sliced DIRECTLY from the
/// raw D-halves at the container-reversed index. A 32-bit container holds 4
/// bytes, so reversing within it is `j ^ 3` — the exact analogue of REV64.16B's
/// `j ^ 7` (8 bytes/container) and REV64.4S's `j ^ 1` (2 lanes/container). XOR
/// leaves the container-selecting high bits untouched, so the permutation
/// provably NEVER crosses a 32-bit boundary.
fn neon_source_rev32_16b_from_halves() -> SmtExpr {
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let arr = VectorArrangement::B16;
    let lanes: Vec<SmtExpr> = (0..arr.lane_count())
        .map(|j| lane_from_halves(&vn_lo, &vn_hi, arr, j ^ 3))
        .collect();
    concat_lanes(&lanes, arr)
}

/// FAITHFUL SOURCE for `REV32.8B` (Q=0): the low 8 bytes reversed within their
/// 32-bit containers exactly as at `.16B`, upper half ZERO.
fn neon_source_rev32_8b_from_halves() -> SmtExpr {
    let low_mask = SmtExpr::bv_const(0, 64).concat(SmtExpr::bv_const(u64::MAX, 64));
    neon_source_rev32_16b_from_halves().bvand(low_mask)
}

/// FAITHFUL: trust_ir per-BYTE container-reversed select (reversal contained
/// within each 32-bit word) == NEON `REV32.16B`.
pub fn proof_neon_rev32v_16b() -> ProofObligation {
    neon_rev64_obligation(
        "NEON Rev32V.16B byte-reverse-intent == D-pair within-word byte reversal (faithful)",
        neon_source_rev32_16b_from_halves(),
        crate::neon_semantics::encode_neon_rev32_16b(&var_128("vn")),
    )
}

/// FAITHFUL: the Q=0 form, upper half zeroed == NEON `REV32.8B`.
pub fn proof_neon_rev32v_8b() -> ProofObligation {
    neon_rev64_obligation(
        "NEON Rev32V.8B byte-reverse-intent == D-pair within-word byte reversal, \
         upper half zeroed (faithful, Q=0)",
        neon_source_rev32_8b_from_halves(),
        crate::neon_semantics::encode_neon_rev32_8b(&var_128("vn")),
    )
}

/// NEGATIVE CONTROLS for `NeonRev32V`. The CONTAINER-GRANULARITY pair is the
/// point: REV32 and REV64 are the same butterfly truncated at different
/// container widths, so confusing them is the realistic lowering bug, and the
/// `.8B`/`.16B` pair pins the Q=0 upper-half zeroing.
pub fn neon_rev32_wrong_encoding_controls() -> Vec<ProofObligation> {
    let vn = var_128("vn");
    vec![
        neon_rev64_obligation(
            "WRONG: Rev32V.16B encoded as IDENTITY (passthrough Vn) must REFUTE",
            neon_source_rev32_16b_from_halves(),
            vn.clone(),
        ),
        neon_rev64_obligation(
            "WRONG: Rev32V.16B encoded with the REV64.16B butterfly (wrong container \
             GRANULARITY -- reverses across the whole doubleword) must REFUTE",
            neon_source_rev32_16b_from_halves(),
            crate::neon_semantics::encode_neon_rev64_16b(&vn),
        ),
        neon_rev64_obligation(
            "WRONG: Rev32V.16B encoded with the .8B (Q=0) form -- upper half WRONGLY \
             zeroed -- must REFUTE",
            neon_source_rev32_16b_from_halves(),
            crate::neon_semantics::encode_neon_rev32_8b(&vn),
        ),
        neon_rev64_obligation(
            "WRONG: Rev32V.8B encoded with the .16B (Q=1) form -- upper half NOT zeroed -- \
             must REFUTE",
            neon_source_rev32_8b_from_halves(),
            crate::neon_semantics::encode_neon_rev32_16b(&vn),
        ),
    ]
}

/// The FAITHFUL byte-reverse obligations the coverage gate CREDITS for
/// `NeonRev32V`, one per EMITTED arrangement. Both come from the vectorizer's
/// `<4 x i32>` / mixed-width `reverse_bits()` lowering
/// (`vectorize.rs::vector_bitreverse_byte_arrangement_for_lanes`: `I32` with 4
/// lanes selects `B16`, with 2 lanes selects `B8`).
pub fn all_neon_rev32_proofs() -> Vec<ProofObligation> {
    vec![proof_neon_rev32v_16b(), proof_neon_rev32v_8b()]
}

/// The FAITHFUL byte/element-reverse obligations the coverage gate CREDITS for
/// `NeonRev64V`, one per EMITTED arrangement:
///   * `.4S` -- the complex-FFT butterfly's `{rp, ip}` pair swap (neon_butterfly);
///   * `.16B` -- the byte-order reversal inside the `<2 x i64>` bit-reverse
///     lowering (vectorize.rs `rewrite_bitreverse_to_neon`).
///
/// The encoder admits both (`encode_vec_byte_2reg`: `B8`/`B16` and `S4`), so
/// crediting only `.4S` would leave the emitted `.16B` form unproven.
pub fn all_neon_rev64_proofs() -> Vec<ProofObligation> {
    vec![proof_neon_rev64v_4s(), proof_neon_rev64v_16b()]
}

// ---------------------------------------------------------------------------
// FAITHFUL per-byte 8-bit reverse proof (RBIT.16B)
// ---------------------------------------------------------------------------
//
// SOUNDNESS -- credits the coverage gate for `NeonRbitV` at the `.16B`
// arrangement (`RBIT Vd.16B, Vn.16B`), the per-byte 8-bit bit reversal the
// `neon-bitrev` vectorizer emits for `out[i] = a[i].reverse_bits()` over a
// `[u8; N]` -- the EXACT instruction LLVM -O3 emits for that loop (4x
// `rbit.16b` over 64 bytes/iter). RBIT is a FIXED PERMUTATION: within each of
// the 16 bytes the 8 bits are reversed in place, and a bit NEVER crosses a byte
// boundary. (The `.8B` half-form remains UNEMITTED and fail-closed at the
// encoder along with REV32/REV64's byte forms.)
//
// The SOURCE side is the mathematical bit-permute built DIRECTLY from the raw
// 64-bit D-halves: every output bit is a SINGLE `Extract` of one input bit at
// the mirrored index (output bit `8k+p` <- input bit `8k+7-p`), reassembled by
// `Concat`. The MACHINE side is the real `encode_neon_rbit_16b` -- the classic
// within-byte SWAR reversal butterfly `((x>>1)&M1)|((x&M1)<<1)` / `..2..M2..` /
// `..4..M4..` in whole-register shift/mask/OR form over the reassembled
// register. STRUCTURALLY DISTINCT (128 per-bit `Extract` leaves vs a
// whole-register shift/mask/AND/OR tree), so `is_genuinely_proven()` holds --
// NOT the degenerate X==X reusing the encoder on both sides would be; provably
// EQUAL because the SWAR routes exactly the mirrored bit into each output
// position.
//
// A WRONG encoding REFUTES (see `neon_rbit_wrong_encoding_controls`):
// rbit-as-identity (passthrough -- drops the reversal), a byte-swap-within-
// halfword (`REV16.8B` -- a BYTE permutation, not a BIT reversal), and a
// 16-bit-lane bit reversal (the WRONG-WIDTH reverse: bits cross the byte
// boundary the per-byte RBIT never crosses). Reference: ARM DDI 0487,
// C7.2.218 RBIT (vector) + B1.2 (Q = {Dlo, Dhi} register view).

/// SOURCE side for `RBIT.16B`: select every output bit DIRECTLY from the raw
/// D-halves of `Vn`, mirrored WITHIN its byte -- output bit `8k+p` is input bit
/// `8k+7-p` (the byte's bits reversed; the reversal never leaves the byte, so
/// bytes 0..7 live in `vn_lo`, 8..15 in `vn_hi`). Independent of the machine
/// encoder's whole-register shift/mask threading (non-degenerate obligation).
fn neon_source_rbit_16b_from_halves() -> SmtExpr {
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let mut bytes: Vec<SmtExpr> = Vec::with_capacity(16);
    for k in 0..16u32 {
        let (half, local) = if k < 8 { (&vn_lo, k) } else { (&vn_hi, k - 8) };
        let base = local * 8;
        // Assemble the reversed byte MSB-first via `Concat` (hi in upper bits):
        // output MSB (position base+7) is input bit `base`; output LSB
        // (position base) is input bit `base+7`.
        let mut byte = half.clone().extract(base, base);
        for q in (base + 1)..=(base + 7) {
            byte = byte.concat(half.clone().extract(q, q));
        }
        bytes.push(byte);
    }
    // Concat all 16 output bytes, byte 0 at the LSB (register byte order).
    let mut result = bytes[0].clone();
    for b in &bytes[1..] {
        result = b.clone().concat(result);
    }
    result
}

/// Assemble a faithful RBIT-shaped (one vector input, plain def) obligation:
/// D-pair SOURCE vs a NEON `machine` expression over the reassembled
/// `Concat(hi, lo)` register.
fn neon_rbit_obligation(name: &str, source: SmtExpr, machine: SmtExpr) -> ProofObligation {
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs: vec![("vn_lo".to_string(), 64), ("vn_hi".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// FAITHFUL: trust_ir per-bit within-byte mirror select (D-pair, reversal
/// contained within each byte) == NEON `RBIT.16B`.
pub fn proof_neon_rbitv_16b() -> ProofObligation {
    neon_rbit_obligation(
        "NEON Rbitv.16B per-byte-reverse-intent == D-pair within-byte bit reversal (faithful)",
        neon_source_rbit_16b_from_halves(),
        encode_neon_rbit_16b(&var_128("vn")),
    )
}

/// FAITHFUL SOURCE for `RBIT.8B`: the LOW 8 bytes are bit-reversed within
/// themselves exactly as at `.16B`, and the upper 64 bits are ZERO — the
/// architectural Q=0 write behaviour. Built by masking the `.16B` D-pair source
/// so the two forms share one within-byte mirror definition and differ ONLY in
/// the upper-half semantics that distinguish them.
fn neon_source_rbit_8b_from_halves() -> SmtExpr {
    let low_mask = SmtExpr::bv_const(0, 64).concat(SmtExpr::bv_const(u64::MAX, 64));
    neon_source_rbit_16b_from_halves().bvand(low_mask)
}

/// FAITHFUL: trust_ir per-bit within-byte mirror select over the LOW 8 bytes,
/// upper half zeroed == NEON `RBIT.8B` (Q=0).
///
/// This is the arrangement the vectorizer emits on its MIXED-WIDTH bit-reverse
/// path (`vectorize.rs`: an `I64` plan whose bit-reverse instruction has `I32`
/// element type takes `lanes = vf`; `vf == 2` selects `NeonArrangement::B8`).
/// The encoder admits it (`encode_vec_byte_2reg` maps `B8` to `q=0`), so
/// `.16B`-only evidence would leave the emitted `.8B` form — and in particular
/// its upper-half zeroing — unproven.
pub fn proof_neon_rbitv_8b() -> ProofObligation {
    neon_rbit_obligation(
        "NEON Rbitv.8B per-byte-reverse-intent == D-pair within-byte bit reversal, \
         upper half zeroed (faithful, Q=0)",
        neon_source_rbit_8b_from_halves(),
        crate::neon_semantics::encode_neon_rbit_8b(&var_128("vn")),
    )
}

/// Swap the two bytes WITHIN each 16-bit halfword (`REV16.8B` shape):
/// `((v>>8)&0x00FF..)|((v<<8)&0xFF00..)`. A BYTE permutation, reused to build
/// the byte-swap and wrong-width controls.
fn neon_byteswap16(v: SmtExpr) -> SmtExpr {
    let bcast = |p: u64| {
        let h = SmtExpr::bv_const(p, 64);
        h.clone().concat(h)
    };
    let lo_mask = bcast(0x00ff_00ff_00ff_00ff);
    let hi_mask = bcast(0xff00_ff00_ff00_ff00);
    let sh8 = SmtExpr::bv_const(8, 128);
    v.clone()
        .bvlshr(sh8.clone())
        .bvand(lo_mask)
        .bvor(v.bvand(hi_mask).bvshl(sh8))
}

/// NEGATIVE CONTROLS for `NeonRbitV`: correct per-bit SOURCE paired with a
/// WRONG NEON `machine` expression. Each MUST refute (SAT counterexample):
///   * rbit-as-identity -- passthrough `Vn`: drops the reversal entirely.
///   * byte-swap-within-halfword (`REV16.8B`): swaps whole BYTES, never touches
///     the bits inside a byte -- a byte permutation, not a bit reversal.
///   * 16-bit-lane bit reversal -- the WRONG-WIDTH reverse (per-byte RBIT
///     followed by the halfword byte swap == reverse all 16 bits of each
///     halfword): bits cross the byte boundary the per-byte RBIT never crosses.
pub fn neon_rbit_wrong_encoding_controls() -> Vec<ProofObligation> {
    let vn = var_128("vn");
    vec![
        neon_rbit_obligation(
            "WRONG: Rbitv.16B encoded as IDENTITY (passthrough Vn) must REFUTE",
            neon_source_rbit_16b_from_halves(),
            vn.clone(),
        ),
        neon_rbit_obligation(
            "WRONG: Rbitv.16B encoded as a BYTE swap (REV16.8B, not a bit reverse) must REFUTE",
            neon_source_rbit_16b_from_halves(),
            neon_byteswap16(vn.clone()),
        ),
        neon_rbit_obligation(
            "WRONG: Rbitv.16B encoded as a 16-bit-lane bit reverse (wrong width) must REFUTE",
            neon_source_rbit_16b_from_halves(),
            neon_byteswap16(encode_neon_rbit_16b(&vn)),
        ),
        // `.8B` (Q=0) controls. The ARRANGEMENT-CONFUSION pair is the point:
        // each must refute, pinning that `.8B` and `.16B` are NOT
        // interchangeable — precisely what a `.16B`-only credit would have let
        // an emitted `.8B` inherit.
        neon_rbit_obligation(
            "WRONG: Rbitv.8B encoded as IDENTITY (passthrough Vn) must REFUTE",
            neon_source_rbit_8b_from_halves(),
            vn.clone(),
        ),
        neon_rbit_obligation(
            "WRONG: Rbitv.8B encoded with the .16B (Q=1) form — upper half NOT zeroed — \
             must REFUTE",
            neon_source_rbit_8b_from_halves(),
            encode_neon_rbit_16b(&vn),
        ),
        neon_rbit_obligation(
            "WRONG: Rbitv.16B encoded with the .8B (Q=0) form — upper half WRONGLY zeroed — \
             must REFUTE",
            neon_source_rbit_16b_from_halves(),
            crate::neon_semantics::encode_neon_rbit_8b(&vn),
        ),
    ]
}

/// The FAITHFUL per-byte-reverse obligations the coverage gate CREDITS for
/// `NeonRbitV`, one per EMITTED arrangement:
///   * `.16B` -- the `neon-bitrev` vectorizer's `[u8; N]` `reverse_bits` map and
///     the 4-lane i32 / 2-lane i64 vectorizer paths;
///   * `.8B` (Q=0) -- the vectorizer's MIXED-WIDTH path (i64 plan, i32
///     bit-reverse, `vf == 2`), whose upper-half zeroing `.16B` does not model.
pub fn all_neon_rbit_proofs() -> Vec<ProofObligation> {
    vec![proof_neon_rbitv_16b(), proof_neon_rbitv_8b()]
}

// ---------------------------------------------------------------------------
// Vector SHL proofs
// ---------------------------------------------------------------------------

/// Proof: trust_ir vector_shl -> NEON SHL at the specified arrangement.
///
/// trust_ir semantics: per-lane `bvshl` by immediate.
/// NEON semantics: `encode_neon_shl`.
fn proof_vector_shl(arrangement: VectorArrangement, imm: u32, label: &str) -> ProofObligation {
    let vn = symbolic_vector("vn", arrangement);
    let trust_ir_expr = map_lanes_binary_imm(&vn, imm as u64, arrangement, |a, b| a.bvshl(b));
    let neon_expr = encode_neon_shl(arrangement, &vn, imm);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("VectorShl -> NEON SHL.{} #imm={}", label, imm),
        trust_ir_expr,
        aarch64_expr: neon_expr,
        inputs: vector_inputs("vn", arrangement),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// Proof: trust_ir vector_shl -> NEON SHL.4H #4 (64-bit, 4x16-bit lanes, shift by 4).
pub fn proof_vector_shl_4h() -> ProofObligation {
    proof_vector_shl(VectorArrangement::H4, 4, "4H")
}

/// Proof: trust_ir vector_shl -> NEON SHL.4S #8 (128-bit, 4x32-bit lanes, shift by 8).
pub fn proof_vector_shl_4s() -> ProofObligation {
    proof_vector_shl(VectorArrangement::S4, 8, "4S")
}

// ---------------------------------------------------------------------------
// Vector USHR proofs
// ---------------------------------------------------------------------------

/// Proof: trust_ir vector_ushr -> NEON USHR at the specified arrangement.
///
/// trust_ir semantics: per-lane `bvlshr` by immediate.
/// NEON semantics: `encode_neon_ushr`.
fn proof_vector_ushr(arrangement: VectorArrangement, imm: u32, label: &str) -> ProofObligation {
    let vn = symbolic_vector("vn", arrangement);
    let trust_ir_expr = map_lanes_binary_imm(&vn, imm as u64, arrangement, |a, b| a.bvlshr(b));
    let neon_expr = encode_neon_ushr(arrangement, &vn, imm);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("VectorUshr -> NEON USHR.{} #imm={}", label, imm),
        trust_ir_expr,
        aarch64_expr: neon_expr,
        inputs: vector_inputs("vn", arrangement),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// Proof: trust_ir vector_ushr -> NEON USHR.8B #2 (64-bit, 8x8-bit lanes, shift by 2).
pub fn proof_vector_ushr_8b() -> ProofObligation {
    proof_vector_ushr(VectorArrangement::B8, 2, "8B")
}

/// Proof: trust_ir vector_ushr -> NEON USHR.2D #16 (128-bit, 2x64-bit lanes, shift by 16).
pub fn proof_vector_ushr_2d() -> ProofObligation {
    proof_vector_ushr(VectorArrangement::D2, 16, "2D")
}

/// Proof: trust_ir vector_ushr -> NEON USHR.4S #2 (128-bit, 4x32-bit lanes, shift by 2).
///
/// Covers the exact arrangement used by the `<4 x i32>` lane-wise logical
/// right-shift lowering (`select_v4i32_vector_shift` -> `NeonUshrVImm`).
pub fn proof_vector_ushr_4s() -> ProofObligation {
    proof_vector_ushr(VectorArrangement::S4, 2, "4S")
}

// ---------------------------------------------------------------------------
// Vector SSHR proofs
// ---------------------------------------------------------------------------

/// Proof: trust_ir vector_sshr -> NEON SSHR at the specified arrangement.
///
/// trust_ir semantics: per-lane `bvashr` by immediate.
/// NEON semantics: `encode_neon_sshr`.
fn proof_vector_sshr(arrangement: VectorArrangement, imm: u32, label: &str) -> ProofObligation {
    let vn = symbolic_vector("vn", arrangement);
    let trust_ir_expr = map_lanes_binary_imm(&vn, imm as u64, arrangement, |a, b| a.bvashr(b));
    let neon_expr = encode_neon_sshr(arrangement, &vn, imm);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("VectorSshr -> NEON SSHR.{} #imm={}", label, imm),
        trust_ir_expr,
        aarch64_expr: neon_expr,
        inputs: vector_inputs("vn", arrangement),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// Proof: trust_ir vector_sshr -> NEON SSHR.2S #1 (64-bit, 2x32-bit lanes, shift by 1).
pub fn proof_vector_sshr_2s() -> ProofObligation {
    proof_vector_sshr(VectorArrangement::S2, 1, "2S")
}

/// Proof: trust_ir vector_sshr -> NEON SSHR.8H #4 (128-bit, 8x16-bit lanes, shift by 4).
pub fn proof_vector_sshr_8h() -> ProofObligation {
    proof_vector_sshr(VectorArrangement::H8, 4, "8H")
}

/// Proof: trust_ir vector_sshr -> NEON SSHR.4S #4 (128-bit, 4x32-bit lanes, shift by 4).
///
/// Covers the exact arrangement used by the `<4 x i32>` lane-wise arithmetic
/// right-shift lowering (`select_v4i32_vector_shift` -> `NeonSshrVImm`).
pub fn proof_vector_sshr_4s() -> ProofObligation {
    proof_vector_sshr(VectorArrangement::S4, 4, "4S")
}

// ---------------------------------------------------------------------------
// Vector MLA proofs
// ---------------------------------------------------------------------------

/// Proof: trust_ir vector_mla -> NEON MLA at the specified arrangement.
///
/// trust_ir semantics: per-lane `va[i] + vn[i] * vm[i]`, reassembled with `concat_lanes`.
/// NEON semantics: `encode_neon_mla`.
fn proof_vector_mla(arrangement: VectorArrangement, label: &str) -> ProofObligation {
    let va = symbolic_vector("va", arrangement);
    let vn = symbolic_vector("vn", arrangement);
    let vm = symbolic_vector("vm", arrangement);

    let lane_count = arrangement.lane_count();
    let lanes: Vec<SmtExpr> = (0..lane_count)
        .map(|i| {
            let a = lane_extract(&va, arrangement, i);
            let n = lane_extract(&vn, arrangement, i);
            let m = lane_extract(&vm, arrangement, i);
            a.bvadd(n.bvmul(m))
        })
        .collect();
    let trust_ir_expr = concat_lanes(&lanes, arrangement);
    let neon_expr = encode_neon_mla(arrangement, &va, &vn, &vm);

    let mut inputs = vector_inputs("va", arrangement);
    inputs.extend(vector_inputs("vn", arrangement));
    inputs.extend(vector_inputs("vm", arrangement));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("VectorMla -> NEON MLA.{}", label),
        trust_ir_expr,
        aarch64_expr: neon_expr,
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// Proof: trust_ir vector_mla -> NEON MLA.8B (64-bit, 8x8-bit lanes).
pub fn proof_vector_mla_8b() -> ProofObligation {
    proof_vector_mla(VectorArrangement::B8, "8B")
}

/// Proof: trust_ir vector_mla -> NEON MLA.4S (128-bit, 4x32-bit lanes).
pub fn proof_vector_mla_4s() -> ProofObligation {
    proof_vector_mla(VectorArrangement::S4, "4S")
}

// ---------------------------------------------------------------------------
// Vector SMIN proofs
// ---------------------------------------------------------------------------

/// Proof: trust_ir vector_smin -> NEON SMIN at the specified arrangement.
fn proof_vector_smin(arrangement: VectorArrangement, label: &str) -> ProofObligation {
    let vn = symbolic_vector("vn", arrangement);
    let vm = symbolic_vector("vm", arrangement);
    let trust_ir_expr = map_lanes_binary(&vn, &vm, arrangement, |a, b| {
        SmtExpr::ite(a.clone().bvslt(b.clone()), a, b)
    });
    let neon_expr = encode_neon_smin(arrangement, &vn, &vm);

    let mut inputs = vector_inputs("vn", arrangement);
    inputs.extend(vector_inputs("vm", arrangement));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("VectorSmin -> NEON SMIN.{}", label),
        trust_ir_expr,
        aarch64_expr: neon_expr,
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// Proof: trust_ir vector_smin -> NEON SMIN.4H (64-bit, 4x16-bit lanes).
pub fn proof_vector_smin_4h() -> ProofObligation {
    proof_vector_smin(VectorArrangement::H4, "4H")
}

/// Proof: trust_ir vector_smin -> NEON SMIN.4S (128-bit, 4x32-bit lanes).
pub fn proof_vector_smin_4s() -> ProofObligation {
    proof_vector_smin(VectorArrangement::S4, "4S")
}

// ---------------------------------------------------------------------------
// Vector UMIN proofs
// ---------------------------------------------------------------------------

/// Proof: trust_ir vector_umin -> NEON UMIN at the specified arrangement.
fn proof_vector_umin(arrangement: VectorArrangement, label: &str) -> ProofObligation {
    let vn = symbolic_vector("vn", arrangement);
    let vm = symbolic_vector("vm", arrangement);
    let trust_ir_expr = map_lanes_binary(&vn, &vm, arrangement, |a, b| {
        SmtExpr::ite(a.clone().bvult(b.clone()), a, b)
    });
    let neon_expr = encode_neon_umin(arrangement, &vn, &vm);

    let mut inputs = vector_inputs("vn", arrangement);
    inputs.extend(vector_inputs("vm", arrangement));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("VectorUmin -> NEON UMIN.{}", label),
        trust_ir_expr,
        aarch64_expr: neon_expr,
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// Proof: trust_ir vector_umin -> NEON UMIN.8B (64-bit, 8x8-bit lanes).
pub fn proof_vector_umin_8b() -> ProofObligation {
    proof_vector_umin(VectorArrangement::B8, "8B")
}

/// Proof: trust_ir vector_umin -> NEON UMIN.8H (128-bit, 8x16-bit lanes).
pub fn proof_vector_umin_8h() -> ProofObligation {
    proof_vector_umin(VectorArrangement::H8, "8H")
}

// ---------------------------------------------------------------------------
// Vector SMAX proofs
// ---------------------------------------------------------------------------

/// Proof: trust_ir vector_smax -> NEON SMAX at the specified arrangement.
fn proof_vector_smax(arrangement: VectorArrangement, label: &str) -> ProofObligation {
    let vn = symbolic_vector("vn", arrangement);
    let vm = symbolic_vector("vm", arrangement);
    let trust_ir_expr = map_lanes_binary(&vn, &vm, arrangement, |a, b| {
        SmtExpr::ite(a.clone().bvsgt(b.clone()), a, b)
    });
    let neon_expr = encode_neon_smax(arrangement, &vn, &vm);

    let mut inputs = vector_inputs("vn", arrangement);
    inputs.extend(vector_inputs("vm", arrangement));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("VectorSmax -> NEON SMAX.{}", label),
        trust_ir_expr,
        aarch64_expr: neon_expr,
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// Proof: trust_ir vector_smax -> NEON SMAX.2S (64-bit, 2x32-bit lanes).
pub fn proof_vector_smax_2s() -> ProofObligation {
    proof_vector_smax(VectorArrangement::S2, "2S")
}

/// Proof: trust_ir vector_smax -> NEON SMAX.16B (128-bit, 16x8-bit lanes).
pub fn proof_vector_smax_16b() -> ProofObligation {
    proof_vector_smax(VectorArrangement::B16, "16B")
}

// ---------------------------------------------------------------------------
// Vector UMAX proofs
// ---------------------------------------------------------------------------

/// Proof: trust_ir vector_umax -> NEON UMAX at the specified arrangement.
fn proof_vector_umax(arrangement: VectorArrangement, label: &str) -> ProofObligation {
    let vn = symbolic_vector("vn", arrangement);
    let vm = symbolic_vector("vm", arrangement);
    let trust_ir_expr = map_lanes_binary(&vn, &vm, arrangement, |a, b| {
        SmtExpr::ite(a.clone().bvugt(b.clone()), a, b)
    });
    let neon_expr = encode_neon_umax(arrangement, &vn, &vm);

    let mut inputs = vector_inputs("vn", arrangement);
    inputs.extend(vector_inputs("vm", arrangement));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("VectorUmax -> NEON UMAX.{}", label),
        trust_ir_expr,
        aarch64_expr: neon_expr,
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// Proof: trust_ir vector_umax -> NEON UMAX.4H (64-bit, 4x16-bit lanes).
pub fn proof_vector_umax_4h() -> ProofObligation {
    proof_vector_umax(VectorArrangement::H4, "4H")
}

/// Proof: trust_ir vector_umax -> NEON UMAX.4S (128-bit, 4x32-bit lanes).
pub fn proof_vector_umax_4s() -> ProofObligation {
    proof_vector_umax(VectorArrangement::S4, "4S")
}

// ---------------------------------------------------------------------------
// Vector CMGT proofs
// ---------------------------------------------------------------------------

/// Proof: trust_ir vector_cmgt -> NEON CMGT at the specified arrangement.
fn proof_vector_cmgt(arrangement: VectorArrangement, label: &str) -> ProofObligation {
    let vn = symbolic_vector("vn", arrangement);
    let vm = symbolic_vector("vm", arrangement);

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

    let trust_ir_expr = map_lanes_binary(&vn, &vm, arrangement, |a, b| {
        SmtExpr::ite(a.bvsgt(b), all_ones_lane.clone(), zero_lane.clone())
    });
    let neon_expr = encode_neon_cmgt(arrangement, &vn, &vm);

    let mut inputs = vector_inputs("vn", arrangement);
    inputs.extend(vector_inputs("vm", arrangement));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("VectorCmgt -> NEON CMGT.{}", label),
        trust_ir_expr,
        aarch64_expr: neon_expr,
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// Proof: trust_ir vector_cmgt -> NEON CMGT.2S (64-bit, 2x32-bit lanes).
pub fn proof_vector_cmgt_2s() -> ProofObligation {
    proof_vector_cmgt(VectorArrangement::S2, "2S")
}

/// Proof: trust_ir vector_cmgt -> NEON CMGT.4S (128-bit, 4x32-bit lanes).
pub fn proof_vector_cmgt_4s() -> ProofObligation {
    proof_vector_cmgt(VectorArrangement::S4, "4S")
}

// ---------------------------------------------------------------------------
// Vector CMGE proofs
// ---------------------------------------------------------------------------

/// Proof: trust_ir vector_cmge -> NEON CMGE at the specified arrangement.
fn proof_vector_cmge(arrangement: VectorArrangement, label: &str) -> ProofObligation {
    let vn = symbolic_vector("vn", arrangement);
    let vm = symbolic_vector("vm", arrangement);

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

    let trust_ir_expr = map_lanes_binary(&vn, &vm, arrangement, |a, b| {
        SmtExpr::ite(a.bvsge(b), all_ones_lane.clone(), zero_lane.clone())
    });
    let neon_expr = encode_neon_cmge(arrangement, &vn, &vm);

    let mut inputs = vector_inputs("vn", arrangement);
    inputs.extend(vector_inputs("vm", arrangement));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!("VectorCmge -> NEON CMGE.{}", label),
        trust_ir_expr,
        aarch64_expr: neon_expr,
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// Proof: trust_ir vector_cmge -> NEON CMGE.4H (64-bit, 4x16-bit lanes).
pub fn proof_vector_cmge_4h() -> ProofObligation {
    proof_vector_cmge(VectorArrangement::H4, "4H")
}

/// Proof: trust_ir vector_cmge -> NEON CMGE.8H (128-bit, 8x16-bit lanes).
pub fn proof_vector_cmge_8h() -> ProofObligation {
    proof_vector_cmge(VectorArrangement::H8, "8H")
}

// ---------------------------------------------------------------------------
// FAITHFUL per-LANE NEON FP obligations (D-register-pair — LANE-PLUMBING ONLY)
// ---------------------------------------------------------------------------
//
// HONESTY — read before citing these as "FP correctness proofs". Both sides of
// every obligation express the per-lane IEEE-754 operation with the SAME
// `SmtExpr` FP node (`fp.add`/`fp.sub`/`fp.mul`/`fp.div`/`fp.gt` at RNE): there
// is no independent symbolic model of the FP circuit here, so these proofs
// carry NO symbolic-FP-arithmetic content. What they DO pin — and all they pin
// — is the LANE PLUMBING of the vector lowering:
//
//   * WHICH BITS feed the op: the SOURCE slices lane `i` DIRECTLY from the raw
//     64-bit D-halves (`Extract(Var(vn_lo|vn_hi), …)`) and REINTERPRETS them as
//     an IEEE value (`((_ to_fp eb sb) bits)` — the bit-cast form); the MACHINE
//     is the real `encode_neon_f*` lane encoder over lanes split from the
//     reassembled `Concat(vn_hi, vn_lo)` register. STRUCTURALLY DISTINCT
//     (raw-half `Var` leaf vs `Extract`-of-`Concat`), so `is_genuinely_proven`
//     holds and a WRONG-LANE-WIRING machine side (lane `i+1` for lane `i`)
//     REFUTES.
//   * WHICH OP and at WHICH LANE WIDTH: an op-confusion machine side
//     (FADD-as-FSUB, FMUL-as-FDIV, FCMGT-as-FCMGE/FCMEQ) REFUTES because the
//     shared FP theory distinguishes the operations; a wrong lane width
//     repacks the element boundaries and is ill-sorted/refuted.
//
// The SEMANTIC weight — that z3's FP theory (and the evaluation lane's
// integer-only `fp_bitmodel`) faithfully model the hardware FADD/FSUB/FMUL/
// FDIV/FCMGT — rests on (a) the scalar FP lowering proofs sharing the same
// model, and (b) the SILICON-VALIDATED differential bridge
// (`tests/bdefs_differential_bridge_neon_fp.rs`: `encode_neon_f*` vs real
// M-series NEON execution) + the whole-array bit-identity differential fuzz
// (`fpmapfuzz.py`). NEVER present these obligations as symbolic FP
// correctness; they are the vector-lowering analog of the scalar FP proofs'
// model-consistency, PLUS genuine lane/op/width-selection content.
//
// One obligation per (op, arrangement, lane) — every lane of `.4S` and `.2D`
// is pinned so a single-lane miswiring cannot hide. Reference: ARM DDI 0487
// C7.2.93/118/114/97 (FADD/FSUB/FMUL/FDIV vector), C7.2.96 (FCMGT register).

/// The IEEE (eb, sb) parameters of an FP lane at the arrangement's lane width.
fn fp_params(arrangement: VectorArrangement) -> (u32, u32) {
    match arrangement.lane_bits() {
        32 => (8, 24),
        64 => (11, 53),
        other => panic!("NEON FP lane obligations: invalid lane width {other}"),
    }
}

/// SOURCE-side FP lane leaf: lane `idx` sliced DIRECTLY from the raw D-halves
/// (`{prefix}_lo` / `{prefix}_hi` `Var`s), reinterpreted as IEEE bits.
fn fp_lane_from_halves(prefix: &str, arrangement: VectorArrangement, idx: u32) -> SmtExpr {
    let lo = SmtExpr::var(format!("{prefix}_lo"), 64);
    let hi = SmtExpr::var(format!("{prefix}_hi"), 64);
    let (eb, sb) = fp_params(arrangement);
    SmtExpr::bv_bits_to_fp(lane_from_halves(&lo, &hi, arrangement, idx), eb, sb)
}

/// MACHINE-side FP lane split: every lane of the REASSEMBLED
/// `Concat({prefix}_hi, {prefix}_lo)` register, reinterpreted as IEEE bits —
/// the symbolic analog of `neon_semantics::neon_fp_lanes`, fed to the real
/// `encode_neon_f*` lane encoders.
fn fp_lanes_from_concat(prefix: &str, arrangement: VectorArrangement) -> Vec<SmtExpr> {
    let reg = var_128(prefix);
    let (eb, sb) = fp_params(arrangement);
    (0..arrangement.lane_count())
        .map(|i| SmtExpr::bv_bits_to_fp(lane_extract(&reg, arrangement, i), eb, sb))
        .collect()
}

/// Assemble one faithful FP lane obligation: D-pair SOURCE lane vs lane `lane`
/// of the real NEON FP `machine` encoder over the reassembled registers.
fn neon_fp_lanewise_obligation<S, M>(
    op_label: &str,
    arrangement: VectorArrangement,
    lane: u32,
    source_op: S,
    machine: M,
) -> ProofObligation
where
    S: Fn(SmtExpr, SmtExpr) -> SmtExpr,
    M: Fn(VectorArrangement, &[SmtExpr], &[SmtExpr]) -> Vec<SmtExpr>,
{
    let arr_label = match arrangement {
        VectorArrangement::S4 => "4s",
        VectorArrangement::D2 => "2d",
        _ => "??",
    };
    let src = source_op(
        fp_lane_from_halves("vn", arrangement, lane),
        fp_lane_from_halves("vm", arrangement, lane),
    );
    let vn_lanes = fp_lanes_from_concat("vn", arrangement);
    let vm_lanes = fp_lanes_from_concat("vm", arrangement);
    let mach = machine(arrangement, &vn_lanes, &vm_lanes).swap_remove(lane as usize);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "NEON {op_label}.{arr_label} lane{lane} lanewise-fp-intent == D-pair per-lane \
             IEEE op (faithful LANE-PLUMBING; FP semantics via shared model, see module docs)"
        ),
        trust_ir_expr: src,
        aarch64_expr: mach,
        inputs: bitwise_inputs(128),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// All faithful NEON FP lane obligations: {FADD, FSUB, FMUL, FDIV, FCMGT} x
/// {.4S lanes 0..4, .2D lanes 0..2} = 30.
pub fn all_neon_fp_lanewise_proofs() -> Vec<ProofObligation> {
    use crate::neon_semantics::{
        encode_neon_fadd, encode_neon_fcmgt, encode_neon_fdiv, encode_neon_fmul, encode_neon_fsub,
    };
    use crate::smt::RoundingMode;
    let mut proofs = Vec::new();
    for &arr in &[VectorArrangement::S4, VectorArrangement::D2] {
        for lane in 0..arr.lane_count() {
            proofs.push(neon_fp_lanewise_obligation(
                "FaddV",
                arr,
                lane,
                |a, b| SmtExpr::fp_add(RoundingMode::RNE, a, b),
                |_, n, m| encode_neon_fadd(n, m),
            ));
            proofs.push(neon_fp_lanewise_obligation(
                "FsubV",
                arr,
                lane,
                |a, b| SmtExpr::fp_sub(RoundingMode::RNE, a, b),
                |_, n, m| encode_neon_fsub(n, m),
            ));
            proofs.push(neon_fp_lanewise_obligation(
                "FmulV",
                arr,
                lane,
                |a, b| SmtExpr::fp_mul(RoundingMode::RNE, a, b),
                |_, n, m| encode_neon_fmul(n, m),
            ));
            proofs.push(neon_fp_lanewise_obligation(
                "FdivV",
                arr,
                lane,
                |a, b| SmtExpr::fp_div(RoundingMode::RNE, a, b),
                |_, n, m| encode_neon_fdiv(n, m),
            ));
            // FCMGT: BV-mask output (all-ones iff ordered-greater; NaN => 0).
            let (ones, zero) = lane_mask_consts(arr);
            proofs.push(neon_fp_lanewise_obligation(
                "FcmgtV",
                arr,
                lane,
                move |a, b| SmtExpr::ite(a.fp_gt(b), ones.clone(), zero.clone()),
                encode_neon_fcmgt,
            ));
        }
    }
    proofs
}

/// NEGATIVE CONTROLS for the FP lane obligations: per (op, arrangement) a
/// WRONG-OP machine side (the discriminating op confusion) at lane 0, plus a
/// WRONG-LANE-WIRING machine side (machine lane 1 paired with source lane 0)
/// for each op family. Verifying any of these MUST refute.
pub fn neon_fp_lanewise_wrong_encoding_controls() -> Vec<ProofObligation> {
    use crate::neon_semantics::{
        encode_neon_fadd, encode_neon_fcmeq, encode_neon_fcmge, encode_neon_fdiv, encode_neon_fmul,
        encode_neon_fsub,
    };
    use crate::smt::RoundingMode;
    let mut controls = Vec::new();
    for &arr in &[VectorArrangement::S4, VectorArrangement::D2] {
        // Op confusions at lane 0.
        controls.push(neon_fp_lanewise_obligation(
            "FaddV-as-FSUB (WRONG-OP control)",
            arr,
            0,
            |a, b| SmtExpr::fp_add(RoundingMode::RNE, a, b),
            |_, n, m| encode_neon_fsub(n, m),
        ));
        controls.push(neon_fp_lanewise_obligation(
            "FsubV-as-FADD (WRONG-OP control)",
            arr,
            0,
            |a, b| SmtExpr::fp_sub(RoundingMode::RNE, a, b),
            |_, n, m| encode_neon_fadd(n, m),
        ));
        controls.push(neon_fp_lanewise_obligation(
            "FmulV-as-FDIV (WRONG-OP control)",
            arr,
            0,
            |a, b| SmtExpr::fp_mul(RoundingMode::RNE, a, b),
            |_, n, m| encode_neon_fdiv(n, m),
        ));
        controls.push(neon_fp_lanewise_obligation(
            "FdivV-as-FMUL (WRONG-OP control)",
            arr,
            0,
            |a, b| SmtExpr::fp_div(RoundingMode::RNE, a, b),
            |_, n, m| encode_neon_fmul(n, m),
        ));
        let (ones, zero) = lane_mask_consts(arr);
        {
            let (ones, zero) = (ones.clone(), zero.clone());
            controls.push(neon_fp_lanewise_obligation(
                "FcmgtV-as-FCMGE (WRONG-OP control)",
                arr,
                0,
                move |a, b| SmtExpr::ite(a.fp_gt(b), ones.clone(), zero.clone()),
                encode_neon_fcmge,
            ));
        }
        controls.push(neon_fp_lanewise_obligation(
            "FcmgtV-as-FCMEQ (WRONG-OP control)",
            arr,
            0,
            move |a, b| SmtExpr::ite(a.fp_gt(b), ones.clone(), zero.clone()),
            encode_neon_fcmeq,
        ));
        // Wrong-lane wiring: machine reads lane 1 where the source reads lane 0.
        controls.push(neon_fp_lanewise_obligation(
            "FaddV lane0-as-lane1 (WRONG-LANE-WIRING control)",
            arr,
            0,
            |a, b| SmtExpr::fp_add(RoundingMode::RNE, a, b),
            |_, n: &[SmtExpr], m: &[SmtExpr]| {
                let full = encode_neon_fadd(n, m);
                // Rotate: present lane 1's result in lane 0's slot.
                let mut rotated: Vec<SmtExpr> = full.clone();
                rotated[0] = full[1].clone();
                rotated
            },
        ));
    }
    controls
}

// ---------------------------------------------------------------------------
// FAITHFUL per-LANE NEON FP-REDUCTION-VECTORIZER (`neon_fpred`) obligations:
// FMLA/FMLS (.2D fused multiply-accumulate), UCVTF/SCVTF (.2D int->FP), and
// DUP Dd,Vn.D[lane] (.2D lane -> 64-bit scalar copy)
// ---------------------------------------------------------------------------
//
// SOUNDNESS — these credit the coverage gate for the 5 ops the IV-synthesized
// FP-reduction vectorizer (`neon_fpred`) emits, all at `.2D` (2 x f64):
//   * FMLA/FMLS (NeonFmlaV/NeonFmlsV): the fused, SINGLE-ROUNDING
//     multiply-accumulate / -subtract — the scalar FMADD `fp.fma` credit lifted
//     per lane. FMLA `Vd' = fma(Vn,Vm,Vd)`; FMLS `Vd' = fma(-Vn,Vm,Vd)` (the
//     PRODUCT negated, the ARM `E` bit — exactly FADD-vs-FSUB). The tied
//     accumulator `Vd` is an INDEPENDENT symbolic input (read AND written),
//     honestly modeling the tied def-use.
//   * UCVTF/SCVTF (NeonUcvtfV/NeonScvtfV): the per-lane int->FP convert — the
//     scalar UCVTF/SCVTF int->FP credit lifted per lane. SCVTF is the signed
//     `BvToFP`; UCVTF zero-extends each lane first so the shared signed `BvToFP`
//     node computes the UNSIGNED magnitude (the scalar-UCVTF trick — the scalar
//     `bv_to_fp(a,11,53)` X==X proof is degenerate + `msb=0`-limited, so the
//     conversion is modeled DIRECTLY here with z3's `to_fp` over the widened,
//     sign-bit-clear operand, valid across the FULL u64 range).
//   * DupScalarD (NeonDupScalarD): the 64-bit lane -> scalar bit-copy. Writing
//     `Dd` zeroes the upper 64 bits of `Qd` (scalar-D-register write semantics),
//     so the meaningful result is exactly the selected lane's 64 bits.
//
// Same D-REGISTER-PAIR faithfulness as the FP lane-wise proofs above: the SOURCE
// slices lane `lane` DIRECTLY from the raw 64-bit D-halves (`Extract(Var(vX_lo|
// vX_hi), …)`); the MACHINE is the real `encode_neon_{fmla,fmls,scvtf_vec,
// ucvtf_vec,dup_scalar_d}` encoder over the reassembled `Concat(hi, lo)`
// register (`Extract(Concat(hi, lo), …)`). STRUCTURALLY DISTINCT, so
// `is_genuinely_proven()` holds and the wrong-encoding controls REFUTE
// (opcode-bit confusion FMLA<->FMLS, accumulator miswire, sign confusion
// UCVTF<->SCVTF, and wrong-lane wiring on every family — both lane indices and
// the tied-vs-product operand axes appear). HONESTY: like the FP lane-wise
// proofs, both sides express the per-lane IEEE op with the SAME SMT FP node, so
// these certify the LANE/OP/WIDTH PLUMBING, NOT an independent FP-circuit model;
// the FP semantic weight rests on the shared QF_FP model + the silicon-validated
// differential bridge. The fused ops use `fp.fma` (SINGLE rounding), NOT
// `fp_mul`+`fp_add` — a round-twice machine model REFUTES.
//
// NOTE on Rn/Rm swap: the fused PRODUCT `Vn*Vm` is COMMUTATIVE, so a pure Rn/Rm
// swap is NON-discriminating (it correctly verifies, like the FADD/FMUL swaps).
// The load-bearing non-commutative wiring axis is the TIED ACCUMULATOR vs the
// product (the accumulator-miswire control) plus the lane index — both refuted.

/// The `.2D` (2 x f64) arrangement every `neon_fpred` op is emitted at.
const NEON_FPRED_ARR: VectorArrangement = VectorArrangement::D2;

/// Input descriptors for a 3-register (tied Vd + Vn + Vm) `.2D` FP obligation.
fn fpred_fma_inputs() -> Vec<(String, u32)> {
    vec![
        ("vd_lo".to_string(), 64),
        ("vd_hi".to_string(), 64),
        ("vn_lo".to_string(), 64),
        ("vn_hi".to_string(), 64),
        ("vm_lo".to_string(), 64),
        ("vm_hi".to_string(), 64),
    ]
}

/// Assemble one faithful FMLA/FMLS `.2D` lane obligation. SOURCE slices Vd/Vn/Vm
/// lane `lane` from the raw D-halves and applies the SINGLE-ROUNDING `fp.fma`
/// (product negated iff `source_negate_n`); MACHINE is `machine` (the real
/// FMLA/FMLS lane encoder, or a WRONG one for a control) over the reassembled
/// registers, at `lane`.
fn neon_fpred_fma_obligation<M>(
    name: String,
    lane: u32,
    source_negate_n: bool,
    machine: M,
) -> ProofObligation
where
    M: Fn(&[SmtExpr], &[SmtExpr], &[SmtExpr]) -> Vec<SmtExpr>,
{
    neon_fpred_fma_obligation_arr(name, NEON_FPRED_ARR, lane, source_negate_n, machine)
}

/// Arrangement-parametric FMLA/FMLS lane obligation (the `.2D` builder above
/// pins `NEON_FPRED_ARR`; the `.4S` (f32) complex-butterfly emitter
/// `neon_butterfly` and the f32 `neon_fmap` map-chain both emit `NeonFmlaV` at
/// `S4`). The per-lane semantics are IDENTICAL — the SAME SINGLE-rounding
/// `fp.fma` SOURCE leaf and the SAME real `encode_neon_{fmla,fmls}` machine
/// encoder — only the lane width (32 vs 64) and lane count (4 vs 2) differ.
fn neon_fpred_fma_obligation_arr<M>(
    name: String,
    arr: VectorArrangement,
    lane: u32,
    source_negate_n: bool,
    machine: M,
) -> ProofObligation
where
    M: Fn(&[SmtExpr], &[SmtExpr], &[SmtExpr]) -> Vec<SmtExpr>,
{
    use crate::smt::RoundingMode;
    let n_lane = fp_lane_from_halves("vn", arr, lane);
    let m_lane = fp_lane_from_halves("vm", arr, lane);
    let d_lane = fp_lane_from_halves("vd", arr, lane);
    let n_lane = if source_negate_n {
        n_lane.fp_neg()
    } else {
        n_lane
    };
    let src = SmtExpr::fp_fma(RoundingMode::RNE, n_lane, m_lane, d_lane);
    let vd_lanes = fp_lanes_from_concat("vd", arr);
    let vn_lanes = fp_lanes_from_concat("vn", arr);
    let vm_lanes = fp_lanes_from_concat("vm", arr);
    let mach = machine(&vd_lanes, &vn_lanes, &vm_lanes).swap_remove(lane as usize);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name,
        trust_ir_expr: src,
        aarch64_expr: mach,
        inputs: fpred_fma_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// The per-lane int->FP SOURCE leaf: `bv_to_fp` of the (optionally
/// zero-extended, for UNSIGNED) integer lane. Mirrors the machine encoders.
fn fpred_int_to_fp(signed: bool, lane: SmtExpr, lane_bits: u32, eb: u32, sb: u32) -> SmtExpr {
    use crate::smt::RoundingMode;
    if signed {
        SmtExpr::bv_to_fp(RoundingMode::RNE, lane, eb, sb)
    } else {
        SmtExpr::bv_to_fp(RoundingMode::RNE, lane.zero_ext(lane_bits), eb, sb)
    }
}

/// Assemble one faithful UCVTF/SCVTF `.2D` lane obligation. SOURCE converts the
/// integer lane sliced from the raw D-halves (`source_signed` selects SCVTF vs
/// UCVTF's zero-extend); MACHINE is the real per-lane int->FP encoder
/// (`machine_signed`) over the reassembled register. Positives set the two flags
/// equal; a sign-confusion control sets them unequal (REFUTES for an MSB-set
/// lane).
fn neon_fpred_cvt_obligation(
    name: String,
    lane: u32,
    source_signed: bool,
    machine_signed: bool,
) -> ProofObligation {
    neon_fpred_cvt_obligation_arr(name, NEON_FPRED_ARR, lane, source_signed, machine_signed)
}

/// Arrangement-parametric UCVTF/SCVTF lane obligation (the `.2D` builder above
/// pins `NEON_FPRED_ARR`; the `.4S` (i32->f32) IOTA-FILL emitter uses `S4`). The
/// per-lane semantics are IDENTICAL — the SAME `bv_to_fp` (RNE) SOURCE leaf and
/// the SAME real `encode_neon_{scvtf,ucvtf}_vec` machine encoder — only the lane
/// width (32 vs 64) and lane count (4 vs 2) differ.
fn neon_fpred_cvt_obligation_arr(
    name: String,
    arr: VectorArrangement,
    lane: u32,
    source_signed: bool,
    machine_signed: bool,
) -> ProofObligation {
    use crate::neon_semantics::{encode_neon_scvtf_vec, encode_neon_ucvtf_vec};
    let (eb, sb) = fp_params(arr);
    let lane_bits = arr.lane_bits();
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let src_lane = lane_from_halves(&vn_lo, &vn_hi, arr, lane);
    let src = fpred_int_to_fp(source_signed, src_lane, lane_bits, eb, sb);
    let reg = var_128("vn");
    let int_lanes: Vec<SmtExpr> = (0..arr.lane_count())
        .map(|i| lane_extract(&reg, arr, i))
        .collect();
    let mut mach_lanes = if machine_signed {
        encode_neon_scvtf_vec(&int_lanes, eb, sb)
    } else {
        encode_neon_ucvtf_vec(&int_lanes, lane_bits, eb, sb)
    };
    let mach = mach_lanes.swap_remove(lane as usize);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name,
        trust_ir_expr: src,
        aarch64_expr: mach,
        inputs: vec![("vn_lo".to_string(), 64), ("vn_hi".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// Assemble one faithful DUP `Dd, Vn.D[lane]` obligation: SOURCE is the raw
/// D-half slice of lane `src_lane`; MACHINE is the real `encode_neon_dup_scalar_d`
/// (lane `mach_lane` of the reassembled register). Positives use the same lane;
/// a wrong-lane control uses different lanes (REFUTES when the halves differ).
fn neon_fpred_dup_obligation(name: String, src_lane: u32, mach_lane: u32) -> ProofObligation {
    use crate::neon_semantics::encode_neon_dup_scalar_d;
    let arr = NEON_FPRED_ARR;
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let src = lane_from_halves(&vn_lo, &vn_hi, arr, src_lane);
    let mach = encode_neon_dup_scalar_d(&var_128("vn"), mach_lane);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name,
        trust_ir_expr: src,
        aarch64_expr: mach,
        inputs: vec![("vn_lo".to_string(), 64), ("vn_hi".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// All 26 FAITHFUL `neon_fpred` obligations: {FMLA, FMLS, UCVTF, SCVTF, DUP} x
/// {.2D lane 0, lane 1} = 10, plus {UCVTF, SCVTF} x {.4S lanes 0..4} = 8, plus
/// {FMLA, FMLS} x {.4S lanes 0..4} = 8. The coverage gate CREDITS NeonFmlaV/
/// NeonFmlsV/NeonUcvtfV/NeonScvtfV/NeonDupScalarD through these — EVERY emitted
/// arrangement is pinned via `aarch64_width_polymorphic_proofs`, so neither a
/// single-lane nor a whole-arrangement miswiring can hide.
pub fn all_neon_fpred_proofs() -> Vec<ProofObligation> {
    use crate::neon_semantics::{encode_neon_fmla, encode_neon_fmls};
    let mut proofs = Vec::new();
    for lane in 0..NEON_FPRED_ARR.lane_count() {
        proofs.push(neon_fpred_fma_obligation(
            format!(
                "NEON FmlaV.2d lane{lane} fused-fp-intent == D-pair per-lane fp.fma \
                 (SINGLE rounding; FP semantics via shared model, see module docs)"
            ),
            lane,
            false,
            encode_neon_fmla,
        ));
        proofs.push(neon_fpred_fma_obligation(
            format!(
                "NEON FmlsV.2d lane{lane} fused-fp-intent == D-pair per-lane fp.fma of \
                 negated product (SINGLE rounding; FP semantics via shared model)"
            ),
            lane,
            true,
            encode_neon_fmls,
        ));
        proofs.push(neon_fpred_cvt_obligation(
            format!(
                "NEON UcvtfV.2d lane{lane} int-to-fp-intent == D-pair per-lane unsigned \
                 int->FP (RNE; via shared model)"
            ),
            lane,
            false,
            false,
        ));
        proofs.push(neon_fpred_cvt_obligation(
            format!(
                "NEON ScvtfV.2d lane{lane} int-to-fp-intent == D-pair per-lane signed \
                 int->FP (RNE; via shared model)"
            ),
            lane,
            true,
            true,
        ));
        proofs.push(neon_fpred_dup_obligation(
            format!(
                "NEON DupScalarD.d lane{lane} lane-copy-intent == D-pair 64-bit lane \
                 bit-copy (faithful)"
            ),
            lane,
            lane,
        ));
    }
    // `.4S` (i32 -> f32) UCVTF/SCVTF — the IOTA-FILL vectorizer (`neon_farray`)
    // emits these to convert the induction lane vector `[j, j+1, j+2, j+3]` to
    // floats (the fp-convert `x[j] = a + (float)j` fill). FAITHFUL per-lane, all 4
    // lanes pinned (a single-lane or sign miswiring cannot hide); the SAME shared
    // int->FP model as the `.2D` obligations above, at 32-bit lanes.
    for lane in 0..VectorArrangement::S4.lane_count() {
        proofs.push(neon_fpred_cvt_obligation_arr(
            format!(
                "NEON UcvtfV.4s lane{lane} int-to-fp-intent == 4S per-lane unsigned \
                 int->FP (RNE; via shared model)"
            ),
            VectorArrangement::S4,
            lane,
            false,
            false,
        ));
        proofs.push(neon_fpred_cvt_obligation_arr(
            format!(
                "NEON ScvtfV.4s lane{lane} int-to-fp-intent == 4S per-lane signed \
                 int->FP (RNE; via shared model)"
            ),
            VectorArrangement::S4,
            lane,
            true,
            true,
        ));
    }
    // `.4S` (f32) FMLA/FMLS — the COMPLEX-BUTTERFLY vectorizer (`neon_butterfly`,
    // `FARR_S4`) and the f32 elementwise map-chain (`neon_fmap`, `ctx.w.farr`
    // = `FARR_S4` at 32-bit lanes) both emit `NeonFmlaV` at this arrangement, so
    // `.2D`-only obligations would leave the emitted `.4S` form uncovered.
    // FAITHFUL per-lane, all 4 lanes pinned (a single-lane or width miswiring
    // cannot hide); the SAME SINGLE-rounding `fp.fma` semantics as the `.2D`
    // obligations above, at 32-bit lanes.
    for lane in 0..VectorArrangement::S4.lane_count() {
        proofs.push(neon_fpred_fma_obligation_arr(
            format!(
                "NEON FmlaV.4s lane{lane} fused-fp-intent == 4S per-lane fp.fma \
                 (SINGLE rounding; FP semantics via shared model, see module docs)"
            ),
            VectorArrangement::S4,
            lane,
            false,
            encode_neon_fmla,
        ));
        proofs.push(neon_fpred_fma_obligation_arr(
            format!(
                "NEON FmlsV.4s lane{lane} fused-fp-intent == 4S per-lane fp.fma of \
                 negated product (SINGLE rounding; FP semantics via shared model)"
            ),
            VectorArrangement::S4,
            lane,
            true,
            encode_neon_fmls,
        ));
    }
    proofs
}

/// NEGATIVE CONTROLS for the `neon_fpred` obligations — each MUST refute:
///   * FMLA-as-FMLS / FMLS-as-FMLA (the `E`-bit opcode confusion; the product
///     sign flips).
///   * FMLA accumulator-miswire (the tied `Vd` swapped with the multiplicand
///     `Vn` — the non-commutative wiring axis of the fused op).
///   * FMLA wrong-lane wiring (machine lane 1 presented in lane 0's slot).
///   * UCVTF-as-SCVTF / SCVTF-as-UCVTF (the sign confusion — diverges on an
///     MSB-set lane).
///   * UCVTF wrong-lane wiring.
///   * DupScalarD wrong-lane (source lane 0 vs machine lane 1).
pub fn neon_fpred_wrong_encoding_controls() -> Vec<ProofObligation> {
    use crate::neon_semantics::{encode_neon_fmla, encode_neon_fmls};
    vec![
        // Opcode-bit confusion FMLA<->FMLS.
        neon_fpred_fma_obligation(
            "WRONG: FmlaV.2d encoded as FMLS (E-bit / product-sign) must REFUTE".to_string(),
            0,
            false,
            encode_neon_fmls,
        ),
        neon_fpred_fma_obligation(
            "WRONG: FmlsV.2d encoded as FMLA (E-bit / product-sign) must REFUTE".to_string(),
            0,
            true,
            encode_neon_fmla,
        ),
        // Accumulator miswire: machine uses Vn as the accumulator and Vd as a
        // multiplicand (fma(Vd,Vm,Vn) instead of fma(Vn,Vm,Vd)).
        neon_fpred_fma_obligation(
            "WRONG: FmlaV.2d accumulator (Vd) swapped with multiplicand (Vn) must REFUTE"
                .to_string(),
            0,
            false,
            |vd, vn, vm| encode_neon_fmla(vn, vd, vm),
        ),
        // Wrong-lane wiring: machine lane 1's result presented in lane 0's slot.
        neon_fpred_fma_obligation(
            "WRONG: FmlaV.2d lane0-as-lane1 (wrong-lane wiring) must REFUTE".to_string(),
            0,
            false,
            |vd, vn, vm| {
                let full = encode_neon_fmla(vd, vn, vm);
                let mut rotated = full.clone();
                rotated[0] = full[1].clone();
                rotated
            },
        ),
        // Sign confusion UCVTF<->SCVTF.
        neon_fpred_cvt_obligation(
            "WRONG: UcvtfV.2d (unsigned) encoded as SCVTF (signed) must REFUTE".to_string(),
            0,
            false,
            true,
        ),
        neon_fpred_cvt_obligation(
            "WRONG: ScvtfV.2d (signed) encoded as UCVTF (unsigned) must REFUTE".to_string(),
            0,
            true,
            false,
        ),
        // Wrong-lane wiring for the convert: source lane 0, machine lane 1.
        {
            use crate::neon_semantics::encode_neon_scvtf_vec;
            let arr = NEON_FPRED_ARR;
            let (eb, sb) = fp_params(arr);
            let vn_lo = SmtExpr::var("vn_lo", 64);
            let vn_hi = SmtExpr::var("vn_hi", 64);
            let src = fpred_int_to_fp(
                true,
                lane_from_halves(&vn_lo, &vn_hi, arr, 0),
                arr.lane_bits(),
                eb,
                sb,
            );
            let reg = var_128("vn");
            let int_lanes: Vec<SmtExpr> = (0..arr.lane_count())
                .map(|i| lane_extract(&reg, arr, i))
                .collect();
            let mach = encode_neon_scvtf_vec(&int_lanes, eb, sb).swap_remove(1);
            ProofObligation {
                machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
                name: "WRONG: ScvtfV.2d lane0-as-lane1 (wrong-lane wiring) must REFUTE".to_string(),
                trust_ir_expr: src,
                aarch64_expr: mach,
                inputs: vec![("vn_lo".to_string(), 64), ("vn_hi".to_string(), 64)],
                preconditions: vec![],
                fp_inputs: vec![],
                category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
            }
        },
        // DupScalarD wrong-lane: source lane 0 vs machine lane 1.
        neon_fpred_dup_obligation(
            "WRONG: DupScalarD.d lane0-as-lane1 (wrong-lane copy) must REFUTE".to_string(),
            0,
            1,
        ),
    ]
}

// ---------------------------------------------------------------------------
// FAITHFUL per-LANE NEON FMLA-BY-ELEMENT (`neon_fmap` da*x broadcast) obligations
// ---------------------------------------------------------------------------
//
// SOUNDNESS — these credit the coverage gate for `NeonFmlaLaneV`, the FP fused
// multiply-accumulate BY ELEMENT (`FMLA Vd.T, Vn.T, Vm.Ts[selector]`) the
// elementwise-FP vectorizer (`neon_fmap`) emits for `y[i] += da*x[i]`: the
// scalar invariant `da` is kept in ONE lane of a vector register and broadcast
// as the multiplier (no `DUP`). Per dest lane `k`:
//   `Vd[k]' = fma(Vn[k], Vm[selector], Vd[k])`  (SINGLE rounding, tied Vd)
// — the SAME fused single-rounding accumulate as `NeonFmlaV`, but the multiplier
// is one FIXED broadcast lane `Vm[selector]` rather than the matching lane
// `Vm[k]`. Emitted at BOTH `.4S` (f32, the daxpy shape) and `.2D` (f64).
//
// The obligations cover the FULL (selector, dest) grid at each width — `.4S`:
// selector 0..3 x dest 0..3 = 16; `.2D`: selector 0..1 x dest 0..1 = 4; total
// 20 — so a wrong broadcast lane cannot hide in any (selector, dest) slot.
//
// Same D-REGISTER-PAIR faithfulness as the fpred proofs: the SOURCE slices
// Vn[dest]/Vm[selector]/Vd[dest] DIRECTLY from the raw D-halves and applies the
// SINGLE-rounding `fp.fma`; the MACHINE is the real `encode_neon_fmla_lane` over
// the reassembled `Concat(hi, lo)`. STRUCTURALLY DISTINCT, so the wrong-encoding
// controls REFUTE: WRONG-LANE-SELECTOR (machine broadcasts a different Vm lane),
// FMLA-as-FMLS polarity (the `E`-bit product-sign flip), and accumulator miswire
// (tied Vd swapped with the multiplicand Vn). HONESTY as the fpred proofs: both
// sides express the per-lane IEEE op with the SAME SMT FP node, so these certify
// the LANE/OP/WIDTH/SELECTOR plumbing, NOT an independent FP-circuit model; the
// fused op uses `fp.fma` (SINGLE rounding), a round-twice machine model REFUTES.

/// Assemble one faithful FMLA-by-element lane obligation. SOURCE computes dest
/// lane `dest_lane` as the SINGLE-rounding `fp.fma` of `Vn[dest_lane]` (product
/// negated iff `source_negate_n`) times the BROADCAST lane `Vm[selector]`, plus
/// the tied accumulator `Vd[dest_lane]`. MACHINE is `machine` (the real
/// by-element encoder, or a WRONG one for a control) over the reassembled
/// registers, at `dest_lane`.
fn neon_fmla_lane_obligation<M>(
    name: String,
    arr: VectorArrangement,
    dest_lane: u32,
    selector: usize,
    source_negate_n: bool,
    machine: M,
) -> ProofObligation
where
    M: Fn(&[SmtExpr], &[SmtExpr], &[SmtExpr]) -> Vec<SmtExpr>,
{
    use crate::smt::RoundingMode;
    let n_lane = fp_lane_from_halves("vn", arr, dest_lane);
    let m_lane = fp_lane_from_halves("vm", arr, selector as u32);
    let d_lane = fp_lane_from_halves("vd", arr, dest_lane);
    let n_lane = if source_negate_n {
        n_lane.fp_neg()
    } else {
        n_lane
    };
    let src = SmtExpr::fp_fma(RoundingMode::RNE, n_lane, m_lane, d_lane);
    let vd_lanes = fp_lanes_from_concat("vd", arr);
    let vn_lanes = fp_lanes_from_concat("vn", arr);
    let vm_lanes = fp_lanes_from_concat("vm", arr);
    let mach = machine(&vd_lanes, &vn_lanes, &vm_lanes).swap_remove(dest_lane as usize);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name,
        trust_ir_expr: src,
        aarch64_expr: mach,
        inputs: fpred_fma_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// All 20 FAITHFUL `NeonFmlaLaneV` obligations: the FULL (selector, dest) grid
/// at `.4S` (16) and `.2D` (4). The coverage gate CREDITS `NeonFmlaLaneV`
/// through this complete grid (see `aarch64_width_polymorphic_proofs`), pinning
/// that EVERY destination lane reads the SAME selected broadcast lane.
pub fn all_neon_fmla_lane_proofs() -> Vec<ProofObligation> {
    use crate::neon_semantics::encode_neon_fmla_lane;
    let mut proofs = Vec::new();
    for &arr in &[VectorArrangement::S4, VectorArrangement::D2] {
        let arr_label = if arr == VectorArrangement::S4 {
            "4s"
        } else {
            "2d"
        };
        let lanes = arr.lane_count();
        for selector in 0..lanes {
            for dest in 0..lanes {
                let sel = selector as usize;
                proofs.push(neon_fmla_lane_obligation(
                    format!(
                        "NEON FmlaLaneV.{arr_label} sel{selector} dest{dest} fused-fp-intent \
                         == D-pair per-lane fp.fma of broadcast Vm lane (SINGLE rounding; FP \
                         semantics via shared model, see module docs)"
                    ),
                    arr,
                    dest,
                    sel,
                    false,
                    move |vd, vn, vm| encode_neon_fmla_lane(vd, vn, vm, sel),
                ));
            }
        }
    }
    proofs
}

/// NEGATIVE CONTROLS for the `NeonFmlaLaneV` obligations — each MUST refute:
///   * FMLA-by-element encoded as FMLS-by-element (the `E`-bit polarity — the
///     product sign flips), at `.4S` and `.2D`.
///   * WRONG-LANE-SELECTOR (source selects Vm lane 1, machine broadcasts lane
///     0 — the load-bearing by-element axis), at `.4S` and `.2D`.
///   * Accumulator miswire (the tied `Vd` swapped with the multiplicand `Vn`),
///     at `.4S` and `.2D`.
pub fn neon_fmla_lane_wrong_encoding_controls() -> Vec<ProofObligation> {
    use crate::neon_semantics::{encode_neon_fmla_lane, encode_neon_fmls_lane};
    let mut controls = Vec::new();
    for &arr in &[VectorArrangement::S4, VectorArrangement::D2] {
        let arr_label = if arr == VectorArrangement::S4 {
            "4s"
        } else {
            "2d"
        };
        // Polarity: FMLA-by-element machine-encoded as FMLS-by-element.
        controls.push(neon_fmla_lane_obligation(
            format!(
                "WRONG: FmlaLaneV.{arr_label} encoded as FMLS-by-element (E-bit/product-sign) \
                 must REFUTE"
            ),
            arr,
            0,
            0,
            false,
            |vd, vn, vm| encode_neon_fmls_lane(vd, vn, vm, 0),
        ));
        // Wrong broadcast lane: SOURCE selects Vm[1], MACHINE broadcasts Vm[0].
        controls.push(neon_fmla_lane_obligation(
            format!(
                "WRONG: FmlaLaneV.{arr_label} selector 1-as-0 (wrong broadcast lane) must REFUTE"
            ),
            arr,
            0,
            1, // source selector = 1
            false,
            |vd, vn, vm| encode_neon_fmla_lane(vd, vn, vm, 0), // machine selector = 0
        ));
        // Accumulator miswire: machine uses Vn as accumulator, Vd as multiplicand.
        controls.push(neon_fmla_lane_obligation(
            format!(
                "WRONG: FmlaLaneV.{arr_label} accumulator (Vd) swapped with multiplicand (Vn) \
                 must REFUTE"
            ),
            arr,
            0,
            0,
            false,
            |vd, vn, vm| encode_neon_fmla_lane(vn, vd, vm, 0),
        ));
    }
    controls
}

// ---------------------------------------------------------------------------
// FAITHFUL per-LANE NEON FCVTL/FCVTL2 (f32 -> f64 widening convert) obligations
// ---------------------------------------------------------------------------
//
// SOUNDNESS — these credit the coverage gate for `NeonFcvtlV` / `NeonFcvtl2V`,
// the vector `f32 -> f64` widen the FP array-reduction vectorizer (`neon_farray`)
// emits for the widening dot (`sum += (double)a_f32[i] * (double)b_f32[i]`, the
// fp-convert kernel). FCVTL widens the LOW two `f32` lanes of `Vn` (the low 64
// bits) into `Vd.2D`; FCVTL2 the HIGH two (lanes 2,3). Both output at `.2D`
// (2 x f64) with TWO lanes, so the gate demands BOTH lane obligations discharge.
//
// Widening `f32 -> f64` is EXACT — every finite/inf/NaN `f32` value is
// representable as an `f64`, so per lane the semantics are a pure `fpext` with NO
// rounding (`SmtExpr::fp_to_fp` to `(11, 53)`; the rounding mode is immaterial).
// The obligation is therefore CLEANER than the int->FP converts: it is a genuine
// FP-to-FP identity, not a model-consistency lift.
//
// Same D-REGISTER-PAIR faithfulness as the fpred proofs: the SOURCE slices the
// source `f32` lane DIRECTLY from the raw 64-bit D-halves (`{vn_lo,vn_hi}` Vars,
// `.4S` view) and widens it; the MACHINE is the real `encode_neon_fcvtl_vec` over
// the reassembled `Concat(vn_hi, vn_lo)` register. STRUCTURALLY DISTINCT, so the
// WRONG-HALF control (FCVTL encoded as FCVTL2 — reading lanes 2,3 instead of 0,1)
// and the WRONG-LANE control (machine lane 1 in lane 0's slot) both REFUTE. As
// with the other NEON-FP obligations, both sides express the widen with the SAME
// SMT `fp_to_fp` node, so these certify the LANE/HALF PLUMBING; the FP semantic
// weight rests on the shared QF_FP model + the silicon-validated NEON-FP
// differential bridge.

/// Assemble one FCVTL/FCVTL2 `.2D` lane obligation. SOURCE widens the `f32` lane
/// `source_lane` of the `source_high` half (`+2` for the high half) sliced from
/// the raw D-halves; MACHINE is the real `encode_neon_fcvtl_vec(_, machine_high)`
/// over the reassembled register, at `machine_lane`. Positives set the two halves
/// equal and the two lanes equal; the wrong-half / wrong-lane controls set them
/// unequal (REFUTE when the two halves / lanes differ).
fn neon_fcvtl_obligation(
    name: String,
    source_high: bool,
    source_lane: u32,
    machine_high: bool,
    machine_lane: u32,
) -> ProofObligation {
    use crate::neon_semantics::encode_neon_fcvtl_vec;
    use crate::smt::RoundingMode;
    let arr = VectorArrangement::S4;
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let src_idx = if source_high {
        source_lane + 2
    } else {
        source_lane
    };
    let src_f32_bits = lane_from_halves(&vn_lo, &vn_hi, arr, src_idx);
    let src = SmtExpr::fp_to_fp(
        RoundingMode::RNE,
        SmtExpr::bv_bits_to_fp(src_f32_bits, 8, 24),
        11,
        53,
    );
    let reg = var_128("vn");
    let mach = encode_neon_fcvtl_vec(&reg, machine_high).swap_remove(machine_lane as usize);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name,
        trust_ir_expr: src,
        aarch64_expr: mach,
        inputs: vec![("vn_lo".to_string(), 64), ("vn_hi".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// All 4 FAITHFUL `neon_farray` FCVTL/FCVTL2 obligations: {FCVTL (low half),
/// FCVTL2 (high half)} x {.2D lane 0, lane 1}. The coverage gate CREDITS
/// NeonFcvtlV / NeonFcvtl2V through these (both `.2D` lanes pinned via
/// `aarch64_width_polymorphic_proofs`, so a single-lane miswiring cannot hide).
pub fn all_neon_fcvtl_proofs() -> Vec<ProofObligation> {
    let mut proofs = Vec::new();
    for lane in 0..2 {
        proofs.push(neon_fcvtl_obligation(
            format!(
                "NEON FcvtlV.2d lane{lane} fpext-intent == low-half f32->f64 widen \
                 (EXACT fpext; FP semantics via shared model, see module docs)"
            ),
            false,
            lane,
            false,
            lane,
        ));
        proofs.push(neon_fcvtl_obligation(
            format!(
                "NEON Fcvtl2V.2d lane{lane} fpext-intent == high-half f32->f64 widen \
                 (EXACT fpext; FP semantics via shared model, see module docs)"
            ),
            true,
            lane,
            true,
            lane,
        ));
    }
    proofs
}

/// NEGATIVE CONTROLS for the FCVTL/FCVTL2 obligations — each MUST refute:
///   * FCVTL-as-FCVTL2 / FCVTL2-as-FCVTL (the wrong-HALF confusion — the Q bit;
///     reads the wrong 64 bits of `Vn`, diverges when the two halves differ).
///   * FCVTL wrong-lane wiring (source lane 0 vs machine lane 1).
///   * FCVTL2 wrong-lane wiring.
pub fn neon_fcvtl_wrong_encoding_controls() -> Vec<ProofObligation> {
    vec![
        neon_fcvtl_obligation(
            "WRONG: FcvtlV.2d (low half) encoded as FCVTL2 (high half) must REFUTE".to_string(),
            false,
            0,
            true,
            0,
        ),
        neon_fcvtl_obligation(
            "WRONG: Fcvtl2V.2d (high half) encoded as FCVTL (low half) must REFUTE".to_string(),
            true,
            0,
            false,
            0,
        ),
        neon_fcvtl_obligation(
            "WRONG: FcvtlV.2d lane0-as-lane1 (wrong-lane wiring) must REFUTE".to_string(),
            false,
            0,
            false,
            1,
        ),
        neon_fcvtl_obligation(
            "WRONG: Fcvtl2V.2d lane0-as-lane1 (wrong-lane wiring) must REFUTE".to_string(),
            true,
            0,
            true,
            1,
        ),
    ]
}

// ---------------------------------------------------------------------------
// FAITHFUL per-(element-size, lane) NEON UMOV (lane -> GPR extract) obligations
// ---------------------------------------------------------------------------
//
// SOUNDNESS — these credit the coverage gate for `NeonUmovGen`
// (`UMOV Wd/Xd, Vn.<T>[lane]`), the single op every NEON lane->scalar extract
// lowers through: the reduction drains (`neon_find`/`neon_array`/`neon_reduce`/
// `neon_fmap`/`neon_minmax`/`neon_predsum` + the `vectorize`/`isel` ordered-sub
// reducers) at `.S`/`.D`, AND the `V{16I8,8I16,4I32,2I64}ExtractLane` isel at
// `.B`/`.H`/`.S`/`.D`. UMOV always ZERO-EXTENDS the selected lane into the GPR
// (in contrast to SMOV's sign-extend): `.B`/`.H`/`.S` produce a 32-bit `Wd`
// (upper 32 of `Xd` cleared), `.D` a 64-bit `Xd` direct copy.
//
// EMITTED (size, lane) MATRIX — every combination the backend can emit, each a
// COMPILE-TIME-CONSTANT lane immediate (the `ExtractLane` opcode carries `lane`
// as a `u8` field bounded `<= max_lane`; the drains iterate `0..vf` emitting a
// literal per lane — NO dynamic/runtime lane index exists, so EVERY combination
// gets a static obligation and NOTHING is left allowlisted for a dynamic lane):
//   * `.16B` (B, element_size 1): lanes 0..=15 -> Wd (zero-ext 8 -> 32)
//   * `.8H`  (H, element_size 2): lanes 0..=7  -> Wd (zero-ext 16 -> 32)
//   * `.4S`  (S, element_size 4): lanes 0..=3  -> Wd (32-bit lane, no ext)
//   * `.2D`  (D, element_size 8): lanes 0..=1  -> Xd (64-bit lane, no ext)
// = 16 + 8 + 4 + 2 = 30 obligations.
//
// FAITHFULNESS — same D-REGISTER-PAIR structure as the compute/FP lane proofs:
// the SOURCE slices lane `lane` DIRECTLY from the raw 64-bit D-halves
// (`Extract(Var(vn_lo|vn_hi), …)`), zero-extended to the GPR width; the MACHINE
// is the real `encode_neon_umov_general` over the reassembled `Concat(hi, lo)`
// (`Extract(Concat(hi, lo), …)`), zero-extended the same way. STRUCTURALLY
// DISTINCT (raw-half `Var` slice vs `Extract`-of-`Concat`), so
// `is_genuinely_proven()` holds and the wrong-encoding controls REFUTE
// (wrong-lane on every size + wrong-size, the element-size operand being
// load-bearing). Unlike the FP lane proofs, BOTH sides are PURE QF_BV terms
// sharing NO opaque semantic node — this is a COMPLETE faithful proof of the
// extract + zero-extend, with no shared-model caveat.

/// Zero-extend `v` (width `from_bits`) up to `to_bits`; identity when equal.
fn umov_zext_to(v: SmtExpr, from_bits: u32, to_bits: u32) -> SmtExpr {
    if to_bits > from_bits {
        v.zero_ext(to_bits - from_bits)
    } else {
        v
    }
}

/// Assemble one `UMOV` `(size, lane)` obligation. SOURCE slices `src_lane` from
/// the raw D-halves at `src_arr`'s element size and zero-extends to `gpr_bits`;
/// MACHINE is the real `encode_neon_umov_general` at `mach_arr`/`mach_lane` over
/// the reassembled register. Positives set `src_arr == mach_arr` and
/// `src_lane == mach_lane`; a wrong-lane control differs in the lane, a
/// wrong-size control differs in the arrangement (same `gpr_bits`) — both REFUTE.
fn neon_umov_obligation(
    name: String,
    src_arr: VectorArrangement,
    src_lane: u32,
    mach_arr: VectorArrangement,
    mach_lane: u32,
    gpr_bits: u32,
) -> ProofObligation {
    use crate::neon_semantics::encode_neon_umov_general;
    let vn_lo = SmtExpr::var("vn_lo", 64);
    let vn_hi = SmtExpr::var("vn_hi", 64);
    let src_lane_val = lane_from_halves(&vn_lo, &vn_hi, src_arr, src_lane);
    let src = umov_zext_to(src_lane_val, src_arr.lane_bits(), gpr_bits);
    let mach = encode_neon_umov_general(&var_128("vn"), mach_arr, mach_lane, gpr_bits);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name,
        trust_ir_expr: src,
        aarch64_expr: mach,
        inputs: vec![("vn_lo".to_string(), 64), ("vn_hi".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
    }
}

/// The four `UMOV` element sizes: (arrangement, name token, destination GPR
/// width). B/H/S -> 32-bit `Wd`; D -> 64-bit `Xd`.
const NEON_UMOV_SIZES: &[(VectorArrangement, &str, u32)] = &[
    (VectorArrangement::B16, "16b", 32),
    (VectorArrangement::H8, "8h", 32),
    (VectorArrangement::S4, "4s", 32),
    (VectorArrangement::D2, "2d", 64),
];

/// All 30 FAITHFUL `NeonUmovGen` obligations — the full emitted `(size, lane)`
/// matrix (`.16B` 16 lanes, `.8H` 8, `.4S` 4, `.2D` 2). The coverage gate CREDITS
/// NeonUmovGen through these (EVERY lane bound via `aarch64_width_polymorphic_proofs`,
/// so a single-lane or wrong-size miswiring cannot hide).
pub fn all_neon_umov_proofs() -> Vec<ProofObligation> {
    let mut proofs = Vec::new();
    for &(arr, label, gpr) in NEON_UMOV_SIZES {
        for lane in 0..arr.lane_count() {
            proofs.push(neon_umov_obligation(
                format!(
                    "NEON UmovGen.{label} lane{lane:02} extract-to-gpr{gpr} == D-pair lane \
                     zero-ext (faithful bitvector)"
                ),
                arr,
                lane,
                arr,
                lane,
                gpr,
            ));
        }
    }
    proofs
}

/// NEGATIVE CONTROLS for the `NeonUmovGen` obligations — each MUST refute:
///   * wrong-LANE on every element size (source lane 0 vs machine lane 1: the
///     lane-select immediate is load-bearing).
///   * wrong-SIZE (source's element size vs machine's, same 32-bit `Wd` output:
///     the element-size immediate is load-bearing — B-as-H, B-as-S, H-as-S each
///     diverge on the extra source bits the wider extract exposes).
pub fn neon_umov_wrong_encoding_controls() -> Vec<ProofObligation> {
    use VectorArrangement::{B16, D2, H8, S4};
    vec![
        // Wrong-lane wiring: machine lane 1 presented in lane 0's slot.
        neon_umov_obligation(
            "WRONG: UmovGen.16b lane0-as-lane1 (wrong-lane) must REFUTE".to_string(),
            B16,
            0,
            B16,
            1,
            32,
        ),
        neon_umov_obligation(
            "WRONG: UmovGen.8h lane0-as-lane1 (wrong-lane) must REFUTE".to_string(),
            H8,
            0,
            H8,
            1,
            32,
        ),
        neon_umov_obligation(
            "WRONG: UmovGen.4s lane0-as-lane1 (wrong-lane) must REFUTE".to_string(),
            S4,
            0,
            S4,
            1,
            32,
        ),
        neon_umov_obligation(
            "WRONG: UmovGen.2d lane0-as-lane1 (wrong-lane) must REFUTE".to_string(),
            D2,
            0,
            D2,
            1,
            64,
        ),
        // Wrong-size: source intends element size X lane 0, machine emits size Y
        // lane 0 (same 32-bit Wd) — the element-size operand confusion.
        neon_umov_obligation(
            "WRONG: UmovGen.16b-as-8h (element-size operand) must REFUTE".to_string(),
            B16,
            0,
            H8,
            0,
            32,
        ),
        neon_umov_obligation(
            "WRONG: UmovGen.16b-as-4s (element-size operand) must REFUTE".to_string(),
            B16,
            0,
            S4,
            0,
            32,
        ),
        neon_umov_obligation(
            "WRONG: UmovGen.8h-as-4s (element-size operand) must REFUTE".to_string(),
            H8,
            0,
            S4,
            0,
            32,
        ),
    ]
}

// ---------------------------------------------------------------------------
// Aggregate: all NEON lowering proofs
// ---------------------------------------------------------------------------

/// Return all NEON SIMD lowering proof obligations.
///
/// 18 operations x 2 arrangements (one 64-bit, one 128-bit) = 36 proofs, plus
/// USHR.4S + SSHR.4S = 38, plus the 5 FAITHFUL per-lane-intent == whole-register
/// bitwise proofs (AND/ORR/EOR/BIC/NOT) = 43, plus the 18 FAITHFUL per-lane
/// D-register-pair COMPUTE proofs (Add/Sub/Mul, Cmeq {`.4S` + the `.16B`
/// byte-lane CMEQ the count-if kernel emits}/Cmge/Cmgt/Cmhi/Cmhs,
/// Smax/Smin/Umax/Umin, Shl/Ushr/Sshr, plus the `.16B` byte-lane USHR #4 / CMHS
/// #10 the hex-nibble-sum kernel emits — the gate-credited lane-wise arith/compare/
/// min-max/shift obligations) = 61, plus the 3 FAITHFUL popcount-fold proofs
/// (CntV.16B + UaddlpV `.16B->.8H` + UaddlpV `.8H->.4S`) = 64, plus the 1 FAITHFUL
/// signed-abs proof (AbsV.4S) = 65, plus the 1 FAITHFUL unsigned
/// dot-product-accumulate proof (UdotV.4S) = 66, plus the 3 FAITHFUL
/// byte-window extract proofs (ExtV.16B #4/#8/#12) = 69.
pub fn all_neon_lowering_proofs() -> Vec<ProofObligation> {
    let mut proofs = all_neon_lowering_proofs_legacy();
    proofs.extend(all_neon_lanewise_compute_proofs());
    proofs.extend(all_neon_lanewise_compute_proofs_2d());
    proofs.extend(all_neon_popcount_proofs());
    proofs.extend(all_neon_saddlp_proofs());
    proofs.extend(all_neon_bit_proofs());
    proofs.extend(all_neon_abs_proofs());
    proofs.extend(all_neon_udot_proofs());
    proofs.extend(all_neon_smlal_proofs());
    proofs.extend(all_neon_uaddw_proofs());
    proofs.extend(all_neon_saddw_proofs());
    proofs.extend(all_neon_mla_proofs());
    proofs.extend(all_neon_uadalp_proofs());
    proofs.extend(all_neon_ext_proofs());
    proofs.extend(all_neon_post_index_writeback_proofs());
    proofs.extend(all_neon_movi_proofs());
    proofs.extend(all_neon_ins_gen_proofs());
    proofs.extend(all_neon_dup_gen_proofs());
    proofs.extend(all_neon_dup_elem_proofs());
    proofs.extend(all_neon_umaxv_proofs());
    proofs.extend(all_neon_rev32_proofs());
    proofs.extend(all_neon_rev64_proofs());
    proofs.extend(all_neon_rbit_proofs());
    proofs.extend(all_neon_fp_lanewise_proofs());
    proofs.extend(all_neon_fpred_proofs());
    proofs.extend(all_neon_fmla_lane_proofs());
    proofs.extend(all_neon_fcvtl_proofs());
    proofs.extend(all_neon_umov_proofs());
    proofs
}

/// The 43 pre-existing NEON lowering proofs (the `proof_vector_*` DEGENERATE X==X
/// model-consistency entries + the 5 FAITHFUL bitwise lane-wise proofs).
fn all_neon_lowering_proofs_legacy() -> Vec<ProofObligation> {
    vec![
        // Arithmetic (4 ops x 2 arrangements = 8 proofs)
        proof_vector_add_2s(),
        proof_vector_add_4s(),
        proof_vector_sub_4h(),
        proof_vector_sub_8h(),
        proof_vector_mul_8b(),
        proof_vector_mul_16b(),
        proof_vector_neg_2s(),
        proof_vector_neg_2d(),
        // Bitwise (4 ops x 2 arrangements = 8 proofs) — DEGENERATE X==X (both
        // sides are the same whole-register op); kept as model-consistency only,
        // the gate does NOT credit them (see the faithful lanewise proofs below).
        proof_vector_and_8b(),
        proof_vector_and_16b(),
        proof_vector_orr_8b(),
        proof_vector_orr_16b(),
        proof_vector_eor_8b(),
        proof_vector_eor_16b(),
        proof_vector_bic_8b(),
        proof_vector_bic_16b(),
        // FAITHFUL per-LANE-intent == whole-register bitwise proofs (5) — these
        // are the NON-degenerate obligations the coverage gate CREDITS for
        // NeonAndV/NeonOrrV/NeonEorV/NeonBicV/NeonNotV.
        proof_neon_andv_lanewise_16b(),
        proof_neon_orrv_lanewise_16b(),
        proof_neon_eorv_lanewise_16b(),
        proof_neon_bicv_lanewise_16b(),
        proof_neon_notv_lanewise_16b(),
        // Shifts (SHL: 2 arrangements; USHR/SSHR: 3 arrangements incl. 4S)
        proof_vector_shl_4h(),
        proof_vector_shl_4s(),
        proof_vector_ushr_8b(),
        proof_vector_ushr_2d(),
        proof_vector_ushr_4s(),
        proof_vector_sshr_2s(),
        proof_vector_sshr_8h(),
        proof_vector_sshr_4s(),
        // Multiply-accumulate (1 op x 2 arrangements = 2 proofs)
        proof_vector_mla_8b(),
        proof_vector_mla_4s(),
        // Min/max (4 ops x 2 arrangements = 8 proofs)
        proof_vector_smin_4h(),
        proof_vector_smin_4s(),
        proof_vector_umin_8b(),
        proof_vector_umin_8h(),
        proof_vector_smax_2s(),
        proof_vector_smax_16b(),
        proof_vector_umax_4h(),
        proof_vector_umax_4s(),
        // Comparisons (2 ops x 2 arrangements = 4 proofs)
        proof_vector_cmgt_2s(),
        proof_vector_cmgt_4s(),
        proof_vector_cmge_4h(),
        proof_vector_cmge_8h(),
    ]
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lowering_proof::verify_by_evaluation;
    use crate::verify::VerificationResult;

    /// Verify a proof obligation and assert it is valid.
    fn assert_valid(obligation: &ProofObligation) {
        let result = verify_by_evaluation(obligation);
        match &result {
            VerificationResult::Valid => {}
            VerificationResult::Invalid { counterexample } => {
                panic!(
                    "Proof '{}' FAILED with counterexample: {}",
                    obligation.name, counterexample
                );
            }
            VerificationResult::Unknown { reason } => {
                panic!("Proof '{}' returned Unknown: {}", obligation.name, reason);
            }
        }
    }

    // =======================================================================
    // Vector ADD
    // =======================================================================

    #[test]
    fn test_proof_vector_add_2s() {
        assert_valid(&proof_vector_add_2s());
    }

    #[test]
    fn test_proof_vector_add_4s() {
        assert_valid(&proof_vector_add_4s());
    }

    // =======================================================================
    // Vector SUB
    // =======================================================================

    #[test]
    fn test_proof_vector_sub_4h() {
        assert_valid(&proof_vector_sub_4h());
    }

    #[test]
    fn test_proof_vector_sub_8h() {
        assert_valid(&proof_vector_sub_8h());
    }

    // =======================================================================
    // Vector MUL
    // =======================================================================

    #[test]
    fn test_proof_vector_mul_8b() {
        assert_valid(&proof_vector_mul_8b());
    }

    #[test]
    fn test_proof_vector_mul_16b() {
        assert_valid(&proof_vector_mul_16b());
    }

    // =======================================================================
    // Vector NEG
    // =======================================================================

    #[test]
    fn test_proof_vector_neg_2s() {
        assert_valid(&proof_vector_neg_2s());
    }

    #[test]
    fn test_proof_vector_neg_2d() {
        assert_valid(&proof_vector_neg_2d());
    }

    // =======================================================================
    // Vector AND
    // =======================================================================

    #[test]
    fn test_proof_vector_and_8b() {
        assert_valid(&proof_vector_and_8b());
    }

    #[test]
    fn test_proof_vector_and_16b() {
        assert_valid(&proof_vector_and_16b());
    }

    // =======================================================================
    // Vector ORR
    // =======================================================================

    #[test]
    fn test_proof_vector_orr_8b() {
        assert_valid(&proof_vector_orr_8b());
    }

    #[test]
    fn test_proof_vector_orr_16b() {
        assert_valid(&proof_vector_orr_16b());
    }

    // =======================================================================
    // Vector EOR
    // =======================================================================

    #[test]
    fn test_proof_vector_eor_8b() {
        assert_valid(&proof_vector_eor_8b());
    }

    #[test]
    fn test_proof_vector_eor_16b() {
        assert_valid(&proof_vector_eor_16b());
    }

    // =======================================================================
    // Vector BIC
    // =======================================================================

    #[test]
    fn test_proof_vector_bic_8b() {
        assert_valid(&proof_vector_bic_8b());
    }

    #[test]
    fn test_proof_vector_bic_16b() {
        assert_valid(&proof_vector_bic_16b());
    }

    // =======================================================================
    // FAITHFUL per-LANE-intent == whole-register bitwise (the gate-credited
    // obligations). Each must DISCHARGE Valid AND be NON-degenerate (the
    // structurally-distinct per-lane-vs-whole property is what makes the
    // obligation refutable — see `is_genuinely_proven`).
    // =======================================================================

    #[test]
    fn test_proof_neon_andv_lanewise_16b() {
        let p = proof_neon_andv_lanewise_16b();
        assert!(
            p.is_genuinely_proven(),
            "AndV lanewise proof is degenerate X==X"
        );
        assert_valid(&p);
    }

    #[test]
    fn test_proof_neon_orrv_lanewise_16b() {
        let p = proof_neon_orrv_lanewise_16b();
        assert!(
            p.is_genuinely_proven(),
            "OrrV lanewise proof is degenerate X==X"
        );
        assert_valid(&p);
    }

    #[test]
    fn test_proof_neon_eorv_lanewise_16b() {
        let p = proof_neon_eorv_lanewise_16b();
        assert!(
            p.is_genuinely_proven(),
            "EorV lanewise proof is degenerate X==X"
        );
        assert_valid(&p);
    }

    #[test]
    fn test_proof_neon_bicv_lanewise_16b() {
        let p = proof_neon_bicv_lanewise_16b();
        assert!(
            p.is_genuinely_proven(),
            "BicV lanewise proof is degenerate X==X"
        );
        assert_valid(&p);
    }

    #[test]
    fn test_proof_neon_notv_lanewise_16b() {
        let p = proof_neon_notv_lanewise_16b();
        assert!(
            p.is_genuinely_proven(),
            "NotV lanewise proof is degenerate X==X"
        );
        assert_valid(&p);
    }

    // =======================================================================
    // Vector SHL
    // =======================================================================

    #[test]
    fn test_proof_vector_shl_4h() {
        assert_valid(&proof_vector_shl_4h());
    }

    #[test]
    fn test_proof_vector_shl_4s() {
        assert_valid(&proof_vector_shl_4s());
    }

    // =======================================================================
    // Vector USHR
    // =======================================================================

    #[test]
    fn test_proof_vector_ushr_8b() {
        assert_valid(&proof_vector_ushr_8b());
    }

    #[test]
    fn test_proof_vector_ushr_2d() {
        assert_valid(&proof_vector_ushr_2d());
    }

    #[test]
    fn test_proof_vector_ushr_4s() {
        assert_valid(&proof_vector_ushr_4s());
    }

    // =======================================================================
    // Vector SSHR
    // =======================================================================

    #[test]
    fn test_proof_vector_sshr_2s() {
        assert_valid(&proof_vector_sshr_2s());
    }

    #[test]
    fn test_proof_vector_sshr_8h() {
        assert_valid(&proof_vector_sshr_8h());
    }

    #[test]
    fn test_proof_vector_sshr_4s() {
        assert_valid(&proof_vector_sshr_4s());
    }

    // =======================================================================
    // Vector MLA
    // =======================================================================

    #[test]
    fn test_proof_vector_mla_8b() {
        assert_valid(&proof_vector_mla_8b());
    }

    #[test]
    fn test_proof_vector_mla_4s() {
        assert_valid(&proof_vector_mla_4s());
    }

    // =======================================================================
    // Vector SMIN
    // =======================================================================

    #[test]
    fn test_proof_vector_smin_4h() {
        assert_valid(&proof_vector_smin_4h());
    }

    #[test]
    fn test_proof_vector_smin_4s() {
        assert_valid(&proof_vector_smin_4s());
    }

    // =======================================================================
    // Vector UMIN
    // =======================================================================

    #[test]
    fn test_proof_vector_umin_8b() {
        assert_valid(&proof_vector_umin_8b());
    }

    #[test]
    fn test_proof_vector_umin_8h() {
        assert_valid(&proof_vector_umin_8h());
    }

    // =======================================================================
    // Vector SMAX
    // =======================================================================

    #[test]
    fn test_proof_vector_smax_2s() {
        assert_valid(&proof_vector_smax_2s());
    }

    #[test]
    fn test_proof_vector_smax_16b() {
        assert_valid(&proof_vector_smax_16b());
    }

    // =======================================================================
    // Vector UMAX
    // =======================================================================

    #[test]
    fn test_proof_vector_umax_4h() {
        assert_valid(&proof_vector_umax_4h());
    }

    #[test]
    fn test_proof_vector_umax_4s() {
        assert_valid(&proof_vector_umax_4s());
    }

    // =======================================================================
    // Vector CMGT
    // =======================================================================

    #[test]
    fn test_proof_vector_cmgt_2s() {
        assert_valid(&proof_vector_cmgt_2s());
    }

    #[test]
    fn test_proof_vector_cmgt_4s() {
        assert_valid(&proof_vector_cmgt_4s());
    }

    // =======================================================================
    // Vector CMGE
    // =======================================================================

    #[test]
    fn test_proof_vector_cmge_4h() {
        assert_valid(&proof_vector_cmge_4h());
    }

    #[test]
    fn test_proof_vector_cmge_8h() {
        assert_valid(&proof_vector_cmge_8h());
    }

    // =======================================================================
    // Aggregate test: all proofs
    // =======================================================================

    #[test]
    fn test_all_neon_lowering_proofs() {
        let proofs = all_neon_lowering_proofs();
        assert_eq!(
            proofs.len(),
            285,
            "expected 36 base proofs + USHR.4S + SSHR.4S (the <4 x i32> \
             lane-wise right-shift lowerings) = 38, + 5 FAITHFUL per-lane-intent \
             == whole-register bitwise proofs (AndV/OrrV/EorV/BicV/NotV) = 43, \
             + 18 FAITHFUL per-lane D-pair COMPUTE proofs (15 `.4S` reps + the \
             `.16B` byte-lane CMEQ the count-if kernel emits + the `.16B` byte-lane \
             USHR #4 / CMHS #10 the hex-nibble-sum kernel emits) = 61, + 10 FAITHFUL \
             `.2D` (2 x i64) lane-wise compute proofs (the ops the i64 vectorizer \
             paths emit) = 71, + 3 FAITHFUL popcount-fold proofs (CntV.16B + \
             UaddlpV .16B->.8H + .8H->.4S) = 74, + 2 FAITHFUL signed \
             add-long-pairwise proofs (SaddlpV .16B->.8H + .8H->.4S) = 76, \
             + 1 FAITHFUL bitwise insert-if-true proof (BitV.16B) = 77, \
             + 1 FAITHFUL signed-abs proof (AbsV.4S) = 78, + 1 FAITHFUL unsigned \
             dot-product-accumulate proof (UdotV.4S) = 79, + 3 FAITHFUL \
             byte-window extract proofs (ExtV.16B #4/#8/#12 middle windows; the \
             #1/#15 stencil-neighbor shifts are added at the end) = 82, + 30 FAITHFUL \
             per-lane FP LANE-PLUMBING proofs (FaddV/FsubV/FmulV/FdivV/FcmgtV x \
             .4S 4 lanes + .2D 2 lanes; see all_neon_fp_lanewise_proofs' honesty \
             note — lane wiring / op / width genuinely proven, FP-circuit semantic \
             weight on the shared QF_FP model + silicon bridge) = 112, + 26 FAITHFUL \
             `neon_fpred` per-lane obligations (FMLA/FMLS fused fp.fma, UCVTF/SCVTF \
             int->FP, DupScalarD 64-bit lane copy, plus the added FP-reduction lane \
             ops; DupScalarD x .2D 2 lanes, FMLA/FMLS and UCVTF/SCVTF x BOTH .2D 2 \
             lanes and .4S 4 lanes) = 138, + 20 FAITHFUL FMLA-by-lane obligations \
             (FmlaLaneV .4S [4 sel x 4 dest = 16] + .2D [2 sel x 2 dest = 4], fused \
             fp broadcast-lane fma) = 158, + 4 FAITHFUL FCVTL/FCVTL2 f32->f64 \
             widening obligations (FCVTL low + FCVTL2 high x .2D 2 lanes — exact \
             fpext) = 162, + 30 FAITHFUL per-(size,lane) NeonUmovGen extract \
             obligations (UMOV lane->GPR: .16B 16 lanes + .8H 8 + .4S 4 + .2D 2, \
             zero-extended, PURE QF_BV) = 192, + 4 FAITHFUL widening \
             multiply-accumulate-long obligations (SMLAL low + SMLAL2 high + UMLAL \
             low + UMLAL2 high, .4S -> .2D i32->i64 MAC; both .2D lanes concatenated \
             per obligation; sign-confusion / no-accumulate / wrong-half / \
             truncating-mul refute controls) = 196, + 2 FAITHFUL widening add-wide \
             obligations (UADDW low + UADDW2 high, .4S -> .2D u32->u64 unsigned \
             three-operand wide add; both .2D lanes concatenated per obligation; \
             sign-confusion / no-addend / wrong-half / truncating-add refute \
             controls) = 198, + 2 FAITHFUL SIGNED widening add-wide obligations \
             (SADDW low + SADDW2 high, .4S -> .2D i32->i64 signed three-operand \
             wide add; both .2D lanes concatenated per obligation; zext-confusion \
             [SADDW-as-UADDW] / no-addend / wrong-half / truncating-add refute \
             controls) = 200, + 2 FAITHFUL 32-bit/byte reverse obligations \
             (Rev64V.4S — the butterfly vectorizer's within-doubleword element \
             swap; identity / doubleword-swap / half-lane-smear refute controls) \
             = 202, + 1 FAITHFUL vector multiply-accumulate obligation \
             (MlaV.4S tied-accumulator i32 MAC mod 2^32, all four lanes \
             concatenated; MLS-confusion / MUL-no-accumulate / lane-swap refute \
             controls) = 203, + 1 FAITHFUL pairwise widening accumulate obligation \
             (UadalpV.2D tied-accumulator u32-pair -> i64, .4S -> .2D, both .2D \
             lanes concatenated; SADALP-sign-confusion / UADDLP-no-accumulate / \
             wrong-pairing refute controls) = 204, + 2 FAITHFUL per-byte 8-bit \
             reverse obligation (Rbitv.16B — the neon-bitrev vectorizer's \
             within-byte bit reversal for `a[i].reverse_bits()` over `[u8; N]`; \
             per-bit D-half mirror SOURCE vs the SWAR machine; identity / \
             byte-swap [REV16.8B] / 16-bit-lane-reverse [wrong-width] refute \
             controls) = 206, + 2 FAITHFUL single-byte shifted-NEIGHBOR extract \
             obligations (ExtV.16B #1 = `a[iv+1]` forward window / #15 = \
             `a[iv-1]` backward window — the neon-bytesum stencil count-if's \
             shifted-neighbor stream; same per-byte D-pair SOURCE vs the \
             whole-register shift/OR machine; opposite-direction / swapped-operand \
             / identity refute controls) = 208, + 2 FAITHFUL per-WORD byte-reverse \
             obligations (Rev32V .16B + .8B — the i32 reverse_bits lowering's byte-order \
             half; wrong-container-granularity [REV64] and .8B/.16B Q=0 confusion refute \
             controls) = 210, + 1 FAITHFUL cross-lane horizontal-reduce obligation \
             (Umaxv.4S — the compare-mask any-lane collapse; balanced-tree bvuge SOURCE \
             vs the real linear bvugt fold; SMAXV-signedness / lane0-passthrough / \
             wrong-element-size refute controls) = 211, + 6 FAITHFUL selected-lane broadcast \
             obligations (DupElem .4S lanes 0..4 + .2D lanes 0..2 — every lane of both \
             emitted arrangements; wrong-LANE and wrong-element-SIZE refute controls) \
             = 217, + 30 FAITHFUL GPR-broadcast round-trip obligations (DupGen .16B 16 + \
             .8H 8 + .4S 4 + .2D 2 — real DUP encoder then real UMOV read-back per lane, \
             REPLACING the degenerate all-lanes==src identity) = 247, + 30 FAITHFUL tied-destination lane-insert obligations (InsGen .16B 16 + \
             .8H 8 + .4S 4 + .2D 2 — GPR truncated into the target lane, every OTHER lane \
             PRESERVED; wrong-LANE and wrong-element-SIZE refute controls) = 277, + 4 FAITHFUL byte-replicated-immediate obligations (Movi, one element view \
             per Q=1 arrangement — symbolic imm8, ARITHMETIC replication vs the machine's \
             Concat chain, REPLACING the degenerate replicated-byte identity) = 281, + 4 PARTIAL post-index base-register WRITEBACK obligations (Ld1Post/St1Post \
             16B + LdpQPost/StpQPost 32B — machine side DECODES imm7/Q out of the real \
             instruction word; these prove the base advance ONLY and the four opcodes \
             deliberately STAY DeferredUnfaithfulModel RED on the transfer) = 285 proofs"
        );
        for obligation in &proofs {
            assert_valid(obligation);
        }
    }

    // =======================================================================
    // FAITHFUL per-LANE D-register-pair COMPUTE obligations (the gate-credited
    // lane-wise arith / compare / min-max / shift obligations). Each must
    // DISCHARGE Valid AND be NON-degenerate (the D-pair SOURCE is structurally
    // distinct from the whole-register `Concat` the encoder threads through), and
    // a WRONG NEON instruction must REFUTE.
    // =======================================================================

    #[test]
    fn neon_lanewise_compute_proofs_verify() {
        for obligation in all_neon_lanewise_compute_proofs() {
            assert_valid(&obligation);
        }
    }

    #[test]
    fn neon_lanewise_compute_proofs_are_non_degenerate() {
        for obligation in all_neon_lanewise_compute_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON lane-wise compute proof '{}' is DEGENERATE (X==X); it proves nothing \
                 (the D-pair SOURCE must be structurally distinct from the encoder's \
                 whole-register Concat)",
                obligation.name
            );
        }
    }

    #[test]
    fn neon_lanewise_compute_wrong_encodings_refute() {
        let controls = neon_lanewise_wrong_encoding_controls();
        // One discriminating negative control per credited opcode.
        assert_eq!(
            controls.len(),
            all_neon_lanewise_compute_proofs().len(),
            "each credited lane-wise opcode needs a wrong-encoding negative control"
        );
        for obligation in controls {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEON lane-wise NEGATIVE control '{}' should be Invalid (a wrong NEON \
                 instruction must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    // =======================================================================
    // FAITHFUL popcount-fold obligations (CNT + UADDLP). Each must DISCHARGE
    // Valid AND be NON-degenerate; each wrong encoding must REFUTE.
    // =======================================================================

    #[test]
    fn neon_popcount_proofs_verify() {
        for obligation in all_neon_popcount_proofs() {
            assert_valid(&obligation);
        }
    }

    #[test]
    fn neon_popcount_proofs_are_non_degenerate() {
        for obligation in all_neon_popcount_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON popcount-fold proof '{}' is DEGENERATE (X==X); it proves nothing \
                 (the D-pair SOURCE must be structurally distinct from the encoder's \
                 whole-register Concat)",
                obligation.name
            );
        }
    }

    #[test]
    fn neon_popcount_wrong_encodings_refute() {
        let controls = neon_popcount_wrong_encoding_controls();
        assert_eq!(
            controls.len(),
            all_neon_popcount_proofs().len(),
            "each credited popcount-fold opcode form needs a wrong-encoding control"
        );
        for obligation in controls {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEON popcount-fold NEGATIVE control '{}' should be Invalid (a wrong NEON \
                 instruction must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    // =======================================================================
    // FAITHFUL `.2D` (2 x i64) lane-wise compute obligations. Must DISCHARGE
    // Valid AND be NON-degenerate; each wrong encoding (op / signedness /
    // direction / ARRANGEMENT) must REFUTE.
    // =======================================================================

    #[test]
    fn neon_lanewise_compute_proofs_2d_verify() {
        let proofs = all_neon_lanewise_compute_proofs_2d();
        assert_eq!(
            proofs.len(),
            10,
            "one `.2D` obligation per op the i64 vectorizer paths emit              (add/sub, 5 compares, 3 imm shifts)"
        );
        for obligation in proofs {
            assert_valid(&obligation);
        }
    }

    #[test]
    fn neon_lanewise_compute_proofs_2d_are_non_degenerate() {
        for obligation in all_neon_lanewise_compute_proofs_2d() {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON `.2D` lane-wise proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
        }
    }

    #[test]
    fn neon_lanewise_compute_2d_wrong_encodings_refute() {
        let controls = neon_lanewise_wrong_encoding_controls_2d();
        // One discriminating control per `.2D` obligation + the extra
        // WRONG-ARRANGEMENT (.2D-as-.4S) control.
        assert_eq!(
            controls.len(),
            all_neon_lanewise_compute_proofs_2d().len() + 1
        );
        for obligation in controls {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEON `.2D` NEGATIVE control '{}' should be Invalid (a wrong NEON                  instruction must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    // =======================================================================
    // FAITHFUL SADDLP (signed add-long-pairwise) obligations. Must DISCHARGE
    // Valid AND be NON-degenerate; the SIGN-CONFUSION control (SADDLP encoded
    // as UADDLP) and the pairwise-SUB control must REFUTE.
    // =======================================================================

    #[test]
    fn neon_saddlp_proofs_verify() {
        let proofs = all_neon_saddlp_proofs();
        assert_eq!(proofs.len(), 2, ".16B->.8H and .8H->.4S");
        for obligation in proofs {
            assert_valid(&obligation);
        }
    }

    #[test]
    fn neon_saddlp_proofs_are_non_degenerate() {
        for obligation in all_neon_saddlp_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON SADDLP proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
        }
    }

    #[test]
    fn neon_saddlp_wrong_encodings_refute() {
        let controls = neon_saddlp_wrong_encoding_controls();
        // 2 SIGN-CONFUSION (as-UADDLP) + 2 pairwise-SUB controls.
        assert_eq!(controls.len(), 4);
        for obligation in controls {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEON SADDLP NEGATIVE control '{}' should be Invalid (a wrong NEON                  instruction must refute — especially the sign-confusion SADDLP-as-UADDLP),                  got: {:?}",
                obligation.name,
                result
            );
        }
    }

    // =======================================================================
    // FAITHFUL BIT (bitwise insert if true) obligation. Must DISCHARGE Valid
    // AND be NON-degenerate; BIF/BSL/AND confusions must REFUTE.
    // =======================================================================

    #[test]
    fn neon_bit_proof_verifies() {
        let proofs = all_neon_bit_proofs();
        assert_eq!(proofs.len(), 1);
        for obligation in proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON BIT proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            assert_valid(&obligation);
        }
    }

    #[test]
    fn neon_bit_wrong_encodings_refute() {
        let controls = neon_bit_wrong_encoding_controls();
        assert_eq!(controls.len(), 3, "BIF + BSL + AND mutations");
        for obligation in controls {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEON BIT NEGATIVE control '{}' should be Invalid, got: {:?}",
                obligation.name,
                result
            );
        }
    }

    // =======================================================================
    // FAITHFUL signed-abs obligation (ABS.4S). Must DISCHARGE Valid AND be
    // NON-degenerate; each wrong encoding must REFUTE.
    // =======================================================================

    #[test]
    fn neon_abs_proof_verify() {
        for obligation in all_neon_abs_proofs() {
            assert_valid(&obligation);
        }
    }

    #[test]
    fn neon_abs_proof_is_non_degenerate() {
        for obligation in all_neon_abs_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON signed-abs proof '{}' is DEGENERATE (X==X); it proves nothing \
                 (the D-pair SOURCE must be structurally distinct from the encoder's \
                 whole-register Concat)",
                obligation.name
            );
        }
    }

    #[test]
    fn neon_abs_wrong_encodings_refute() {
        let controls = neon_abs_wrong_encoding_controls();
        assert_eq!(
            controls.len(),
            2,
            "abs needs both wrong-encoding controls (identity + negate-always)"
        );
        for obligation in controls {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEON signed-abs NEGATIVE control '{}' should be Invalid (a wrong NEON \
                 instruction must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    // =======================================================================
    // FAITHFUL unsigned dot-product-accumulate obligation (UDOT.4S). Must
    // DISCHARGE Valid AND be NON-degenerate; each wrong encoding must REFUTE.
    // =======================================================================

    #[test]
    fn neon_udot_proof_verify() {
        for obligation in all_neon_udot_proofs() {
            assert_valid(&obligation);
        }
    }

    #[test]
    fn neon_udot_proof_is_non_degenerate() {
        for obligation in all_neon_udot_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON udot proof '{}' is DEGENERATE (X==X); it proves nothing \
                 (the D-pair SOURCE must be structurally distinct from the encoder's \
                 whole-register Concat)",
                obligation.name
            );
        }
    }

    #[test]
    fn neon_udot_wrong_encodings_refute() {
        let controls = neon_udot_wrong_encoding_controls();
        assert_eq!(
            controls.len(),
            3,
            "udot needs all three wrong-encoding controls (no-accumulate + SDOT + \
             wrong byte group)"
        );
        for obligation in controls {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEON udot NEGATIVE control '{}' should be Invalid (a wrong NEON \
                 instruction must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    // =======================================================================
    // FAITHFUL widening multiply-accumulate-long obligations (SMLAL/SMLAL2/
    // UMLAL/UMLAL2 .4S -> .2D). Must DISCHARGE Valid AND be NON-degenerate; each
    // wrong encoding must REFUTE.
    // =======================================================================

    #[test]
    fn neon_smlal_proofs_verify() {
        let proofs = all_neon_smlal_proofs();
        assert_eq!(
            proofs.len(),
            4,
            "one whole-register D-pair obligation per opcode (SMLAL/SMLAL2/UMLAL/UMLAL2)"
        );
        for obligation in proofs {
            assert_valid(&obligation);
        }
    }

    #[test]
    fn neon_smlal_proofs_are_non_degenerate() {
        for obligation in all_neon_smlal_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON smlal proof '{}' is DEGENERATE (X==X); it proves nothing \
                 (the D-pair SOURCE must be structurally distinct from the encoder's \
                 whole-register Concat)",
                obligation.name
            );
        }
    }

    #[test]
    fn neon_smlal_wrong_encodings_refute() {
        let controls = neon_smlal_wrong_encoding_controls();
        assert_eq!(
            controls.len(),
            4,
            "smlal needs all four wrong-encoding controls (sign-confusion + \
             no-accumulate + wrong-half + truncating-mul)"
        );
        for obligation in controls {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEON smlal NEGATIVE control '{}' should be Invalid (a wrong NEON \
                 instruction must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    // =======================================================================
    // FAITHFUL widening add-wide obligations (UADDW/UADDW2 .4S -> .2D). Must
    // DISCHARGE Valid AND be NON-degenerate; each wrong encoding must REFUTE.
    // =======================================================================

    #[test]
    fn neon_uaddw_proofs_verify() {
        let proofs = all_neon_uaddw_proofs();
        assert_eq!(
            proofs.len(),
            2,
            "one whole-register D-pair obligation per opcode (UADDW/UADDW2)"
        );
        for obligation in proofs {
            assert_valid(&obligation);
        }
    }

    #[test]
    fn neon_uaddw_proofs_are_non_degenerate() {
        for obligation in all_neon_uaddw_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON uaddw proof '{}' is DEGENERATE (X==X); it proves nothing \
                 (the D-pair SOURCE must be structurally distinct from the encoder's \
                 whole-register Concat)",
                obligation.name
            );
        }
    }

    #[test]
    fn neon_uaddw_wrong_encodings_refute() {
        let controls = neon_uaddw_wrong_encoding_controls();
        assert_eq!(
            controls.len(),
            4,
            "uaddw needs all four wrong-encoding controls (sign-confusion + \
             no-addend + wrong-half + truncating-add)"
        );
        for obligation in controls {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEON uaddw NEGATIVE control '{}' should be Invalid (a wrong NEON \
                 instruction must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    // =======================================================================
    // FAITHFUL SIGNED widening add-wide obligations (SADDW/SADDW2 .4S -> .2D).
    // Must DISCHARGE Valid AND be NON-degenerate; each wrong encoding must
    // REFUTE.
    // =======================================================================

    #[test]
    fn neon_saddw_proofs_verify() {
        let proofs = all_neon_saddw_proofs();
        assert_eq!(
            proofs.len(),
            2,
            "one whole-register D-pair obligation per opcode (SADDW/SADDW2)"
        );
        for obligation in proofs {
            assert_valid(&obligation);
        }
    }

    #[test]
    fn neon_saddw_proofs_are_non_degenerate() {
        for obligation in all_neon_saddw_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON saddw proof '{}' is DEGENERATE (X==X); it proves nothing \
                 (the D-pair SOURCE must be structurally distinct from the encoder's \
                 whole-register Concat)",
                obligation.name
            );
        }
    }

    #[test]
    fn neon_saddw_wrong_encodings_refute() {
        let controls = neon_saddw_wrong_encoding_controls();
        assert_eq!(
            controls.len(),
            4,
            "saddw needs all four wrong-encoding controls (zext-confusion \
             [SADDW-as-UADDW] + no-addend + wrong-half + truncating-add)"
        );
        for obligation in controls {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEON saddw NEGATIVE control '{}' should be Invalid (a wrong NEON \
                 instruction must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn neon_saddw_sign_axis_is_refuted_both_ways() {
        // The sign axis must be closed in BOTH directions: the UADDW proofs
        // carry a SADDW-confusion control (sext-for-zext) and the SADDW proofs
        // carry a UADDW-confusion control (zext-for-sext). A miswire in either
        // direction — signed opcode emitted where unsigned semantics were
        // proven, or vice versa — therefore refutes.
        let uaddw_as_saddw = neon_uaddw_wrong_encoding_controls()
            .into_iter()
            .find(|o| o.name.contains("encoded as SADDW"))
            .expect("the UADDW proofs must keep their SADDW-confusion control");
        let saddw_as_uaddw = neon_saddw_wrong_encoding_controls()
            .into_iter()
            .find(|o| o.name.contains("encoded as UADDW"))
            .expect("the SADDW proofs must carry a UADDW-confusion control");
        for obligation in [uaddw_as_saddw, saddw_as_uaddw] {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "sign-axis control '{}' should be Invalid, got: {:?}",
                obligation.name,
                result
            );
        }
    }

    // =======================================================================
    // FAITHFUL vector multiply-accumulate obligation (MLA.4S). Must DISCHARGE
    // Valid AND be NON-degenerate; each wrong encoding must REFUTE.
    // =======================================================================

    #[test]
    fn neon_mla_proofs_verify() {
        let proofs = all_neon_mla_proofs();
        assert_eq!(
            proofs.len(),
            1,
            "one whole-register D-pair obligation for MLA.4S"
        );
        for obligation in proofs {
            assert_valid(&obligation);
        }
    }

    #[test]
    fn neon_mla_proofs_are_non_degenerate() {
        for obligation in all_neon_mla_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON mla proof '{}' is DEGENERATE (X==X); it proves nothing \
                 (the D-pair SOURCE must be structurally distinct from the encoder's \
                 whole-register Concat)",
                obligation.name
            );
        }
    }

    #[test]
    fn neon_mla_wrong_encodings_refute() {
        let controls = neon_mla_wrong_encoding_controls();
        assert_eq!(
            controls.len(),
            3,
            "mla needs all three wrong-encoding controls (MLS-confusion + \
             MUL-no-accumulate + lane-swap)"
        );
        for obligation in controls {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEON mla NEGATIVE control '{}' should be Invalid (a wrong NEON \
                 instruction must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    // =======================================================================
    // FAITHFUL pairwise widening accumulate obligation (UADALP .4S -> .2D).
    // Must DISCHARGE Valid AND be NON-degenerate; each wrong encoding must
    // REFUTE.
    // =======================================================================

    #[test]
    fn neon_uadalp_proofs_verify() {
        let proofs = all_neon_uadalp_proofs();
        assert_eq!(
            proofs.len(),
            1,
            "one whole-register D-pair obligation for UADALP.2D"
        );
        for obligation in proofs {
            assert_valid(&obligation);
        }
    }

    #[test]
    fn neon_uadalp_proofs_are_non_degenerate() {
        for obligation in all_neon_uadalp_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON uadalp proof '{}' is DEGENERATE (X==X); it proves nothing \
                 (the D-pair SOURCE must be structurally distinct from the encoder's \
                 whole-register Concat)",
                obligation.name
            );
        }
    }

    #[test]
    fn neon_uadalp_wrong_encodings_refute() {
        let controls = neon_uadalp_wrong_encoding_controls();
        assert_eq!(
            controls.len(),
            3,
            "uadalp needs all three wrong-encoding controls (SADALP-sign-confusion \
             + UADDLP-no-accumulate + wrong-pairing)"
        );
        for obligation in controls {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEON uadalp NEGATIVE control '{}' should be Invalid (a wrong NEON \
                 instruction must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    // =======================================================================
    // FAITHFUL byte-window extract obligations (EXT.16B #1/#4/#8/#12/#15). Must
    // DISCHARGE Valid AND be NON-degenerate; each wrong encoding must REFUTE.
    // =======================================================================

    #[test]
    fn neon_ext_proofs_verify() {
        let proofs = all_neon_ext_proofs();
        assert_eq!(
            proofs.len(),
            5,
            "one EXT obligation per emitted immediate (#1, #4, #8, #12, #15)"
        );
        for obligation in proofs {
            assert_valid(&obligation);
        }
    }

    #[test]
    fn neon_ext_proofs_are_non_degenerate() {
        for obligation in all_neon_ext_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON ext proof '{}' is DEGENERATE (X==X); it proves nothing \
                 (the D-pair SOURCE must be structurally distinct from the encoder's \
                 whole-register Concat+Extract)",
                obligation.name
            );
        }
    }

    #[test]
    fn neon_rev64_proof_verifies() {
        let proofs = all_neon_rev64_proofs();
        assert_eq!(
            proofs.len(),
            2,
            "two REV64 obligations, one per EMITTED arrangement (.4S butterfly pair swap \
             + .16B byte reversal in the <2 x i64> bit-reverse lowering)"
        );
        for obligation in proofs {
            assert_valid(&obligation);
        }
    }

    #[test]
    fn neon_rev64_proof_is_non_degenerate() {
        for obligation in all_neon_rev64_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON rev64 proof '{}' is DEGENERATE (X==X); it proves nothing \
                 (the D-pair SOURCE must be structurally distinct from the encoder's \
                 whole-register shift/mask form)",
                obligation.name
            );
        }
    }

    #[test]
    fn neon_rbit_proof_verifies() {
        let proofs = all_neon_rbit_proofs();
        assert_eq!(
            proofs.len(),
            2,
            "two RBIT obligations, one per EMITTED arrangement (.16B per-byte form \
             + the mixed-width path's .8B (Q=0) form, which zeroes the upper half)"
        );
        for obligation in proofs {
            assert_valid(&obligation);
        }
    }

    #[test]
    fn neon_rbit_proof_is_non_degenerate() {
        for obligation in all_neon_rbit_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON rbit proof '{}' is DEGENERATE (X==X); it proves nothing \
                 (the per-bit D-half mirror SOURCE must be structurally distinct \
                 from the encoder's whole-register SWAR shift/mask form)",
                obligation.name
            );
        }
    }

    #[test]
    fn neon_rbit_wrong_encodings_refute() {
        let controls = neon_rbit_wrong_encoding_controls();
        assert_eq!(
            controls.len(),
            6,
            "rbit needs its .16B controls (identity + byte swap [REV16.8B] + 16-bit-lane \
             reverse [wrong width]) AND the .8B controls (identity + the two \
             arrangement-confusion directions, which pin Q=0 upper-half zeroing)"
        );
        for obligation in controls {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEON rbit NEGATIVE control '{}' should be Invalid (a wrong NEON \
                 instruction must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn neon_rev32_proofs_discharge_and_are_non_degenerate() {
        let proofs = all_neon_rev32_proofs();
        assert_eq!(
            proofs.len(),
            2,
            "two REV32 obligations, one per EMITTED arrangement (.16B + the \
             mixed-width path's .8B Q=0 form)"
        );
        for p in &proofs {
            assert!(
                p.is_genuinely_proven(),
                "rev32 proof '{}' is DEGENERATE (X==X)",
                p.name
            );
            assert_valid(p);
        }
    }

    #[test]
    fn neon_rev32_wrong_encodings_refute() {
        let controls = neon_rev32_wrong_encoding_controls();
        assert_eq!(
            controls.len(),
            4,
            "rev32 needs identity + wrong container GRANULARITY (the REV64 butterfly) \
             + .8B/.16B Q=0 confusion in BOTH directions"
        );
        for c in &controls {
            let result = verify_by_evaluation(c);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEGATIVE control '{}' did not refute: {:?}",
                c.name,
                result
            );
        }
    }

    #[test]
    fn neon_post_index_writeback_proofs_discharge_and_are_non_degenerate() {
        let proofs = all_neon_post_index_writeback_proofs();
        assert_eq!(
            proofs.len(),
            4,
            "LdpQPost + StpQPost (32B) and Ld1Post + St1Post (16B)"
        );
        for p in &proofs {
            assert!(
                p.is_genuinely_proven(),
                "writeback proof '{}' is DEGENERATE (X==X) — the machine side must DECODE the \
                 immediate out of the instruction word, not restate `base + imm` (that is the \
                 shape of the already-RETRACTED proof_post_index_writeback)",
                p.name
            );
            assert_valid(p);
        }
    }

    #[test]
    fn neon_post_index_writeback_wrong_encodings_refute() {
        let controls = neon_post_index_writeback_wrong_encoding_controls();
        assert_eq!(
            controls.len(),
            3,
            "half-transfer, negative imm7, and wrong Q bit"
        );
        for c in &controls {
            let result = verify_by_evaluation(c);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEGATIVE control '{}' did not refute: {:?}",
                c.name,
                result
            );
        }
    }

    #[test]
    fn neon_post_index_memory_opcodes_stay_deferred_red() {
        // The writeback obligations above are PARTIAL: they prove the base
        // advances correctly and say NOTHING about the memory transfer. These
        // four opcodes must therefore REMAIN explicit DeferredUnfaithfulModel
        // rows. Crediting them as covered on the strength of the writeback alone
        // would be exactly the overclaim the RED row exists to prevent.
        use trust_cg_ir::AArch64Opcode as O;
        for op in [
            O::NeonLd1Post,
            O::NeonSt1Post,
            O::NeonLdpQPost,
            O::NeonStpQPost,
        ] {
            let reason = crate::coverage_gate::aarch64_deferred_value_op_reason(op);
            assert!(
                reason.is_some(),
                "{op:?} must KEEP its honest deferral — the vector dereference is still \
                 unmodeled; only the base-register writeback is proven"
            );
            let reason = reason.unwrap_or_default();
            assert!(
                reason.contains("writeback") || reason.contains("base-register"),
                "{op:?} deferral reason must NAME the writeback evidence that now exists, so \
                 the residue is stated precisely rather than as blanket debt: {reason}"
            );
        }
    }

    #[test]
    fn neon_movi_proofs_discharge_and_are_non_degenerate() {
        let proofs = all_neon_movi_proofs();
        assert_eq!(proofs.len(), 4, "one element view per Q=1 arrangement");
        for p in &proofs {
            assert!(
                p.is_genuinely_proven(),
                "movi proof '{}' is DEGENERATE (X==X) — the ARITHMETIC replication on the \
                 SOURCE side is what keeps it distinct from the machine's Concat chain",
                p.name
            );
            assert_valid(p);
        }
    }

    #[test]
    fn neon_movi_wrong_encodings_refute() {
        let controls = neon_movi_wrong_encoding_controls();
        assert_eq!(
            controls.len(),
            2,
            "Q=0 upper-half zeroing + dropped replication"
        );
        for c in &controls {
            let result = verify_by_evaluation(c);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEGATIVE control '{}' did not refute: {:?}",
                c.name,
                result
            );
        }
    }

    #[test]
    fn neon_ins_gen_proofs_discharge_and_are_non_degenerate() {
        let proofs = all_neon_ins_gen_proofs();
        assert_eq!(
            proofs.len(),
            30,
            ".16B 16 + .8H 8 + .4S 4 + .2D 2 = 30 INS-general obligations"
        );
        for p in &proofs {
            assert!(
                p.is_genuinely_proven(),
                "ins-gen proof '{}' is DEGENERATE (X==X)",
                p.name
            );
            assert_valid(p);
        }
    }

    #[test]
    fn neon_ins_gen_wrong_encodings_refute() {
        let controls = neon_ins_gen_wrong_encoding_controls();
        assert_eq!(
            controls.len(),
            4,
            "wrong LANE (which also clobbers a PRESERVED lane) + wrong element SIZE"
        );
        for c in &controls {
            let result = verify_by_evaluation(c);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEGATIVE control '{}' did not refute: {:?}",
                c.name,
                result
            );
        }
    }

    #[test]
    fn neon_dup_gen_proofs_discharge_and_are_non_degenerate() {
        let proofs = all_neon_dup_gen_proofs();
        assert_eq!(
            proofs.len(),
            30,
            ".16B 16 + .8H 8 + .4S 4 + .2D 2 = 30 DUP-general obligations"
        );
        for p in &proofs {
            assert!(
                p.is_genuinely_proven(),
                "dup-gen proof '{}' is DEGENERATE (X==X) — declaring the GPR at 64 bits and \
                 reading the lane back through the real UMOV encoder is what keeps the two \
                 sides structurally distinct",
                p.name
            );
            assert_valid(p);
        }
    }

    #[test]
    fn neon_dup_gen_wrong_encodings_refute() {
        let controls = neon_dup_gen_wrong_encoding_controls();
        assert_eq!(
            controls.len(),
            3,
            "wrong element SIZE, read back at lane >= 1"
        );
        for c in &controls {
            let result = verify_by_evaluation(c);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEGATIVE control '{}' did not refute: {:?}",
                c.name,
                result
            );
        }
    }

    #[test]
    fn neon_dup_elem_proofs_discharge_and_are_non_degenerate() {
        let proofs = all_neon_dup_elem_proofs();
        assert_eq!(
            proofs.len(),
            6,
            ".4S lanes 0..4 + .2D lanes 0..2 = 6 DUP-element obligations"
        );
        for p in &proofs {
            assert!(
                p.is_genuinely_proven(),
                "dup-elem proof '{}' is DEGENERATE (X==X)",
                p.name
            );
            assert_valid(p);
        }
    }

    #[test]
    fn neon_dup_elem_wrong_encodings_refute() {
        let controls = neon_dup_elem_wrong_encoding_controls();
        assert_eq!(
            controls.len(),
            4,
            "wrong-LANE (both directions, both arrangements) + wrong element SIZE"
        );
        for c in &controls {
            let result = verify_by_evaluation(c);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEGATIVE control '{}' did not refute: {:?}",
                c.name,
                result
            );
        }
    }

    #[test]
    fn neon_umaxv_proof_discharges_and_is_non_degenerate() {
        let proofs = all_neon_umaxv_proofs();
        assert_eq!(
            proofs.len(),
            1,
            "one UMAXV obligation (the emitted .4S form)"
        );
        for p in &proofs {
            assert!(
                p.is_genuinely_proven(),
                "umaxv proof '{}' is DEGENERATE (X==X) — the balanced-tree bvuge SOURCE \
                 must stay structurally distinct from the linear bvugt machine fold",
                p.name
            );
            assert_valid(p);
        }
    }

    #[test]
    fn neon_umaxv_wrong_encodings_refute() {
        let controls = neon_umaxv_wrong_encoding_controls();
        assert_eq!(
            controls.len(),
            4,
            "umaxv needs SMAXV-signedness + lane0-passthrough + .16B and .8H \
             wrong-element-size controls"
        );
        for c in &controls {
            let result = verify_by_evaluation(c);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEGATIVE control '{}' did not refute: {:?}",
                c.name,
                result
            );
        }
    }

    #[test]
    fn neon_rev64_wrong_encodings_refute() {
        let controls = neon_rev64_wrong_encoding_controls();
        assert_eq!(
            controls.len(),
            6,
            "rev64 needs its .4S controls (identity + doubleword swap + half-lane smear) \
             AND the .16B controls (identity + wrong container GRANULARITY + doubleword \
             swap)"
        );
        for obligation in controls {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEON rev64 NEGATIVE control '{}' should be Invalid (a wrong NEON \
                 instruction must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn neon_ext_wrong_encodings_refute() {
        let controls = neon_ext_wrong_encoding_controls();
        assert_eq!(
            controls.len(),
            8,
            "ext needs the #4 middle-window controls (swapped operands + wrong \
             immediate + identity = 3) plus the stencil-neighbor #1/#15 controls \
             (#1: opposite-direction #15 / swapped / identity = 3; #15: \
             opposite-direction #1 / swapped = 2) = 8"
        );
        for obligation in controls {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEON ext NEGATIVE control '{}' should be Invalid (a wrong NEON \
                 instruction must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    // =======================================================================
    // Negative test: wrong NEON instruction detected
    // =======================================================================

    /// Verify that mapping vector_add to NEON SUB is caught as invalid.
    #[test]
    fn test_wrong_neon_lowering_detected() {
        let arrangement = VectorArrangement::S2;
        let vn = symbolic_vector("vn", arrangement);
        let vm = symbolic_vector("vm", arrangement);

        let mut inputs = vector_inputs("vn", arrangement);
        inputs.extend(vector_inputs("vm", arrangement));

        // trust_ir says ADD, NEON says SUB -- should find counterexample.
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "WRONG: VectorAdd -> NEON SUB.2S".to_string(),
            trust_ir_expr: map_lanes_binary(&vn, &vm, arrangement, |a, b| a.bvadd(b)),
            aarch64_expr: encode_neon_sub(arrangement, &vn, &vm),
            inputs,
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::Vectorization),
        };

        let result = verify_by_evaluation(&obligation);
        match result {
            VerificationResult::Invalid { .. } => {} // expected
            other => panic!("Expected Invalid for wrong NEON lowering, got {:?}", other),
        }
    }

    // =======================================================================
    // FAITHFUL per-LANE FP obligations (LANE-PLUMBING; module-docs honesty
    // note applies). Each must be NON-degenerate, DISCHARGE Valid under the
    // evaluator, and every wrong-encoding control must REFUTE.
    // =======================================================================

    #[test]
    fn neon_fp_lanewise_proofs_discharge_and_are_non_degenerate() {
        let proofs = all_neon_fp_lanewise_proofs();
        assert_eq!(
            proofs.len(),
            30,
            "5 ops x (.4S 4 lanes + .2D 2 lanes) = 30 FP lane obligations"
        );
        for p in &proofs {
            assert!(
                p.is_genuinely_proven(),
                "FP lane proof '{}' is DEGENERATE (X==X)",
                p.name
            );
            assert_valid(p);
        }
    }

    #[test]
    fn neon_fp_lanewise_wrong_encodings_refute() {
        let controls = neon_fp_lanewise_wrong_encoding_controls();
        assert_eq!(controls.len(), 14, "7 controls x 2 arrangements");
        for c in &controls {
            let result = verify_by_evaluation(c);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEGATIVE control '{}' did not refute: {:?}",
                c.name,
                result
            );
        }
    }

    // =======================================================================
    // FAITHFUL per-LANE `neon_fpred` obligations (FMLA/FMLS/UCVTF/SCVTF/DUP).
    // Each must be NON-degenerate, DISCHARGE Valid under the evaluator, and
    // every wrong-encoding control must REFUTE.
    // =======================================================================

    #[test]
    fn neon_fpred_proofs_discharge_and_are_non_degenerate() {
        let proofs = all_neon_fpred_proofs();
        assert_eq!(
            proofs.len(),
            26,
            "{{FMLA, FMLS, UCVTF, SCVTF, DupScalarD}} x .2D 2 lanes = 10, plus \
             {{UCVTF, SCVTF}} x .4S 4 lanes = 8, plus {{FMLA, FMLS}} x .4S 4 lanes \
             = 8 -> 26 fpred obligations"
        );
        for p in &proofs {
            assert!(
                p.is_genuinely_proven(),
                "fpred lane proof '{}' is DEGENERATE (X==X)",
                p.name
            );
            assert_valid(p);
        }
    }

    #[test]
    fn neon_fpred_wrong_encodings_refute() {
        let controls = neon_fpred_wrong_encoding_controls();
        assert_eq!(controls.len(), 8, "8 fpred negative controls");
        for c in &controls {
            let result = verify_by_evaluation(c);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEGATIVE control '{}' did not refute: {:?}",
                c.name,
                result
            );
        }
    }

    #[test]
    fn neon_fmla_lane_proofs_discharge_and_are_non_degenerate() {
        let proofs = all_neon_fmla_lane_proofs();
        assert_eq!(
            proofs.len(),
            20,
            ".4S (selector 0..3 x dest 0..3 = 16) + .2D (selector 0..1 x dest 0..1 = 4) = 20 \
             fmla-by-element obligations"
        );
        for p in &proofs {
            assert!(
                p.is_genuinely_proven(),
                "fmla-lane proof '{}' is DEGENERATE (X==X)",
                p.name
            );
            assert_valid(p);
        }
    }

    #[test]
    fn neon_fmla_lane_wrong_encodings_refute() {
        let controls = neon_fmla_lane_wrong_encoding_controls();
        assert_eq!(
            controls.len(),
            6,
            "{{polarity, wrong-lane-selector, accumulator-miswire}} x {{.4S, .2D}} = 6 controls"
        );
        for c in &controls {
            let result = verify_by_evaluation(c);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEGATIVE control '{}' did not refute: {:?}",
                c.name,
                result
            );
        }
    }

    // =======================================================================
    // FAITHFUL FCVTL/FCVTL2 (f32->f64 widen) obligations. Each must be
    // NON-degenerate, DISCHARGE Valid under the evaluator, and every
    // wrong-encoding (wrong-half / wrong-lane) control must REFUTE.
    // =======================================================================

    #[test]
    fn neon_fcvtl_proofs_discharge_and_are_non_degenerate() {
        let proofs = all_neon_fcvtl_proofs();
        assert_eq!(
            proofs.len(),
            4,
            "{{FCVTL, FCVTL2}} x .2D 2 lanes = 4 fcvtl obligations"
        );
        for p in &proofs {
            assert!(
                p.is_genuinely_proven(),
                "fcvtl lane proof '{}' is DEGENERATE (X==X)",
                p.name
            );
            assert_valid(p);
        }
    }

    #[test]
    fn neon_fcvtl_wrong_encodings_refute() {
        let controls = neon_fcvtl_wrong_encoding_controls();
        assert_eq!(controls.len(), 4, "4 fcvtl negative controls");
        for c in &controls {
            let result = verify_by_evaluation(c);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEGATIVE control '{}' did not refute: {:?}",
                c.name,
                result
            );
        }
    }

    // =======================================================================
    // FAITHFUL per-(size, lane) `NeonUmovGen` extract obligations. Each must be
    // NON-degenerate, DISCHARGE Valid under the evaluator, and every
    // wrong-encoding (wrong-lane / wrong-size) control must REFUTE.
    // =======================================================================

    #[test]
    fn neon_umov_proofs_discharge_and_are_non_degenerate() {
        let proofs = all_neon_umov_proofs();
        assert_eq!(
            proofs.len(),
            30,
            ".16B 16 lanes + .8H 8 + .4S 4 + .2D 2 = 30 UMOV (size,lane) obligations"
        );
        for p in &proofs {
            assert!(
                p.is_genuinely_proven(),
                "UMOV extract proof '{}' is DEGENERATE (X==X)",
                p.name
            );
            assert_valid(p);
        }
    }

    #[test]
    fn neon_umov_wrong_encodings_refute() {
        let controls = neon_umov_wrong_encoding_controls();
        assert_eq!(
            controls.len(),
            7,
            "4 wrong-lane (one per size) + 3 wrong-size UMOV negative controls"
        );
        for c in &controls {
            let result = verify_by_evaluation(c);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "NEGATIVE control '{}' did not refute: {:?}",
                c.name,
                result
            );
        }
    }
}
