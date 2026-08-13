// trust-cg-verify/wasm_semantics.rs - WebAssembly instruction semantics (SMT)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Operational semantics of the WebAssembly instructions the trust-cg wasm
//! backend emits, encoded as [`SmtExpr`] bitvector terms — the wasm analogue of
//! [`crate::aarch64_semantics`] / `x86_64_semantics`.
//!
//! These mirror the opcode table in the backend
//! (`trust-cg-codegen/src/wasm/lower.rs`: `int_binop_opcode` and `icmp_opcode`,
//! `wasm/encode.rs` opcode bytes). The dependency direction is codegen → verify,
//! so this crate cannot import the backend; the mapping is hand-mirrored here
//! and kept honest by the lowering-proof anti-tautology test plus the backend's
//! own opcode unit tests.
//!
//! Semantics rationale: wasm `i32`/`i64` arithmetic wraps modulo 2^N exactly
//! like SMT-LIB `bvadd`/`bvsub`/`bvmul` (low-N-bits result, no flags). wasm
//! comparison ops **produce an `i32`** (1 if true, else 0) — never a Bool — even
//! for i64 operands, so each predicate is lifted to a 32-bit value with `ite`.
//!
//! We model the value-level data function only. The stack-machine discipline
//! (that exactly the right operands are on top of the value stack, in order) is
//! a property of the relooper + local-slot allocation, argued structurally, not
//! here.

use crate::smt::{RoundingMode, SmtExpr, SmtSort};
use std::sync::Arc;

/// The integer ALU operation a wasm opcode byte computes. This is the **source
/// of truth** the refinement proofs in [`crate::wasm_lowering_proofs`] validate
/// (each variant's SMT semantics is proven equal to the corresponding trust-ir
/// op). The backend's `int_binop_opcode` (in `trust-cg-codegen`) is cross-checked
/// against this decode by a test there, so a wrong opcode mapping in the backend
/// fails a test — closing the gap that the proofs alone (which hand-mirror the
/// table) cannot catch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmAluOp {
    Add,
    Sub,
    Mul,
    DivS,
    DivU,
    RemS,
    RemU,
    And,
    Or,
    Xor,
    Shl,
    ShrS,
    ShrU,
}

/// Decode a wasm integer-ALU opcode byte to the operation it computes.
/// `None` for non-integer-ALU opcodes. Covers both i32 and i64 (same operation,
/// different width).
pub fn decode_int_binop(op_byte: u8) -> Option<WasmAluOp> {
    use WasmAluOp::*;
    Some(match op_byte {
        0x6a | 0x7c => Add,
        0x6b | 0x7d => Sub,
        0x6c | 0x7e => Mul,
        0x6d | 0x7f => DivS,
        0x6e | 0x80 => DivU,
        0x6f | 0x81 => RemS,
        0x70 | 0x82 => RemU,
        0x71 | 0x83 => And,
        0x72 | 0x84 => Or,
        0x73 | 0x85 => Xor,
        0x74 | 0x86 => Shl,
        0x75 | 0x87 => ShrS,
        0x76 | 0x88 => ShrU,
        _ => return None,
    })
}

/// The integer COMPARISON a wasm comparison opcode byte computes (operand width
/// N; result is an i32 0/1). Decoded from the REAL emitted opcode byte by
/// [`decode_int_cmp`] for the function-verifier's operand reconstruction: the
/// machine side is rebuilt from THIS decoded predicate, so a wrong comparison
/// byte (e.g. `lt_s` 0x48 where `lt_u` 0x49 was intended) refutes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmIntCmpOp {
    Eq,
    Ne,
    LtS,
    LtU,
    GtS,
    GtU,
    LeS,
    LeU,
    GeS,
    GeU,
}

/// Decode a wasm integer-comparison opcode byte to the predicate it computes.
/// `None` for non-comparison opcodes. Covers both i32 and i64 (same predicate).
pub fn decode_int_cmp(op_byte: u8) -> Option<WasmIntCmpOp> {
    use WasmIntCmpOp::*;
    Some(match op_byte {
        0x46 | 0x51 => Eq,
        0x47 | 0x52 => Ne,
        0x48 | 0x53 => LtS,
        0x49 | 0x54 => LtU,
        0x4a | 0x55 => GtS,
        0x4b | 0x56 => GtU,
        0x4c | 0x57 => LeS,
        0x4d | 0x58 => LeU,
        0x4e | 0x59 => GeS,
        0x4f | 0x5a => GeU,
        _ => return None,
    })
}

/// The FP binary arithmetic op a wasm FP-arith opcode byte computes. Decoded by
/// [`decode_fp_binop`] for operand reconstruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmFpBinOp {
    Add,
    Sub,
    Mul,
    Div,
}

/// Decode a wasm FP-arithmetic opcode byte. `None` otherwise. f32 and f64.
pub fn decode_fp_binop(op_byte: u8) -> Option<WasmFpBinOp> {
    use WasmFpBinOp::*;
    Some(match op_byte {
        0x92 | 0xa0 => Add,
        0x93 | 0xa1 => Sub,
        0x94 | 0xa2 => Mul,
        0x95 | 0xa3 => Div,
        _ => return None,
    })
}

/// The FP unary value op a wasm FP-unary opcode byte computes. Decoded by
/// [`decode_fp_unop`] for operand reconstruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmFpUnOp {
    Abs,
    Neg,
    Sqrt,
    Ceil,
    Floor,
    Trunc,
}

/// Decode a wasm FP-unary opcode byte. `None` otherwise. f32 and f64.
pub fn decode_fp_unop(op_byte: u8) -> Option<WasmFpUnOp> {
    use WasmFpUnOp::*;
    Some(match op_byte {
        0x8b | 0x99 => Abs,
        0x8c | 0x9a => Neg,
        0x91 | 0x9f => Sqrt,
        0x8d | 0x9b => Ceil,
        0x8e | 0x9c => Floor,
        0x8f | 0x9d => Trunc,
        _ => return None,
    })
}

/// The FP comparison predicate a wasm FP-compare opcode byte computes (result
/// i32 0/1). Decoded by [`decode_fp_cmp`] for operand reconstruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmFpCmpOp {
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
}

/// Decode a wasm FP-comparison opcode byte. `None` otherwise. f32 and f64.
pub fn decode_fp_cmp(op_byte: u8) -> Option<WasmFpCmpOp> {
    use WasmFpCmpOp::*;
    Some(match op_byte {
        0x5b | 0x61 => Eq,
        0x5c | 0x62 => Ne,
        0x5d | 0x63 => Lt,
        0x5e | 0x64 => Gt,
        0x5f | 0x65 => Le,
        0x60 | 0x66 => Ge,
        _ => return None,
    })
}

/// The integer-width cast a wasm cast opcode byte computes. Decoded by
/// [`decode_int_cast`] for operand reconstruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmIntCastOp {
    /// `i32.wrap_i64` (0xa7).
    WrapI64,
    /// `i64.extend_i32_s` (0xac).
    ExtendI32S,
    /// `i64.extend_i32_u` (0xad).
    ExtendI32U,
}

/// Decode a wasm integer-width-cast opcode byte. `None` otherwise.
pub fn decode_int_cast(op_byte: u8) -> Option<WasmIntCastOp> {
    use WasmIntCastOp::*;
    Some(match op_byte {
        0xa7 => WrapI64,
        0xac => ExtendI32S,
        0xad => ExtendI32U,
        _ => return None,
    })
}

// ---------------------------------------------------------------------------
// SIMD / v128 lane-vector value ops (0xfd prefix; sub-opcode selects the form)
// ---------------------------------------------------------------------------

/// The lane-wise SIMD VALUE op a wasm 0xfd sub-opcode computes. Decoded by
/// [`decode_simd_lane_op`] for the v128 operand reconstruction: the machine side
/// is rebuilt from THIS decoded (lane-op, lane-shape) pair, so a WRONG sub-opcode
/// (e.g. `i32x4.mul` 0xb5 where `i32x4.add` 0xae was intended, or `f32x4.mul`
/// where `i32x4.mul` was intended) decodes to a DIFFERENT lane operation / lane
/// shape ⇒ REFUTE.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmSimdLaneOp {
    /// `i32x4.add` (0xfd 0xae) — four 32-bit integer lanes, lane-wise wrapping add.
    I32x4Add,
    /// `i32x4.mul` (0xfd 0xb5) — four 32-bit integer lanes, lane-wise low multiply.
    I32x4Mul,
    /// `f32x4.add` (0xfd 0xe4) — four binary32 lanes, lane-wise IEEE add (RNE).
    F32x4Add,
    /// `f32x4.mul` (0xfd 0xe6) — four binary32 lanes, lane-wise IEEE mul (RNE).
    F32x4Mul,
}

/// Decode a wasm 0xfd SIMD sub-opcode to the lane-wise VALUE op it computes.
/// `None` for non-value (memory/materialization) sub-opcodes and anything not in
/// the reconstructable lane-op set.
pub fn decode_simd_lane_op(sub_opcode: u32) -> Option<WasmSimdLaneOp> {
    use WasmSimdLaneOp::*;
    Some(match sub_opcode {
        0xae => I32x4Add,
        0xb5 => I32x4Mul,
        0xe4 => F32x4Add,
        0xe6 => F32x4Mul,
        _ => return None,
    })
}

/// Encode `i32x4.add` — four 32-bit integer lanes, lane-wise wrapping add over a
/// 128-bit vector. `src1`/`src2` are 128-bit bitvectors; the result is the lane-
/// wise reconstruction (extract each 32-bit lane, add, concat). A WRONG lane width
/// (e.g. treating it as `i16x8`) yields a structurally different 128-bit value ⇒
/// REFUTE.
pub fn encode_i32x4_add(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    crate::smt::map_lanes_binary(&src1, &src2, crate::smt::VectorArrangement::S4, |a, b| {
        a.bvadd(b)
    })
}

/// Encode `i32x4.mul` — four 32-bit integer lanes, lane-wise low multiply (the low
/// 32 bits of each lane product) over a 128-bit vector.
pub fn encode_i32x4_mul(src1: SmtExpr, src2: SmtExpr) -> SmtExpr {
    crate::smt::map_lanes_binary(&src1, &src2, crate::smt::VectorArrangement::S4, |a, b| {
        a.bvmul(b)
    })
}

/// Encode ONE binary32 lane of `f32x4.add` — IEEE add under RNE. The packed op
/// applies this independently to each of its four lanes, so one representative
/// lane (FP-typed) witnesses the full-vector value equivalence (mirrors the x86
/// `encode_packed_fp_add_lane`). A wrong op / wrong lane width refutes under the
/// FP evaluator.
pub fn encode_f32x4_add_lane(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    SmtExpr::fp_add(RoundingMode::RNE, a, b)
}

/// Encode ONE binary32 lane of `f32x4.mul` — IEEE mul under RNE.
pub fn encode_f32x4_mul_lane(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    SmtExpr::fp_mul(RoundingMode::RNE, a, b)
}

/// The FP-format cast a wasm cast opcode byte computes. Decoded by
/// [`decode_fp_format_cast`] for operand reconstruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmFpFormatCastOp {
    /// `f32.demote_f64` (0xb6) — narrow f64 -> f32.
    DemoteF64,
    /// `f64.promote_f32` (0xbb) — widen f32 -> f64.
    PromoteF32,
}

/// Decode a wasm FP-format-cast opcode byte. `None` otherwise.
pub fn decode_fp_format_cast(op_byte: u8) -> Option<WasmFpFormatCastOp> {
    use WasmFpFormatCastOp::*;
    Some(match op_byte {
        0xb6 => DemoteF64,
        0xbb => PromoteF32,
        _ => return None,
    })
}

/// The int->FP CONVERT a wasm `f*.convert_i*` opcode byte computes. Decoded by
/// [`decode_convert`] for operand reconstruction; the machine side is rebuilt as
/// the SIGNED or UNSIGNED convert at the decoded src/dest widths, so a wrong byte
/// (signed where unsigned was intended, or a wrong width) decodes to a different
/// convert ⇒ REFUTE.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WasmConvertOp {
    /// Source integer width (32 or 64).
    pub src_width: u32,
    /// Destination FP width (32 = f32, 64 = f64).
    pub fp_width: u32,
    /// `true` for the SIGNED `_s` form, `false` for the UNSIGNED `_u` form.
    pub signed: bool,
}

/// Decode a wasm `f{32,64}.convert_i{32,64}_{s,u}` opcode byte (0xb2..=0xba range,
/// minus the demote/promote/reinterpret bytes). `None` otherwise.
pub fn decode_convert(op_byte: u8) -> Option<WasmConvertOp> {
    let op = |src_width, fp_width, signed| WasmConvertOp {
        src_width,
        fp_width,
        signed,
    };
    Some(match op_byte {
        0xb2 => op(32, 32, true),  // f32.convert_i32_s
        0xb3 => op(32, 32, false), // f32.convert_i32_u
        0xb4 => op(64, 32, true),  // f32.convert_i64_s
        0xb5 => op(64, 32, false), // f32.convert_i64_u
        0xb7 => op(32, 64, true),  // f64.convert_i32_s
        0xb8 => op(32, 64, false), // f64.convert_i32_u
        0xb9 => op(64, 64, true),  // f64.convert_i64_s
        0xba => op(64, 64, false), // f64.convert_i64_u
        _ => return None,
    })
}

/// The saturating FP->int TRUNC a wasm `i*.trunc_sat_f*` op computes. Decoded by
/// [`decode_trunc_sat`] from the 0xfc PREFIX + sub-index; the machine side is
/// rebuilt as the SIGNED or UNSIGNED saturating truncation at the decoded
/// fp/int widths, so a wrong sub-index (unsigned where signed intended, or a
/// non-saturating wrap) decodes to a different op ⇒ REFUTE.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WasmTruncSatOp {
    /// Source FP width (32 = f32, 64 = f64).
    pub fp_width: u32,
    /// Destination integer width (32 or 64).
    pub int_width: u32,
    /// `true` for the SIGNED `_s` form, `false` for the UNSIGNED `_u` form.
    pub signed: bool,
}

/// Decode a wasm saturating conversion from the 0xfc PREFIX byte + sub-index, per
/// the wasm spec. `None` if `prefix != 0xfc` or the sub-index is not a defined
/// `trunc_sat` form (fail closed).
pub fn decode_trunc_sat(prefix: u8, sub: u32) -> Option<WasmTruncSatOp> {
    if prefix != 0xfc {
        return None;
    }
    let op = |fp_width, int_width, signed| WasmTruncSatOp {
        fp_width,
        int_width,
        signed,
    };
    Some(match sub {
        0 => op(32, 32, true),  // i32.trunc_sat_f32_s
        1 => op(32, 32, false), // i32.trunc_sat_f32_u
        2 => op(64, 32, true),  // i32.trunc_sat_f64_s
        3 => op(64, 32, false), // i32.trunc_sat_f64_u
        4 => op(32, 64, true),  // i64.trunc_sat_f32_s
        5 => op(32, 64, false), // i64.trunc_sat_f32_u
        6 => op(64, 64, true),  // i64.trunc_sat_f64_s
        7 => op(64, 64, false), // i64.trunc_sat_f64_u
        _ => return None,
    })
}

/// The population-count width a wasm `popcnt` opcode byte operates at. Decoded by
/// [`decode_popcnt`] for operand reconstruction: the machine side is rebuilt as a
/// bit-count at THIS width, so a wrong opcode byte that does NOT decode to popcnt
/// fails closed (and a popcnt-for-some-other-bitop machine encoder diverges from
/// the trust-ir `Ctpop` reference for almost every input ⇒ REFUTE).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmPopcntOp {
    /// `i32.popcnt` (0x69) — 32-bit population count.
    I32,
    /// `i64.popcnt` (0x7b) — 64-bit population count.
    I64,
}

/// Decode a wasm `popcnt` opcode byte to its operand width. `None` otherwise.
pub fn decode_popcnt(op_byte: u8) -> Option<WasmPopcntOp> {
    use WasmPopcntOp::*;
    Some(match op_byte {
        0x69 => I32,
        0x7b => I64,
        _ => return None,
    })
}

/// `i32.popcnt` (0x69) / `i64.popcnt` (0x7b) — population count (number of set
/// bits), materialized as a sum of the `width` individual source bits each
/// zero-extended to the result width. The result lies in `[0, width]`. Mirrors
/// `x86_64_semantics::encode_popcnt` (the genuine, faithfully-modeled bit-count).
pub fn encode_popcnt(x: SmtExpr) -> SmtExpr {
    let width = x.bv_width();
    let mut acc = SmtExpr::bv_const(0, width);
    for i in 0..width {
        let bit = x.clone().extract(i, i);
        let bit_w = if width == 1 {
            bit
        } else {
            bit.zero_ext(width - 1)
        };
        acc = acc.bvadd(bit_w);
    }
    acc
}

/// The bit-reinterpret (bitcast) a wasm `reinterpret_*` opcode byte computes. The
/// operand-and-result WIDTH is what carries the reconstruction content: a
/// wrong-WIDTH byte (e.g. `i64.reinterpret_f64` 0xbd where `i32.reinterpret_f32`
/// 0xbc was intended) decodes to a different width ⇒ the reconstructed machine
/// side has a different bitvector width than the trust-ir source ⇒ structurally
/// distinct ⇒ REFUTE (the reconstruction fails closed on the width mismatch).
///
/// Within a single width both directions (`iN.reinterpret_fN` and
/// `fN.reinterpret_iN`) are genuinely bit-identity, so a same-width direction
/// swap is itself correct (a no-op bit copy) — exactly like the x86 cross-domain
/// `MovdToXmm`/`MovdFromXmm` "preserves bits" pair. The WIDTH is the discriminator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmReinterpretOp {
    /// `i32.reinterpret_f32` (0xbc) — 32-bit bit copy f32 -> i32.
    I32F32,
    /// `i64.reinterpret_f64` (0xbd) — 64-bit bit copy f64 -> i64.
    I64F64,
    /// `f32.reinterpret_i32` (0xbe) — 32-bit bit copy i32 -> f32.
    F32I32,
    /// `f64.reinterpret_i64` (0xbf) — 64-bit bit copy i64 -> f64.
    F64I64,
}

impl WasmReinterpretOp {
    /// The (operand == result) bit WIDTH of this reinterpret. Bit-reinterpret is
    /// width-preserving, so source and destination share this width.
    pub fn width(self) -> u32 {
        match self {
            WasmReinterpretOp::I32F32 | WasmReinterpretOp::F32I32 => 32,
            WasmReinterpretOp::I64F64 | WasmReinterpretOp::F64I64 => 64,
        }
    }
}

/// Decode a wasm bit-reinterpret opcode byte. `None` otherwise.
pub fn decode_reinterpret(op_byte: u8) -> Option<WasmReinterpretOp> {
    use WasmReinterpretOp::*;
    Some(match op_byte {
        0xbc => I32F32,
        0xbd => I64F64,
        0xbe => F32I32,
        0xbf => F64I64,
        _ => return None,
    })
}

/// `iN.reinterpret_fN` / `fN.reinterpret_iN` — a pure, width-preserving bit copy
/// (no rounding, no NaN sanitization, no saturation). At the SMT bitvector level
/// the operand bits ARE the result bits, so this is the identity on the operand
/// bitvector. Mirrors the trust-ir `Bitcast` (`encode_trust_ir_bitcast`, also the
/// identity) and the x86 `MOVD ... preserves bits` proof.
pub fn encode_reinterpret(x: SmtExpr) -> SmtExpr {
    x
}

// --- Arithmetic (result width == operand width) -----------------------------

/// `i32.add` (0x6a) / `i64.add` (0x7c): `(a + b) mod 2^N`.
pub fn encode_add(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    a.bvadd(b)
}

/// `i32.sub` (0x6b) / `i64.sub` (0x7d): `(a - b) mod 2^N`.
pub fn encode_sub(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    a.bvsub(b)
}

/// `i32.mul` (0x6c) / `i64.mul` (0x7e): low-N-bits of `a * b`.
pub fn encode_mul(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    a.bvmul(b)
}

// --- Division / remainder (conditionally defined; see proof preconditions) --
//
// wasm `iN.div_s`/`div_u` TRAP on divisor 0, and `div_s` also traps on the
// signed-overflow case `INT_MIN / -1`. `rem_s`/`rem_u` trap only on divisor 0
// (`rem_s` at `INT_MIN/-1` is defined to be 0). On the non-trapping domain the
// value functions are the usual bitvector operations, so the refinement proofs
// carry the matching preconditions (`b != 0`, plus `¬(a==INT_MIN ∧ b==-1)` for
// `div_s`).

/// `i32.div_s` (0x6d) / `i64.div_s` (0x7f): truncating signed quotient.
pub fn encode_div_s(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    a.bvsdiv(b)
}

/// `i32.div_u` (0x6e) / `i64.div_u` (0x80): unsigned quotient.
pub fn encode_div_u(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    a.bvudiv(b)
}

/// `i32.rem_s` (0x6f) / `i64.rem_s` (0x81): signed remainder `a - (a /s b) * b`
/// (sign follows the dividend) — matches the `Srem` encoding in
/// `trust_ir_semantics`.
pub fn encode_rem_s(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    let q = a.clone().bvsdiv(b.clone());
    a.bvsub(q.bvmul(b))
}

/// `i32.rem_u` (0x70) / `i64.rem_u` (0x82): unsigned remainder `a - (a /u b) * b`.
pub fn encode_rem_u(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    let q = a.clone().bvudiv(b.clone());
    a.bvsub(q.bvmul(b))
}

// --- Bitwise and shifts -----------------------------------------------------
//
// wasm `iN.shl`/`shr_s`/`shr_u` mask the shift amount mod N (`shift & (N-1)`);
// SMT `bvshl`/`bvashr`/`bvlshr` do NOT mask (amount >= N gives 0 / sign-fill).
// The shift refinement proofs carry the precondition `b <u N` (trust-ir's
// well-defined shift domain), under which the mask is the identity.

/// `i32.and` (0x71) / `i64.and` (0x83).
pub fn encode_and(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    a.bvand(b)
}

/// `i32.or` (0x72) / `i64.or` (0x84).
pub fn encode_or(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    a.bvor(b)
}

/// `i32.xor` (0x73) / `i64.xor` (0x85).
pub fn encode_xor(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    a.bvxor(b)
}

/// Mask a shift amount to `width` bits (`b & (width-1)`), as wasm does.
fn shift_mask(b: SmtExpr, width: u32) -> SmtExpr {
    b.bvand(SmtExpr::bv_const(u64::from(width - 1), width))
}

/// `i32.shl` (0x74) / `i64.shl` (0x86): left shift by `b mod width`.
pub fn encode_shl(a: SmtExpr, b: SmtExpr, width: u32) -> SmtExpr {
    a.bvshl(shift_mask(b, width))
}

/// `i32.shr_s` (0x75) / `i64.shr_s` (0x87): arithmetic right shift by `b mod width`.
pub fn encode_shr_s(a: SmtExpr, b: SmtExpr, width: u32) -> SmtExpr {
    a.bvashr(shift_mask(b, width))
}

/// `i32.shr_u` (0x76) / `i64.shr_u` (0x88): logical right shift by `b mod width`.
pub fn encode_shr_u(a: SmtExpr, b: SmtExpr, width: u32) -> SmtExpr {
    a.bvlshr(shift_mask(b, width))
}

// --- Comparisons (operand width N, result i32 in {0,1}) ---------------------

/// Lift a Bool predicate to a 32-bit wasm boolean (`1` if true, else `0`).
pub fn bool_to_i32(cond: SmtExpr) -> SmtExpr {
    SmtExpr::ite(cond, SmtExpr::bv_const(1, 32), SmtExpr::bv_const(0, 32))
}

/// `i32.eq` (0x46) / `i64.eq` (0x51).
pub fn encode_eq(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    bool_to_i32(a.eq_expr(b))
}

/// `i32.ne` (0x47) / `i64.ne` (0x52).
pub fn encode_ne(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    bool_to_i32(a.eq_expr(b).not_expr())
}

/// `i32.lt_s` (0x48) / `i64.lt_s` (0x53).
pub fn encode_lt_s(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    bool_to_i32(a.bvslt(b))
}

/// `i32.le_s` (0x4c) / `i64.le_s` (0x57).
pub fn encode_le_s(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    bool_to_i32(a.bvsle(b))
}

/// `i32.gt_s` (0x4a) / `i64.gt_s` (0x55).
pub fn encode_gt_s(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    bool_to_i32(a.bvsgt(b))
}

/// `i32.ge_s` (0x4e) / `i64.ge_s` (0x59).
pub fn encode_ge_s(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    bool_to_i32(a.bvsge(b))
}

/// `i32.lt_u` (0x49) / `i64.lt_u` (0x54).
pub fn encode_lt_u(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    bool_to_i32(a.bvult(b))
}

/// `i32.le_u` (0x4d) / `i64.le_u` (0x58).
pub fn encode_le_u(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    bool_to_i32(a.bvule(b))
}

/// `i32.gt_u` (0x4b) / `i64.gt_u` (0x56).
pub fn encode_gt_u(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    bool_to_i32(a.bvugt(b))
}

/// `i32.ge_u` (0x4f) / `i64.ge_u` (0x5a).
pub fn encode_ge_u(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    bool_to_i32(a.bvuge(b))
}

// --- Integer-width casts ----------------------------------------------------

/// `i32.wrap_i64`: low 32 bits of a 64-bit value.
pub fn encode_wrap(x: SmtExpr) -> SmtExpr {
    x.extract(31, 0)
}

/// `i64.extend_i32_u`: zero-extend i32 → i64.
pub fn encode_zext_i32_i64(x: SmtExpr) -> SmtExpr {
    x.zero_ext(32)
}

/// `i64.extend_i32_s`: sign-extend i32 → i64.
pub fn encode_sext_i32_i64(x: SmtExpr) -> SmtExpr {
    x.sign_ext(32)
}

// --- Unary ops --------------------------------------------------------------

/// Integer negate — wasm has no `ineg`, so the backend emits `0 - x`. This
/// models that expansion; the refinement proof shows it equals trust-ir's
/// `bvneg`.
pub fn encode_ineg(x: SmtExpr, width: u32) -> SmtExpr {
    SmtExpr::bv_const(0, width).bvsub(x)
}

/// `f32.neg` (0x8c) / `f64.neg` (0x9a).
pub fn encode_fneg(x: SmtExpr) -> SmtExpr {
    x.fp_neg()
}

/// `f32.abs` (0x8b) / `f64.abs` (0x99).
pub fn encode_fabs(x: SmtExpr) -> SmtExpr {
    x.fp_abs()
}

/// `f32.sqrt` (0x91) / `f64.sqrt` (0x9f).
pub fn encode_fsqrt(x: SmtExpr) -> SmtExpr {
    SmtExpr::fp_sqrt(RoundingMode::RNE, x)
}

/// `f32.ceil` (0x8d) / `f64.ceil` (0x9b) — round-to-integral toward +inf.
pub fn encode_fceil(x: SmtExpr) -> SmtExpr {
    SmtExpr::fp_round_to_integral(RoundingMode::RTP, x)
}

/// `f32.floor` (0x8e) / `f64.floor` (0x9c) — round-to-integral toward -inf.
pub fn encode_ffloor(x: SmtExpr) -> SmtExpr {
    SmtExpr::fp_round_to_integral(RoundingMode::RTN, x)
}

/// `f32.trunc` (0x8f) / `f64.trunc` (0x9d) — round-to-integral toward zero.
pub fn encode_ftrunc(x: SmtExpr) -> SmtExpr {
    SmtExpr::fp_round_to_integral(RoundingMode::RTZ, x)
}

// --- IEEE-754 float arithmetic (round-to-nearest-ties-to-even) --------------
//
// wasm `f32`/`f64` add/sub/mul/div are IEEE-754 with roundTiesToEven and the
// usual NaN/inf/signed-zero rules — i.e. exactly SMT-LIB `fp.add`/`fp.sub`/
// `fp.mul`/`fp.div` with rounding mode RNE. (FP `=` in SMT-LIB treats all NaNs
// as equal, so the refinement is up to NaN payload — the standard granularity.)

/// `f32.add` (0x92) / `f64.add` (0xa0).
pub fn encode_fadd(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    SmtExpr::fp_add(RoundingMode::RNE, a, b)
}

/// `f32.sub` (0x93) / `f64.sub` (0xa1).
pub fn encode_fsub(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    SmtExpr::fp_sub(RoundingMode::RNE, a, b)
}

/// `f32.mul` (0x94) / `f64.mul` (0xa2).
pub fn encode_fmul(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    SmtExpr::fp_mul(RoundingMode::RNE, a, b)
}

/// `f32.div` (0x95) / `f64.div` (0xa3).
pub fn encode_fdiv(a: SmtExpr, b: SmtExpr) -> SmtExpr {
    SmtExpr::fp_div(RoundingMode::RNE, a, b)
}

// --- Float <-> int conversions ----------------------------------------------
//
// These are the wasm machine encoders for the float<->int CONVERSION family
// that was previously DEFERRED (the native evaluator could not faithfully model
// rounding / signedness / saturation). The evaluator now models all three
// (smt.rs `FPToSBv`/`FPToUBv` round-then-saturate-with-NaN->0; `BvToFP`
// sign-interprets its operand, so unsigned converts zero-extend first), so these
// are now genuinely checkable: a signed-for-unsigned or saturating-for-wrapping
// lowering DIVERGES from the source spec ⇒ REFUTE.

/// `(eb, sb)` IEEE format for a wasm FP width (32 -> binary32, 64 -> binary64).
fn fp_format(fp_width: u32) -> (u32, u32) {
    if fp_width == 32 { (8, 24) } else { (11, 53) }
}

/// `f{32,64}.convert_i{32,64}_s` — SIGNED int -> FP, round-to-nearest-even.
///
/// `src` is the integer bitvector; `fp_width` selects the destination format.
/// `BvToFP` interprets its operand as a SIGNED bitvector, so this is the signed
/// convert directly. The i64->f32 / large i64->f64 cases that are not exactly
/// representable round to nearest (the RNE default), matching the wasm spec.
pub fn encode_convert_s(src: SmtExpr, fp_width: u32) -> SmtExpr {
    let (eb, sb) = fp_format(fp_width);
    SmtExpr::bv_to_fp(RoundingMode::RNE, src, eb, sb)
}

/// `f{32,64}.convert_i{32,64}_u` — UNSIGNED int -> FP, round-to-nearest-even.
///
/// `BvToFP` interprets its operand as SIGNED, so the source is FIRST zero-extended
/// by `src_width` bits (clearing the sign bit) to give the correct non-negative
/// magnitude. A signed-for-unsigned lowering bug feeds the un-extended (sign-bit-
/// set) operand here and DIVERGES for a high-bit-set input ⇒ REFUTE.
pub fn encode_convert_u(src: SmtExpr, src_width: u32, fp_width: u32) -> SmtExpr {
    let (eb, sb) = fp_format(fp_width);
    let zext = SmtExpr::ZeroExtend {
        operand: Arc::new(src),
        extra_bits: src_width,
        width: src_width * 2,
    };
    SmtExpr::bv_to_fp(RoundingMode::RNE, zext, eb, sb)
}

/// `i{32,64}.trunc_sat_f{32,64}_s` (0xfc prefix) — SATURATING FP -> signed int,
/// round toward zero.
///
/// `int_width` is the result width. `FPToSBv` now rounds toward zero and SATURATES
/// to the signed `int_width` range with NaN -> 0 (the wasm `trunc_sat` semantics);
/// a wrapping (mask-only) machine would DIVERGE for an out-of-range input ⇒ REFUTE.
pub fn encode_trunc_sat_s(src: SmtExpr, int_width: u32) -> SmtExpr {
    SmtExpr::fp_to_sbv(RoundingMode::RTZ, src, int_width)
}

/// `i{32,64}.trunc_sat_f{32,64}_u` (0xfc prefix) — SATURATING FP -> unsigned int,
/// round toward zero (NaN/negative -> 0, overflow -> UINT_MAX).
pub fn encode_trunc_sat_u(src: SmtExpr, int_width: u32) -> SmtExpr {
    SmtExpr::fp_to_ubv(RoundingMode::RTZ, src, int_width)
}

// --- Linear memory (byte-addressed, little-endian) --------------------------
//
// wasm linear memory is a byte array; `i32.store`/`i32.load` (and i64) access
// `N` consecutive bytes in **little-endian** order at the effective address
// (here, the pointer the backend's `local.get ptr` placed on the stack; the
// memarg static offset is 0 in the current lowering). We model memory as
// `(Array (BitVec 32) (BitVec 8))` and an N-byte access as N byte ops.

/// A zero-initialized linear memory: `(Array (BitVec 32) (BitVec 8))` of 0s.
pub fn zero_memory() -> SmtExpr {
    SmtExpr::const_array(SmtSort::BitVec(32), SmtExpr::bv_const(0, 8))
}

fn addr_plus(addr: &SmtExpr, k: u64) -> SmtExpr {
    if k == 0 {
        addr.clone()
    } else {
        addr.clone().bvadd(SmtExpr::bv_const(k, 32))
    }
}

/// Store an `n_bytes`-wide value `val` at `addr` into `mem`, little-endian.
fn store_bytes(mem: SmtExpr, addr: &SmtExpr, val: &SmtExpr, n_bytes: u32) -> SmtExpr {
    let mut m = mem;
    for i in 0..n_bytes {
        let byte = val.clone().extract(8 * i + 7, 8 * i);
        m = SmtExpr::store(m, addr_plus(addr, u64::from(i)), byte);
    }
    m
}

/// Load an `n_bytes`-wide value at `addr` from `mem`, little-endian.
fn load_bytes(mem: &SmtExpr, addr: &SmtExpr, n_bytes: u32) -> SmtExpr {
    // Reassemble high byte first via concat: byte[n-1] ++ ... ++ byte[0].
    let mut acc: Option<SmtExpr> = None;
    for i in 0..n_bytes {
        let byte = SmtExpr::select(mem.clone(), addr_plus(addr, u64::from(i)));
        acc = Some(match acc {
            None => byte,                // lowest byte
            Some(hi) => byte.concat(hi), // new byte is more significant
        });
    }
    acc.expect("n_bytes >= 1")
}

/// `i32.store`: write 4 little-endian bytes of `val` at `addr`.
pub fn encode_store_i32(mem: SmtExpr, addr: SmtExpr, val: SmtExpr) -> SmtExpr {
    store_bytes(mem, &addr, &val, 4)
}

/// `i32.load`: read 4 little-endian bytes at `addr`.
pub fn encode_load_i32(mem: SmtExpr, addr: SmtExpr) -> SmtExpr {
    load_bytes(&mem, &addr, 4)
}

/// `i64.store`: write 8 little-endian bytes of `val` at `addr`.
pub fn encode_store_i64(mem: SmtExpr, addr: SmtExpr, val: SmtExpr) -> SmtExpr {
    store_bytes(mem, &addr, &val, 8)
}

/// `i64.load`: read 8 little-endian bytes at `addr`.
pub fn encode_load_i64(mem: SmtExpr, addr: SmtExpr) -> SmtExpr {
    load_bytes(&mem, &addr, 8)
}

// --- Address arithmetic (mirrors the backend's GEP lowering) ----------------

/// Single-index `GEP` element address: `base + index * elem_size_bytes`.
///
/// Mirrors the backend's GEP arm (`trust-cg-codegen/src/wasm/lower.rs`:
/// `local.get base; local.get index; i32.const elem_size; i32.mul; i32.add`).
/// `elem_size_bytes` is the element size the layout engine yields. This is the
/// independently-encoded "wasm side" — proving a property of THIS formula (e.g.
/// non-overlap of distinct elements) validates the stride the backend emits.
pub fn encode_gep_element(base: SmtExpr, index: SmtExpr, elem_size_bytes: u32) -> SmtExpr {
    base.bvadd(index.bvmul(SmtExpr::bv_const(u64::from(elem_size_bytes), 32)))
}
