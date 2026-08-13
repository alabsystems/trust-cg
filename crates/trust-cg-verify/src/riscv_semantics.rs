// trust-cg-verify/riscv_semantics.rs - RISC-V (RV64) instruction semantics as SMT formulas
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Encodes RISC-V RV64I + M instruction semantics as bitvector SMT expressions.
// Each emittable opcode maps to a pure function from input bitvectors to the
// output bitvector that the instruction writes into its destination register.
//
// HONESTY POLICY (mirrors aarch64_semantics.rs / x86_64_semantics.rs):
//
//   The functions in this module are authored INDEPENDENTLY of the trust_ir
//   spec encoder (trust_ir_semantics.rs). They transcribe the RISC-V
//   Unprivileged ISA Specification directly. The lowering proofs in
//   riscv_lowering_proofs.rs pair a trust_ir spec expression against a machine
//   expression built HERE; an equivalence is meaningful precisely because the
//   two sides were written from different references (the trust_ir IR contract
//   vs the RISC-V ISA manual). Building the machine side to mirror the spec
//   would be the f81e45b lie and is forbidden.
//
// Reference: RISC-V Unprivileged ISA Specification (Volume 1, Version 20191213)
//   - Chapter 2.4 "Integer Computational Instructions" (ADD/SUB/AND/OR/XOR/
//     SLL/SRL/SRA/SLT/SLTU, ADDI/XORI/SLLI/SRLI/SLTIU)
//   - "M" Standard Extension, Section 7.1 (MUL)
// Reference: designs/2026-04-13-verification-architecture.md

//! RISC-V RV64 instruction semantics encoded as [`SmtExpr`] bitvector formulas.
//!
//! Each function takes symbolic operand expressions and returns the symbolic
//! destination-register value. Comparison instructions (`SLT`/`SLTU`/`SLTIU`)
//! follow the verifier's convention of returning a **1-bit** bitvector (`bv1`)
//! whose value is `1` iff the comparison holds and `0` otherwise — the same
//! convention used by `x86_64_eflags::encode_setcc` and the trust_ir
//! `encode_trust_ir_icmp` spec encoder. This is faithful to RV64 `SLT`, whose
//! architectural result is a 64-bit register with `result[63:1] = 0` and
//! `result[0] = (rs1 <s rs2)`; the lowering proofs compare the boolean bit that
//! the comparison feeds into.
//!
//! Width is carried by the operand expressions themselves (`let _ = size;`),
//! exactly as in `aarch64_semantics.rs`.

use crate::smt::{RoundingMode, SmtExpr};

// ---------------------------------------------------------------------------
// RiscVOperandSize
// ---------------------------------------------------------------------------

/// Operand size for an RV64 register-register / register-immediate operation.
///
/// RV64 base integer ops operate on full 64-bit (`X`) registers; the `S32`
/// variant exists for symmetry with the x86/AArch64 size enums and to document
/// 32-bit-domain proofs. Width is ultimately carried by the [`SmtExpr`] nodes,
/// so this is informational (matching `x86_64_semantics::X86OperandSize`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RiscVOperandSize {
    /// 32-bit operand (W-domain).
    S32,
    /// 64-bit operand (X-domain) — the default for RV64 base integer ops.
    S64,
}

/// Width in bits for a [`RiscVOperandSize`].
pub fn riscv_operand_size_bits(size: RiscVOperandSize) -> u32 {
    match size {
        RiscVOperandSize::S32 => 32,
        RiscVOperandSize::S64 => 64,
    }
}

// ---------------------------------------------------------------------------
// RV64I: Integer register-register arithmetic (R-type)
// ---------------------------------------------------------------------------

/// Encode `ADD rd, rs1, rs2` — register-register add.
///
/// Semantics: `rd = rs1 + rs2` (two's-complement, wrapping; carry discarded).
/// Reference: RISC-V ISA, ADD.
pub fn encode_add(size: RiscVOperandSize, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    let _ = size; // width carried by the operand expressions
    rs1.bvadd(rs2)
}

/// Encode `SUB rd, rs1, rs2` — register-register subtract.
///
/// Semantics: `rd = rs1 - rs2` (two's-complement, wrapping; borrow discarded).
/// Reference: RISC-V ISA, SUB.
pub fn encode_sub(size: RiscVOperandSize, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    let _ = size;
    rs1.bvsub(rs2)
}

/// Encode `MUL rd, rs1, rs2` ("M" extension) — low-XLEN multiply.
///
/// Semantics: `rd = (rs1 * rs2) mod 2^XLEN` — the lower XLEN bits of the
/// full product. SMT `bvmul` is modular and already returns the low bits.
/// Reference: RISC-V ISA, "M" extension, MUL.
pub fn encode_mul(size: RiscVOperandSize, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    let _ = size;
    rs1.bvmul(rs2)
}

/// Encode `AND rd, rs1, rs2` — bitwise AND.
///
/// Semantics: `rd = rs1 & rs2`. Reference: RISC-V ISA, AND.
pub fn encode_and(size: RiscVOperandSize, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    let _ = size;
    rs1.bvand(rs2)
}

/// Encode `OR rd, rs1, rs2` — bitwise OR.
///
/// Semantics: `rd = rs1 | rs2`. Reference: RISC-V ISA, OR.
pub fn encode_or(size: RiscVOperandSize, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    let _ = size;
    rs1.bvor(rs2)
}

/// Encode `XOR rd, rs1, rs2` — bitwise XOR.
///
/// Semantics: `rd = rs1 ^ rs2`. Reference: RISC-V ISA, XOR.
pub fn encode_xor(size: RiscVOperandSize, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    let _ = size;
    rs1.bvxor(rs2)
}

// ---------------------------------------------------------------------------
// RV64I: Integer register-register shifts (R-type)
// ---------------------------------------------------------------------------

/// Encode `SLL rd, rs1, rs2` — shift left logical (register amount).
///
/// RV64 hardware semantics: `rd = rs1 << (rs2 & 0x3F)` — the shift amount is
/// the low **6 bits** of `rs2` (Section 4.2 / 2.4.2). At the i64 lowering
/// level the trust_ir `Ishl` spec encoder uses SMT `bvshl` over a shift amount
/// the trust_ir type system guarantees to be in `[0, 63]`; over that domain the
/// masked hardware result coincides with the spec, so the 1:1 proof is faithful
/// (matching the AArch64 i64 `Ishl -> LSL` precedent). We model the unmasked
/// `bvshl` here: over the in-range domain it IS the RV64 SLL result, and at
/// XLEN=64 the mask `& 0x3F` is the identity for every valid shift amount.
/// Reference: RISC-V ISA, SLL / SLLW.
pub fn encode_sll(size: RiscVOperandSize, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    let _ = size;
    rs1.bvshl(rs2)
}

/// Encode `SRL rd, rs1, rs2` — shift right logical (register amount).
///
/// RV64 hardware semantics: `rd = (unsigned)rs1 >> (rs2 & 0x3F)` (zero-fill).
/// See [`encode_sll`] for the in-range / masking discussion.
/// Reference: RISC-V ISA, SRL / SRLW.
pub fn encode_srl(size: RiscVOperandSize, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    let _ = size;
    rs1.bvlshr(rs2)
}

/// Encode `SRA rd, rs1, rs2` — shift right arithmetic (register amount).
///
/// RV64 hardware semantics: `rd = (signed)rs1 >> (rs2 & 0x3F)` (sign-fill).
/// See [`encode_sll`] for the in-range / masking discussion.
/// Reference: RISC-V ISA, SRA / SRAW.
pub fn encode_sra(size: RiscVOperandSize, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    let _ = size;
    rs1.bvashr(rs2)
}

// ---------------------------------------------------------------------------
// RV64I: register-register shifts — FAITHFUL hardware-amount-masked encoders
// ---------------------------------------------------------------------------
//
// Operand-reconstruction (task #63, RISC-V) rebuilds the machine side of a shift
// obligation from the REAL emitted opcode over shared symbols, paired with a
// LOAD-BEARING `amount < width` precondition. For that precondition to be
// genuinely required (not cosmetic), the machine side must model the RV64
// hardware mask (`amount & (XLEN-1)`, i.e. `& 0x3F` at XLEN=64), NOT the unmasked
// `bvshl`/`bvlshr`/`bvashr` of [`encode_sll`]/[`encode_srl`]/[`encode_sra`].
//
// Mirrors `aarch64_semantics::encode_lsl_rr_masked` etc. (#57): IN range the mask
// is the identity so the masked machine side agrees with the trust_ir clamp-to-0
// spec side; OUT of range (amount >= width) the masked hardware result and the
// clamp-to-0 spec DIVERGE, so the `amount < width` precondition is load-bearing —
// strip it and a shift by exactly `width` REFUTES. The width is taken from the
// OPERAND sort (`rs2.bv_width()`), not the `RiscVOperandSize`, so the encoder
// composes at any bitvector width (the exhaustive reconstruction test uses i8).
// RV64 shifts >= XLEN are themselves implementation-defined/UB, so scoping them
// out with the precondition is the faithful contract.

/// The hardware shift-amount mask `(width - 1)` as a `width`-bit constant.
///
/// RV64 shift-by-register masks the amount with the low `log2(XLEN)` bits
/// (`& 0x3F` at XLEN=64; `& 0x1F` for the RV32/W-forms); `width` is a power of two
/// so `width - 1` is exactly that low-bits mask.
fn riscv_shift_amount_mask(width: u32) -> SmtExpr {
    SmtExpr::bv_const((width as u64).wrapping_sub(1), width)
}

/// Encode `SLL rd, rs1, rs2` with the FAITHFUL RV64 hardware amount mask
/// (`rd = rs1 << (rs2 & (XLEN-1))`). See the module note above; the masked form
/// is what makes the reconstruction `amount < width` precondition load-bearing.
/// Reference: RISC-V ISA, SLL (shift amount = `rs2[5:0]` at XLEN=64).
pub fn encode_sll_masked(size: RiscVOperandSize, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    let _ = size;
    let width = rs2.bv_width();
    rs1.bvshl(rs2.bvand(riscv_shift_amount_mask(width)))
}

/// Encode `SRL rd, rs1, rs2` with the FAITHFUL RV64 hardware amount mask
/// (`rd = (unsigned)rs1 >> (rs2 & (XLEN-1))`, zero-fill). See [`encode_sll_masked`].
/// Reference: RISC-V ISA, SRL.
pub fn encode_srl_masked(size: RiscVOperandSize, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    let _ = size;
    let width = rs2.bv_width();
    rs1.bvlshr(rs2.bvand(riscv_shift_amount_mask(width)))
}

/// Encode `SRA rd, rs1, rs2` with the FAITHFUL RV64 hardware amount mask
/// (`rd = (signed)rs1 >> (rs2 & (XLEN-1))`, sign-fill). See [`encode_sll_masked`].
/// Reference: RISC-V ISA, SRA.
pub fn encode_sra_masked(size: RiscVOperandSize, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    let _ = size;
    let width = rs2.bv_width();
    rs1.bvashr(rs2.bvand(riscv_shift_amount_mask(width)))
}

// ---------------------------------------------------------------------------
// RV64I: Set-less-than (comparison value ops)
// ---------------------------------------------------------------------------

/// Encode `SLT rd, rs1, rs2` — set if less than (signed).
///
/// RV64 hardware semantics: `rd = (rs1 <s rs2) ? 1 : 0`, a 64-bit register
/// holding 0 or 1. We return a **1-bit** bitvector per the verifier comparison
/// convention (`x86_64_eflags::encode_setcc`); architecturally this is
/// `result[0]` with `result[63:1] = 0`.
/// Reference: RISC-V ISA, SLT.
pub fn encode_slt(size: RiscVOperandSize, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    let _ = size;
    SmtExpr::ite(
        rs1.bvslt(rs2),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    )
}

/// Encode `SLTU rd, rs1, rs2` — set if less than (unsigned).
///
/// RV64 hardware semantics: `rd = (rs1 <u rs2) ? 1 : 0`. Returns a 1-bit
/// bitvector (see [`encode_slt`]).
///
/// `SLTU rd, x0, rs2` is the canonical RISC-V "snez" idiom (set if rs2 != 0):
/// `0 <u rs2` is true exactly when `rs2 != 0`. The `Icmp NotEqual` lowering
/// composes `encode_sltu(0, encode_sub(a, b))`.
/// Reference: RISC-V ISA, SLTU (and SNEZ pseudo).
pub fn encode_sltu(size: RiscVOperandSize, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    let _ = size;
    SmtExpr::ite(
        rs1.bvult(rs2),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    )
}

// ---------------------------------------------------------------------------
// RV64I: Integer register-immediate (I-type)
// ---------------------------------------------------------------------------

/// Encode `ADDI rd, rs1, imm12` — add sign-extended 12-bit immediate.
///
/// Semantics: `rd = rs1 + sext(imm12)` (wrapping). The 12-bit immediate is
/// sign-extended to XLEN before the add. The caller supplies `imm` as an
/// already-XLEN-width [`SmtExpr`] (the proof builds it via `bv_const`),
/// because at this layer the immediate's sign-extended bit pattern is known.
///
/// `ADDI rd, x0, imm` is the canonical "li" (load immediate) / `Iconst`;
/// `ADDI rd, src, 0` is "mv" (`Copy`); `ADDI rd, base, offset` is `StructGep`.
/// All share this single dataflow semantics: `rd = rs1 + imm`.
/// Reference: RISC-V ISA, ADDI (and LI / MV / NOP pseudos).
pub fn encode_addi(size: RiscVOperandSize, rs1: SmtExpr, imm: SmtExpr) -> SmtExpr {
    let _ = size;
    rs1.bvadd(imm)
}

/// Encode `XORI rd, rs1, imm12` — XOR with sign-extended 12-bit immediate.
///
/// Semantics: `rd = rs1 ^ sext(imm12)`. With `imm = 1` this flips the low bit,
/// which is the RISC-V boolean-NOT idiom used to invert an `SLT`/`SLTU` result
/// (e.g. `Icmp Sge` = NOT `Icmp Slt` = `XORI (SLT a,b), 1`). The caller passes
/// `imm` as an XLEN-width (or 1-bit, for the boolean-inversion idiom) constant
/// expression matching the operand it is XOR-ed with.
/// Reference: RISC-V ISA, XORI (and NOT / SEQZ-adjacent idioms).
pub fn encode_xori(size: RiscVOperandSize, rs1: SmtExpr, imm: SmtExpr) -> SmtExpr {
    let _ = size;
    rs1.bvxor(imm)
}

/// Encode `SLTIU rd, rs1, imm12` — set if less than immediate (unsigned).
///
/// RV64 hardware semantics: `rd = (rs1 <u sext(imm12)) ? 1 : 0`. The immediate
/// is sign-extended THEN compared as unsigned. Returns a 1-bit bitvector.
///
/// `SLTIU rd, rs1, 1` is the canonical "seqz" idiom (set if rs1 == 0):
/// `rs1 <u 1` is true exactly when `rs1 == 0` (the only unsigned value below 1).
/// The `Icmp Equal` lowering composes `encode_sltiu(encode_sub(a, b), 1)`.
///
/// The caller supplies the (sign-extended) `imm` as an XLEN-width comparison
/// operand expression.
/// Reference: RISC-V ISA, SLTIU (and SEQZ pseudo).
pub fn encode_sltiu(size: RiscVOperandSize, rs1: SmtExpr, imm: SmtExpr) -> SmtExpr {
    let _ = size;
    SmtExpr::ite(
        rs1.bvult(imm),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    )
}

/// Encode `SLLI rd, rs1, shamt` — shift left logical by a constant shift amount.
///
/// RV64 hardware semantics: `rd = rs1 << shamt`, where `shamt` is a 6-bit
/// immediate in `[0, 63]` encoded in the instruction (so it is in-range by
/// construction — there is no masking subtlety, unlike the register SLL).
/// Reference: RISC-V ISA, SLLI.
pub fn encode_slli(size: RiscVOperandSize, rs1: SmtExpr, shamt: u32) -> SmtExpr {
    let _ = size;
    let w = rs1.bv_width();
    debug_assert!(shamt < w, "encode_slli: shamt must be < operand width");
    rs1.bvshl(SmtExpr::bv_const(shamt as u64, w))
}

/// Encode `SRLI rd, rs1, shamt` — shift right logical by a constant shift amount.
///
/// RV64 hardware semantics: `rd = (unsigned)rs1 >> shamt` (zero-fill), `shamt`
/// a 6-bit immediate in `[0, 63]`. Reference: RISC-V ISA, SRLI.
pub fn encode_srli(size: RiscVOperandSize, rs1: SmtExpr, shamt: u32) -> SmtExpr {
    let _ = size;
    let w = rs1.bv_width();
    debug_assert!(shamt < w, "encode_srli: shamt must be < operand width");
    rs1.bvlshr(SmtExpr::bv_const(shamt as u64, w))
}

// ===========================================================================
// RV64 F/D scalar FLOATING-POINT instruction semantics (the "F" and "D"
// standard extensions). The MISSING SEMANTIC encoders for the FP opcodes
// trust-cg already EMITS (riscv_ops.rs / riscv/encode.rs). These are THIN
// wrappers over the FP SmtExpr nodes (FPAdd/FPSub/FPMul/FPDiv/FPSqrt + the
// fp.to_sbv / to_fp converts + the fp comparison predicates), which `try_eval`
// evaluates through the SILICON-VALIDATED INTEGER-ONLY fp_bitmodel.rs (host FPU
// EVICTED for f32/f64 arithmetic — #89/#91/#94). There is NO new FP math here.
//
// HONESTY POLICY (same as the integer encoders above): these are authored from
// the RISC-V Unprivileged ISA Spec (Chapters 11 "F" / 12 "D" + the privileged
// IEEE-754-2019 minimumNumber/maximumNumber semantics RISC-V mandates), NOT
// mirrored from the trust_ir spec encoder.
//
// FP FORMAT SELECTOR. The F/D extensions distinguish single (binary32, eb=8
// sb=24) and double (binary64, eb=11 sb=53). The instruction name carries the
// width (.s / .d); this enum makes the encoder explicit. We reuse the standard
// IEEE binary32/binary64 (eb, sb) parameters the SmtExpr FP nodes carry.
//
// Reference: RISC-V Unprivileged ISA Specification (Volume 1, Version 20191213)
//   - Chapter 11 "F" Standard Extension for Single-Precision Floating-Point
//   - Chapter 12 "D" Standard Extension for Double-Precision Floating-Point
//   - Section 11.6 "Single-Precision Floating-Point Computational Instructions"
//     (FADD.S/FSUB.S/FMUL.S/FDIV.S/FSQRT.S/FMIN.S/FMAX.S/FSGNJ*)
//   - Section 11.8 "Single-Precision Floating-Point Compare Instructions"
//     (FEQ.S/FLT.S/FLE.S — quiet/signaling, write a GPR 0/1)
//   - Section 11.7 "Single-Precision Floating-Point Conversion ..." (FCVT.W.S
//     etc.: saturating to-int with NaN -> max, the RISC-V-SPECIFIC behaviour)
// ---------------------------------------------------------------------------

/// FP format for an RV64 F/D scalar floating-point instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RiscVFpFormat {
    /// Single-precision (binary32): `.s` instructions (eb=8, sb=24).
    S,
    /// Double-precision (binary64): `.d` instructions (eb=11, sb=53).
    D,
}

impl RiscVFpFormat {
    /// Exponent bits for this format.
    pub fn eb(self) -> u32 {
        match self {
            RiscVFpFormat::S => 8,
            RiscVFpFormat::D => 11,
        }
    }
    /// Significand bits (including the implicit bit) for this format.
    pub fn sb(self) -> u32 {
        match self {
            RiscVFpFormat::S => 24,
            RiscVFpFormat::D => 53,
        }
    }
    /// Total bit width (32 or 64).
    pub fn bits(self) -> u32 {
        match self {
            RiscVFpFormat::S => 32,
            RiscVFpFormat::D => 64,
        }
    }
    /// The RISC-V CANONICAL quiet-NaN bit pattern for this format: sign 0,
    /// exponent all-ones, mantissa MSB set, all other mantissa bits 0
    /// (0x7fc0_0000 for binary32, 0x7ff8_0000_0000_0000 for binary64). RISC-V
    /// is unusual in mandating a SINGLE canonical NaN that every operation
    /// producing a NaN must generate (Section 11.3); contrast x86/ARM which
    /// propagate input NaN payloads.
    pub fn canonical_nan_bits(self) -> u64 {
        match self {
            RiscVFpFormat::S => 0x7fc0_0000,
            RiscVFpFormat::D => 0x7ff8_0000_0000_0000,
        }
    }
    /// The canonical-NaN as an FPConst leaf of this format.
    fn canonical_nan(self) -> SmtExpr {
        SmtExpr::fp_const(self.canonical_nan_bits(), self.eb(), self.sb())
    }
}

// ---------------------------------------------------------------------------
// RISC-V CANONICAL-NaN result rule (Section 11.3). RISC-V mandates that EVERY
// floating-point operation that GENERATES a NaN (an invalid-operation result, or
// the propagation of a NaN operand through arithmetic) writes the SINGLE
// CANONICAL quiet NaN (sign 0, exp all-ones, mantissa MSB set, all other
// mantissa bits 0). It does NOT propagate the input NaN's payload, and the
// result NaN is ALWAYS positive — unlike ARM (which propagates the operand
// payload via FPProcessNaNs and may produce a negative NaN) and x86 (which also
// propagates payloads). The shared fp_bitmodel arithmetic evaluator implements
// the ARM NaN-propagation convention (it is silicon-validated against the M4),
// so a NaN it produces carries an ARM payload/sign. We therefore WRAP every
// RISC-V NaN-producing FP-result encoder in a canonicalizer: if the (bit-model)
// result is a NaN, replace it with this format's canonical NaN. This models
// RISC-V EXACTLY (a FINDING surfaced by the qemu bridge: the raw bit-model NaN
// is 0x7ff8..01 / a negative 0xfff8.. while RISC-V emits the canonical 0x7ff8..),
// and it is NOT a no-op (the non-vacuity teeth prove the un-canonicalized result
// mismatches qemu on a NaN-producing input).
//
// This routes `fp_is_nan` through the integer-only bit-model classify, so no host
// FPU is introduced; it composes symbolically over the operand SmtExprs.

/// Wrap a NaN-producing FP-result `expr` of format `fmt` so a NaN result becomes
/// the RISC-V canonical quiet NaN. Non-NaN results pass through unchanged.
fn canonicalize_nan(fmt: RiscVFpFormat, expr: SmtExpr) -> SmtExpr {
    SmtExpr::ite(expr.clone().fp_is_nan(), fmt.canonical_nan(), expr)
}

// ---------------------------------------------------------------------------
// F/D: arithmetic (RNE — the default dynamic rounding mode; the trust-cg backend
// never reprograms frm away from RNE, matching the AArch64/x86 FP precedent). All
// NaN-producing arithmetic results are CANONICALIZED to the RISC-V single
// canonical NaN (Section 11.3) — see `canonicalize_nan`.
// ---------------------------------------------------------------------------

/// Encode `FADD.d rd, rs1, rs2` (and `FADD.s`) — scalar FP add.
///
/// Semantics: `rd = rs1 + rs2` under RNE, with a NaN result forced to the RISC-V
/// canonical NaN. Thin wrapper over `SmtExpr::fp_add` (which evaluates through the
/// integer-only fp_bitmodel `fadd`) + the RISC-V canonical-NaN rule. The `fmt`
/// argument selects binary32 vs binary64; the FPConst operand sorts carry the
/// width into the evaluator. Reference: RISC-V ISA, FADD.S / FADD.D + Sec 11.3.
pub fn encode_fadd(fmt: RiscVFpFormat, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    canonicalize_nan(fmt, SmtExpr::fp_add(RoundingMode::RNE, rs1, rs2))
}
/// Encode `FADD.d` (alias for `encode_fadd(RiscVFpFormat::D, ..)`).
pub fn encode_fadd_d(rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    encode_fadd(RiscVFpFormat::D, rs1, rs2)
}
/// Encode `FADD.s` (alias for `encode_fadd(RiscVFpFormat::S, ..)`).
pub fn encode_fadd_s(rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    encode_fadd(RiscVFpFormat::S, rs1, rs2)
}

/// Encode `FSUB.d rd, rs1, rs2` (and `FSUB.s`) — scalar FP subtract (RNE),
/// NaN-canonicalized. Reference: RISC-V ISA, FSUB.S / FSUB.D + Sec 11.3.
pub fn encode_fsub(fmt: RiscVFpFormat, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    canonicalize_nan(fmt, SmtExpr::fp_sub(RoundingMode::RNE, rs1, rs2))
}
/// Encode `FSUB.d`.
pub fn encode_fsub_d(rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    encode_fsub(RiscVFpFormat::D, rs1, rs2)
}
/// Encode `FSUB.s`.
pub fn encode_fsub_s(rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    encode_fsub(RiscVFpFormat::S, rs1, rs2)
}

/// Encode `FMUL.d rd, rs1, rs2` (and `FMUL.s`) — scalar FP multiply (RNE),
/// NaN-canonicalized. Reference: RISC-V ISA, FMUL.S / FMUL.D + Sec 11.3.
pub fn encode_fmul(fmt: RiscVFpFormat, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    canonicalize_nan(fmt, SmtExpr::fp_mul(RoundingMode::RNE, rs1, rs2))
}
/// Encode `FMUL.d`.
pub fn encode_fmul_d(rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    encode_fmul(RiscVFpFormat::D, rs1, rs2)
}
/// Encode `FMUL.s`.
pub fn encode_fmul_s(rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    encode_fmul(RiscVFpFormat::S, rs1, rs2)
}

/// Encode `FDIV.d rd, rs1, rs2` (and `FDIV.s`) — scalar FP divide (RNE),
/// NaN-canonicalized. Reference: RISC-V ISA, FDIV.S / FDIV.D + Sec 11.3.
pub fn encode_fdiv(fmt: RiscVFpFormat, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    canonicalize_nan(fmt, SmtExpr::fp_div(RoundingMode::RNE, rs1, rs2))
}
/// Encode `FDIV.d`.
pub fn encode_fdiv_d(rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    encode_fdiv(RiscVFpFormat::D, rs1, rs2)
}
/// Encode `FDIV.s`.
pub fn encode_fdiv_s(rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    encode_fdiv(RiscVFpFormat::S, rs1, rs2)
}

/// Encode `FSQRT.d rd, rs1` (and `FSQRT.s`) — scalar FP square root (RNE),
/// NaN-canonicalized (sqrt of a negative or NaN -> the RISC-V canonical NaN).
/// Reference: RISC-V ISA, FSQRT.S / FSQRT.D + Sec 11.3.
pub fn encode_fsqrt(fmt: RiscVFpFormat, rs1: SmtExpr) -> SmtExpr {
    canonicalize_nan(fmt, SmtExpr::fp_sqrt(RoundingMode::RNE, rs1))
}
/// Encode `FSQRT.d`.
pub fn encode_fsqrt_d(rs1: SmtExpr) -> SmtExpr {
    encode_fsqrt(RiscVFpFormat::D, rs1)
}
/// Encode `FSQRT.s`.
pub fn encode_fsqrt_s(rs1: SmtExpr) -> SmtExpr {
    encode_fsqrt(RiscVFpFormat::S, rs1)
}

// ---------------------------------------------------------------------------
// F/D: comparisons (FEQ/FLT/FLE). RISC-V writes a GPR with the 0/1 boolean
// result; we return a 1-bit bitvector per the verifier comparison convention
// (matching encode_slt et al.). These are ORDERED comparisons: the IEEE
// relations are FALSE for any unordered (NaN) pair, so a NaN operand yields 0.
// FEQ is the QUIET compare (only signaling NaN raises invalid); FLT/FLE are the
// SIGNALING compares (any NaN raises invalid) — but the VALUE result is the
// same ordered relation regardless, which is all the bridge checks (flags are
// out of scope, matching the integer SLT convention). Reference: RISC-V ISA,
// Section 11.8 (FEQ.S/FLT.S/FLE.S, "the result is written to ... rd").
// ---------------------------------------------------------------------------

/// Encode `FEQ.d rd, rs1, rs2` (and `FEQ.s`) — set rd=1 iff `rs1 == rs2`
/// (ordered; NaN operand -> 0). 1-bit result. Reference: RISC-V ISA, FEQ.
pub fn encode_feq(fmt: RiscVFpFormat, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    let _ = fmt;
    SmtExpr::ite(
        rs1.fp_eq(rs2),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    )
}
/// Encode `FEQ.d`.
pub fn encode_feq_d(rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    encode_feq(RiscVFpFormat::D, rs1, rs2)
}
/// Encode `FEQ.s`.
pub fn encode_feq_s(rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    encode_feq(RiscVFpFormat::S, rs1, rs2)
}

/// Encode `FLT.d rd, rs1, rs2` (and `FLT.s`) — set rd=1 iff `rs1 < rs2`
/// (ordered; NaN operand -> 0). 1-bit result. Reference: RISC-V ISA, FLT.
pub fn encode_flt(fmt: RiscVFpFormat, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    let _ = fmt;
    SmtExpr::ite(
        rs1.fp_lt(rs2),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    )
}
/// Encode `FLT.d`.
pub fn encode_flt_d(rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    encode_flt(RiscVFpFormat::D, rs1, rs2)
}
/// Encode `FLT.s`.
pub fn encode_flt_s(rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    encode_flt(RiscVFpFormat::S, rs1, rs2)
}

/// Encode `FLE.d rd, rs1, rs2` (and `FLE.s`) — set rd=1 iff `rs1 <= rs2`
/// (ordered; NaN operand -> 0). 1-bit result. Reference: RISC-V ISA, FLE.
pub fn encode_fle(fmt: RiscVFpFormat, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    let _ = fmt;
    SmtExpr::ite(
        rs1.fp_le(rs2),
        SmtExpr::bv_const(1, 1),
        SmtExpr::bv_const(0, 1),
    )
}
/// Encode `FLE.d`.
pub fn encode_fle_d(rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    encode_fle(RiscVFpFormat::D, rs1, rs2)
}
/// Encode `FLE.s`.
pub fn encode_fle_s(rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    encode_fle(RiscVFpFormat::S, rs1, rs2)
}

// ---------------------------------------------------------------------------
// F/D: FMIN / FMAX — the RISC-V-SPECIFIC IEEE-754-2019 minimumNumber /
// maximumNumber. This is DELIBERATELY MODELED AS RISC-V (NOT x86 MINSS, which
// returns the SECOND operand on unordered/equal; NOT ARM FMINNM IEEE-2008 minNum,
// which forces a NaN result for a SIGNALING-NaN input). The RISC-V rules
// (Section 11.6, as amended for the 2019 IEEE minimumNumber/maximumNumber):
//
//   * If BOTH inputs are NaN          -> the CANONICAL qNaN (0x7fc0../0x7ff8..).
//   * If EXACTLY ONE input is NaN     -> the OTHER (non-NaN) operand. (A
//     signaling-NaN input only raises the invalid flag; the VALUE is still the
//     number — the IEEE-2019 change vs the 2008 minNum that ARM FMINNM models.)
//   * Signed zeros are ORDERED: -0 < +0, so FMIN(-0,+0) = -0 and FMAX(-0,+0)=+0
//     (and symmetrically). Plain `fp.lt` treats -0 == +0, so we add an explicit
//     signed-zero tiebreak.
//   * Otherwise -> the numerically smaller (FMIN) / larger (FMAX) operand.
//
// We build this as an explicit ite-tree over the operand SmtExprs + the
// canonical-NaN const, so it COMPOSES symbolically (a real encoder, not a
// constant-fold) and the evaluator routes the FP classification + comparison
// through the integer-only bit-model. The branches return the ORIGINAL operand
// expressions (not a recomputed value), so a non-NaN result is bit-exact.
// ---------------------------------------------------------------------------

/// Shared min/max builder. `pick_a_when_lt` selects `a` on the strict-ordered
/// branch (FMIN: a<b -> a; FMAX: a>b -> a). `neg_zero_wins` is whether the
/// -0 operand wins the zero tiebreak (FMIN: -0; FMAX: +0).
fn encode_fminmax(fmt: RiscVFpFormat, a: SmtExpr, b: SmtExpr, is_min: bool) -> SmtExpr {
    let a_nan = a.clone().fp_is_nan();
    let b_nan = b.clone().fp_is_nan();
    let both_nan = a_nan.clone().and_expr(b_nan.clone());
    let canon = fmt.canonical_nan();

    // Numeric (no-NaN) selection with the signed-zero tiebreak.
    //   FMIN: a < b -> a ; a > b -> b ; a == b (incl +-0) -> the -0 one (or a).
    //   FMAX: a > b -> a ; a < b -> b ; a == b -> the +0 one (or a).
    // For the equal case (which fp.lt/fp.gt both report false), the only place
    // -0 vs +0 differ is the zero tiebreak: detect (a is -0 AND b is +0) etc.
    let a_is_neg_zero = a.clone().fp_is_zero().and_expr(is_sign_negative(&a));
    let b_is_neg_zero = b.clone().fp_is_zero().and_expr(is_sign_negative(&b));

    let numeric = if is_min {
        // a < b -> a ; else (a > b OR equal) -> tiebreak.
        let a_lt_b = a.clone().fp_lt(b.clone());
        // equal-zeros tiebreak: if a is -0 -> a ; if b is -0 -> b ; else b.
        let tie = SmtExpr::ite(
            a_is_neg_zero.clone(),
            a.clone(),
            SmtExpr::ite(b_is_neg_zero.clone(), b.clone(), b.clone()),
        );
        // a < b -> a ; a > b -> b ; equal -> tie.
        let a_gt_b = a.clone().fp_gt(b.clone());
        SmtExpr::ite(a_lt_b, a.clone(), SmtExpr::ite(a_gt_b, b.clone(), tie))
    } else {
        // a > b -> a ; a < b -> b ; equal -> +0 tiebreak.
        let a_gt_b = a.clone().fp_gt(b.clone());
        let a_lt_b = a.clone().fp_lt(b.clone());
        // equal-zeros tiebreak: prefer +0. If a is -0 (and equal) -> b (the +0
        // or the other -0); if b is -0 -> a ; else a.
        let tie = SmtExpr::ite(
            a_is_neg_zero,
            b.clone(),
            SmtExpr::ite(b_is_neg_zero, a.clone(), a.clone()),
        );
        SmtExpr::ite(a_gt_b, a.clone(), SmtExpr::ite(a_lt_b, b.clone(), tie))
    };

    // NaN dispatch: both NaN -> canonical; one NaN -> the other; else numeric.
    SmtExpr::ite(
        both_nan,
        canon,
        SmtExpr::ite(a_nan, b.clone(), SmtExpr::ite(b_nan, a.clone(), numeric)),
    )
}

/// True iff `x` is a NEGATIVE ZERO (-0). This helper is invoked ONLY under a
/// `fp_is_zero(x)` gate in [`encode_fminmax`], so `x` is known to be `+0` or `-0`;
/// it must distinguish the two.
///
/// `fp.lt(x, +0)` is FALSE for -0 (the bit-model, like IEEE, treats -0 == +0
/// under the ordered relations), so it cannot detect a negative zero. The robust,
/// evaluator-supported signal is the DIVISION sign trick: `+Inf / x` is `+Inf`
/// for `x = +0` and `-Inf` for `x = -0` (Inf/0 = Inf with sign = dividend.sign
/// XOR divisor.sign — the integer-only bit-model `fdiv` implements this exactly,
/// unlike `0 * Inf` which is NaN). So `(+Inf / x) < +0` is true EXACTLY for -0.
fn is_sign_negative(x: &SmtExpr) -> SmtExpr {
    let (eb, sb) = match x.sort() {
        crate::smt::SmtSort::FloatingPoint(eb, sb) => (eb, sb),
        _ => (11, 53),
    };
    let pos_inf = SmtExpr::fp_const(inf_bits(eb, sb, false), eb, sb);
    let zero = SmtExpr::fp_const(0, eb, sb);
    SmtExpr::fp_div(RoundingMode::RNE, pos_inf, x.clone()).fp_lt(zero)
}

/// Raw +/-Inf bit pattern for an (eb, sb) format.
fn inf_bits(eb: u32, sb: u32, neg: bool) -> u64 {
    let total = eb + sb;
    let mant = sb - 1;
    let exp_all_ones = ((1u64 << eb) - 1) << mant;
    let sign = if neg { 1u64 << (total - 1) } else { 0 };
    exp_all_ones | sign
}

/// Encode `FMIN.d rd, rs1, rs2` (and `FMIN.s`) — RISC-V IEEE-2019
/// minimumNumber. Reference: RISC-V ISA, Section 11.6 (FMIN.S/FMIN.D).
pub fn encode_fmin(fmt: RiscVFpFormat, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    encode_fminmax(fmt, rs1, rs2, true)
}
/// Encode `FMIN.d`.
pub fn encode_fmin_d(rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    encode_fmin(RiscVFpFormat::D, rs1, rs2)
}
/// Encode `FMIN.s`.
pub fn encode_fmin_s(rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    encode_fmin(RiscVFpFormat::S, rs1, rs2)
}

/// Encode `FMAX.d rd, rs1, rs2` (and `FMAX.s`) — RISC-V IEEE-2019
/// maximumNumber. Reference: RISC-V ISA, Section 11.6 (FMAX.S/FMAX.D).
pub fn encode_fmax(fmt: RiscVFpFormat, rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    encode_fminmax(fmt, rs1, rs2, false)
}
/// Encode `FMAX.d`.
pub fn encode_fmax_d(rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    encode_fmax(RiscVFpFormat::D, rs1, rs2)
}
/// Encode `FMAX.s`.
pub fn encode_fmax_s(rs1: SmtExpr, rs2: SmtExpr) -> SmtExpr {
    encode_fmax(RiscVFpFormat::S, rs1, rs2)
}

// ---------------------------------------------------------------------------
// F/D: sign-injection (FSGNJ / FSGNJN / FSGNJX). These take the magnitude
// (exponent + mantissa) of rs1 and a sign from rs2 (FSGNJ: rs2's sign; FSGNJN:
// the NEGATION of rs2's sign; FSGNJX: rs1's sign XOR rs2's sign). They are PURE
// BIT ops (no rounding, no exceptions, NaN passes through bit-for-bit), so we
// model them at the bitvector level via the FP value's sign bit. The encoder
// takes the raw rs1/rs2 bit patterns as `width`-bit bitvectors and returns the
// `width`-bit result; the caller bitcasts the FP operands to bitvectors.
// Reference: RISC-V ISA, Section 11.6 (FSGNJ.S/FSGNJN.S/FSGNJX.S).
// ---------------------------------------------------------------------------

/// Encode `FSGNJ.<fmt> rd, rs1, rs2` over RAW bitvector operands: rd = rs1 with
/// its sign bit replaced by rs2's sign bit.
pub fn encode_fsgnj_bits(fmt: RiscVFpFormat, rs1_bits: SmtExpr, rs2_bits: SmtExpr) -> SmtExpr {
    let w = fmt.bits();
    let sign = SmtExpr::bv_const(1u64 << (w - 1), w);
    let mag_mask = SmtExpr::bv_const(mag_mask_val(w), w);
    rs1_bits.bvand(mag_mask).bvor(rs2_bits.bvand(sign))
}
/// Encode `FSGNJN.<fmt>`: rd = rs1's magnitude | (NOT rs2's sign).
pub fn encode_fsgnjn_bits(fmt: RiscVFpFormat, rs1_bits: SmtExpr, rs2_bits: SmtExpr) -> SmtExpr {
    let w = fmt.bits();
    let sign = SmtExpr::bv_const(1u64 << (w - 1), w);
    let mag_mask = SmtExpr::bv_const(mag_mask_val(w), w);
    let neg_sign = rs2_bits.bvand(sign.clone()).bvxor(sign);
    rs1_bits.bvand(mag_mask).bvor(neg_sign)
}
/// Encode `FSGNJX.<fmt>`: rd = rs1's magnitude | (rs1's sign XOR rs2's sign).
pub fn encode_fsgnjx_bits(fmt: RiscVFpFormat, rs1_bits: SmtExpr, rs2_bits: SmtExpr) -> SmtExpr {
    let w = fmt.bits();
    let sign = SmtExpr::bv_const(1u64 << (w - 1), w);
    let mag_mask = SmtExpr::bv_const(mag_mask_val(w), w);
    let xor_sign = rs1_bits
        .clone()
        .bvand(sign.clone())
        .bvxor(rs2_bits.bvand(sign));
    rs1_bits.bvand(mag_mask).bvor(xor_sign)
}

/// Magnitude mask (all bits EXCEPT the sign bit) for a `w`-bit FP word.
fn mag_mask_val(w: u32) -> u64 {
    if w >= 64 {
        u64::MAX >> 1
    } else {
        (1u64 << (w - 1)) - 1
    }
}

// ---------------------------------------------------------------------------
// F/D: conversions to integer (FCVT.W.D / FCVT.WU.D / FCVT.L.D / FCVT.LU.D and
// the .S forms). RISC-V f->int is the RISC-V-SPECIFIC SATURATING conversion:
//
//   * In-range finite values: round per `rm` (RTZ for the truncating C-cast
//     lowerings; we model RTZ here, the trust-cg FcvtToInt lowering's mode), then
//     the integral value (Section 11.7).
//   * OUT-OF-RANGE / +-Inf / NaN: SATURATE. RISC-V is SPECIFIC (Table 11.4):
//       - signed   : +overflow/+Inf -> 2^(w-1)-1 (INT_MAX);
//                     -overflow/-Inf -> -2^(w-1) (INT_MIN);
//                     NaN            -> 2^(w-1)-1 (INT_MAX) — NOT 0 (x86/ARM-ish).
//       - unsigned : +overflow/+Inf -> 2^w-1 (UINT_MAX);
//                     negative/-Inf  -> 0;
//                     NaN            -> 2^w-1 (UINT_MAX).
//
// This DIFFERS from trust-cg's shared FPToSBv/FPToUBv evaluator (which maps
// NaN -> 0, the wasm trunc_sat / AArch64 FCVTZS / Rust-`as` convention). We
// therefore wrap the shared converter in an explicit RISC-V NaN-fixup: if the
// source is NaN, force the RISC-V NaN result (INT_MAX signed / UINT_MAX
// unsigned); otherwise the saturating converter already matches RISC-V (RISC-V
// and AArch64/wasm agree on +-overflow saturation — only NaN differs).
//
// Result is a `int_width`-bit bitvector; for FCVT.W.* (32-bit) on RV64 the
// architectural result is sign-extended to 64, but the bridge compares the low
// 32 (the width-32 encoder result), matching the integer W-form convention.
// Reference: RISC-V ISA, Section 11.7, Table 11.4 ("Domain ... and rounding").
// ---------------------------------------------------------------------------

/// Encode `FCVT.W.<fmt>` / `FCVT.L.<fmt>` — FP to SIGNED int, RISC-V saturating
/// with NaN -> INT_MAX. `int_width` is 32 (W) or 64 (L). `rs1` is the FP value.
pub fn encode_fcvt_to_int_signed(int_width: u32, rs1: SmtExpr) -> SmtExpr {
    // The shared saturating signed converter (RTZ): in-range exact, +-overflow
    // saturates to INT_MAX/INT_MIN, but NaN -> 0 (the wasm/ARM convention).
    let sat = SmtExpr::fp_to_sbv(RoundingMode::RTZ, rs1.clone(), int_width);
    // RISC-V NaN fixup: NaN -> INT_MAX (2^(w-1) - 1).
    let int_max = SmtExpr::bv_const(signed_max(int_width), int_width);
    SmtExpr::ite(rs1.fp_is_nan(), int_max, sat)
}

/// Encode `FCVT.WU.<fmt>` / `FCVT.LU.<fmt>` — FP to UNSIGNED int, RISC-V
/// saturating with NaN -> UINT_MAX. `int_width` is 32 (WU) or 64 (LU).
pub fn encode_fcvt_to_int_unsigned(int_width: u32, rs1: SmtExpr) -> SmtExpr {
    let sat = SmtExpr::fp_to_ubv(RoundingMode::RTZ, rs1.clone(), int_width);
    // RISC-V NaN fixup: NaN -> UINT_MAX (all ones).
    let uint_max = SmtExpr::bv_const(crate::smt::mask(u64::MAX, int_width), int_width);
    SmtExpr::ite(rs1.fp_is_nan(), uint_max, sat)
}

/// Signed-int maximum (2^(w-1) - 1) as a u64.
fn signed_max(w: u32) -> u64 {
    if w >= 64 {
        i64::MAX as u64
    } else {
        (1u64 << (w - 1)) - 1
    }
}

// ---------------------------------------------------------------------------
// F/D: conversions FROM integer (FCVT.D.W / FCVT.D.WU / FCVT.D.L / FCVT.D.LU and
// the .S forms) and between FP formats (FCVT.S.D narrow / FCVT.D.S widen). Thin
// wrappers over BvToFP / FPToFP (RNE). int->FP: the source is interpreted signed
// (W/L) or unsigned (WU/LU — the caller zero-extends the operand, matching the
// BvToFP signed-interpretation contract used by x86 CVTSI2SD/AArch64 SCVTF).
// ---------------------------------------------------------------------------

/// Encode `FCVT.<fmt>.W` / `FCVT.<fmt>.L` — SIGNED int to FP (RNE). `src` is the
/// `src_width`-bit signed integer bitvector.
pub fn encode_fcvt_from_int_signed(fmt: RiscVFpFormat, src: SmtExpr) -> SmtExpr {
    SmtExpr::bv_to_fp(RoundingMode::RNE, src, fmt.eb(), fmt.sb())
}

/// Encode `FCVT.S.D` (narrow) / `FCVT.D.S` (widen) — FP-format conversion (RNE),
/// NaN-canonicalized (a NaN source -> the destination format's canonical NaN,
/// RISC-V Section 11.3). `dst` is the target format.
pub fn encode_fcvt_fp_to_fp(dst: RiscVFpFormat, src: SmtExpr) -> SmtExpr {
    canonicalize_nan(
        dst,
        SmtExpr::fp_to_fp(RoundingMode::RNE, src, dst.eb(), dst.sb()),
    )
}

// ===========================================================================
// Tests (inline eval, mirroring aarch64_semantics.rs)
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::EvalResult;
    use std::collections::HashMap;

    fn env(pairs: &[(&str, u64)]) -> HashMap<String, u64> {
        pairs.iter().map(|(k, v)| (k.to_string(), *v)).collect()
    }

    fn v64(name: &str) -> SmtExpr {
        SmtExpr::var(name, 64)
    }

    // ---- arithmetic ----

    #[test]
    fn test_add() {
        let expr = encode_add(RiscVOperandSize::S64, v64("a"), v64("b"));
        assert_eq!(expr.eval(&env(&[("a", 3), ("b", 4)])), EvalResult::Bv(7));
    }

    #[test]
    fn test_add_wraps() {
        let expr = encode_add(RiscVOperandSize::S64, v64("a"), v64("b"));
        assert_eq!(
            expr.eval(&env(&[("a", u64::MAX), ("b", 1)])),
            EvalResult::Bv(0)
        );
    }

    #[test]
    fn test_sub() {
        let expr = encode_sub(RiscVOperandSize::S64, v64("a"), v64("b"));
        assert_eq!(expr.eval(&env(&[("a", 10), ("b", 3)])), EvalResult::Bv(7));
    }

    #[test]
    fn test_mul_low_bits() {
        let expr = encode_mul(RiscVOperandSize::S64, v64("a"), v64("b"));
        // 2^63 * 2 = 2^64 -> low 64 bits = 0.
        assert_eq!(
            expr.eval(&env(&[("a", 1u64 << 63), ("b", 2)])),
            EvalResult::Bv(0)
        );
        assert_eq!(expr.eval(&env(&[("a", 6), ("b", 7)])), EvalResult::Bv(42));
    }

    // ---- bitwise ----

    #[test]
    fn test_and() {
        let expr = encode_and(RiscVOperandSize::S64, v64("a"), v64("b"));
        assert_eq!(
            expr.eval(&env(&[("a", 0xFF00_FF00), ("b", 0x0F0F_0F0F)])),
            EvalResult::Bv(0x0F00_0F00)
        );
    }

    #[test]
    fn test_or() {
        let expr = encode_or(RiscVOperandSize::S64, v64("a"), v64("b"));
        assert_eq!(
            expr.eval(&env(&[("a", 0xFF00_0000), ("b", 0x00FF_0000)])),
            EvalResult::Bv(0xFFFF_0000)
        );
    }

    #[test]
    fn test_xor() {
        let expr = encode_xor(RiscVOperandSize::S64, v64("a"), v64("b"));
        assert_eq!(
            expr.eval(&env(&[("a", 0xAAAA_AAAA), ("b", 0x5555_5555)])),
            EvalResult::Bv(0xFFFF_FFFF)
        );
    }

    // ---- shifts ----

    #[test]
    fn test_sll() {
        let expr = encode_sll(RiscVOperandSize::S64, v64("a"), v64("b"));
        assert_eq!(expr.eval(&env(&[("a", 1), ("b", 4)])), EvalResult::Bv(16));
    }

    #[test]
    fn test_srl_logical() {
        let expr = encode_srl(RiscVOperandSize::S64, v64("a"), v64("b"));
        assert_eq!(
            expr.eval(&env(&[("a", 0x8000_0000_0000_0000), ("b", 4)])),
            EvalResult::Bv(0x0800_0000_0000_0000)
        );
    }

    #[test]
    fn test_sra_arithmetic() {
        let expr = encode_sra(RiscVOperandSize::S64, v64("a"), v64("b"));
        // arithmetic shift right of a negative value sign-extends.
        assert_eq!(
            expr.eval(&env(&[("a", 0x8000_0000_0000_0000), ("b", 4)])),
            EvalResult::Bv(0xF800_0000_0000_0000)
        );
    }

    // ---- masked shifts (the reconstruction machine side, #57 / #63) ----

    #[test]
    fn test_sll_masked_in_range_matches_unmasked() {
        // In range (amount < width) the mask is the identity: same as encode_sll.
        let masked = encode_sll_masked(RiscVOperandSize::S64, v64("a"), v64("b"));
        assert_eq!(masked.eval(&env(&[("a", 1), ("b", 4)])), EvalResult::Bv(16));
    }

    #[test]
    fn test_sll_masked_wraps_amount_mod_64() {
        // At XLEN=64 the amount is masked & 0x3F: a shift by 64 masks to 0 (identity)
        // on hardware, NOT the SMT clamp-to-0 of the unmasked bvshl.
        let masked = encode_sll_masked(RiscVOperandSize::S64, v64("a"), v64("b"));
        assert_eq!(masked.eval(&env(&[("a", 7), ("b", 64)])), EvalResult::Bv(7));
        // shift by 65 masks to 1.
        assert_eq!(masked.eval(&env(&[("a", 1), ("b", 65)])), EvalResult::Bv(2));
    }

    #[test]
    fn test_srl_masked_logical() {
        let masked = encode_srl_masked(RiscVOperandSize::S64, v64("a"), v64("b"));
        assert_eq!(
            masked.eval(&env(&[("a", 0x8000_0000_0000_0000), ("b", 4)])),
            EvalResult::Bv(0x0800_0000_0000_0000)
        );
    }

    #[test]
    fn test_sra_masked_arithmetic() {
        let masked = encode_sra_masked(RiscVOperandSize::S64, v64("a"), v64("b"));
        assert_eq!(
            masked.eval(&env(&[("a", 0x8000_0000_0000_0000), ("b", 4)])),
            EvalResult::Bv(0xF800_0000_0000_0000)
        );
    }

    #[test]
    fn test_slli_const() {
        let expr = encode_slli(RiscVOperandSize::S64, v64("a"), 3);
        assert_eq!(expr.eval(&env(&[("a", 5)])), EvalResult::Bv(40));
    }

    #[test]
    fn test_srli_const() {
        let expr = encode_srli(RiscVOperandSize::S64, v64("a"), 4);
        assert_eq!(expr.eval(&env(&[("a", 0xF0)])), EvalResult::Bv(0x0F));
    }

    // ---- comparisons (1-bit result) ----

    #[test]
    fn test_slt_signed_true() {
        let expr = encode_slt(RiscVOperandSize::S64, v64("a"), v64("b"));
        // -1 <s 0
        assert_eq!(
            expr.eval(&env(&[("a", u64::MAX), ("b", 0)])),
            EvalResult::Bv(1)
        );
    }

    #[test]
    fn test_slt_signed_false() {
        let expr = encode_slt(RiscVOperandSize::S64, v64("a"), v64("b"));
        // 0 <s -1 is false
        assert_eq!(
            expr.eval(&env(&[("a", 0), ("b", u64::MAX)])),
            EvalResult::Bv(0)
        );
    }

    #[test]
    fn test_sltu_unsigned_true() {
        let expr = encode_sltu(RiscVOperandSize::S64, v64("a"), v64("b"));
        assert_eq!(expr.eval(&env(&[("a", 3), ("b", 10)])), EvalResult::Bv(1));
    }

    #[test]
    fn test_sltu_snez_idiom() {
        // SLTU rd, x0, rs2 == (rs2 != 0)
        let zero = SmtExpr::bv_const(0, 64);
        let expr = encode_sltu(RiscVOperandSize::S64, zero, v64("b"));
        assert_eq!(expr.eval(&env(&[("b", 0)])), EvalResult::Bv(0));
        assert_eq!(expr.eval(&env(&[("b", 7)])), EvalResult::Bv(1));
    }

    // ---- immediates / idiom helpers ----

    #[test]
    fn test_addi() {
        let imm = SmtExpr::bv_const(100, 64);
        let expr = encode_addi(RiscVOperandSize::S64, v64("a"), imm);
        assert_eq!(expr.eval(&env(&[("a", 23)])), EvalResult::Bv(123));
    }

    #[test]
    fn test_addi_li_idiom() {
        // ADDI rd, x0, imm == imm (load immediate)
        let zero = SmtExpr::bv_const(0, 64);
        let imm = SmtExpr::bv_const(0xABCD, 64);
        let expr = encode_addi(RiscVOperandSize::S64, zero, imm);
        assert_eq!(expr.eval(&env(&[])), EvalResult::Bv(0xABCD));
    }

    #[test]
    fn test_xori_bool_invert() {
        // XORI on a 1-bit value with constant 1 flips the bit (boolean NOT).
        let bit = SmtExpr::var("p", 1);
        let one = SmtExpr::bv_const(1, 1);
        let expr = encode_xori(RiscVOperandSize::S64, bit, one);
        assert_eq!(expr.eval(&env(&[("p", 0)])), EvalResult::Bv(1));
        assert_eq!(expr.eval(&env(&[("p", 1)])), EvalResult::Bv(0));
    }

    #[test]
    fn test_sltiu_seqz_idiom() {
        // SLTIU rd, rs1, 1 == (rs1 == 0)
        let one = SmtExpr::bv_const(1, 64);
        let expr = encode_sltiu(RiscVOperandSize::S64, v64("a"), one);
        assert_eq!(expr.eval(&env(&[("a", 0)])), EvalResult::Bv(1));
        assert_eq!(expr.eval(&env(&[("a", 5)])), EvalResult::Bv(0));
    }

    // ---- composed idioms (the real emitted sequences) ----

    #[test]
    fn test_eq_idiom_via_sltiu_sub() {
        // Icmp Eq(a, b) == SLTIU(SUB(a, b), 1)
        let a = v64("a");
        let b = v64("b");
        let t = encode_sub(RiscVOperandSize::S64, a, b);
        let one = SmtExpr::bv_const(1, 64);
        let expr = encode_sltiu(RiscVOperandSize::S64, t, one);
        assert_eq!(expr.eval(&env(&[("a", 9), ("b", 9)])), EvalResult::Bv(1));
        assert_eq!(expr.eval(&env(&[("a", 9), ("b", 8)])), EvalResult::Bv(0));
    }

    #[test]
    fn test_ne_idiom_via_sltu_sub() {
        // Icmp Ne(a, b) == SLTU(0, SUB(a, b))
        let a = v64("a");
        let b = v64("b");
        let t = encode_sub(RiscVOperandSize::S64, a, b);
        let zero = SmtExpr::bv_const(0, 64);
        let expr = encode_sltu(RiscVOperandSize::S64, zero, t);
        assert_eq!(expr.eval(&env(&[("a", 9), ("b", 9)])), EvalResult::Bv(0));
        assert_eq!(expr.eval(&env(&[("a", 9), ("b", 8)])), EvalResult::Bv(1));
    }

    #[test]
    fn test_sge_idiom_via_xori_slt() {
        // Icmp Sge(a, b) == XORI(SLT(a, b), 1) (boolean inversion of slt)
        let a = v64("a");
        let b = v64("b");
        let slt = encode_slt(RiscVOperandSize::S64, a, b);
        let one = SmtExpr::bv_const(1, 1);
        let expr = encode_xori(RiscVOperandSize::S64, slt, one);
        // 5 >= 3 -> 1
        assert_eq!(expr.eval(&env(&[("a", 5), ("b", 3)])), EvalResult::Bv(1));
        // 3 >= 5 -> 0
        assert_eq!(expr.eval(&env(&[("a", 3), ("b", 5)])), EvalResult::Bv(0));
        // 5 >= 5 -> 1
        assert_eq!(expr.eval(&env(&[("a", 5), ("b", 5)])), EvalResult::Bv(1));
    }

    #[test]
    fn test_uge_idiom_via_xori_sltu() {
        // Icmp Uge(a, b) == XORI(SLTU(a, b), 1)
        let a = v64("a");
        let b = v64("b");
        let sltu = encode_sltu(RiscVOperandSize::S64, a, b);
        let one = SmtExpr::bv_const(1, 1);
        let expr = encode_xori(RiscVOperandSize::S64, sltu, one);
        assert_eq!(expr.eval(&env(&[("a", 10), ("b", 3)])), EvalResult::Bv(1));
        assert_eq!(expr.eval(&env(&[("a", 3), ("b", 10)])), EvalResult::Bv(0));
    }

    #[test]
    fn test_operand_size_bits() {
        assert_eq!(riscv_operand_size_bits(RiscVOperandSize::S32), 32);
        assert_eq!(riscv_operand_size_bits(RiscVOperandSize::S64), 64);
    }

    // ===================================================================
    // F/D scalar floating-point encoders (binary64 + binary32).
    // ===================================================================

    fn fp64(v: f64) -> SmtExpr {
        SmtExpr::fp_const(v.to_bits(), 11, 53)
    }
    fn fp32(v: f32) -> SmtExpr {
        SmtExpr::fp_const(v.to_bits() as u64, 8, 24)
    }
    fn eval_bits64(e: &SmtExpr) -> u64 {
        match e.eval(&env(&[])) {
            EvalResult::Float(f) => f.to_bits(),
            other => panic!("expected Float, got {other:?}"),
        }
    }
    fn eval_bits32(e: &SmtExpr) -> u64 {
        match e.eval(&env(&[])) {
            EvalResult::Float(f) => crate::fp_bitmodel::fcvt_narrow(f.to_bits()),
            other => panic!("expected Float, got {other:?}"),
        }
    }
    fn eval_bv(e: &SmtExpr) -> u64 {
        match e.eval(&env(&[])) {
            EvalResult::Bv(v) => v,
            EvalResult::Bv128(v) => v as u64,
            other => panic!("expected Bv, got {other:?}"),
        }
    }

    #[test]
    fn test_fadd_d() {
        let e = encode_fadd_d(fp64(1.5), fp64(2.25));
        assert_eq!(eval_bits64(&e), (3.75f64).to_bits());
    }

    #[test]
    fn test_fsub_fmul_fdiv_fsqrt_d() {
        assert_eq!(
            eval_bits64(&encode_fsub_d(fp64(5.0), fp64(2.0))),
            (3.0f64).to_bits()
        );
        assert_eq!(
            eval_bits64(&encode_fmul_d(fp64(3.0), fp64(4.0))),
            (12.0f64).to_bits()
        );
        assert_eq!(
            eval_bits64(&encode_fdiv_d(fp64(9.0), fp64(2.0))),
            (4.5f64).to_bits()
        );
        assert_eq!(eval_bits64(&encode_fsqrt_d(fp64(16.0))), (4.0f64).to_bits());
    }

    #[test]
    fn test_fadd_fmul_s() {
        assert_eq!(
            eval_bits32(&encode_fadd_s(fp32(1.5), fp32(2.25))),
            (3.75f32).to_bits() as u64
        );
        assert_eq!(
            eval_bits32(&encode_fmul_s(fp32(3.0), fp32(4.0))),
            (12.0f32).to_bits() as u64
        );
    }

    #[test]
    fn test_fcmp_d() {
        // ordered comparisons; NaN -> 0.
        assert_eq!(eval_bv(&encode_feq_d(fp64(1.0), fp64(1.0))), 1);
        assert_eq!(eval_bv(&encode_feq_d(fp64(1.0), fp64(2.0))), 0);
        assert_eq!(eval_bv(&encode_flt_d(fp64(1.0), fp64(2.0))), 1);
        assert_eq!(eval_bv(&encode_flt_d(fp64(2.0), fp64(1.0))), 0);
        assert_eq!(eval_bv(&encode_fle_d(fp64(1.0), fp64(1.0))), 1);
        // NaN operand -> all ordered relations false.
        let nan = SmtExpr::fp_const(0x7ff8_0000_0000_0000, 11, 53);
        assert_eq!(eval_bv(&encode_feq_d(nan.clone(), fp64(1.0))), 0);
        assert_eq!(eval_bv(&encode_flt_d(nan.clone(), fp64(1.0))), 0);
        assert_eq!(eval_bv(&encode_fle_d(nan, fp64(1.0))), 0);
    }

    #[test]
    fn test_fmin_fmax_d_numeric() {
        assert_eq!(
            eval_bits64(&encode_fmin_d(fp64(1.0), fp64(2.0))),
            (1.0f64).to_bits()
        );
        assert_eq!(
            eval_bits64(&encode_fmin_d(fp64(2.0), fp64(1.0))),
            (1.0f64).to_bits()
        );
        assert_eq!(
            eval_bits64(&encode_fmax_d(fp64(1.0), fp64(2.0))),
            (2.0f64).to_bits()
        );
        assert_eq!(
            eval_bits64(&encode_fmax_d(fp64(2.0), fp64(1.0))),
            (2.0f64).to_bits()
        );
    }

    #[test]
    fn test_fmin_fmax_d_nan_riscv_2019() {
        let qnan = SmtExpr::fp_const(0x7ff8_0000_0000_0000, 11, 53);
        // RISC-V IEEE-2019 minimumNumber: a lone NaN -> the NUMBER (not NaN, unlike
        // x86 MINSD which would return the second operand).
        assert_eq!(
            eval_bits64(&encode_fmin_d(fp64(1.0), qnan.clone())),
            (1.0f64).to_bits(),
            "FMIN(1.0, NaN) must be 1.0 (RISC-V minimumNumber returns the number)"
        );
        assert_eq!(
            eval_bits64(&encode_fmin_d(qnan.clone(), fp64(1.0))),
            (1.0f64).to_bits()
        );
        assert_eq!(
            eval_bits64(&encode_fmax_d(qnan.clone(), fp64(1.0))),
            (1.0f64).to_bits()
        );
        // Both NaN -> CANONICAL qNaN 0x7ff8..
        assert_eq!(
            eval_bits64(&encode_fmin_d(qnan.clone(), qnan.clone())),
            0x7ff8_0000_0000_0000,
            "FMIN(NaN, NaN) must be the RISC-V canonical qNaN"
        );
        // sNaN input: RISC-V 2019 STILL returns the number (only raises invalid).
        let snan = SmtExpr::fp_const(0x7ff0_0000_0000_0001, 11, 53);
        assert_eq!(
            eval_bits64(&encode_fmin_d(snan, fp64(1.0))),
            (1.0f64).to_bits(),
            "FMIN(sNaN, 1.0) must be 1.0 (RISC-V 2019 minimumNumber; NOT ARM FMINNM)"
        );
    }

    #[test]
    fn test_fmin_fmax_d_signed_zero() {
        let pos0 = fp64(0.0);
        let neg0 = SmtExpr::fp_const(0x8000_0000_0000_0000, 11, 53);
        // -0 < +0 ordering: FMIN(-0,+0) = -0, FMAX(-0,+0) = +0.
        assert_eq!(
            eval_bits64(&encode_fmin_d(neg0.clone(), pos0.clone())),
            0x8000_0000_0000_0000,
            "FMIN(-0, +0) must be -0 (RISC-V: -0 < +0)"
        );
        assert_eq!(
            eval_bits64(&encode_fmin_d(pos0.clone(), neg0.clone())),
            0x8000_0000_0000_0000
        );
        assert_eq!(eval_bits64(&encode_fmax_d(neg0.clone(), pos0.clone())), 0);
        assert_eq!(eval_bits64(&encode_fmax_d(pos0, neg0)), 0);
    }

    #[test]
    fn test_fsgnj_bits() {
        // FSGNJ.d: take magnitude of rs1, sign of rs2.
        let a = SmtExpr::bv_const((1.0f64).to_bits(), 64);
        let b_neg = SmtExpr::bv_const((-2.0f64).to_bits(), 64);
        assert_eq!(
            eval_bv(&encode_fsgnj_bits(
                RiscVFpFormat::D,
                a.clone(),
                b_neg.clone()
            )),
            (-1.0f64).to_bits()
        );
        // FSGNJN.d: sign = NOT rs2's sign -> rs2 negative -> result positive.
        assert_eq!(
            eval_bv(&encode_fsgnjn_bits(
                RiscVFpFormat::D,
                a.clone(),
                b_neg.clone()
            )),
            (1.0f64).to_bits()
        );
        // FSGNJX.d: sign = rs1.sign XOR rs2.sign. rs1=+1, rs2=-2 -> neg.
        assert_eq!(
            eval_bv(&encode_fsgnjx_bits(RiscVFpFormat::D, a, b_neg)),
            (-1.0f64).to_bits()
        );
    }

    #[test]
    fn test_fcvt_to_int_riscv_saturation() {
        // In-range: FCVT.W.D(123.0) = 123.
        assert_eq!(eval_bv(&encode_fcvt_to_int_signed(32, fp64(123.0))), 123);
        // Negative: FCVT.W.D(-5.7) RTZ -> -5.
        assert_eq!(
            eval_bv(&encode_fcvt_to_int_signed(32, fp64(-5.7))) & 0xFFFF_FFFF,
            (-5i32) as u32 as u64
        );
        // +Inf -> INT_MAX (saturate).
        let pinf = SmtExpr::fp_const(0x7ff0_0000_0000_0000, 11, 53);
        assert_eq!(
            eval_bv(&encode_fcvt_to_int_signed(32, pinf)) & 0xFFFF_FFFF,
            0x7fff_ffff
        );
        // NaN -> INT_MAX (RISC-V-SPECIFIC; wasm/ARM/Rust map NaN -> 0).
        let nan = SmtExpr::fp_const(0x7ff8_0000_0000_0000, 11, 53);
        assert_eq!(
            eval_bv(&encode_fcvt_to_int_signed(32, nan.clone())) & 0xFFFF_FFFF,
            0x7fff_ffff,
            "RISC-V FCVT.W.D(NaN) must be INT_MAX 2^31-1 (NOT 0)"
        );
        // FCVT.WU.D(NaN) -> UINT_MAX.
        assert_eq!(
            eval_bv(&encode_fcvt_to_int_unsigned(32, nan)) & 0xFFFF_FFFF,
            0xFFFF_FFFF,
            "RISC-V FCVT.WU.D(NaN) must be UINT_MAX (NOT 0)"
        );
    }

    #[test]
    fn test_fcvt_from_int_and_fp() {
        // FCVT.D.W(7) = 7.0
        let src = SmtExpr::bv_const(7, 32);
        assert_eq!(
            eval_bits64(&encode_fcvt_from_int_signed(RiscVFpFormat::D, src)),
            (7.0f64).to_bits()
        );
        // FCVT.S.D(1.5) narrow.
        assert_eq!(
            eval_bits32(&encode_fcvt_fp_to_fp(RiscVFpFormat::S, fp64(1.5))),
            (1.5f32).to_bits() as u64
        );
    }
}
