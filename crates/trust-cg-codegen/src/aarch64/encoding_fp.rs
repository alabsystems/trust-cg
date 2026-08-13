// trust-cg-codegen/aarch64/encoding_fp.rs - AArch64 floating-point instruction encoding
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! AArch64 floating-point instruction encoding.
//!
//! Implements encoding for AArch64 FP instruction formats:
//! - FP data-processing 2-source (FADD, FSUB, FMUL, FDIV)
//! - FP data-processing 1-source (FMOV reg, FABS, FNEG, FSQRT)
//! - FP compare (FCMP, FCMPE, with register or zero)
//! - FP ↔ integer conversion (FCVTZS, SCVTF, FMOV between GP and FP)
//!
//! Encoding formats follow the ARM Architecture Reference Manual (DDI 0487).

use thiserror::Error;

/// Errors produced during floating-point instruction encoding.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum FpEncodeError {
    #[error("register index {reg} out of range (max {max})")]
    RegisterOutOfRange { reg: u8, max: u8 },
}

// ---------------------------------------------------------------------------
// Enums
// ---------------------------------------------------------------------------

/// Floating-point data size (maps to `ftype` field).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FpSize {
    /// Single precision (32-bit) — ftype = 0b00
    Single = 0b00,
    /// Double precision (64-bit) — ftype = 0b01
    Double = 0b01,
    /// Half precision (16-bit) — ftype = 0b11
    Half = 0b11,
}

/// FP arithmetic operation (2-source data-processing).
///
/// Maps to the 4-bit `opcode` field in bits [15:12].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FpArithOp {
    /// FMUL — opcode = 0b0000
    Mul = 0b0000,
    /// FDIV — opcode = 0b0001
    Div = 0b0001,
    /// FADD — opcode = 0b0010
    Add = 0b0010,
    /// FSUB — opcode = 0b0011
    Sub = 0b0011,
    /// FMAXNM — IEEE maxNum (Rust `f{32,64}::max`). opcode = 0b0110
    Maxnm = 0b0110,
    /// FMINNM — IEEE minNum (Rust `f{32,64}::min`). opcode = 0b0111
    Minnm = 0b0111,
}

/// FP fused multiply-add operation (3-source data-processing).
///
/// Selects the (o1, o0) pair in bits [21] and [15] of the FP 3-source encoding.
/// Semantics (Rd, Rn, Rm, Ra): FMADD `Ra + Rn*Rm`, FMSUB `Ra - Rn*Rm`,
/// FNMADD `-(Ra + Rn*Rm)`, FNMSUB `-Ra + Rn*Rm` — each with a SINGLE rounding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FpMaddOp {
    /// FMADD — o1=0, o0=0 — `Rd = Ra + Rn*Rm`.
    Madd,
    /// FMSUB — o1=0, o0=1 — `Rd = Ra - Rn*Rm`.
    Msub,
    /// FNMADD — o1=1, o0=0 — `Rd = -(Ra + Rn*Rm)`.
    Nmadd,
    /// FNMSUB — o1=1, o0=1 — `Rd = -Ra + Rn*Rm`.
    Nmsub,
}

impl FpMaddOp {
    /// Returns (o1, o0) for bits [21] and [15].
    #[inline]
    fn o1_o0(self) -> (u32, u32) {
        match self {
            FpMaddOp::Madd => (0, 0),
            FpMaddOp::Msub => (0, 1),
            FpMaddOp::Nmadd => (1, 0),
            FpMaddOp::Nmsub => (1, 1),
        }
    }
}

/// FP compare operation.
///
/// Maps to the 5-bit `opc` field in bits [4:0] of FCMP encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FpCmpOp {
    /// FCMP (register) — opc = 0b00000
    Cmp = 0b00000,
    /// FCMP with zero — opc = 0b01000
    CmpZero = 0b01000,
    /// FCMPE (signalling, register) — opc = 0b10000
    Cmpe = 0b10000,
    /// FCMPE with zero — opc = 0b11000
    CmpeZero = 0b11000,
}

/// FP ↔ integer conversion operation.
///
/// Each variant encodes a (rmode, opcode) pair for bits [20:19] and [18:16].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FpConvOp {
    /// FCVTZS — FP to signed integer, round toward zero.
    /// rmode = 0b11, opcode = 0b000
    FcvtzsToInt,
    /// FCVTZU — FP to unsigned integer, round toward zero.
    /// rmode = 0b11, opcode = 0b001
    FcvtzuToInt,
    /// SCVTF — signed integer to FP.
    /// rmode = 0b00, opcode = 0b010
    ScvtfToFp,
    /// UCVTF — unsigned integer to FP.
    /// rmode = 0b00, opcode = 0b011
    UcvtfToFp,
    /// FMOV — move GP register to FP register.
    /// rmode = 0b00, opcode = 0b111
    FmovToFp,
    /// FMOV — move FP register to GP register.
    /// rmode = 0b00, opcode = 0b110
    FmovToGp,
}

impl FpConvOp {
    /// Returns (rmode, opcode) for the conversion instruction.
    fn rmode_opcode(self) -> (u32, u32) {
        match self {
            FpConvOp::FcvtzsToInt => (0b11, 0b000),
            FpConvOp::FcvtzuToInt => (0b11, 0b001),
            FpConvOp::ScvtfToFp => (0b00, 0b010),
            FpConvOp::UcvtfToFp => (0b00, 0b011),
            FpConvOp::FmovToFp => (0b00, 0b111),
            FpConvOp::FmovToGp => (0b00, 0b110),
        }
    }
}

/// FP unary (1-source) data-processing operation.
///
/// Maps to the 2-bit `opcode` field in bits [16:15].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FpUnaryOp {
    /// FMOV (register to register) — opcode = 0b00
    FmovReg = 0b00,
    /// FABS — opcode = 0b01
    Fabs = 0b01,
    /// FNEG — opcode = 0b10
    Fneg = 0b10,
    /// FSQRT — opcode = 0b11
    Fsqrt = 0b11,
    /// FRINTP — round to integral, toward +inf (ceil) — opcode = 0b001001.
    FrintP = 0b001001,
    /// FRINTM — round to integral, toward -inf (floor) — opcode = 0b001010.
    FrintM = 0b001010,
    /// FRINTZ — round to integral, toward zero (trunc) — opcode = 0b001011.
    FrintZ = 0b001011,
}

// ---------------------------------------------------------------------------
// Validation
// ---------------------------------------------------------------------------

#[inline]
fn check_reg(reg: u8, max: u8) -> Result<(), FpEncodeError> {
    if reg > max {
        return Err(FpEncodeError::RegisterOutOfRange { reg, max });
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// FP data-processing 2-source (FADD, FSUB, FMUL, FDIV)
// ---------------------------------------------------------------------------

/// Encode a 2-source FP data-processing instruction.
///
/// ```text
/// 0 | 00 | 11110 | ftype(2) | 1 | Rm(5) | opcode(4) | 10 | Rn(5) | Rd(5)
/// ```
pub fn encode_fp_arith(
    fp_size: FpSize,
    op: FpArithOp,
    rm: u8,
    rn: u8,
    rd: u8,
) -> Result<u32, FpEncodeError> {
    check_reg(rm, 31)?;
    check_reg(rn, 31)?;
    check_reg(rd, 31)?;

    let mut inst: u32 = 0;
    // bits[31:29] = 000
    inst |= 0b11110 << 24;
    inst |= (fp_size as u32) << 22;
    inst |= 1 << 21;
    inst |= (rm as u32) << 16;
    inst |= (op as u32) << 12;
    inst |= 0b10 << 10;
    inst |= (rn as u32) << 5;
    inst |= rd as u32;
    Ok(inst)
}

/// Encode a scalar FP conditional select `FCSEL Rd, Rn, Rm, cond`.
///
/// ```text
/// 0 | 00 | 11110 | ftype(2) | 1 | Rm(5) | cond(4) | 11 | Rn(5) | Rd(5)
/// ```
///
/// Semantics: `Rd = cond ? Rn : Rm`, copied bit-for-bit (NO FP arithmetic).
/// `ftype` selects S/D/H, `cond` is the 4-bit ARM condition code. Distinguished
/// from the 2-source data-processing form (`encode_fp_arith`) ONLY by bits
/// [11:10] = `0b11` (vs `0b10`) and by carrying the condition in [15:12].
/// Byte-pinned against Apple `clang` (S + D forms, several conditions). Reference:
/// ARM DDI 0487, C7.2.75 FCSEL.
pub fn encode_fcsel(
    fp_size: FpSize,
    cond: u32,
    rm: u8,
    rn: u8,
    rd: u8,
) -> Result<u32, FpEncodeError> {
    check_reg(rm, 31)?;
    check_reg(rn, 31)?;
    check_reg(rd, 31)?;
    debug_assert!(cond < 16, "condition code must be 4 bits");

    let mut inst: u32 = 0;
    // bits[31:29] = 000
    inst |= 0b11110 << 24;
    inst |= (fp_size as u32) << 22;
    inst |= 1 << 21;
    inst |= (rm as u32) << 16;
    inst |= (cond & 0xF) << 12;
    inst |= 0b11 << 10;
    inst |= (rn as u32) << 5;
    inst |= rd as u32;
    Ok(inst)
}

// ---------------------------------------------------------------------------
// FP data-processing 3-source (FMADD, FMSUB, FNMADD, FNMSUB)
// ---------------------------------------------------------------------------

/// Encode a scalar FP fused multiply-add (3-source) instruction.
///
/// ```text
/// 0 | 00 | 11111 | ftype(2) | o1 | Rm(5) | o0 | Ra(5) | Rn(5) | Rd(5)
/// ```
///
/// The base opcode is `0x1F00_0000` (bits[28:24]=11111); `ftype` selects
/// S/D/H, `o1`/`o0` select FMADD/FMSUB/FNMADD/FNMSUB. Semantics (single
/// rounding): FMADD `Rd = Ra + Rn*Rm`. Byte-pinned against the assembler
/// (clang -c + objdump) for all four forms × {S,D} incl. high registers.
pub fn encode_fp_madd(
    fp_size: FpSize,
    op: FpMaddOp,
    rm: u8,
    ra: u8,
    rn: u8,
    rd: u8,
) -> Result<u32, FpEncodeError> {
    check_reg(rm, 31)?;
    check_reg(ra, 31)?;
    check_reg(rn, 31)?;
    check_reg(rd, 31)?;

    let (o1, o0) = op.o1_o0();
    let mut inst: u32 = 0;
    inst |= 0b11111 << 24;
    inst |= (fp_size as u32) << 22;
    inst |= o1 << 21;
    inst |= (rm as u32) << 16;
    inst |= o0 << 15;
    inst |= (ra as u32) << 10;
    inst |= (rn as u32) << 5;
    inst |= rd as u32;
    Ok(inst)
}

// ---------------------------------------------------------------------------
// FCMP / FCMPE
// ---------------------------------------------------------------------------

/// Encode an FP compare instruction.
///
/// ```text
/// 0 | 00 | 11110 | ftype(2) | 1 | Rm(5) | 00 | 1000 | Rn(5) | opc(5)
/// ```
///
/// For zero-compare variants (`CmpZero`, `CmpeZero`), `rm` is ignored and
/// encoded as 0 (matching LLVM's `fixOneOperandFPComparison`).
pub fn encode_fcmp(fp_size: FpSize, cmp_op: FpCmpOp, rm: u8, rn: u8) -> Result<u32, FpEncodeError> {
    check_reg(rn, 31)?;

    // For register-compare variants, validate Rm.
    let rm_val = match cmp_op {
        FpCmpOp::CmpZero | FpCmpOp::CmpeZero => 0u32,
        _ => {
            check_reg(rm, 31)?;
            rm as u32
        }
    };

    let mut inst: u32 = 0;
    inst |= 0b11110 << 24;
    inst |= (fp_size as u32) << 22;
    inst |= 1 << 21;
    inst |= rm_val << 16;
    inst |= 0b00 << 14;
    inst |= 0b1000 << 10;
    inst |= (rn as u32) << 5;
    inst |= cmp_op as u32;
    Ok(inst)
}

// ---------------------------------------------------------------------------
// FP ↔ integer conversion
// ---------------------------------------------------------------------------

/// Encode an FP-to-integer or integer-to-FP conversion instruction.
///
/// ```text
/// sf(1) | 00 | 11110 | ftype(2) | 1 | rmode(2) | opcode(3) | 000000 | Rn(5) | Rd(5)
/// ```
///
/// * `sf_64` — `true` for 64-bit integer (X register), `false` for 32-bit (W)
/// * `fp_size` — floating-point precision
/// * `conv_op` — conversion type
/// * `rn` — source register (0..31)
/// * `rd` — destination register (0..31)
pub fn encode_fp_int_conv(
    sf_64: bool,
    fp_size: FpSize,
    conv_op: FpConvOp,
    rn: u8,
    rd: u8,
) -> Result<u32, FpEncodeError> {
    check_reg(rn, 31)?;
    check_reg(rd, 31)?;

    let (rmode, opcode) = conv_op.rmode_opcode();

    let mut inst: u32 = 0;
    inst |= (sf_64 as u32) << 31;
    // bits[30:29] = 00
    inst |= 0b11110 << 24;
    inst |= (fp_size as u32) << 22;
    inst |= 1 << 21;
    inst |= rmode << 19;
    inst |= opcode << 16;
    // bits[15:10] = 000000
    inst |= (rn as u32) << 5;
    inst |= rd as u32;
    Ok(inst)
}

// ---------------------------------------------------------------------------
// FP data-processing 1-source (FMOV reg, FABS, FNEG, FSQRT)
// ---------------------------------------------------------------------------

/// Encode a 1-source FP data-processing instruction.
///
/// ```text
/// 0 | 00 | 11110 | ftype(2) | 1 | 0000 | opcode(2) | 10000 | Rn(5) | Rd(5)
/// ```
pub fn encode_fp_unary(
    fp_size: FpSize,
    op: FpUnaryOp,
    rn: u8,
    rd: u8,
) -> Result<u32, FpEncodeError> {
    check_reg(rn, 31)?;
    check_reg(rd, 31)?;

    let mut inst: u32 = 0;
    inst |= 0b11110 << 24;
    inst |= (fp_size as u32) << 22;
    inst |= 1 << 21;
    // bits[20:17] = 0000
    inst |= (op as u32) << 15;
    inst |= 0b10000 << 10;
    inst |= (rn as u32) << 5;
    inst |= rd as u32;
    Ok(inst)
}

/// Encode a float precision conversion instruction (FCVT between sizes).
///
/// ```text
/// 0 | 00 | 11110 | ftype(2) | 1 | 0001 | opc(2) | 10000 | Rn(5) | Rd(5)
/// ```
///
/// - `src_size`: the FP size of the source register
/// - `dst_size`: the FP size of the destination register
///
/// `ftype` is derived from `src_size`, `opc` from `dst_size`:
///   FCVT Dd, Sn: ftype=00 (single), opc=01 (double)
///   FCVT Ss, Dn: ftype=01 (double), opc=00 (single)
pub fn encode_fp_precision_cvt(
    src_size: FpSize,
    dst_size: FpSize,
    rn: u8,
    rd: u8,
) -> Result<u32, FpEncodeError> {
    check_reg(rn, 31)?;
    check_reg(rd, 31)?;

    let ftype = src_size as u32;
    let opc = dst_size as u32;

    let mut inst: u32 = 0;
    inst |= 0b11110 << 24;
    inst |= ftype << 22;
    inst |= 1 << 21;
    inst |= 0b0001 << 17;
    inst |= opc << 15;
    inst |= 0b10000 << 10;
    inst |= (rn as u32) << 5;
    inst |= rd as u32;
    Ok(inst)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // === FP fused multiply-add (3-source) ===
    // Exact-byte pins vs the assembler: `clang -c fma.s + objdump -d`. All four
    // (o1,o0) forms × {S,D} + high-register operands. Base 0x1F00_0000; ftype
    // [23:22]; o1 [21]; Rm [20:16]; o0 [15]; Ra [14:10]; Rn [9:5]; Rd [4:0].

    #[test]
    fn test_fmadd_pins() {
        use FpMaddOp::*;
        // (op, size, rm, ra, rn, rd) -> expected word (from objdump).
        let cases: &[(FpMaddOp, FpSize, u8, u8, u8, u8, u32)] = &[
            // fmadd s0,s0,s0,s0 ; fmadd d0,d0,d0,d0
            (Madd, FpSize::Single, 0, 0, 0, 0, 0x1F00_0000),
            (Madd, FpSize::Double, 0, 0, 0, 0, 0x1F40_0000),
            // fmadd s5,s6,s7,s8  => rd=5, rn=6, rm=7, ra=8
            (Madd, FpSize::Single, 7, 8, 6, 5, 0x1F07_20C5),
            (Madd, FpSize::Double, 7, 8, 6, 5, 0x1F47_20C5),
            // fmsub s0,s0,s0,s0 ; fmsub d0,d0,d0,d0
            (Msub, FpSize::Single, 0, 0, 0, 0, 0x1F00_8000),
            (Msub, FpSize::Double, 0, 0, 0, 0, 0x1F40_8000),
            // fmsub s5,s6,s7,s8
            (Msub, FpSize::Single, 7, 8, 6, 5, 0x1F07_A0C5),
            // fnmadd s0,s0,s0,s0 ; fnmadd d0,d0,d0,d0
            (Nmadd, FpSize::Single, 0, 0, 0, 0, 0x1F20_0000),
            (Nmadd, FpSize::Double, 0, 0, 0, 0, 0x1F60_0000),
            // fnmsub s0,s0,s0,s0 ; fnmsub d0,d0,d0,d0
            (Nmsub, FpSize::Single, 0, 0, 0, 0, 0x1F20_8000),
            (Nmsub, FpSize::Double, 0, 0, 0, 0, 0x1F60_8000),
            // high registers: fmadd s31,s31,s31,s31 ; fmadd d31,d31,d31,d31
            (Madd, FpSize::Single, 31, 31, 31, 31, 0x1F1F_7FFF),
            (Madd, FpSize::Double, 31, 31, 31, 31, 0x1F5F_7FFF),
            // fmadd s10,s20,s30,s1 => rd=10, rn=20, rm=30, ra=1
            (Madd, FpSize::Single, 30, 1, 20, 10, 0x1F1E_068A),
        ];
        for &(op, size, rm, ra, rn, rd, want) in cases {
            let enc = encode_fp_madd(size, op, rm, ra, rn, rd).unwrap();
            assert_eq!(
                enc, want,
                "encode_fp_madd({op:?},{size:?},rm={rm},ra={ra},rn={rn},rd={rd}) = {enc:#010x}, want {want:#010x}"
            );
        }
    }

    #[test]
    fn test_fmadd_reg_out_of_range() {
        assert!(encode_fp_madd(FpSize::Single, FpMaddOp::Madd, 32, 0, 0, 0).is_err());
        assert!(encode_fp_madd(FpSize::Double, FpMaddOp::Madd, 0, 0, 0, 32).is_err());
    }

    // === FP arithmetic (2-source) ===

    #[test]
    fn test_fadd_single() {
        // FADD S0, S1, S2
        let enc = encode_fp_arith(FpSize::Single, FpArithOp::Add, 2, 1, 0).unwrap();
        assert_eq!(enc, 0x1E22_2820);
    }

    #[test]
    fn test_fadd_double() {
        // FADD D0, D1, D2
        let enc = encode_fp_arith(FpSize::Double, FpArithOp::Add, 2, 1, 0).unwrap();
        assert_eq!(enc, 0x1E62_2820);
    }

    #[test]
    fn test_fminnm_fmaxnm() {
        // Same operands as FADD above; only the opcode nibble [15:12] differs
        // (Add=0010 -> Minnm=0111 / Maxnm=0110), so the encodings track FADD.
        // FMINNM D0, D1, D2  (double, opcode 0b0111)
        assert_eq!(
            encode_fp_arith(FpSize::Double, FpArithOp::Minnm, 2, 1, 0).unwrap(),
            0x1E62_7820
        );
        // FMAXNM D0, D1, D2  (double, opcode 0b0110)
        assert_eq!(
            encode_fp_arith(FpSize::Double, FpArithOp::Maxnm, 2, 1, 0).unwrap(),
            0x1E62_6820
        );
        // FMINNM S0, S1, S2  (single, ptype 00)
        assert_eq!(
            encode_fp_arith(FpSize::Single, FpArithOp::Minnm, 2, 1, 0).unwrap(),
            0x1E22_7820
        );
        // FMAXNM S0, S1, S2  (single)
        assert_eq!(
            encode_fp_arith(FpSize::Single, FpArithOp::Maxnm, 2, 1, 0).unwrap(),
            0x1E22_6820
        );
    }

    #[test]
    fn test_fsub_double() {
        // FSUB D3, D4, D5
        let enc = encode_fp_arith(FpSize::Double, FpArithOp::Sub, 5, 4, 3).unwrap();
        assert_eq!(enc, 0x1E65_3883);
    }

    #[test]
    fn test_fmul_single() {
        // FMUL S10, S11, S12
        let enc = encode_fp_arith(FpSize::Single, FpArithOp::Mul, 12, 11, 10).unwrap();
        assert_eq!(enc, 0x1E2C_096A);
    }

    #[test]
    fn test_fdiv_double() {
        // FDIV D0, D1, D2
        let enc = encode_fp_arith(FpSize::Double, FpArithOp::Div, 2, 1, 0).unwrap();
        assert_eq!(enc, 0x1E62_1820);
    }

    #[test]
    fn test_fp_arith_half() {
        // FADD H5, H6, H7 — ftype=11
        let enc = encode_fp_arith(FpSize::Half, FpArithOp::Add, 7, 6, 5).unwrap();
        // Expected: 0|00|11110|11|1|00111|0010|10|00110|00101
        let expected = (0b11110u32 << 24)
            | (0b11 << 22)
            | (1 << 21)
            | (7 << 16)
            | (0b0010 << 12)
            | (0b10 << 10)
            | (6 << 5)
            | 5;
        assert_eq!(enc, expected);
    }

    #[test]
    fn test_fp_arith_reg_overflow() {
        let err = encode_fp_arith(FpSize::Single, FpArithOp::Add, 32, 0, 0);
        assert!(matches!(
            err,
            Err(FpEncodeError::RegisterOutOfRange { reg: 32, max: 31 })
        ));
    }

    // === FCMP ===

    #[test]
    fn test_fcmp_single_regs() {
        // FCMP S1, S2
        let enc = encode_fcmp(FpSize::Single, FpCmpOp::Cmp, 2, 1).unwrap();
        assert_eq!(enc, 0x1E22_2020);
    }

    #[test]
    fn test_fcmp_double_zero() {
        // FCMP D1, #0.0
        let enc = encode_fcmp(FpSize::Double, FpCmpOp::CmpZero, 0, 1).unwrap();
        assert_eq!(enc, 0x1E60_2028);
    }

    #[test]
    fn test_fcmpe_single_regs() {
        // FCMPE S0, S1
        let enc = encode_fcmp(FpSize::Single, FpCmpOp::Cmpe, 1, 0).unwrap();
        // opc = 0b10000
        let expected = (0b11110u32 << 24) | (1 << 21) | (1 << 16) | (0b1000 << 10) | 0b10000;
        assert_eq!(enc, expected);
    }

    #[test]
    fn test_fcmpe_double_zero() {
        // FCMPE D0, #0.0  — Rm zeroed
        let enc = encode_fcmp(FpSize::Double, FpCmpOp::CmpeZero, 255, 0).unwrap();
        // Rm is forced to 0 for zero variants (rm parameter ignored)
        let expected = (0b11110u32 << 24) | (0b01 << 22) | (1 << 21) | (0b1000 << 10) | 0b11000;
        assert_eq!(enc, expected);
    }

    // === FP ↔ integer conversion ===

    #[test]
    fn test_fcvtzs_w_s() {
        // FCVTZS W0, S1: sf=0, ftype=00, rmode=11, opcode=000
        let enc = encode_fp_int_conv(false, FpSize::Single, FpConvOp::FcvtzsToInt, 1, 0).unwrap();
        assert_eq!(enc, 0x1E38_0020);
    }

    #[test]
    fn test_scvtf_s_w() {
        // SCVTF S0, W1: sf=0, ftype=00, rmode=00, opcode=010
        let enc = encode_fp_int_conv(false, FpSize::Single, FpConvOp::ScvtfToFp, 1, 0).unwrap();
        assert_eq!(enc, 0x1E22_0020);
    }

    #[test]
    fn test_scvtf_d_x() {
        // SCVTF D0, X1: sf=1, ftype=01, rmode=00, opcode=010
        let enc = encode_fp_int_conv(true, FpSize::Double, FpConvOp::ScvtfToFp, 1, 0).unwrap();
        assert_eq!(enc, 0x9E62_0020);
    }

    #[test]
    fn test_fmov_gp_to_fp() {
        // FMOV S0, W1: sf=0, ftype=00, rmode=00, opcode=111
        let enc = encode_fp_int_conv(false, FpSize::Single, FpConvOp::FmovToFp, 1, 0).unwrap();
        let expected = (0b11110u32 << 24) | (1 << 21) | (0b111 << 16) | (1 << 5);
        assert_eq!(enc, expected);
    }

    #[test]
    fn test_fmov_fp_to_gp() {
        // FMOV W0, S1: sf=0, ftype=00, rmode=00, opcode=110
        let enc = encode_fp_int_conv(false, FpSize::Single, FpConvOp::FmovToGp, 1, 0).unwrap();
        let expected = (0b11110u32 << 24) | (1 << 21) | (0b110 << 16) | (1 << 5);
        assert_eq!(enc, expected);
    }

    #[test]
    fn test_fp_conv_reg_overflow() {
        let err = encode_fp_int_conv(false, FpSize::Single, FpConvOp::FcvtzsToInt, 32, 0);
        assert!(matches!(
            err,
            Err(FpEncodeError::RegisterOutOfRange { reg: 32, .. })
        ));
    }

    // === FP unary (1-source) ===

    #[test]
    fn test_fneg_single() {
        // FNEG S0, S1: ftype=00, opcode=10
        let enc = encode_fp_unary(FpSize::Single, FpUnaryOp::Fneg, 1, 0).unwrap();
        assert_eq!(enc, 0x1E21_4020);
    }

    #[test]
    fn test_fabs_double() {
        // FABS D3, D4: ftype=01, opcode=01
        let enc = encode_fp_unary(FpSize::Double, FpUnaryOp::Fabs, 4, 3).unwrap();
        assert_eq!(enc, 0x1E60_C083);
    }

    #[test]
    fn test_fsqrt_double() {
        // FSQRT D0, D1: ftype=01, opcode=11
        let enc = encode_fp_unary(FpSize::Double, FpUnaryOp::Fsqrt, 1, 0).unwrap();
        assert_eq!(enc, 0x1E61_C020);
    }

    #[test]
    fn test_frint_double() {
        // FRINTM/FRINTP/FRINTZ Dd, Dn (ftype=01, opcode=001010/001001/001011).
        assert_eq!(
            encode_fp_unary(FpSize::Double, FpUnaryOp::FrintM, 0, 0).unwrap(),
            0x1E65_4000 // FRINTM D0, D0
        );
        assert_eq!(
            encode_fp_unary(FpSize::Double, FpUnaryOp::FrintP, 0, 0).unwrap(),
            0x1E64_C000 // FRINTP D0, D0
        );
        assert_eq!(
            encode_fp_unary(FpSize::Double, FpUnaryOp::FrintZ, 0, 0).unwrap(),
            0x1E65_C000 // FRINTZ D0, D0
        );
    }

    #[test]
    fn test_frint_single() {
        // FRINTM/FRINTP/FRINTZ Sd, Sn (ftype=00).
        assert_eq!(
            encode_fp_unary(FpSize::Single, FpUnaryOp::FrintM, 0, 0).unwrap(),
            0x1E25_4000 // FRINTM S0, S0
        );
        assert_eq!(
            encode_fp_unary(FpSize::Single, FpUnaryOp::FrintP, 0, 0).unwrap(),
            0x1E24_C000 // FRINTP S0, S0
        );
        assert_eq!(
            encode_fp_unary(FpSize::Single, FpUnaryOp::FrintZ, 0, 0).unwrap(),
            0x1E25_C000 // FRINTZ S0, S0
        );
    }

    #[test]
    fn test_fmov_reg_single() {
        // FMOV S5, S6: ftype=00, opcode=00
        let enc = encode_fp_unary(FpSize::Single, FpUnaryOp::FmovReg, 6, 5).unwrap();
        let expected = (0b11110u32 << 24) | (1 << 21) | (0b10000 << 10) | (6 << 5) | 5;
        assert_eq!(enc, expected);
    }

    #[test]
    fn test_fp_unary_reg_overflow() {
        let err = encode_fp_unary(FpSize::Single, FpUnaryOp::Fneg, 0, 32);
        assert!(matches!(
            err,
            Err(FpEncodeError::RegisterOutOfRange { reg: 32, .. })
        ));
    }

    // === All FpArithOp opcodes ===

    #[test]
    fn test_fp_arith_opcodes() {
        for (op, expected_bits) in [
            (FpArithOp::Mul, 0b0000u32),
            (FpArithOp::Div, 0b0001),
            (FpArithOp::Add, 0b0010),
            (FpArithOp::Sub, 0b0011),
        ] {
            let enc = encode_fp_arith(FpSize::Single, op, 0, 0, 0).unwrap();
            let opcode_field = (enc >> 12) & 0b1111;
            assert_eq!(opcode_field, expected_bits, "opcode mismatch for {:?}", op);
        }
    }

    // === All FpSize ftype values ===

    #[test]
    fn test_fp_size_ftype() {
        for (size, expected_bits) in [
            (FpSize::Single, 0b00u32),
            (FpSize::Double, 0b01),
            (FpSize::Half, 0b11),
        ] {
            let enc = encode_fp_arith(size, FpArithOp::Add, 0, 0, 0).unwrap();
            let ftype_field = (enc >> 22) & 0b11;
            assert_eq!(ftype_field, expected_bits, "ftype mismatch for {:?}", size);
        }
    }
}
