// trust-cg-codegen/aarch64/encoding_neon.rs - AArch64 NEON SIMD instruction encoding
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! AArch64 NEON (Advanced SIMD) instruction encoding.
//!
//! Implements encoding for AArch64 NEON instruction formats from the
//! ARM Architecture Reference Manual (DDI 0487):
//!
//! - **Three-register same**: vector arithmetic (ADD, SUB, MUL, FADD, FSUB, FMUL, FDIV),
//!   logic (AND, ORR, EOR, BIC), compare (CMEQ, CMGT, CMGE, CMHI, CMHS)
//! - **Two-register misc**: NOT (bitwise NOT / MVN), RBIT, REV32, REV64
//! - **Modified immediate**: MOVI (move immediate to vector)
//! - **Vector copy**: DUP (scalar to vector), INS (insert element), UMOV (extract element)
//! - **Across-lanes reductions**: UMAXV.4S, ADDP.2D
//! - **SIMD load/store**: LD1, ST1 (single-structure, post-index)
//!
//! Reference: ARM ARM C7.2.x, `~/llvm-project-ref/llvm/lib/Target/AArch64/AArch64InstrFormats.td`

use thiserror::Error;

/// Errors produced during NEON instruction encoding.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum NeonEncodeError {
    #[error("register index {reg} out of range (max 31)")]
    RegisterOutOfRange { reg: u8 },
    #[error("invalid arrangement size {0}")]
    InvalidSize(u8),
    #[error("invalid lane index {lane} for arrangement")]
    InvalidLane { lane: u8 },
    #[error("immediate {0:#X} out of range for MOVI")]
    ImmediateOutOfRange(u64),
    #[error("{op} vector shift amount {shift} out of range for {esize}-bit lanes")]
    InvalidShiftAmount {
        shift: u32,
        esize: u32,
        op: &'static str,
    },
    #[error(
        "LDP Q post-index offset {0} invalid: must be a multiple of 16 in [-1024, 1008] \
         (imm7 scaled by 16)"
    )]
    InvalidLdpQPostOffset(i64),
    #[error("LDP with identical destination registers q{0} is UNPREDICTABLE — rejected")]
    LdpDuplicateDest(u8),
    #[error(
        "STP Q post-index offset {0} invalid: must be a multiple of 16 in [-1024, 1008] \
         (imm7 scaled by 16)"
    )]
    InvalidStpQPostOffset(i64),
    #[error(
        "EXT byte shift {0} invalid: only the whole-i32-lane shifts 4, 8, 12 are emitted \
         and proof-credited — rejected (fail-closed)"
    )]
    InvalidExtImmediate(i64),
}

// ---------------------------------------------------------------------------
// Arrangement / size enums
// ---------------------------------------------------------------------------

/// NEON vector arrangement (Q and size fields).
///
/// Determines element size and whether the instruction operates on
/// 64-bit (D-register) or 128-bit (Q-register / V-register) vectors.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VectorArrangement {
    /// 8B:  8 x 8-bit  elements in 64-bit register (Q=0, size=00)
    B8,
    /// 16B: 16 x 8-bit elements in 128-bit register (Q=1, size=00)
    B16,
    /// 4H:  4 x 16-bit elements in 64-bit register (Q=0, size=01)
    H4,
    /// 8H:  8 x 16-bit elements in 128-bit register (Q=1, size=01)
    H8,
    /// 2S:  2 x 32-bit elements in 64-bit register (Q=0, size=10)
    S2,
    /// 4S:  4 x 32-bit elements in 128-bit register (Q=1, size=10)
    S4,
    /// 2D:  2 x 64-bit elements in 128-bit register (Q=1, size=11)
    D2,
}

impl VectorArrangement {
    /// Returns (Q, size) fields for this arrangement.
    pub fn q_size(self) -> (u32, u32) {
        match self {
            Self::B8 => (0, 0b00),
            Self::B16 => (1, 0b00),
            Self::H4 => (0, 0b01),
            Self::H8 => (1, 0b01),
            Self::S2 => (0, 0b10),
            Self::S4 => (1, 0b10),
            Self::D2 => (1, 0b11),
        }
    }

    /// Returns the Q bit for this arrangement.
    pub fn q(self) -> u32 {
        self.q_size().0
    }

    /// Returns the size field for this arrangement.
    pub fn size(self) -> u32 {
        self.q_size().1
    }
}

/// FP vector arrangement (for FADD/FSUB/FMUL/FDIV).
///
/// AArch64 NEON FP instructions use `sz` (1 bit) instead of `size` (2 bits).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FpVectorArrangement {
    /// 2S: 2 x f32 in 64-bit register (Q=0, sz=0)
    S2,
    /// 4S: 4 x f32 in 128-bit register (Q=1, sz=0)
    S4,
    /// 2D: 2 x f64 in 128-bit register (Q=1, sz=1)
    D2,
}

impl FpVectorArrangement {
    /// Returns (Q, sz) for this FP arrangement.
    pub fn q_sz(self) -> (u32, u32) {
        match self {
            Self::S2 => (0, 0),
            Self::S4 => (1, 0),
            Self::D2 => (1, 1),
        }
    }
}

// ---------------------------------------------------------------------------
// Validation
// ---------------------------------------------------------------------------

#[inline]
fn check_reg(reg: u8) -> Result<(), NeonEncodeError> {
    if reg > 31 {
        return Err(NeonEncodeError::RegisterOutOfRange { reg });
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Three-register same: integer vector arithmetic
// ARM ARM C7.2.x: Advanced SIMD three same
//
//   0 | Q | U | 01110 | size(2) | 1 | Rm(5) | opcode(5) | 1 | Rn(5) | Rd(5)
//
// ---------------------------------------------------------------------------

/// Integer vector three-register-same opcode (5-bit `opcode` field, bits [15:11]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntVec3Op {
    /// ADD: opcode = 10000, U = 0
    Add,
    /// SUB: opcode = 10000, U = 1
    Sub,
    /// MUL: opcode = 10011, U = 0
    Mul,
    /// CMEQ (register): opcode = 10001, U = 1
    Cmeq,
    /// CMGT (signed): opcode = 00110, U = 0
    Cmgt,
    /// CMGE (signed): opcode = 00111, U = 0
    Cmge,
    /// CMHI (unsigned): opcode = 00110, U = 1
    Cmhi,
    /// CMHS (unsigned): opcode = 00111, U = 1
    Cmhs,
    /// SMAX (signed max): opcode = 01100, U = 0
    Smax,
    /// SMIN (signed min): opcode = 01101, U = 0
    Smin,
    /// UMAX (unsigned max): opcode = 01100, U = 1
    Umax,
    /// UMIN (unsigned min): opcode = 01101, U = 1
    Umin,
}

impl IntVec3Op {
    /// Returns (U, opcode) for the instruction.
    fn u_opcode(self) -> (u32, u32) {
        match self {
            Self::Add => (0, 0b10000),
            Self::Sub => (1, 0b10000),
            Self::Mul => (0, 0b10011),
            Self::Cmeq => (1, 0b10001),
            Self::Cmgt => (0, 0b00110),
            Self::Cmge => (0, 0b00111),
            Self::Cmhi => (1, 0b00110),
            Self::Cmhs => (1, 0b00111),
            Self::Smax => (0, 0b01100),
            Self::Smin => (0, 0b01101),
            Self::Umax => (1, 0b01100),
            Self::Umin => (1, 0b01101),
        }
    }
}

/// Encode a NEON integer three-register-same instruction.
///
/// Format: `0 | Q | U | 01110 | size(2) | 1 | Rm(5) | opcode(5) | 1 | Rn(5) | Rd(5)`
///
/// ARM ARM: C7.2.1 (ADD vector), C7.2.299 (SUB vector), C7.2.211 (MUL vector)
pub fn encode_int_vec3_same(
    arr: VectorArrangement,
    op: IntVec3Op,
    rm: u8,
    rn: u8,
    rd: u8,
) -> Result<u32, NeonEncodeError> {
    check_reg(rm)?;
    check_reg(rn)?;
    check_reg(rd)?;

    // FAIL-CLOSED ISA legality: baseline NEON has NO 64-bit-lane (`.2D`) form of
    // integer MUL or SMAX/SMIN/UMAX/UMIN (ARM DDI 0487 C7.2.211 MUL, C7.2.281+
    // SMAX/..: size==11 is RESERVED for these "three same" opcodes; only
    // ADD/SUB/CMEQ/CMGT/CMGE/CMHI/CMHS allocate size==11). Encoding size=11
    // would emit an UNALLOCATED instruction, so reject it here rather than
    // trusting every emitter to know the table.
    if arr == VectorArrangement::D2
        && matches!(
            op,
            IntVec3Op::Mul | IntVec3Op::Smax | IntVec3Op::Smin | IntVec3Op::Umax | IntVec3Op::Umin
        )
    {
        return Err(NeonEncodeError::InvalidSize(arr.size() as u8));
    }

    let (q, size) = arr.q_size();
    let (u, opcode) = op.u_opcode();

    Ok((q << 30)
        | (u << 29)
        | (0b01110 << 24)
        | (size << 22)
        | (1 << 21)
        | ((rm as u32) << 16)
        | (opcode << 11)
        | (1 << 10)
        | ((rn as u32) << 5)
        | (rd as u32))
}

// ---------------------------------------------------------------------------
// Three-register same: logic vector (AND, ORR, EOR, BIC)
// ARM ARM C7.2.x: Advanced SIMD three same
//
//   0 | Q | op2(2) | 01110 | size(2) | 1 | Rm(5) | 00011 | 1 | Rn(5) | Rd(5)
//
// Logic instructions use a special encoding:
//   AND: 0|Q|0|01110|00|1|Rm|00011|1|Rn|Rd
//   ORR: 0|Q|0|01110|10|1|Rm|00011|1|Rn|Rd
//   EOR: 0|Q|1|01110|00|1|Rm|00011|1|Rn|Rd
//   BIC: 0|Q|0|01110|01|1|Rm|00011|1|Rn|Rd
// ---------------------------------------------------------------------------

/// Vector logic operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VecLogicOp {
    /// AND vector: U=0, size=00
    And,
    /// ORR vector: U=0, size=10
    Orr,
    /// EOR vector: U=1, size=00
    Eor,
    /// BIC vector (AND-NOT): U=0, size=01
    Bic,
    /// BIT vector (bitwise insert if true, Vd tied): U=1, size=10.
    /// `Vd = Vd ^ ((Vd ^ Vn) & Vm)`. ARM DDI 0487 C7.2.16 BIT.
    Bit,
}

impl VecLogicOp {
    /// Returns (U, size) for the logic instruction.
    fn u_size(self) -> (u32, u32) {
        match self {
            Self::And => (0, 0b00),
            Self::Orr => (0, 0b10),
            Self::Eor => (1, 0b00),
            Self::Bic => (0, 0b01),
            Self::Bit => (1, 0b10),
        }
    }
}

/// Encode a NEON vector logic instruction (AND, ORR, EOR, BIC).
///
/// Format: `0 | Q | U | 01110 | size(2) | 1 | Rm(5) | 00011 | 1 | Rn(5) | Rd(5)`
///
/// ARM ARM: C7.2.8 (AND vector), C7.2.219 (ORR vector), C7.2.87 (EOR vector)
pub fn encode_vec_logic(
    q: u32,
    op: VecLogicOp,
    rm: u8,
    rn: u8,
    rd: u8,
) -> Result<u32, NeonEncodeError> {
    check_reg(rm)?;
    check_reg(rn)?;
    check_reg(rd)?;

    let (u, size) = op.u_size();

    Ok((q << 30)
        | (u << 29)
        | (0b01110 << 24)
        | (size << 22)
        | (1 << 21)
        | ((rm as u32) << 16)
        | (0b00011 << 11)
        | (1 << 10)
        | ((rn as u32) << 5)
        | (rd as u32))
}

// ---------------------------------------------------------------------------
// Two-register misc: NOT (bitwise NOT / MVN)
// ARM ARM C7.2.216: NOT (vector)
//
//   0 | Q | 1 | 01110 | 00 | 10000 | 00101 | 10 | Rn(5) | Rd(5)
//
// This is actually encoded as: 2Q|1|01110|size=00|10000|opcode=00101|10|Rn|Rd
// NOT is an alias for MVN: Q|U=1|01110|00|10000|00101|10|Rn|Rd
// ---------------------------------------------------------------------------

/// Encode a NEON NOT (bitwise NOT / MVN) instruction.
///
/// Format: `0 | Q | 1 | 01110 | 00 | 10000 | 00101 | 10 | Rn(5) | Rd(5)`
///
/// ARM ARM: C7.2.216 NOT (vector)
pub fn encode_vec_not(q: u32, rn: u8, rd: u8) -> Result<u32, NeonEncodeError> {
    check_reg(rn)?;
    check_reg(rd)?;

    // NOT is MVN (alias): 0|Q|1|01110|00|10000|00101|10|Rn|Rd
    Ok(((q << 30)
        | (1 << 29)       // U = 1
        | (0b01110 << 24))    // size = 00
        | (0b10000 << 17)
        | (0b00101 << 12)
        | (0b10 << 10)
        | ((rn as u32) << 5)
        | (rd as u32))
}

/// Two-register byte operation accepted by [`encode_vec_byte_2reg`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VecByte2Op {
    /// RBIT Vd.{8B,16B}, Vn.{8B,16B}
    Rbit,
    /// REV32 Vd.{8B,16B}, Vn.{8B,16B}
    Rev32,
    /// REV64 Vd.{8B,16B}, Vn.{8B,16B}
    Rev64,
}

impl VecByte2Op {
    fn base(self) -> u32 {
        match self {
            Self::Rbit => 0x2E60_5800,
            Self::Rev32 => 0x2E20_0800,
            Self::Rev64 => 0x0E20_0800,
        }
    }
}

/// Encode NEON two-register byte/element reverse operations.
///
/// Supported forms:
/// - `RBIT Vd.8B, Vn.8B` and `RBIT Vd.16B, Vn.16B`
/// - `REV32 Vd.8B, Vn.8B` and `REV32 Vd.16B, Vn.16B`
/// - `REV64 Vd.8B, Vn.8B` and `REV64 Vd.16B, Vn.16B`
/// - `REV64 Vd.4S, Vn.4S` (size=10): reverses the 32-bit ELEMENTS within each
///   64-bit doubleword — the complex `{rp, ip}` pair swap the AoS butterfly
///   vectorizer (`neon_butterfly`) emits. Byte-verified vs the system
///   assembler: `rev64 v6.4s, v7.4s` = `0x4EA008E6`
///   (base `0x0E20_0800` | Q<<30 | size(0b10)<<22 | Rn<<5 | Rd).
///
/// Every other (op, arrangement) combination is REJECTED fail-closed.
///
/// Reference: ARM DDI 0487, C7.2.219 REV64 (vector).
pub fn encode_vec_byte_2reg(
    arr: VectorArrangement,
    op: VecByte2Op,
    rn: u8,
    rd: u8,
) -> Result<u32, NeonEncodeError> {
    check_reg(rn)?;
    check_reg(rd)?;

    let (q, size) = match (op, arr) {
        (_, VectorArrangement::B8) => (0u32, 0u32),
        (_, VectorArrangement::B16) => (1, 0),
        (VecByte2Op::Rev64, VectorArrangement::S4) => (1, 0b10),
        _ => return Err(NeonEncodeError::InvalidSize(arr.size() as u8)),
    };

    Ok(op.base() | (q << 30) | (size << 22) | ((rn as u32) << 5) | (rd as u32))
}

// ---------------------------------------------------------------------------
// Two-register miscellaneous: CNT (population count) and UADDLP (unsigned add
// long pairwise)
// ARM ARM: Advanced SIMD two-register miscellaneous
//
//   0 | Q | U | 01110 | size(2) | 10000 | opcode(5) | 10 | Rn(5) | Rd(5)
//
// CNT:    U=0, size=00, opcode=00101  (8B/16B only)
// UADDLP: U=1,          opcode=00010  (size = input element size)
// ---------------------------------------------------------------------------

/// Encode `CNT Vd.T, Vn.T` — per-byte population count. Only the byte
/// arrangements exist in the ISA (`8B` Q=0 / `16B` Q=1); any other arrangement
/// is rejected.
///
/// Verified against the assembler: `cnt v0.16b, v1.16b` = `0x4E205820`
/// (base `0x4E205800` | (Rn<<5) | Rd).
///
/// Reference: ARM DDI 0487, C7.2.34 CNT.
pub fn encode_cnt(arr: VectorArrangement, rn: u8, rd: u8) -> Result<u32, NeonEncodeError> {
    check_reg(rn)?;
    check_reg(rd)?;
    let q = match arr {
        VectorArrangement::B8 => 0u32,
        VectorArrangement::B16 => 1u32,
        _ => return Err(NeonEncodeError::InvalidSize(arr.size() as u8)),
    };
    // Q-independent base is the Q=0 form `0x0E205800`; OR in the Q bit.
    Ok(0x0E20_5800 | (q << 30) | ((rn as u32) << 5) | (rd as u32))
}

/// Encode `UADDLP Vd.Ta, Vn.Tb` — unsigned add long pairwise. `in_arr` is the
/// INPUT arrangement `Tb`; the output arrangement `Ta` is the widened,
/// half-lane-count sibling (`16B→8H`, `8H→4S`). Only the two 128-bit widening
/// pairs the popcount fold uses are accepted.
///
/// Verified against the assembler:
///   `uaddlp v0.8h, v1.16b` = `0x6E202820` (base `0x6E202800`, size=00)
///   `uaddlp v0.4s, v1.8h`  = `0x6E602820` (base `0x6E602800`, size=01)
///
/// Reference: ARM DDI 0487, C7.2.351 UADDLP.
pub fn encode_uaddlp(in_arr: VectorArrangement, rn: u8, rd: u8) -> Result<u32, NeonEncodeError> {
    check_reg(rn)?;
    check_reg(rd)?;
    // Q=1 (128-bit) for the widening pairs we emit; `size` = INPUT element size.
    let size = match in_arr {
        VectorArrangement::B16 => 0b00u32, // 16B -> 8H
        VectorArrangement::H8 => 0b01u32,  // 8H  -> 4S
        _ => return Err(NeonEncodeError::InvalidSize(in_arr.size() as u8)),
    };
    Ok((1 << 30)          // Q = 1
        | (1 << 29)       // U = 1
        | (0b01110 << 24)
        | (size << 22)
        | (0b10000 << 17)
        | (0b00010 << 12) // opcode = 00010 (UADDLP)
        | (0b10 << 10)
        | ((rn as u32) << 5)
        | (rd as u32))
}

/// Encode `SADDLP Vd.Ta, Vn.Tb` — signed add long pairwise. `in_arr` is the
/// INPUT arrangement `Tb`; the output arrangement `Ta` is the widened,
/// half-lane-count sibling (`16B→8H`, `8H→4S`). Only the two 128-bit widening
/// pairs the sext-widening reductions use are accepted. Identical layout to
/// [`encode_uaddlp`] except `U = 0` (signed).
///
/// Verified against the assembler (`llvm-mc`):
///   `saddlp v0.8h, v1.16b` = `0x4E202820` (base `0x4E202800`, size=00)
///   `saddlp v0.4s, v1.8h`  = `0x4E602820` (base `0x4E602800`, size=01)
///
/// Reference: ARM DDI 0487, C7.2.252 SADDLP.
pub fn encode_saddlp(in_arr: VectorArrangement, rn: u8, rd: u8) -> Result<u32, NeonEncodeError> {
    check_reg(rn)?;
    check_reg(rd)?;
    // Q=1 (128-bit) for the widening pairs we emit; `size` = INPUT element size.
    let size = match in_arr {
        VectorArrangement::B16 => 0b00u32, // 16B -> 8H
        VectorArrangement::H8 => 0b01u32,  // 8H  -> 4S
        _ => return Err(NeonEncodeError::InvalidSize(in_arr.size() as u8)),
    };
    Ok((1 << 30)          // Q = 1
        // U = 0 (signed) — the ONLY bit differing from UADDLP.
        | (0b01110 << 24)
        | (size << 22)
        | (0b10000 << 17)
        | (0b00010 << 12) // opcode = 00010 (xADDLP)
        | (0b10 << 10)
        | ((rn as u32) << 5)
        | (rd as u32))
}

/// Encode `ABS Vd.4S, Vn.4S` — per-lane signed absolute value (two's complement).
/// Two-register-miscellaneous form: `U=0, opcode=01011`, `size=10` for `.4S`.
/// Only the `.4S` arrangement the abs-sum reduction lowering emits is accepted; any
/// other arrangement is rejected (fail-closed — no proof credit exists for it).
///
/// Verified against the assembler: `abs v0.4s, v1.4s` = `0x4EA0B820`
/// (base `0x4EA0B800` | (Rn<<5) | Rd).
///
/// Reference: ARM DDI 0487, C7.2.1 ABS (vector).
pub fn encode_abs(arr: VectorArrangement, rn: u8, rd: u8) -> Result<u32, NeonEncodeError> {
    check_reg(rn)?;
    check_reg(rd)?;
    match arr {
        VectorArrangement::S4 => {}
        _ => return Err(NeonEncodeError::InvalidSize(arr.size() as u8)),
    }
    Ok(0x4EA0_B800 | ((rn as u32) << 5) | (rd as u32))
}

/// Encode `UDOT Vd.4S, Vn.16B, Vm.16B` — unsigned dot-product ACCUMULATE
/// (FEAT_DotProd): each 32-bit lane of `Vd` accumulates the sum of the four
/// products of the corresponding zero-extended byte lanes of `Vn` and `Vm`
/// (`Vd[i] += sum_j zext(Vn.b[4i+j]) * zext(Vm.b[4i+j])`). `Vd` is BOTH source
/// and destination (the encoder has no def/use role — that is modeled by
/// `has_tied_def_use` in trust-cg-opt/effects.rs).
///
/// Dot-product class: `0 Q 1 01110 size 0 Rm 1001 0 1 Rn Rd` with `Q=1`
/// (128-bit), `U=1` (bit 29; unsigned — `U=0` would be SDOT, a sign-extending
/// MISCOMPILE for byte values >= 0x80), `size=10`. `in_arr` is the INPUT
/// arrangement; only the `.16B -> .4S` form the ctpop-reduction lowering emits
/// is accepted — anything else is rejected (fail-closed: no proof credit
/// exists for it).
///
/// Verified against the assembler (`clang -c -march=armv8.2-a+dotprod` +
/// `objdump -d`):
///   `udot v0.4s,  v1.16b,  v2.16b`  = `0x6E829420`
///   `udot v31.4s, v30.16b, v29.16b` = `0x6E9D97DF`
/// (base `0x6E809400` | (Rm<<16) | (Rn<<5) | Rd).
///
/// Reference: ARM DDI 0487, C7.2.361 UDOT (vector).
pub fn encode_udot(
    in_arr: VectorArrangement,
    rm: u8,
    rn: u8,
    rd: u8,
) -> Result<u32, NeonEncodeError> {
    check_reg(rm)?;
    check_reg(rn)?;
    check_reg(rd)?;
    match in_arr {
        VectorArrangement::B16 => {}
        _ => return Err(NeonEncodeError::InvalidSize(in_arr.size() as u8)),
    }
    Ok(0x6E80_9400 | ((rm as u32) << 16) | ((rn as u32) << 5) | (rd as u32))
}

/// Encode `SMLAL/SMLAL2/UMLAL/UMLAL2 Vd.2D, Vn.<2S|4S>, Vm.<2S|4S>` — widening
/// multiply-ACCUMULATE-LONG (Advanced SIMD three different). Each of the two i64
/// output lanes accumulates the EXACT (no-truncation) i32xi32->i64 product of a
/// pair of source `.4S` lanes, sign-extended (`signed`) or zero-extended:
/// `Vd.d[j] += ext(Vn.4S[base+j]) * ext(Vm.4S[base+j])` where `base = 0` for the
/// LOW form (`high=false`, SMLAL/UMLAL, lanes {0,1}) and `base = 2` for the HIGH
/// form (`high=true`, SMLAL2/UMLAL2, lanes {2,3}). `Vd` is BOTH source and
/// destination (the accumulator) — modeled by `has_tied_def_use` in
/// trust-cg-opt/effects.rs.
///
/// Bit layout: `0 Q U 01110 size 1 Rm opcode(1000) 00 Rn Rd` with `size=10`
/// (source element = S/32-bit), `opcode=1000` (xMLAL — `1100` would be SMULL/
/// UMULL, a NON-accumulating MISCOMPILE, verified distinct: smull.2d = 0x0EA2C020
/// vs smlal.2d = 0x0EA28020), `Q` = low(0)/high(1), `U` = signed(0)/unsigned(1).
/// Base words (Rm=Rn=Rd=0): SMLAL 0x0EA08000, SMLAL2 0x4EA08000, UMLAL
/// 0x2EA08000, UMLAL2 0x6EA08000.
///
/// Only the `.4S -> .2D` input arrangement the neon_array widening dot emits is
/// accepted (the ISA has no other size for this widening dot); anything else is
/// rejected fail-closed (no proof credit exists for it).
///
/// Verified against the assembler (`clang -c -target arm64-apple-macos` +
/// `otool -tvj`):
///   `smlal.2d  v0,v1,v2`    = 0x0EA28020   `smlal2.2d v0,v1,v2`    = 0x4EA28020
///   `umlal.2d  v0,v1,v2`    = 0x2EA28020   `umlal2.2d v0,v1,v2`    = 0x6EA28020
///   `smlal.2d  v31,v30,v29` = 0x0EBD83DF   `smlal2.2d v31,v30,v29` = 0x4EBD83DF
///   `smlal.2d  v5,v20,v11`  = 0x0EAB8285   `smlal2.2d v7,v3,v9`    = 0x4EA98067
/// (base `| (Rm<<16) | (Rn<<5) | Rd`).
///
/// Reference: ARM DDI 0487, C7.2.267 SMLAL/SMLAL2, C7.2.352 UMLAL/UMLAL2.
pub fn encode_smlal(
    in_arr: VectorArrangement,
    high: bool,
    signed: bool,
    rm: u8,
    rn: u8,
    rd: u8,
) -> Result<u32, NeonEncodeError> {
    check_reg(rm)?;
    check_reg(rn)?;
    check_reg(rd)?;
    match in_arr {
        VectorArrangement::S4 => {}
        _ => return Err(NeonEncodeError::InvalidSize(in_arr.size() as u8)),
    }
    let base = 0x0EA0_8000 | (if high { 1 } else { 0 } << 30) | (if signed { 0 } else { 1 } << 29);
    Ok(base | ((rm as u32) << 16) | ((rn as u32) << 5) | (rd as u32))
}

/// Encode `UADDW/UADDW2 Vd.2D, Vn.2D, Vm.<2S|4S>` — UNSIGNED widening add-WIDE
/// (Advanced SIMD three different). Each of the two i64 output lanes is the i64
/// addend lane of `Vn` plus a zero-extended source `.4S` lane of `Vm`:
/// `Vd.d[j] = Vn.d[j] + zext64(Vm.4S[base+j])` where `base = 0` for the LOW form
/// (`high=false`, UADDW, lanes {0,1}) and `base = 2` for the HIGH form
/// (`high=true`, UADDW2, lanes {2,3}). The ISA's plain THREE-OPERAND form: the
/// addend is the SEPARATE source register `Vn`, `Vd` is a pure def — NOT a tied
/// accumulator (contrast `encode_smlal`); see `has_tied_def_use` in
/// trust-cg-opt/effects.rs.
///
/// Bit layout: `0 Q U 01110 size 1 Rm opcode(0001) 00 Rn Rd` with `size=10`
/// (source element = S/32-bit), `opcode=0001` (xADDW — `0000` would be
/// UADDL/SADDL, which widens BOTH operands and reads the WRONG `Vn` lanes,
/// verified distinct: uaddl.2d = 0x2EA20020 vs uaddw.2d = 0x2EA21020), `Q` =
/// low(0)/high(1), `U` = 1 (unsigned; `U=0` is SADDW, a sign-extending
/// MISCOMPILE for lanes >= 2^31 — the signed form is a SEPARATE opcode with its
/// own faithful proof, see [`encode_saddw`], and each proof's sign-confusion
/// control refutes the other). Base words (Rm=Rn=Rd=0): UADDW 0x2EA01000,
/// UADDW2 0x6EA01000.
///
/// Only the `.4S -> .2D` input arrangement the neon_array widening abs-sum
/// (TRACK D) emits is accepted; anything else is rejected fail-closed (no proof
/// credit exists for it).
///
/// Verified against the assembler (`clang -c -target arm64-apple-macos` +
/// `otool -tvj`):
///   `uaddw.2d  v0,v1,v2`    = 0x2EA21020   `uaddw2.2d v0,v1,v2`    = 0x6EA21020
///   `uaddw.2d  v31,v30,v29` = 0x2EBD13DF   `uaddw2.2d v31,v30,v29` = 0x6EBD13DF
///   `uaddw.2d  v5,v20,v11`  = 0x2EAB1285   `uaddw2.2d v7,v3,v9`    = 0x6EA91067
/// (base `| (Rm<<16) | (Rn<<5) | Rd`).
///
/// Reference: ARM DDI 0487, C7.2.350 UADDW/UADDW2.
pub fn encode_uaddw(
    in_arr: VectorArrangement,
    high: bool,
    rm: u8,
    rn: u8,
    rd: u8,
) -> Result<u32, NeonEncodeError> {
    check_reg(rm)?;
    check_reg(rn)?;
    check_reg(rd)?;
    match in_arr {
        VectorArrangement::S4 => {}
        _ => return Err(NeonEncodeError::InvalidSize(in_arr.size() as u8)),
    }
    let base = 0x2EA0_1000 | (if high { 1 } else { 0 } << 30);
    Ok(base | ((rm as u32) << 16) | ((rn as u32) << 5) | (rd as u32))
}

/// Encode `SADDW/SADDW2 Vd.2D, Vn.2D, Vm.<2S|4S>` — SIGNED widening add-WIDE
/// (Advanced SIMD three different), the signed sibling of [`encode_uaddw`].
/// Each of the two i64 output lanes is the i64 addend lane of `Vn` plus a
/// SIGN-extended source `.4S` lane of `Vm`:
/// `Vd.d[j] = Vn.d[j] + sext64(Vm.4S[base+j])` where `base = 0` for the LOW
/// form (`high=false`, SADDW, lanes {0,1}) and `base = 2` for the HIGH form
/// (`high=true`, SADDW2, lanes {2,3}). The ISA's plain THREE-OPERAND form: the
/// addend is the SEPARATE source register `Vn`, `Vd` is a pure def — NOT a
/// tied accumulator (contrast `encode_smlal`); see `has_tied_def_use` in
/// trust-cg-opt/effects.rs.
///
/// Bit layout: `0 Q U 01110 size 1 Rm opcode(0001) 00 Rn Rd` with `size=10`
/// (source element = S/32-bit), `opcode=0001` (xADDW — `0000` would be
/// SADDL/UADDL, which widens BOTH operands and reads the WRONG `Vn` lanes,
/// verified distinct: saddl.2d = 0x0EA20020 vs saddw.2d = 0x0EA21020), `Q` =
/// low(0)/high(1), `U` = 0 (SIGNED; `U=1` is UADDW, a zero-extending
/// MISCOMPILE for every negative lane — the unsigned form is the SEPARATE
/// [`encode_uaddw`], each with its own faithful proof and a sign-confusion
/// refute control against the other, verified distinct: uaddw.2d =
/// 0x2EA21020). Base words (Rm=Rn=Rd=0): SADDW 0x0EA01000, SADDW2 0x4EA01000.
///
/// Only the `.4S -> .2D` input arrangement the neon_predsum widening i64-acc
/// condsum emits is accepted; anything else is rejected fail-closed (no proof
/// credit exists for it).
///
/// Verified against the assembler (`clang -c -target arm64-apple-macos` +
/// `otool -tvj`):
///   `saddw.2d  v0,v1,v2`    = 0x0EA21020   `saddw2.2d v0,v1,v2`    = 0x4EA21020
///   `saddw.2d  v31,v30,v29` = 0x0EBD13DF   `saddw2.2d v31,v30,v29` = 0x4EBD13DF
///   `saddw.2d  v5,v20,v11`  = 0x0EAB1285   `saddw2.2d v7,v3,v9`    = 0x4EA91067
/// (base `| (Rm<<16) | (Rn<<5) | Rd`).
///
/// Reference: ARM DDI 0487, C7.2.207 SADDW/SADDW2.
pub fn encode_saddw(
    in_arr: VectorArrangement,
    high: bool,
    rm: u8,
    rn: u8,
    rd: u8,
) -> Result<u32, NeonEncodeError> {
    check_reg(rm)?;
    check_reg(rn)?;
    check_reg(rd)?;
    match in_arr {
        VectorArrangement::S4 => {}
        _ => return Err(NeonEncodeError::InvalidSize(in_arr.size() as u8)),
    }
    let base = 0x0EA0_1000 | (if high { 1 } else { 0 } << 30);
    Ok(base | ((rm as u32) << 16) | ((rn as u32) << 5) | (rd as u32))
}

/// Encode `MLA Vd.4S, Vn.4S, Vm.4S` — vector integer multiply-ACCUMULATE
/// (Advanced SIMD three same): per 32-bit lane
/// `Vd[i] = Vd[i] + Vn[i]*Vm[i]` (mod 2^32 — the low 32 bits of the product,
/// the same truncating multiply as `MUL.4S`, added into the PRIOR value of
/// `Vd`). `Vd` is BOTH source and destination (the accumulator) — modeled by
/// `has_tied_def_use` in trust-cg-opt/effects.rs (the UDOT/xMLAL class, NOT
/// the three-operand UADDW class).
///
/// Bit layout: `0 Q U 01110 size 1 Rm opcode(10010) 1 Rn Rd` with `Q=1`
/// (128-bit), `size=10` (S/32-bit lanes), `opcode=10010` (MLA — `10011` would
/// be MUL, a NON-accumulating MISCOMPILE that drops the running sum, verified
/// distinct: mul.4s = 0x4EA29C20 vs mla.4s = 0x4EA29420), `U=0` (MLA — `U=1`
/// is MLS, a SUBTRACTING miscompile that negates every contribution, verified
/// distinct: mls.4s = 0x6EA29420). Base word (Rm=Rn=Rd=0): 0x4EA09400.
///
/// Only the `.4S` arrangement the neon_predsum MLA-by-mask condsum accumulate
/// emits is accepted; anything else is rejected fail-closed (no proof credit
/// exists for it).
///
/// Verified against the assembler (`clang -c -target arm64-apple-macos` +
/// `otool -tvj`):
///   `mla.4s v0, v1, v2`    = 0x4EA29420   `mla.4s v31, v30, v29` = 0x4EBD97DF
///   `mla.4s v5, v20, v11`  = 0x4EAB9685   `mla.4s v7, v3, v9`    = 0x4EA99467
/// (base `| (Rm<<16) | (Rn<<5) | Rd`).
///
/// Reference: ARM DDI 0487, C7.2.200 MLA (vector).
pub fn encode_mla(arr: VectorArrangement, rm: u8, rn: u8, rd: u8) -> Result<u32, NeonEncodeError> {
    check_reg(rm)?;
    check_reg(rn)?;
    check_reg(rd)?;
    match arr {
        VectorArrangement::S4 => {}
        _ => return Err(NeonEncodeError::InvalidSize(arr.size() as u8)),
    }
    Ok(0x4EA0_9400 | ((rm as u32) << 16) | ((rn as u32) << 5) | (rd as u32))
}

/// Encode `UADALP Vd.2D, Vn.4S` — UNSIGNED pairwise widening ACCUMULATE
/// (Advanced SIMD two-register miscellaneous): each of the two i64 output
/// lanes accumulates the sum of a ZERO-extended adjacent source-lane pair:
/// `Vd.d[j] = Vd.d[j] + zext64(Vn.4S[2j]) + zext64(Vn.4S[2j+1])` (mod 2^64).
/// `Vd` is BOTH source and destination (the accumulator) — modeled by
/// `has_tied_def_use` in trust-cg-opt/effects.rs (the UDOT/xMLAL class;
/// CONTRAST the non-accumulating `encode_uaddlp`, whose Vd is a pure def).
///
/// Bit layout: `0 Q U 01110 size 10000 opcode(00110) 10 Rn Rd` with `Q=1`
/// (128-bit), `size=10` (source element = S/32-bit), `opcode=00110` (UADALP —
/// `00010` would be UADDLP, a NON-accumulating MISCOMPILE that drops the
/// running sum, verified distinct: uaddlp.2d = 0x6EA02820 vs uadalp.2d =
/// 0x6EA06820), `U=1` (unsigned — `U=0` is SADALP, a SIGN-extending
/// MISCOMPILE for source lanes >= 2^31, exactly the abs-sum's `i32::MIN`
/// lanes; verified distinct: sadalp.2d = 0x4EA06820). Base word (Rn=Rd=0):
/// 0x6EA06800.
///
/// Only the `.4S -> .2D` input arrangement the neon_array widening abs-sum
/// (TRACK D) emits is accepted; anything else is rejected fail-closed (no
/// proof credit exists for it).
///
/// Verified against the assembler (`clang -c -target arm64-apple-macos` +
/// `otool -tvj`):
///   `uadalp v0.2d, v1.4s`  = 0x6EA06820   `uadalp v31.2d, v30.4s` = 0x6EA06BDF
///   `uadalp v5.2d, v20.4s` = 0x6EA06A85   `uadalp v7.2d, v3.4s`   = 0x6EA06867
/// (base `| (Rn<<5) | Rd`).
///
/// Reference: ARM DDI 0487, C7.2.346 UADALP.
pub fn encode_uadalp(in_arr: VectorArrangement, rn: u8, rd: u8) -> Result<u32, NeonEncodeError> {
    check_reg(rn)?;
    check_reg(rd)?;
    match in_arr {
        VectorArrangement::S4 => {}
        _ => return Err(NeonEncodeError::InvalidSize(in_arr.size() as u8)),
    }
    Ok(0x6EA0_6800 | ((rn as u32) << 5) | (rd as u32))
}

/// Encode `EXT Vd.16B, Vn.16B, Vm.16B, #imm` — byte-wise extract/concatenate:
/// the result is bytes `imm .. imm+15` of the 32-byte concatenation `Vm:Vn`
/// (`Vn` supplies the LOW bytes, `Vm` the HIGH — operand ORDER is load-bearing:
/// `Vd.byte[j] = if j+imm < 16 then Vn.byte[j+imm] else Vm.byte[j+imm-16]`).
/// Swapping `Rn`/`Rm` selects the complementary window — a classic silent
/// miscompile — so the field placement is pinned by asymmetric exact-byte
/// vectors below AND by the swapped-operand SMT refute control
/// (trust-cg-verify/neon_lowering_proofs.rs).
///
/// The accepted byte shifts are the whole-i32-lane shifts `#4 / #8 / #12` the
/// stencil vectorizer emits, plus the SINGLE-byte shifts `#1` and `#15` the
/// neon-bytesum stencil count-if emits to form its shifted-neighbor stream
/// (`#1` = `a[iv+1]` window, `#15` = `a[iv-1]` window). Every other immediate
/// (including the valid-in-hardware `#0 / #2 / #3 / ...`) is REJECTED —
/// fail-closed: no proof credit exists for them. Only the `Q=1` (`.16B`) form.
///
/// Verified against the assembler (`clang -c` + `otool -t`; llvm-mc absent):
///   `ext v0.16b,  v1.16b,  v2.16b,  #1`  = `0x6E020820`
///   `ext v0.16b,  v1.16b,  v2.16b,  #4`  = `0x6E022020`
///   `ext v0.16b,  v1.16b,  v2.16b,  #8`  = `0x6E024020`
///   `ext v0.16b,  v1.16b,  v2.16b,  #12` = `0x6E026020`
///   `ext v0.16b,  v1.16b,  v2.16b,  #15` = `0x6E027820`
///   `ext v31.16b, v30.16b, v29.16b, #1`  = `0x6E1D0BDF`   (high reg numbers)
///   `ext v31.16b, v30.16b, v29.16b, #12` = `0x6E1D63DF`   (high reg numbers)
///   `ext v17.16b, v0.16b,  v31.16b, #4`  = `0x6E1F2011`
///   `ext v17.16b, v0.16b,  v31.16b, #15` = `0x6E1F7811`   (asymmetric)
///   `ext v5.16b,  v20.16b, v11.16b, #8`  = `0x6E0B4285`
/// (base `0x6E00_0000` | (Rm<<16) | (imm4<<11) | (Rn<<5) | Rd).
///
/// Reference: ARM DDI 0487, C7.2.116 EXT.
pub fn encode_ext(imm: i64, rm: u8, rn: u8, rd: u8) -> Result<u32, NeonEncodeError> {
    check_reg(rm)?;
    check_reg(rn)?;
    check_reg(rd)?;
    match imm {
        1 | 4 | 8 | 12 | 15 => {}
        _ => return Err(NeonEncodeError::InvalidExtImmediate(imm)),
    }
    Ok(0x6E00_0000 | ((rm as u32) << 16) | ((imm as u32) << 11) | ((rn as u32) << 5) | (rd as u32))
}

// ---------------------------------------------------------------------------
// Across-lanes integer reductions: UMAXV
// ARM ARM: Advanced SIMD across lanes
//
//   0 | Q | U | 01110 | size(2) | 11000 | opcode(5) | 10 | Rn(5) | Rd(5)
//
// UMAXV.4S uses Q=1, U=1, size=10, opcode=01010 and writes an S register.
// ---------------------------------------------------------------------------

/// Encode `UMAXV Sd, Vn.4S`.
///
/// This is the reduction used for horizontal-any over `CMEQ.4S` masks:
/// unsigned max across four `u32` lanes produces either `0xFFFF_FFFF` or `0`.
pub fn encode_umaxv_4s(rn: u8, rd: u8) -> Result<u32, NeonEncodeError> {
    check_reg(rn)?;
    check_reg(rd)?;

    Ok((1 << 30)       // Q = 1 (Vn.4S)
        | (1 << 29)    // U = 1 (unsigned max)
        | (0b01110 << 24)
        | (0b10 << 22) // size = S lanes
        | (0b11000 << 17)
        | (0b01010 << 12)
        | (0b10 << 10)
        | ((rn as u32) << 5)
        | (rd as u32))
}

/// Encode `ADDP Dd, Vn.2D`.
///
/// This pairwise-add scalar form is the 64-bit horizontal sum needed to reduce
/// a two-lane i64 vector before feeding an ordered scalar subtract accumulator.
pub fn encode_addp_scalar_2d(rn: u8, rd: u8) -> Result<u32, NeonEncodeError> {
    check_reg(rn)?;
    check_reg(rd)?;

    Ok((1 << 30)        // Q = 1 (Vn.2D)
        | (0b11110 << 24)
        | (0b11 << 22)  // size = D lanes
        | (0b11000 << 17)
        | (0b11011 << 12)
        | (0b10 << 10)
        | ((rn as u32) << 5)
        | (rd as u32))
}

// ---------------------------------------------------------------------------
// Three-register same: FP vector arithmetic (FADD, FSUB, FMUL, FDIV)
// ARM ARM: Advanced SIMD three same (FP)
//
//   0 | Q | U | 01110 | 0 | sz | 1 | Rm(5) | opcode(3) | 0 | 1 | Rn(5) | Rd(5)
//
// FADD: U=0, opcode=11010 → bits[15:11] = 11010
// FSUB: U=0, opcode=11010 → same but U=1
// Actually per ARM ARM:
//   FADD: 0|Q|0|01110|0|sz|1|Rm|110101|Rn|Rd
//   FSUB: 0|Q|0|01110|1|sz|1|Rm|110101|Rn|Rd
//   FMUL: 0|Q|1|01110|0|sz|1|Rm|110111|Rn|Rd
//   FDIV: 0|Q|1|01110|0|sz|1|Rm|111111|Rn|Rd
// ---------------------------------------------------------------------------

/// FP vector three-register-same operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FpVec3Op {
    /// FADD vector
    Fadd,
    /// FSUB vector
    Fsub,
    /// FMUL vector
    Fmul,
    /// FDIV vector
    Fdiv,
    /// FCMGT (register) vector — ordered greater-than per-lane mask.
    Fcmgt,
    /// FMLA (vector) — fused multiply-accumulate `Vd += Vn*Vm` (single rounding).
    Fmla,
    /// FMLS (vector) — fused multiply-subtract `Vd -= Vn*Vm` (single rounding).
    Fmls,
}

impl FpVec3Op {
    /// Returns (U, bit23, opcode_bits[15:10]) for encoding.
    ///
    /// The FP three-same encoding uses:
    ///   bit 29 = U, bit 23 = extra distinguisher, bits [15:10] = opcode|1
    fn u_bit23_opcode(self) -> (u32, u32, u32) {
        match self {
            //               U    bit23  bits[15:10]
            Self::Fadd => (0, 0, 0b110101),
            Self::Fsub => (0, 1, 0b110101),
            Self::Fmul => (1, 0, 0b110111),
            Self::Fdiv => (1, 0, 0b111111),
            // FCMGT (register): U=1, E(bit23)=1, opcode 111001
            // (FCMEQ is U=0/E=0 and FCMGE is U=1/E=0 on the same opcode bits —
            // the (U, E) pair is the load-bearing discriminator).
            // ARM ARM: C7.2.96 FCMGT (register, vector).
            Self::Fcmgt => (1, 1, 0b111001),
            // FMLA (vector): U=0, E(bit23)=0, opcode 110011.
            //   fmla v0.2d, v1.2d, v2.2d = 0x4E60CC00 base (verified below).
            // ARM ARM: C7.2.104 FMLA (vector).
            Self::Fmla => (0, 0, 0b110011),
            // FMLS (vector): U=0, E(bit23)=1, opcode 110011 (the E bit is the
            // add/sub discriminator, exactly like FADD vs FSUB).
            //   fmls v0.2d, v1.2d, v2.2d = 0x4EE0CC00 base.
            // ARM ARM: C7.2.106 FMLS (vector).
            Self::Fmls => (0, 1, 0b110011),
        }
    }
}

/// Encode a NEON per-lane integer-to-FP conversion (`UCVTF`/`SCVTF`, vector,
/// integer form) — advanced-SIMD two-register-miscellaneous.
///
/// Format: `0 | Q | U | 01110 | 0 | sz | 10000 | 11101 | 10 | Rn(5) | Rd(5)`
/// where `U=0` → SCVTF (signed), `U=1` → UCVTF (unsigned), and `sz` (bit 22)
/// selects single (`0`, `.4S`) vs double (`1`, `.2D`) lanes.
///
/// Verified against the assembler (`clang -c` + `objdump -d`):
///   `scvtf v0.2d, v1.2d` = `0x4E61D820`   (base `0x4E61D800`)
///   `ucvtf v0.2d, v1.2d` = `0x6E61D820`   (base `0x6E61D800`)
///   `scvtf v0.4s, v1.4s` = `0x4E21D820`   (base `0x4E21D800`)
///   `ucvtf v0.4s, v1.4s` = `0x6E21D820`   (base `0x6E21D800`)
/// (base | (Rn<<5) | Rd). Only the `.2D`/`.4S` forms are accepted; any other
/// arrangement is REJECTED (fail-closed — no proof credit exists for it).
///
/// Reference: ARM DDI 0487, C7.2.297 UCVTF / C7.2.271 SCVTF (vector, integer).
pub fn encode_fp_int_cvt_vec(
    arr: FpVectorArrangement,
    signed: bool,
    rn: u8,
    rd: u8,
) -> Result<u32, NeonEncodeError> {
    check_reg(rn)?;
    check_reg(rd)?;
    let base = match (arr, signed) {
        (FpVectorArrangement::D2, true) => 0x4E61_D800,
        (FpVectorArrangement::D2, false) => 0x6E61_D800,
        (FpVectorArrangement::S4, true) => 0x4E21_D800,
        (FpVectorArrangement::S4, false) => 0x6E21_D800,
        (FpVectorArrangement::S2, _) => {
            let (_, sz) = arr.q_sz();
            return Err(NeonEncodeError::InvalidSize(sz as u8));
        }
    };
    Ok(base | ((rn as u32) << 5) | (rd as u32))
}

/// Encode a NEON `f32 -> f64` widening convert (`FCVTL`/`FCVTL2`, vector) —
/// advanced-SIMD two-register-miscellaneous, "FP convert to higher precision,
/// long".
///
/// Format: `0 | Q | 0 | 01110 | 0 | sz | 10000 | 10111 | 10 | Rn(5) | Rd(5)`,
/// with `sz=1` selecting the `f32→f64` (`.2S/.4S -> .2D`) widening and `Q`
/// selecting `FCVTL` (`Q=0`, reads the LOW 64 bits, `Vn.2S`) vs `FCVTL2`
/// (`Q=1`, reads the HIGH 64 bits, `Vn.4S`). The output is always `Vd.2D`.
///
/// Verified against the assembler (`clang -c` + `objdump -d`):
///   `fcvtl  v0.2d, v1.2s`  = `0x0E617820`   (base `0x0E617800`)
///   `fcvtl2 v0.2d, v1.4s`  = `0x4E617820`   (base `0x4E617800`)
///   `fcvtl  v3.2d, v5.2s`  = `0x0E6178A3`
///   `fcvtl2 v7.2d, v9.4s`  = `0x4E617927`
/// (base | (Rn<<5) | Rd). Only the `f32→f64` (`sz=1`) widening is emitted; the
/// `f16→f32` form (`sz=0`) has no proof credit and is not produced here.
///
/// Reference: ARM DDI 0487, C7.2.98 FCVTL, FCVTL2 (vector).
pub fn encode_fcvtl_vec(high: bool, rn: u8, rd: u8) -> Result<u32, NeonEncodeError> {
    check_reg(rn)?;
    check_reg(rd)?;
    // sz=1 (f32->f64). FCVTL: Q=0 -> base 0x0E617800; FCVTL2: Q=1 -> 0x4E617800.
    let base = if high { 0x4E61_7800 } else { 0x0E61_7800 };
    Ok(base | ((rn as u32) << 5) | (rd as u32))
}

/// Encode `DUP Dd, Vn.D[lane]` — copy one 64-bit FP lane of a `.2D` vector into
/// a SCALAR `Dd` register (assembler `MOV Dd, Vn.D[lane]`). SIMD scalar copy
/// (advanced-SIMD scalar "DUP (element)"):
/// `01 | 0 | 11110000 | imm5(5) | 0 | 0000 | 1 | Rn(5) | Rd(5)` with the D-lane
/// `imm5 = (lane << 4) | 0b01000` (lane 0 → `01000`, lane 1 → `11000`).
///
/// Verified against the assembler:
///   `mov d16, v5.d[1]` = `0x5E1804B0`   (imm5=11000, Rn=5, Rd=16)
/// (base `0x5E000400` | (imm5<<16) | (Rn<<5) | Rd). Only lanes 0 and 1 are
/// accepted (a `.2D` register has exactly two 64-bit lanes).
///
/// Reference: ARM DDI 0487, C7.2.85 DUP (element) — scalar variant.
pub fn encode_dup_scalar_d(lane: u8, rn: u8, rd: u8) -> Result<u32, NeonEncodeError> {
    check_reg(rn)?;
    check_reg(rd)?;
    if lane > 1 {
        return Err(NeonEncodeError::InvalidLane { lane });
    }
    let imm5: u32 = ((lane as u32) << 4) | 0b01000;
    Ok(0x5E00_0400 | (imm5 << 16) | ((rn as u32) << 5) | (rd as u32))
}

/// Encode a NEON FP three-register-same instruction.
///
/// Format: `0 | Q | U | 01110 | bit23 | sz | 1 | Rm(5) | opcode(6) | Rn(5) | Rd(5)`
///
/// ARM ARM: C7.2.93 (FADD vector), C7.2.118 (FSUB vector),
///          C7.2.114 (FMUL vector), C7.2.97 (FDIV vector)
pub fn encode_fp_vec3_same(
    arr: FpVectorArrangement,
    op: FpVec3Op,
    rm: u8,
    rn: u8,
    rd: u8,
) -> Result<u32, NeonEncodeError> {
    check_reg(rm)?;
    check_reg(rn)?;
    check_reg(rd)?;

    let (q, sz) = arr.q_sz();
    let (u, bit23, opcode) = op.u_bit23_opcode();

    Ok((q << 30)
        | (u << 29)
        | (0b01110 << 24)
        | (bit23 << 23)
        | (sz << 22)
        | (1 << 21)
        | ((rm as u32) << 16)
        | (opcode << 10)
        | ((rn as u32) << 5)
        | (rd as u32))
}

/// Encode `FMLA (by element)` / `FMLS (by element)` — FP vector fused
/// multiply-accumulate/-subtract reading a SINGLE broadcast lane `Vm.Ts[lane]`
/// of the second source: `Vd.T[i] = Vd.T[i] ± Vn.T[i] * Vm.Ts[lane]` (SINGLE
/// rounding, `Vd` tied). The multiplier is one fixed lane of `Vm` broadcast
/// across all lanes — the shape clang emits for `y[i] += da*x[i]` with the
/// scalar invariant `da` kept in a lane (no `DUP`).
///
/// Advanced-SIMD "vector x indexed element":
/// `0 | Q | 0 | 01111 | size(2) | L | M | Rm(4) | opcode(4) | H | 0 | Rn(5) | Rd(5)`
/// with `size=10` (single `.4S`, index = `H:L`, 0..3) or `size=11` (double
/// `.2D`, index = `H`, `L=0`, 0..1); `opcode=0001` (FMLA) / `0101` (FMLS — the
/// `E`-bit polarity, exactly FADD vs FSUB); `Vm` is `M:Rm` so any V0..V31 (the
/// high register bit is the `M` bit). `Q=1` always (both accepted forms are
/// 128-bit).
///
/// Verified against the assembler (`clang -c` + `objdump -d`):
///   `fmla.4s  v0, v1, v2[0]`    = `0x4F821020`   (base `0x4F801000`)
///   `fmla.4s  v0, v1, v2[1]`    = `0x4FA21020`   (L=1, bit21)
///   `fmla.4s  v0, v1, v2[2]`    = `0x4F821820`   (H=1, bit11)
///   `fmla.4s  v0, v1, v2[3]`    = `0x4FA21820`   (H:L = 1:1)
///   `fmla.2d  v0, v1, v2[0]`    = `0x4FC21020`   (base `0x4FC01000`)
///   `fmla.2d  v0, v1, v2[1]`    = `0x4FC21820`   (H=1)
///   `fmla.4s  v5, v6, v20[3]`   = `0x4FB418C5`   (M=1 => Vm=20)
///   `fmla.2d  v7, v8, v17[1]`   = `0x4FD11907`   (M=1 => Vm=17)
///   `fmls.4s  v0, v1, v2[2]`    = `0x4F825820`   (opcode 0101)
///   `fmla.4s  v31, v30, v15[1]` = `0x4FAF13DF`
/// (base | (L<<21) | (M<<20) | (Rm_lo<<16) | (opcode<<12) | (H<<11) | (Rn<<5) | Rd).
/// Only `.4S`/`.2D` are accepted; any other arrangement or out-of-range lane is
/// REJECTED (fail-closed — no proof credit exists for it).
///
/// Reference: ARM DDI 0487, C7.2.105 FMLA (by element) / C7.2.107 FMLS (by element).
pub fn encode_fmla_lane(
    arr: FpVectorArrangement,
    fmls: bool,
    lane: u8,
    rm: u8,
    rn: u8,
    rd: u8,
) -> Result<u32, NeonEncodeError> {
    check_reg(rm)?;
    check_reg(rn)?;
    check_reg(rd)?;
    // size field (bits[23:22]) + index-bit split. Single (.4S): index = H:L,
    // lanes 0..3, M is a genuine register bit. Double (.2D): index = H, L=0,
    // lanes 0..1.
    let (size, h, l) = match arr {
        FpVectorArrangement::S4 => {
            if lane > 3 {
                return Err(NeonEncodeError::InvalidLane { lane });
            }
            (0b10u32, ((lane >> 1) & 1) as u32, (lane & 1) as u32)
        }
        FpVectorArrangement::D2 => {
            if lane > 1 {
                return Err(NeonEncodeError::InvalidLane { lane });
            }
            (0b11u32, (lane & 1) as u32, 0u32)
        }
        FpVectorArrangement::S2 => {
            // 64-bit `.2S` by-element FMLA is neither emitted nor proven.
            let (_, sz) = arr.q_sz();
            return Err(NeonEncodeError::InvalidSize(sz as u8));
        }
    };
    let m = ((rm >> 4) & 1) as u32;
    let rm_lo = (rm & 0xF) as u32;
    let opcode = if fmls { 0b0101u32 } else { 0b0001u32 };
    Ok(
        (1 << 30)          // Q = 1 (128-bit); bit 31 = 0, bit 29 (U) = 0
        | (0b01111 << 24)
        | (size << 22)
        | (l << 21)
        | (m << 20)
        | (rm_lo << 16)
        | (opcode << 12)
        | (h << 11)
        | ((rn as u32) << 5)
        | (rd as u32),
    )
}

// ---------------------------------------------------------------------------
// DUP (element, scalar to vector)
// ARM ARM C7.2.82: DUP (element)
//
//   0 | Q | 0 | 01110000 | imm5(5) | 0 | 0000 | 1 | Rn(5) | Rd(5)
//
// imm5 encodes which lane and element size:
//   B: imm5 = xxxx1, H: imm5 = xxx10, S: imm5 = xx100, D: imm5 = x1000
// DUP (general): duplicates a GPR into all vector lanes
//   0 | Q | 0 | 01110000 | imm5(5) | 0 | 0001 | 1 | Rn(5) | Rd(5)
// ---------------------------------------------------------------------------

/// Element size for DUP / INS operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ElementSize {
    B = 1, // imm5[0] = 1
    H = 2, // imm5[1:0] = 10
    S = 4, // imm5[2:0] = 100
    D = 8, // imm5[3:0] = 1000
}

/// Encode DUP (element) - duplicate a vector element to all lanes.
///
/// `lane` specifies which element of `Rn` to duplicate.
///
/// ARM ARM C7.2.82
pub fn encode_dup_element(
    q: u32,
    elem: ElementSize,
    lane: u8,
    rn: u8,
    rd: u8,
) -> Result<u32, NeonEncodeError> {
    check_reg(rn)?;
    check_reg(rd)?;

    let imm5 = match elem {
        ElementSize::B => ((lane as u32) << 1) | 0b1,
        ElementSize::H => ((lane as u32) << 2) | 0b10,
        ElementSize::S => ((lane as u32) << 3) | 0b100,
        ElementSize::D => ((lane as u32) << 4) | 0b1000,
    };

    if imm5 > 0b11111 {
        return Err(NeonEncodeError::InvalidLane { lane });
    }

    // DUP (element): 0|Q|0|01110000|imm5|0|0000|1|Rn|Rd
    Ok(((q << 30) | (0b001110000 << 21) | (imm5 << 16))
        | (1 << 10)
        | ((rn as u32) << 5)
        | (rd as u32))
}

/// Encode DUP (general) - duplicate a GPR value to all vector lanes.
///
/// ARM ARM C7.2.83
pub fn encode_dup_general(
    q: u32,
    elem: ElementSize,
    rn: u8,
    rd: u8,
) -> Result<u32, NeonEncodeError> {
    check_reg(rn)?;
    check_reg(rd)?;

    let imm5: u32 = match elem {
        ElementSize::B => 0b00001,
        ElementSize::H => 0b00010,
        ElementSize::S => 0b00100,
        ElementSize::D => 0b01000,
    };

    // DUP (general): 0|Q|0|01110000|imm5|0|0001|1|Rn|Rd
    Ok(((q << 30) | (0b001110000 << 21) | (imm5 << 16))
        | (0b0001 << 11)
        | (1 << 10)
        | ((rn as u32) << 5)
        | (rd as u32))
}

// ---------------------------------------------------------------------------
// INS (element, insert from GPR)
// ARM ARM C7.2.152: INS (general)
//
//   0 | 1 | 0 | 01110000 | imm5(5) | 0 | 0011 | 1 | Rn(5) | Rd(5)
//
// imm5 encodes the destination lane + element size.
// ---------------------------------------------------------------------------

/// Encode INS (general) - insert a GPR value into a vector lane.
///
/// ARM ARM C7.2.152
pub fn encode_ins_general(
    elem: ElementSize,
    lane: u8,
    rn: u8,
    rd: u8,
) -> Result<u32, NeonEncodeError> {
    check_reg(rn)?;
    check_reg(rd)?;

    let imm5 = match elem {
        ElementSize::B => ((lane as u32) << 1) | 0b1,
        ElementSize::H => ((lane as u32) << 2) | 0b10,
        ElementSize::S => ((lane as u32) << 3) | 0b100,
        ElementSize::D => ((lane as u32) << 4) | 0b1000,
    };

    if imm5 > 0b11111 {
        return Err(NeonEncodeError::InvalidLane { lane });
    }

    // INS (general): 0|1|0|01110000|imm5|0|0011|1|Rn|Rd
    // Q=1 always for INS (operates on full 128-bit register)
    Ok(((1 << 30) | (0b01110000 << 21) | (imm5 << 16))
        | (0b0011 << 11)
        | (1 << 10)
        | ((rn as u32) << 5)
        | (rd as u32))
}

/// Encode UMOV (general) - extract a vector lane into a GPR.
///
/// Supports `UMOV Wd, Vn.B/H/S[lane]` and `UMOV Xd, Vn.D[lane]`.
///
/// ARM ARM C7.2.334
pub fn encode_umov_general(
    elem: ElementSize,
    lane: u8,
    rn: u8,
    rd: u8,
) -> Result<u32, NeonEncodeError> {
    check_reg(rn)?;
    check_reg(rd)?;

    let (q, imm5) = match elem {
        ElementSize::B => (0, ((lane as u32) << 1) | 0b00001),
        ElementSize::H => (0, ((lane as u32) << 2) | 0b00010),
        ElementSize::S => (0, ((lane as u32) << 3) | 0b00100),
        ElementSize::D => (1, ((lane as u32) << 4) | 0b01000),
    };
    if imm5 > 0b11111 {
        return Err(NeonEncodeError::InvalidLane { lane });
    }

    // UMOV Wd/Xd, Vn.B/H/S/D[lane]: 0|Q|0|01110000|imm5|0|0111|1|Rn|Rd
    Ok((q << 30)
        | (0b001110000 << 21)
        | (imm5 << 16)
        | (0b0111 << 11)
        | (1 << 10)
        | ((rn as u32) << 5)
        | (rd as u32))
}

// ---------------------------------------------------------------------------
// MOVI (move immediate to vector)
// ARM ARM C7.2.207: MOVI
//
// Simplified 8-bit immediate form (cmode = 1110, op = 0):
//   0 | Q | op | 0111100000 | abc(3) | cmode(4) | 01 | defgh(5) | Rd(5)
//
// The 8-bit immediate is split: abc = imm8[7:5], defgh = imm8[4:0]
// Full byte-replication: MOVI Vd.{8B,16B}, #imm8
// ---------------------------------------------------------------------------

/// Encode MOVI (vector, 8-bit immediate replicated to all byte lanes).
///
/// This encodes the simplest MOVI form: `MOVI Vd.{8B,16B}, #imm8`
/// using cmode=1110, op=0 (byte mask / 8-bit immediate to all bytes).
///
/// ARM ARM C7.2.207
pub fn encode_movi_byte(q: u32, imm8: u8, rd: u8) -> Result<u32, NeonEncodeError> {
    check_reg(rd)?;

    let abc = ((imm8 as u32) >> 5) & 0b111;
    let defgh = (imm8 as u32) & 0b11111;

    // MOVI (byte): 0|Q|op=0|0111100000|abc|cmode=1110|o2=0|1|defgh|Rd
    Ok((q << 30)        // op = 0
        | (0b0111100000 << 19)
        | (abc << 16)
        | (0b1110 << 12)     // cmode = 1110 (byte mask)
        | (0b01 << 10)
        | (defgh << 5)
        | (rd as u32))
}

// ---------------------------------------------------------------------------
// Advanced SIMD shift by immediate: SHL, USHR, SSHR
// ARM ARM C7-2 "Advanced SIMD shift by immediate"
//
//   0 | Q | U | 011110 | immh(4) | immb(3) | opcode(5) | 1 | Rn(5) | Rd(5)
//
// `immh:immb` (7 bits) jointly encode the element size and the shift amount.
// The element-size class is selected by the most-significant set bit of immh:
//   immh = 0001    -> 8-bit  lanes (esize = 8)
//   immh = 001x    -> 16-bit lanes (esize = 16)
//   immh = 01xx    -> 32-bit lanes (esize = 32)
//   immh = 1xxx    -> 64-bit lanes (esize = 64)
// For a *left* shift (SHL):      immh:immb = esize + shift,    shift in [0, esize-1]
// For a *right* shift (USHR/SSHR): immh:immb = 2*esize - shift, shift in [1, esize]
//
//   SHL:  U=0, opcode=01010
//   USHR: U=1, opcode=00000
//   SSHR: U=0, opcode=00000
//
// Encodings independently checked against the system assembler
// (clang -target aarch64; objdump -d) for the 4S arrangement across the
// full immediate range — see the `shift_imm_*` unit tests below.
// ---------------------------------------------------------------------------

/// NEON SIMD shift-by-immediate operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VecShiftImmOp {
    /// SHL Vd.T, Vn.T, #shift — left shift (U=0, opcode=01010).
    Shl,
    /// USHR Vd.T, Vn.T, #shift — unsigned (logical) right shift (U=1, opcode=00000).
    Ushr,
    /// SSHR Vd.T, Vn.T, #shift — signed (arithmetic) right shift (U=0, opcode=00000).
    Sshr,
}

impl VecShiftImmOp {
    /// Returns (U, opcode) for the instruction.
    fn u_opcode(self) -> (u32, u32) {
        match self {
            Self::Shl => (0, 0b01010),
            Self::Ushr => (1, 0b00000),
            Self::Sshr => (0, 0b00000),
        }
    }

    /// Whether this is a right shift (uses the `2*esize - shift` immediate form).
    fn is_right_shift(self) -> bool {
        matches!(self, Self::Ushr | Self::Sshr)
    }
}

/// Element size (in bits) for the integer arrangement of a shift-by-immediate.
fn shift_esize_bits(arr: VectorArrangement) -> u32 {
    match arr {
        VectorArrangement::B8 | VectorArrangement::B16 => 8,
        VectorArrangement::H4 | VectorArrangement::H8 => 16,
        VectorArrangement::S2 | VectorArrangement::S4 => 32,
        VectorArrangement::D2 => 64,
    }
}

/// Encode a NEON Advanced-SIMD shift-by-immediate instruction (SHL/USHR/SSHR).
///
/// `shift` is the lane shift amount. The hardware does not encode a 0-count
/// right shift (its `2*esize - shift` immediate would alias the next larger
/// element size), and rejects out-of-range counts; both fail closed here so a
/// bad count is never silently re-encoded as a different element width.
///
/// Format: `0 | Q | U | 011110 | immh(4) | immb(3) | opcode(5) | 1 | Rn(5) | Rd(5)`
///
/// ARM ARM: C7.2.x SHL / USHR / SSHR (vector, immediate).
pub fn encode_vec_shift_imm(
    arr: VectorArrangement,
    op: VecShiftImmOp,
    shift: u32,
    rn: u8,
    rd: u8,
) -> Result<u32, NeonEncodeError> {
    check_reg(rn)?;
    check_reg(rd)?;

    let esize = shift_esize_bits(arr);
    let immhb = if op.is_right_shift() {
        // Right shift: count in [1, esize]; encoded as 2*esize - shift.
        if shift == 0 || shift > esize {
            return Err(NeonEncodeError::InvalidShiftAmount {
                shift,
                esize,
                op: "right",
            });
        }
        2 * esize - shift
    } else {
        // Left shift (SHL): count in [0, esize-1]; encoded as esize + shift.
        if shift >= esize {
            return Err(NeonEncodeError::InvalidShiftAmount {
                shift,
                esize,
                op: "left",
            });
        }
        esize + shift
    };
    // `immh:immb` occupies the 7-bit field [22:16]. The construction above keeps
    // it within [1, 2*esize-1] (<= 127 for esize<=64), so it always fits.
    debug_assert!(immhb <= 0x7F, "immh:immb out of range: {immhb:#x}");

    let (q, _size) = arr.q_size();
    let (u, opcode) = op.u_opcode();

    Ok((q << 30)
        | (u << 29)
        | (0b011110 << 23)
        | (immhb << 16)
        | (opcode << 11)
        | (1 << 10)
        | ((rn as u32) << 5)
        | (rd as u32))
}

// ---------------------------------------------------------------------------
// LD1 / ST1 (single structure, post-index)
// ARM ARM C7.2.167: LD1 (single structure)
// ARM ARM C7.2.282: ST1 (single structure)
//
// No-offset (single, 1 register):
//   0 | Q | 0011000 | L | 0 | 00000 | opcode(4) | size(2) | Rn(5) | Rt(5)
//   L=1 for LD1, L=0 for ST1
//
// Post-index (single, 1 register, immediate):
//   0 | Q | 0011001 | L | 0 | 11111 | opcode(4) | size(2) | Rn(5) | Rt(5)
//   The post-index immediate = 8 (for 8B) or 16 (for 16B), etc.
//
// For multiple structures, the encoding differs. We use the simple
// single-register form: LD1 {Vt.T}, [Xn], #bytes
// ---------------------------------------------------------------------------

/// Encode LD1 (single structure, 1 register, post-index by immediate).
///
/// `arr` determines the vector arrangement and post-index amount.
///
/// ARM ARM C7.2.167
pub fn encode_ld1_post_imm(arr: VectorArrangement, rn: u8, rt: u8) -> Result<u32, NeonEncodeError> {
    check_reg(rn)?;
    check_reg(rt)?;

    let (q, size) = arr.q_size();

    // LD1 single register, post-index immediate:
    // 0|Q|0011001|L=1|0|11111|opcode=0111|size|Rn|Rt
    Ok(((q << 30)
        | (0b0011001 << 23)
        | (1 << 22))
        | (0b11111 << 16)   // Rm = 11111 (immediate post-index)
        | (0b0111 << 12)    // opcode = 0111 (1 register)
        | (size << 10)
        | ((rn as u32) << 5)
        | (rt as u32))
}

/// Encode ST1 (single structure, 1 register, post-index by immediate).
///
/// ARM ARM C7.2.282
pub fn encode_st1_post_imm(arr: VectorArrangement, rn: u8, rt: u8) -> Result<u32, NeonEncodeError> {
    check_reg(rn)?;
    check_reg(rt)?;

    let (q, size) = arr.q_size();

    // ST1 single register, post-index immediate:
    // 0|Q|0011001|L=0|0|11111|opcode=0111|size|Rn|Rt
    Ok(((q << 30)
        | (0b0011001 << 23))
        | (0b11111 << 16)   // Rm = 11111 (immediate post-index)
        | (0b0111 << 12)    // opcode = 0111 (1 register)
        | (size << 10)
        | ((rn as u32) << 5)
        | (rt as u32))
}

// ---------------------------------------------------------------------------
// LDP (SIMD&FP, 128-bit Q pair, post-index)
// ARM ARM C7.2.190: LDP (SIMD&FP)
//
// Post-index (Q form):
//   opc(2)=10 | 101 | V=1 | 001 | L=1 | imm7(7) | Rt2(5) | Rn(5) | Rt(5)
//   = 0xACC00000 | imm7<<15 | Rt2<<10 | Rn<<5 | Rt
//   imm7 is the byte offset scaled by 16 (Q granule), signed 7-bit.
//
// This is the SIMD&FP form ONLY (V bit set, opc=0b10 selects Q). The integer
// LDP pair forms live in encoding_mem.rs; keeping this Q-pair encoder separate
// and V-hardwired prevents the prior P0 class where a hardcoded GPR pair form
// clobbered FPR pairs.
// ---------------------------------------------------------------------------

/// Encode `LDP Qt1, Qt2, [Xn], #offset` — load pair of 128-bit SIMD&FP
/// registers, post-index writeback (`Qt1 = [Xn]`, `Qt2 = [Xn + 16]`,
/// `Xn += offset`).
///
/// `offset` is the raw byte offset; it must be a multiple of 16 with
/// `offset/16` in the signed 7-bit range. `rt == rt2` is architecturally
/// UNPREDICTABLE for load pairs and is rejected (fail-closed).
///
/// Verified against llvm-mc (`-triple=aarch64 -show-encoding`):
/// `ldp q0, q1, [x0], #32` == `0xACC10400` (bytes `00 04 c1 ac`).
pub fn encode_ldp_q_post_imm(offset: i64, rt2: u8, rn: u8, rt: u8) -> Result<u32, NeonEncodeError> {
    check_reg(rt)?;
    check_reg(rt2)?;
    check_reg(rn)?;
    if rt == rt2 {
        return Err(NeonEncodeError::LdpDuplicateDest(rt));
    }
    // Range-check the i64 quotient BEFORE narrowing (mirrors the fail-closed
    // scaled_pair_imm7 guards in encode.rs): a `& 0x7F` mask on an unchecked
    // value would silently truncate an out-of-range offset into a DIFFERENT
    // in-range one — a silent miscompile, not an error.
    if offset % 16 != 0 {
        return Err(NeonEncodeError::InvalidLdpQPostOffset(offset));
    }
    let imm7 = offset / 16;
    if !(-64..=63).contains(&imm7) {
        return Err(NeonEncodeError::InvalidLdpQPostOffset(offset));
    }
    let imm7_bits = (imm7 as i32 as u32) & 0x7F;

    Ok(0xACC0_0000 | (imm7_bits << 15) | ((rt2 as u32) << 10) | ((rn as u32) << 5) | (rt as u32))
}

// ---------------------------------------------------------------------------
// STP (SIMD&FP, 128-bit Q pair, post-index)
// ARM ARM C7.2.331: STP (SIMD&FP)
//
// Post-index (Q form) — IDENTICAL to LDP (above) with the L bit CLEAR (bit 22):
//   opc(2)=10 | 101 | V=1 | 001 | L=0 | imm7(7) | Rt2(5) | Rn(5) | Rt(5)
//   = 0xAC80_0000 | imm7<<15 | Rt2<<10 | Rn<<5 | Rt
//   imm7 is the byte offset scaled by 16 (Q granule), signed 7-bit.
//
// This is the SIMD&FP form ONLY (V bit set, opc=0b10 selects Q). The integer
// STP pair forms live in encoding_mem.rs; keeping this Q-pair encoder separate
// and V-hardwired prevents the LdpQPost P0 class where a hardcoded GPR pair
// form (V=0) would clobber FPR pairs.
// ---------------------------------------------------------------------------

/// Encode `STP Qt1, Qt2, [Xn], #offset` — store pair of 128-bit SIMD&FP
/// registers, post-index writeback (`[Xn] = Qt1`, `[Xn + 16] = Qt2`,
/// `Xn += offset`).
///
/// `offset` is the raw byte offset; it must be a multiple of 16 with
/// `offset/16` in the signed 7-bit range. Unlike LDP, `rt == rt2` is NOT
/// UNPREDICTABLE for stores (both source registers are read, storing the same
/// value twice) — so it is permitted; the vectorizers never emit it.
///
/// Verified against clang -c + objdump (`arm64-apple-macos`):
/// `stp q0, q1, [x0], #32` == `0xAC810400` (bytes `00 04 81 ac`) — exactly the
/// `ldp q0, q1, [x0], #32` == `0xACC10400` encoding with the L bit (0x40_0000)
/// cleared. The V bit (0x400_0000) STAYS SET (SIMD&FP form).
pub fn encode_stp_q_post_imm(offset: i64, rt2: u8, rn: u8, rt: u8) -> Result<u32, NeonEncodeError> {
    check_reg(rt)?;
    check_reg(rt2)?;
    check_reg(rn)?;
    // Range-check the i64 quotient BEFORE narrowing (mirrors LDP): a `& 0x7F`
    // mask on an unchecked value would silently truncate an out-of-range offset
    // into a DIFFERENT in-range one — a silent miscompile, not an error.
    if offset % 16 != 0 {
        return Err(NeonEncodeError::InvalidStpQPostOffset(offset));
    }
    let imm7 = offset / 16;
    if !(-64..=63).contains(&imm7) {
        return Err(NeonEncodeError::InvalidStpQPostOffset(offset));
    }
    let imm7_bits = (imm7 as i32 as u32) & 0x7F;

    Ok(0xAC80_0000 | (imm7_bits << 15) | ((rt2 as u32) << 10) | ((rn as u32) << 5) | (rt as u32))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // === Integer vector arithmetic ===

    #[test]
    fn test_add_vec_4s() {
        // ADD V0.4S, V1.4S, V2.4S
        // Q=1, U=0, size=10, opcode=10000
        // 0|1|0|01110|10|1|00010|10000|1|00001|00000
        let enc = encode_int_vec3_same(VectorArrangement::S4, IntVec3Op::Add, 2, 1, 0).unwrap();
        assert_eq!(enc & (0b111 << 29), 0b010 << 29, "Q=1,U=0");
        assert_eq!((enc >> 24) & 0b11111, 0b01110);
        assert_eq!((enc >> 22) & 0b11, 0b10, "size=10");
        assert_eq!((enc >> 21) & 1, 1);
        assert_eq!((enc >> 16) & 0b11111, 2, "Rm=2");
        assert_eq!((enc >> 11) & 0b11111, 0b10000, "opcode=10000");
        assert_eq!((enc >> 10) & 1, 1);
        assert_eq!((enc >> 5) & 0b11111, 1, "Rn=1");
        assert_eq!(enc & 0b11111, 0, "Rd=0");
    }

    #[test]
    fn test_sub_vec_8h() {
        // SUB V3.8H, V4.8H, V5.8H
        let enc = encode_int_vec3_same(VectorArrangement::H8, IntVec3Op::Sub, 5, 4, 3).unwrap();
        assert_eq!((enc >> 30) & 1, 1, "Q=1");
        assert_eq!((enc >> 29) & 1, 1, "U=1 for SUB");
        assert_eq!((enc >> 22) & 0b11, 0b01, "size=01 for H");
        assert_eq!((enc >> 11) & 0b11111, 0b10000, "opcode=10000");
    }

    #[test]
    fn test_mul_vec_4s() {
        // MUL V0.4S, V1.4S, V2.4S
        let enc = encode_int_vec3_same(VectorArrangement::S4, IntVec3Op::Mul, 2, 1, 0).unwrap();
        assert_eq!((enc >> 29) & 1, 0, "U=0 for MUL");
        assert_eq!((enc >> 11) & 0b11111, 0b10011, "opcode=10011 for MUL");
    }

    #[test]
    fn test_add_vec_16b() {
        // ADD V0.16B, V1.16B, V2.16B
        let enc = encode_int_vec3_same(VectorArrangement::B16, IntVec3Op::Add, 2, 1, 0).unwrap();
        assert_eq!((enc >> 30) & 1, 1, "Q=1 for 16B");
        assert_eq!((enc >> 22) & 0b11, 0b00, "size=00 for B");
    }

    #[test]
    fn test_sub_vec_8b() {
        // SUB V0.8B, V1.8B, V2.8B
        let enc = encode_int_vec3_same(VectorArrangement::B8, IntVec3Op::Sub, 2, 1, 0).unwrap();
        assert_eq!((enc >> 30) & 1, 0, "Q=0 for 8B");
        assert_eq!((enc >> 29) & 1, 1, "U=1 for SUB");
    }

    #[test]
    fn test_add_vec_2d() {
        // ADD V10.2D, V11.2D, V12.2D
        let enc = encode_int_vec3_same(VectorArrangement::D2, IntVec3Op::Add, 12, 11, 10).unwrap();
        assert_eq!((enc >> 30) & 1, 1, "Q=1 for 2D");
        assert_eq!((enc >> 22) & 0b11, 0b11, "size=11 for D");
        assert_eq!((enc >> 16) & 0b11111, 12);
        assert_eq!((enc >> 5) & 0b11111, 11);
        assert_eq!(enc & 0b11111, 10);
    }

    // === Compare ===

    #[test]
    fn test_cmeq_vec_4s() {
        // CMEQ V0.4S, V1.4S, V2.4S
        let enc = encode_int_vec3_same(VectorArrangement::S4, IntVec3Op::Cmeq, 2, 1, 0).unwrap();
        assert_eq!((enc >> 29) & 1, 1, "U=1 for CMEQ");
        assert_eq!((enc >> 11) & 0b11111, 0b10001, "opcode for CMEQ");
    }

    #[test]
    fn test_cmgt_vec_4s() {
        let enc = encode_int_vec3_same(VectorArrangement::S4, IntVec3Op::Cmgt, 2, 1, 0).unwrap();
        assert_eq!((enc >> 29) & 1, 0, "U=0 for CMGT");
        assert_eq!((enc >> 11) & 0b11111, 0b00110, "opcode for CMGT");
    }

    #[test]
    fn test_cmge_vec_4s() {
        let enc = encode_int_vec3_same(VectorArrangement::S4, IntVec3Op::Cmge, 2, 1, 0).unwrap();
        assert_eq!((enc >> 29) & 1, 0, "U=0 for CMGE");
        assert_eq!((enc >> 11) & 0b11111, 0b00111, "opcode for CMGE");
    }

    #[test]
    fn test_unsigned_compare_vec_4s() {
        let cmhi = encode_int_vec3_same(VectorArrangement::S4, IntVec3Op::Cmhi, 2, 1, 0).unwrap();
        assert_eq!((cmhi >> 29) & 1, 1, "U=1 for CMHI");
        assert_eq!((cmhi >> 11) & 0b11111, 0b00110, "opcode for CMHI");
        assert_eq!(cmhi, 0x6EA2_3420, "CMHI V0.4S, V1.4S, V2.4S");

        let cmhs = encode_int_vec3_same(VectorArrangement::S4, IntVec3Op::Cmhs, 5, 4, 3).unwrap();
        assert_eq!((cmhs >> 29) & 1, 1, "U=1 for CMHS");
        assert_eq!((cmhs >> 11) & 0b11111, 0b00111, "opcode for CMHS");
        assert_eq!(cmhs, 0x6EA5_3C83, "CMHS V3.4S, V4.4S, V5.4S");
    }

    // === Vector logic ===

    #[test]
    fn test_and_vec() {
        // AND V0.16B, V1.16B, V2.16B
        let enc = encode_vec_logic(1, VecLogicOp::And, 2, 1, 0).unwrap();
        assert_eq!((enc >> 29) & 1, 0, "U=0 for AND");
        assert_eq!((enc >> 22) & 0b11, 0b00, "size=00 for AND");
        assert_eq!((enc >> 11) & 0b11111, 0b00011, "opcode=00011");
    }

    #[test]
    fn test_orr_vec() {
        let enc = encode_vec_logic(1, VecLogicOp::Orr, 2, 1, 0).unwrap();
        assert_eq!((enc >> 22) & 0b11, 0b10, "size=10 for ORR");
    }

    #[test]
    fn test_eor_vec() {
        let enc = encode_vec_logic(1, VecLogicOp::Eor, 2, 1, 0).unwrap();
        assert_eq!((enc >> 29) & 1, 1, "U=1 for EOR");
        assert_eq!((enc >> 22) & 0b11, 0b00, "size=00 for EOR");
    }

    #[test]
    fn test_bic_vec() {
        let enc = encode_vec_logic(1, VecLogicOp::Bic, 2, 1, 0).unwrap();
        assert_eq!((enc >> 22) & 0b11, 0b01, "size=01 for BIC");
    }

    // === NOT ===

    #[test]
    fn test_not_vec_16b() {
        // NOT V0.16B, V1.16B
        let enc = encode_vec_not(1, 1, 0).unwrap();
        assert_eq!((enc >> 30) & 1, 1, "Q=1");
        assert_eq!((enc >> 29) & 1, 1, "U=1");
        assert_eq!((enc >> 12) & 0b11111, 0b00101, "opcode=00101");
        assert_eq!((enc >> 5) & 0b11111, 1, "Rn=1");
        assert_eq!(enc & 0b11111, 0, "Rd=0");
    }

    // === RBIT / REV byte two-register ===

    #[test]
    fn test_rbit_vec_8b_exact_bits() {
        let enc = encode_vec_byte_2reg(VectorArrangement::B8, VecByte2Op::Rbit, 1, 0).unwrap();
        assert_eq!(enc, 0x2E60_5820, "RBIT V0.8B, V1.8B = {enc:#010X}");
    }

    #[test]
    fn test_rbit_vec_16b_exact_bits() {
        let enc = encode_vec_byte_2reg(VectorArrangement::B16, VecByte2Op::Rbit, 3, 2).unwrap();
        assert_eq!(enc, 0x6E60_5862, "RBIT V2.16B, V3.16B = {enc:#010X}");
    }

    #[test]
    fn test_rev32_vec_8b_exact_bits() {
        let enc = encode_vec_byte_2reg(VectorArrangement::B8, VecByte2Op::Rev32, 5, 4).unwrap();
        assert_eq!(enc, 0x2E20_08A4, "REV32 V4.8B, V5.8B = {enc:#010X}");
    }

    #[test]
    fn test_rev64_vec_16b_exact_bits() {
        let enc = encode_vec_byte_2reg(VectorArrangement::B16, VecByte2Op::Rev64, 7, 6).unwrap();
        assert_eq!(enc, 0x4E20_08E6, "REV64 V6.16B, V7.16B = {enc:#010X}");
    }

    // === FCVTL / FCVTL2 (f32->f64 widening convert) ===

    #[test]
    fn test_fcvtl_exact_bits() {
        // `fcvtl v0.2d, v1.2s` = 0x0E617820 (assembler-verified).
        assert_eq!(encode_fcvtl_vec(false, 1, 0).unwrap(), 0x0E61_7820);
        // `fcvtl v3.2d, v5.2s` = 0x0E6178A3.
        assert_eq!(encode_fcvtl_vec(false, 5, 3).unwrap(), 0x0E61_78A3);
        // `fcvtl v2.2d, v0.2s` = 0x0E617802.
        assert_eq!(encode_fcvtl_vec(false, 0, 2).unwrap(), 0x0E61_7802);
    }

    #[test]
    fn test_fcvtl2_exact_bits() {
        // `fcvtl2 v0.2d, v1.4s` = 0x4E617820 (assembler-verified).
        assert_eq!(encode_fcvtl_vec(true, 1, 0).unwrap(), 0x4E61_7820);
        // `fcvtl2 v7.2d, v9.4s` = 0x4E617927.
        assert_eq!(encode_fcvtl_vec(true, 9, 7).unwrap(), 0x4E61_7927);
    }

    #[test]
    fn test_fcvtl_only_q_bit_differs() {
        // FCVTL vs FCVTL2 differ ONLY in the Q bit (bit 30) — the low/high-half
        // selector. Everything else is identical.
        let lo = encode_fcvtl_vec(false, 5, 3).unwrap();
        let hi = encode_fcvtl_vec(true, 5, 3).unwrap();
        assert_eq!(hi ^ lo, 1 << 30, "FCVTL/FCVTL2 differ only in Q (bit 30)");
    }

    #[test]
    fn test_fcvtl_rejects_bad_reg() {
        assert!(encode_fcvtl_vec(false, 32, 0).is_err());
        assert!(encode_fcvtl_vec(true, 0, 32).is_err());
    }

    #[test]
    fn test_byte_2reg_rejects_non_byte_arrangement() {
        assert!(matches!(
            encode_vec_byte_2reg(VectorArrangement::S4, VecByte2Op::Rbit, 1, 0),
            Err(NeonEncodeError::InvalidSize(2))
        ));
    }

    // === Population count / add-long-pairwise (popcount fold) ===

    #[test]
    fn test_cnt_16b_exact_bits() {
        // `cnt v0.16b, v1.16b` = 0x4E205820 (assembler-verified).
        assert_eq!(
            encode_cnt(VectorArrangement::B16, 1, 0).unwrap(),
            0x4E20_5820
        );
        // `cnt v3.16b, v7.16b` = 0x4E2058E3.
        assert_eq!(
            encode_cnt(VectorArrangement::B16, 7, 3).unwrap(),
            0x4E20_58E3
        );
    }

    #[test]
    fn test_cnt_8b_exact_bits() {
        // `cnt v0.8b, v1.8b` = 0x0E205820 (Q=0 form).
        assert_eq!(
            encode_cnt(VectorArrangement::B8, 1, 0).unwrap(),
            0x0E20_5820
        );
    }

    #[test]
    fn test_cnt_rejects_non_byte_arrangement() {
        assert!(matches!(
            encode_cnt(VectorArrangement::S4, 1, 0),
            Err(NeonEncodeError::InvalidSize(_))
        ));
    }

    #[test]
    fn test_uaddlp_16b_to_8h_exact_bits() {
        // `uaddlp v0.8h, v1.16b` = 0x6E202820 (assembler-verified, size=00).
        assert_eq!(
            encode_uaddlp(VectorArrangement::B16, 1, 0).unwrap(),
            0x6E20_2820
        );
        assert_eq!(
            encode_uaddlp(VectorArrangement::B16, 7, 3).unwrap(),
            0x6E20_28E3
        );
    }

    #[test]
    fn test_uaddlp_8h_to_4s_exact_bits() {
        // `uaddlp v0.4s, v1.8h` = 0x6E602820 (assembler-verified, size=01).
        assert_eq!(
            encode_uaddlp(VectorArrangement::H8, 1, 0).unwrap(),
            0x6E60_2820
        );
        assert_eq!(
            encode_uaddlp(VectorArrangement::H8, 7, 3).unwrap(),
            0x6E60_28E3
        );
    }

    #[test]
    fn test_uaddlp_rejects_unsupported_arrangement() {
        // Only the 16B->8H and 8H->4S widening pairs the popcount fold uses.
        assert!(matches!(
            encode_uaddlp(VectorArrangement::S4, 1, 0),
            Err(NeonEncodeError::InvalidSize(_))
        ));
        assert!(matches!(
            encode_uaddlp(VectorArrangement::B8, 1, 0),
            Err(NeonEncodeError::InvalidSize(_))
        ));
    }

    #[test]
    fn test_saddlp_16b_to_8h_exact_bits() {
        // `saddlp v0.8h, v1.16b` = 0x4E202820 (llvm-mc-verified, size=00, U=0).
        assert_eq!(
            encode_saddlp(VectorArrangement::B16, 1, 0).unwrap(),
            0x4E20_2820
        );
        // `saddlp v3.8h, v7.16b` = 0x4E2028E3 (llvm-mc-verified).
        assert_eq!(
            encode_saddlp(VectorArrangement::B16, 7, 3).unwrap(),
            0x4E20_28E3
        );
    }

    #[test]
    fn test_saddlp_8h_to_4s_exact_bits() {
        // `saddlp v0.4s, v1.8h` = 0x4E602820 (llvm-mc-verified, size=01, U=0).
        assert_eq!(
            encode_saddlp(VectorArrangement::H8, 1, 0).unwrap(),
            0x4E60_2820
        );
        // `saddlp v3.4s, v7.8h` = 0x4E6028E3 (llvm-mc-verified).
        assert_eq!(
            encode_saddlp(VectorArrangement::H8, 7, 3).unwrap(),
            0x4E60_28E3
        );
    }

    #[test]
    fn test_saddlp_differs_from_uaddlp_only_in_u_bit() {
        // SIGN-CONFUSION pin: SADDLP (U=0) and UADDLP (U=1) must differ in
        // EXACTLY bit 29 — encoding either as the other is the classic
        // signedness miscompile this test makes structurally impossible.
        let s = encode_saddlp(VectorArrangement::B16, 1, 0).unwrap();
        let u = encode_uaddlp(VectorArrangement::B16, 1, 0).unwrap();
        assert_eq!(s ^ u, 1 << 29);
    }

    #[test]
    fn test_saddlp_rejects_unsupported_arrangement() {
        // Only the 16B->8H and 8H->4S widening pairs the sext reductions use.
        assert!(matches!(
            encode_saddlp(VectorArrangement::S4, 1, 0),
            Err(NeonEncodeError::InvalidSize(_))
        ));
        assert!(matches!(
            encode_saddlp(VectorArrangement::B8, 1, 0),
            Err(NeonEncodeError::InvalidSize(_))
        ));
    }

    #[test]
    fn test_bit_16b_exact_bits() {
        // llvm-mc-verified:
        //   bit v0.16b, v1.16b, v2.16b  = 0x6EA21C20
        //   bit v3.16b, v7.16b, v16.16b = 0x6EB01CE3
        // and DISTINCT from BSL (0x6E621C20) / BIF (0x6EE21C20) — the size
        // field is the operand-wiring selector in this family, so pinning the
        // exact bytes pins the wiring.
        assert_eq!(
            encode_vec_logic(1, VecLogicOp::Bit, 2, 1, 0).unwrap(),
            0x6EA2_1C20
        );
        assert_eq!(
            encode_vec_logic(1, VecLogicOp::Bit, 16, 7, 3).unwrap(),
            0x6EB0_1CE3
        );
    }

    // === .2D ISA-legality fail-closed rejections (three-register-same) ===

    #[test]
    fn test_int_vec3_rejects_2d_mul_and_minmax() {
        // Baseline NEON has NO `.2D` integer MUL or SMAX/SMIN/UMAX/UMIN
        // (size==11 RESERVED; llvm-mc rejects `mul/smax v0.2d, ...`). The
        // encoder must fail closed rather than emit an UNALLOCATED word.
        for op in [
            IntVec3Op::Mul,
            IntVec3Op::Smax,
            IntVec3Op::Smin,
            IntVec3Op::Umax,
            IntVec3Op::Umin,
        ] {
            assert!(
                matches!(
                    encode_int_vec3_same(VectorArrangement::D2, op, 2, 1, 0),
                    Err(NeonEncodeError::InvalidSize(_))
                ),
                "{op:?}.2D must be rejected (unallocated in the ISA)"
            );
        }
    }

    #[test]
    fn test_int_vec3_2d_add_sub_cmp_exact_bits() {
        // llvm-mc-verified `.2D` forms (all ALLOCATED at size==11):
        //   add  v0.2d, v1.2d, v2.2d = 0x4EE28420
        //   sub  v0.2d, v1.2d, v2.2d = 0x6EE28420
        //   cmeq v0.2d, v1.2d, v2.2d = 0x6EE28C20
        //   cmgt v0.2d, v1.2d, v2.2d = 0x4EE23420
        //   cmge v0.2d, v1.2d, v2.2d = 0x4EE23C20
        //   cmhi v0.2d, v1.2d, v2.2d = 0x6EE23420
        //   cmhs v0.2d, v1.2d, v2.2d = 0x6EE23C20
        let d2 = VectorArrangement::D2;
        assert_eq!(
            encode_int_vec3_same(d2, IntVec3Op::Add, 2, 1, 0).unwrap(),
            0x4EE2_8420
        );
        assert_eq!(
            encode_int_vec3_same(d2, IntVec3Op::Sub, 2, 1, 0).unwrap(),
            0x6EE2_8420
        );
        assert_eq!(
            encode_int_vec3_same(d2, IntVec3Op::Cmeq, 2, 1, 0).unwrap(),
            0x6EE2_8C20
        );
        assert_eq!(
            encode_int_vec3_same(d2, IntVec3Op::Cmgt, 2, 1, 0).unwrap(),
            0x4EE2_3420
        );
        assert_eq!(
            encode_int_vec3_same(d2, IntVec3Op::Cmge, 2, 1, 0).unwrap(),
            0x4EE2_3C20
        );
        assert_eq!(
            encode_int_vec3_same(d2, IntVec3Op::Cmhi, 2, 1, 0).unwrap(),
            0x6EE2_3420
        );
        assert_eq!(
            encode_int_vec3_same(d2, IntVec3Op::Cmhs, 2, 1, 0).unwrap(),
            0x6EE2_3C20
        );
    }

    #[test]
    fn test_vec_shift_imm_2d_exact_bits() {
        // llvm-mc-verified `.2D` immediate shifts:
        //   shl  v0.2d, v1.2d, #3 = 0x4F435420
        //   ushr v0.2d, v1.2d, #5 = 0x6F7B0420
        //   sshr v0.2d, v1.2d, #7 = 0x4F790420
        let d2 = VectorArrangement::D2;
        assert_eq!(
            encode_vec_shift_imm(d2, VecShiftImmOp::Shl, 3, 1, 0).unwrap(),
            0x4F43_5420
        );
        assert_eq!(
            encode_vec_shift_imm(d2, VecShiftImmOp::Ushr, 5, 1, 0).unwrap(),
            0x6F7B_0420
        );
        assert_eq!(
            encode_vec_shift_imm(d2, VecShiftImmOp::Sshr, 7, 1, 0).unwrap(),
            0x4F79_0420
        );
    }

    // === Per-lane signed absolute value (abs-sum fold) ===

    #[test]
    fn test_abs_4s_exact_bits() {
        // Assembler-verified (`clang -c` + `otool -t`):
        //   abs v0.4s,  v1.4s  = 0x4EA0B820
        //   abs v3.4s,  v7.4s  = 0x4EA0B8E3
        //   abs v31.4s, v31.4s = 0x4EA0BBFF
        //   abs v0.4s,  v0.4s  = 0x4EA0B800
        assert_eq!(
            encode_abs(VectorArrangement::S4, 1, 0).unwrap(),
            0x4EA0_B820
        );
        assert_eq!(
            encode_abs(VectorArrangement::S4, 7, 3).unwrap(),
            0x4EA0_B8E3
        );
        assert_eq!(
            encode_abs(VectorArrangement::S4, 31, 31).unwrap(),
            0x4EA0_BBFF
        );
        assert_eq!(
            encode_abs(VectorArrangement::S4, 0, 0).unwrap(),
            0x4EA0_B800
        );
    }

    #[test]
    fn test_abs_rejects_non_4s_arrangement() {
        // The abs-sum lowering only emits (and only proves) the `.4S` form.
        for arr in [
            VectorArrangement::B8,
            VectorArrangement::B16,
            VectorArrangement::H4,
            VectorArrangement::H8,
            VectorArrangement::S2,
            VectorArrangement::D2,
        ] {
            assert!(matches!(
                encode_abs(arr, 1, 0),
                Err(NeonEncodeError::InvalidSize(_))
            ));
        }
    }

    // === Unsigned dot-product accumulate (UDOT, FEAT_DotProd) ===

    #[test]
    fn test_udot_4s_exact_bits() {
        // Assembler-verified (`clang -c -march=armv8.2-a+dotprod` + `objdump -d`):
        //   udot v0.4s,  v1.16b,  v2.16b  = 0x6E829420
        //   udot v3.4s,  v7.16b,  v9.16b  = 0x6E8994E3
        //   udot v31.4s, v30.16b, v29.16b = 0x6E9D97DF   (high reg numbers)
        //   udot v17.4s, v0.16b,  v31.16b = 0x6E9F9411
        //   udot v5.4s,  v20.16b, v11.16b = 0x6E8B9685
        assert_eq!(
            encode_udot(VectorArrangement::B16, 2, 1, 0).unwrap(),
            0x6E82_9420
        );
        assert_eq!(
            encode_udot(VectorArrangement::B16, 9, 7, 3).unwrap(),
            0x6E89_94E3
        );
        assert_eq!(
            encode_udot(VectorArrangement::B16, 29, 30, 31).unwrap(),
            0x6E9D_97DF
        );
        assert_eq!(
            encode_udot(VectorArrangement::B16, 31, 0, 17).unwrap(),
            0x6E9F_9411
        );
        assert_eq!(
            encode_udot(VectorArrangement::B16, 11, 20, 5).unwrap(),
            0x6E8B_9685
        );
    }

    #[test]
    fn test_udot_is_not_sdot() {
        // The U bit (29) distinguishes UDOT from SDOT: `sdot v0.4s, v1.16b,
        // v2.16b` = 0x4E829420 (assembler-verified). Emitting SDOT would
        // SIGN-extend the bytes — a miscompile for byte values >= 0x80. Pin
        // that the encoder's output has bit 29 SET (unsigned form).
        let enc = encode_udot(VectorArrangement::B16, 2, 1, 0).unwrap();
        assert_ne!(enc, 0x4E82_9420, "must not encode the SDOT form");
        assert_eq!(
            enc & (1 << 29),
            1 << 29,
            "U bit (29) must be set: UDOT, not SDOT"
        );
    }

    #[test]
    fn test_udot_rejects_non_16b_arrangement() {
        // The ctpop-reduction lowering only emits (and only proves) the
        // `.16B -> .4S` form.
        for arr in [
            VectorArrangement::B8,
            VectorArrangement::H4,
            VectorArrangement::H8,
            VectorArrangement::S2,
            VectorArrangement::S4,
            VectorArrangement::D2,
        ] {
            assert!(matches!(
                encode_udot(arr, 2, 1, 0),
                Err(NeonEncodeError::InvalidSize(_))
            ));
        }
    }

    // === Widening multiply-accumulate-long (SMLAL/SMLAL2/UMLAL/UMLAL2) ===

    #[test]
    fn test_smlal_2d_exact_bits() {
        // Assembler-verified (`clang -c -target arm64-apple-macos` + `otool -tvj`);
        // operand order encode_smlal(in_arr, high, signed, rm=Vm, rn=Vn, rd=Vd):
        //   smlal.2d  v0,v1,v2    = 0x0EA28020   smlal2.2d v0,v1,v2    = 0x4EA28020
        //   umlal.2d  v0,v1,v2    = 0x2EA28020   umlal2.2d v0,v1,v2    = 0x6EA28020
        //   smlal.2d  v31,v30,v29 = 0x0EBD83DF   smlal2.2d v31,v30,v29 = 0x4EBD83DF
        //   smlal.2d  v5,v20,v11  = 0x0EAB8285   smlal2.2d v7,v3,v9    = 0x4EA98067
        use VectorArrangement::S4;
        // SMLAL (low, signed): Q=0, U=0.
        assert_eq!(encode_smlal(S4, false, true, 2, 1, 0).unwrap(), 0x0EA2_8020);
        assert_eq!(
            encode_smlal(S4, false, true, 29, 30, 31).unwrap(),
            0x0EBD_83DF
        );
        assert_eq!(
            encode_smlal(S4, false, true, 11, 20, 5).unwrap(),
            0x0EAB_8285
        );
        // SMLAL2 (high, signed): Q=1, U=0.
        assert_eq!(encode_smlal(S4, true, true, 2, 1, 0).unwrap(), 0x4EA2_8020);
        assert_eq!(
            encode_smlal(S4, true, true, 29, 30, 31).unwrap(),
            0x4EBD_83DF
        );
        assert_eq!(encode_smlal(S4, true, true, 9, 3, 7).unwrap(), 0x4EA9_8067);
        // UMLAL (low, unsigned): Q=0, U=1.
        assert_eq!(
            encode_smlal(S4, false, false, 2, 1, 0).unwrap(),
            0x2EA2_8020
        );
        // UMLAL2 (high, unsigned): Q=1, U=1.
        assert_eq!(encode_smlal(S4, true, false, 2, 1, 0).unwrap(), 0x6EA2_8020);
    }

    #[test]
    fn test_smlal_is_not_smull() {
        // opcode field 1000 (xMLAL, accumulate) vs 1100 (SMULL/UMULL, NO
        // accumulate). `smull.2d v0,v1,v2` = 0x0EA2C020 — emitting SMULL would
        // DROP the accumulator, a miscompile. Pin the encoder's opcode field.
        let smlal = encode_smlal(VectorArrangement::S4, false, true, 2, 1, 0).unwrap();
        assert_ne!(
            smlal, 0x0EA2_C020,
            "must not encode the SMULL (non-accumulate) form"
        );
        assert_eq!(
            smlal & (0b1111 << 12),
            0b1000 << 12,
            "opcode field must be 1000 (xMLAL)"
        );
    }

    #[test]
    fn test_smlal_rejects_non_4s_input() {
        // The widening dot only emits (and only proves) the `.4S -> .2D` form; any
        // other input arrangement must fail CLOSED.
        for arr in [
            VectorArrangement::B8,
            VectorArrangement::B16,
            VectorArrangement::H4,
            VectorArrangement::H8,
            VectorArrangement::S2,
            VectorArrangement::D2,
        ] {
            for (high, signed) in [(false, true), (true, true), (false, false), (true, false)] {
                assert!(matches!(
                    encode_smlal(arr, high, signed, 2, 1, 0),
                    Err(NeonEncodeError::InvalidSize(_))
                ));
            }
        }
    }

    // === Widening add-wide (UADDW/UADDW2) ===

    #[test]
    fn test_uaddw_2d_exact_bits() {
        // Assembler-verified (`clang -c -target arm64-apple-macos` + `otool -tvj`);
        // operand order encode_uaddw(in_arr, high, rm=Vm, rn=Vn, rd=Vd):
        //   uaddw.2d  v0,v1,v2    = 0x2EA21020   uaddw2.2d v0,v1,v2    = 0x6EA21020
        //   uaddw.2d  v31,v30,v29 = 0x2EBD13DF   uaddw2.2d v31,v30,v29 = 0x6EBD13DF
        //   uaddw.2d  v5,v20,v11  = 0x2EAB1285   uaddw2.2d v7,v3,v9    = 0x6EA91067
        use VectorArrangement::S4;
        // UADDW (low): Q=0, U=1.
        assert_eq!(encode_uaddw(S4, false, 2, 1, 0).unwrap(), 0x2EA2_1020);
        assert_eq!(encode_uaddw(S4, false, 29, 30, 31).unwrap(), 0x2EBD_13DF);
        assert_eq!(encode_uaddw(S4, false, 11, 20, 5).unwrap(), 0x2EAB_1285);
        // UADDW2 (high): Q=1, U=1.
        assert_eq!(encode_uaddw(S4, true, 2, 1, 0).unwrap(), 0x6EA2_1020);
        assert_eq!(encode_uaddw(S4, true, 29, 30, 31).unwrap(), 0x6EBD_13DF);
        assert_eq!(encode_uaddw(S4, true, 9, 3, 7).unwrap(), 0x6EA9_1067);
    }

    #[test]
    fn test_uaddw_is_not_uaddl_nor_saddw() {
        // opcode field 0001 (xADDW, wide addend Vn.2D) vs 0000 (UADDL, which
        // widens BOTH operands and would read the WRONG Vn lanes):
        // `uaddl.2d v0,v1,v2` = 0x2EA20020. And U=1 (unsigned) vs U=0 (SADDW,
        // `saddw.2d v0,v1,v2` = 0x0EA21020) — sign-extending lanes >= 2^31 is a
        // silent miscompile for the abs-sum's u32 bit patterns. Pin both fields.
        let uaddw = encode_uaddw(VectorArrangement::S4, false, 2, 1, 0).unwrap();
        assert_ne!(
            uaddw, 0x2EA2_0020,
            "must not encode the UADDL (widen-both) form"
        );
        assert_eq!(
            uaddw & (0b1111 << 12),
            0b0001 << 12,
            "opcode field must be 0001 (xADDW)"
        );
        assert_ne!(
            uaddw, 0x0EA2_1020,
            "must not encode the SADDW (sign-extending) form"
        );
        assert_eq!(uaddw & (1 << 29), 1 << 29, "U bit must be 1 (unsigned)");
    }

    #[test]
    fn test_uaddw_rejects_non_4s_input() {
        // Only the `.4S -> .2D` form is emitted (and proven); any other input
        // arrangement must fail CLOSED.
        for arr in [
            VectorArrangement::B8,
            VectorArrangement::B16,
            VectorArrangement::H4,
            VectorArrangement::H8,
            VectorArrangement::S2,
            VectorArrangement::D2,
        ] {
            for high in [false, true] {
                assert!(matches!(
                    encode_uaddw(arr, high, 2, 1, 0),
                    Err(NeonEncodeError::InvalidSize(_))
                ));
            }
        }
    }

    // === SIGNED widening add-wide (SADDW/SADDW2) ===

    #[test]
    fn test_saddw_2d_exact_bits() {
        // Assembler-verified (`clang -c -target arm64-apple-macos` + `otool -tvj`);
        // operand order encode_saddw(in_arr, high, rm=Vm, rn=Vn, rd=Vd):
        //   saddw.2d  v0,v1,v2    = 0x0EA21020   saddw2.2d v0,v1,v2    = 0x4EA21020
        //   saddw.2d  v31,v30,v29 = 0x0EBD13DF   saddw2.2d v31,v30,v29 = 0x4EBD13DF
        //   saddw.2d  v5,v20,v11  = 0x0EAB1285   saddw2.2d v7,v3,v9    = 0x4EA91067
        use VectorArrangement::S4;
        // SADDW (low): Q=0, U=0.
        assert_eq!(encode_saddw(S4, false, 2, 1, 0).unwrap(), 0x0EA2_1020);
        assert_eq!(encode_saddw(S4, false, 29, 30, 31).unwrap(), 0x0EBD_13DF);
        assert_eq!(encode_saddw(S4, false, 11, 20, 5).unwrap(), 0x0EAB_1285);
        // SADDW2 (high): Q=1, U=0.
        assert_eq!(encode_saddw(S4, true, 2, 1, 0).unwrap(), 0x4EA2_1020);
        assert_eq!(encode_saddw(S4, true, 29, 30, 31).unwrap(), 0x4EBD_13DF);
        assert_eq!(encode_saddw(S4, true, 9, 3, 7).unwrap(), 0x4EA9_1067);
    }

    #[test]
    fn test_saddw_is_not_saddl_nor_uaddw() {
        // opcode field 0001 (xADDW, wide addend Vn.2D) vs 0000 (SADDL, which
        // widens BOTH operands and would read the WRONG Vn lanes):
        // `saddl.2d v0,v1,v2` = 0x0EA20020. And U=0 (signed) vs U=1 (UADDW,
        // `uaddw.2d v0,v1,v2` = 0x2EA21020) — zero-extending a negative masked
        // lane is a silent miscompile for the condsum's i32 lanes. Pin both
        // fields.
        let saddw = encode_saddw(VectorArrangement::S4, false, 2, 1, 0).unwrap();
        assert_ne!(
            saddw, 0x0EA2_0020,
            "must not encode the SADDL (widen-both) form"
        );
        assert_eq!(
            saddw & (0b1111 << 12),
            0b0001 << 12,
            "opcode field must be 0001 (xADDW)"
        );
        assert_ne!(
            saddw, 0x2EA2_1020,
            "must not encode the UADDW (zero-extending) form"
        );
        assert_eq!(saddw & (1 << 29), 0, "U bit must be 0 (signed)");
    }

    #[test]
    fn test_saddw_rejects_non_4s_input() {
        // Only the `.4S -> .2D` form is emitted (and proven); any other input
        // arrangement must fail CLOSED.
        for arr in [
            VectorArrangement::B8,
            VectorArrangement::B16,
            VectorArrangement::H4,
            VectorArrangement::H8,
            VectorArrangement::S2,
            VectorArrangement::D2,
        ] {
            for high in [false, true] {
                assert!(matches!(
                    encode_saddw(arr, high, 2, 1, 0),
                    Err(NeonEncodeError::InvalidSize(_))
                ));
            }
        }
    }

    // === Vector multiply-accumulate (MLA.4S) ===

    #[test]
    fn test_mla_4s_exact_bits() {
        // Assembler-verified (`clang -c -target arm64-apple-macos` + `otool -tvj`);
        // operand order encode_mla(arr, rm=Vm, rn=Vn, rd=Vd):
        //   mla.4s v0, v1, v2    = 0x4EA29420   mla.4s v31, v30, v29 = 0x4EBD97DF
        //   mla.4s v5, v20, v11  = 0x4EAB9685   mla.4s v7, v3, v9    = 0x4EA99467
        use VectorArrangement::S4;
        assert_eq!(encode_mla(S4, 2, 1, 0).unwrap(), 0x4EA2_9420);
        assert_eq!(encode_mla(S4, 29, 30, 31).unwrap(), 0x4EBD_97DF);
        assert_eq!(encode_mla(S4, 11, 20, 5).unwrap(), 0x4EAB_9685);
        assert_eq!(encode_mla(S4, 9, 3, 7).unwrap(), 0x4EA9_9467);
    }

    #[test]
    fn test_mla_is_not_mls_nor_mul() {
        // U=0 (MLA, accumulating ADD) vs U=1 (MLS — SUBTRACTS every product,
        // `mls.4s v0,v1,v2` = 0x6EA29420): a silent sign-flip miscompile of the
        // whole reduction. And opcode field 10010 (MLA) vs 10011 (MUL —
        // NON-accumulating, drops the running sum, `mul.4s v0,v1,v2` =
        // 0x4EA29C20). Pin both fields.
        let mla = encode_mla(VectorArrangement::S4, 2, 1, 0).unwrap();
        assert_ne!(
            mla, 0x6EA2_9420,
            "must not encode the MLS (subtracting) form"
        );
        assert_eq!(mla & (1 << 29), 0, "U bit must be 0 (MLA, not MLS)");
        assert_ne!(
            mla, 0x4EA2_9C20,
            "must not encode the MUL (no-accumulate) form"
        );
        assert_eq!(
            (mla >> 11) & 0b11111,
            0b10010,
            "opcode field must be 10010 (MLA)"
        );
    }

    #[test]
    fn test_mla_rejects_non_4s() {
        // Only the `.4S` form is emitted (and proven); any other arrangement
        // must fail CLOSED.
        for arr in [
            VectorArrangement::B8,
            VectorArrangement::B16,
            VectorArrangement::H4,
            VectorArrangement::H8,
            VectorArrangement::S2,
            VectorArrangement::D2,
        ] {
            assert!(matches!(
                encode_mla(arr, 2, 1, 0),
                Err(NeonEncodeError::InvalidSize(_))
            ));
        }
    }

    // === Pairwise widening accumulate (UADALP .4S -> .2D) ===

    #[test]
    fn test_uadalp_2d_exact_bits() {
        // Assembler-verified (`clang -c -target arm64-apple-macos` + `otool -tvj`);
        // operand order encode_uadalp(in_arr, rn=Vn, rd=Vd):
        //   uadalp v0.2d, v1.4s  = 0x6EA06820   uadalp v31.2d, v30.4s = 0x6EA06BDF
        //   uadalp v5.2d, v20.4s = 0x6EA06A85   uadalp v7.2d, v3.4s   = 0x6EA06867
        use VectorArrangement::S4;
        assert_eq!(encode_uadalp(S4, 1, 0).unwrap(), 0x6EA0_6820);
        assert_eq!(encode_uadalp(S4, 30, 31).unwrap(), 0x6EA0_6BDF);
        assert_eq!(encode_uadalp(S4, 20, 5).unwrap(), 0x6EA0_6A85);
        assert_eq!(encode_uadalp(S4, 3, 7).unwrap(), 0x6EA0_6867);
    }

    #[test]
    fn test_uadalp_is_not_uaddlp_nor_sadalp() {
        // opcode field 00110 (UADALP, ACCUMULATING) vs 00010 (UADDLP — drops
        // the running sum, `uaddlp v0.2d,v1.4s` = 0x6EA02820): a silent
        // no-accumulate miscompile. And U=1 (unsigned) vs U=0 (SADALP,
        // `sadalp v0.2d,v1.4s` = 0x4EA06820) — sign-extending source lanes
        // >= 2^31 (exactly the abs-sum's `i32::MIN` lanes) is a silent
        // miscompile. Pin both fields.
        let uadalp = encode_uadalp(VectorArrangement::S4, 1, 0).unwrap();
        assert_ne!(
            uadalp, 0x6EA0_2820,
            "must not encode the UADDLP (no-accumulate) form"
        );
        assert_eq!(
            (uadalp >> 12) & 0b11111,
            0b00110,
            "opcode field must be 00110 (UADALP)"
        );
        assert_ne!(
            uadalp, 0x4EA0_6820,
            "must not encode the SADALP (sign-extending) form"
        );
        assert_eq!(uadalp & (1 << 29), 1 << 29, "U bit must be 1 (unsigned)");
    }

    #[test]
    fn test_uadalp_rejects_non_4s_input() {
        // Only the `.4S -> .2D` form is emitted (and proven); any other input
        // arrangement must fail CLOSED (in particular the `.16B`/`.8H` inputs
        // that ARE legal for the non-accumulating UADDLP encoder).
        for arr in [
            VectorArrangement::B8,
            VectorArrangement::B16,
            VectorArrangement::H4,
            VectorArrangement::H8,
            VectorArrangement::S2,
            VectorArrangement::D2,
        ] {
            assert!(matches!(
                encode_uadalp(arr, 1, 0),
                Err(NeonEncodeError::InvalidSize(_))
            ));
        }
    }

    // === Byte-wise extract/concatenate (EXT) ===

    #[test]
    fn test_ext_16b_exact_bits() {
        // Assembler-verified (`clang -c` + `objdump -d`):
        //   ext v0.16b,  v1.16b,  v2.16b,  #4  = 0x6E022020
        //   ext v0.16b,  v1.16b,  v2.16b,  #8  = 0x6E024020
        //   ext v0.16b,  v1.16b,  v2.16b,  #12 = 0x6E026020
        //   ext v31.16b, v30.16b, v29.16b, #12 = 0x6E1D63DF   (high reg numbers)
        //   ext v17.16b, v0.16b,  v31.16b, #4  = 0x6E1F2011
        //   ext v5.16b,  v20.16b, v11.16b, #8  = 0x6E0B4285
        assert_eq!(encode_ext(1, 2, 1, 0).unwrap(), 0x6E02_0820);
        assert_eq!(encode_ext(4, 2, 1, 0).unwrap(), 0x6E02_2020);
        assert_eq!(encode_ext(8, 2, 1, 0).unwrap(), 0x6E02_4020);
        assert_eq!(encode_ext(12, 2, 1, 0).unwrap(), 0x6E02_6020);
        assert_eq!(encode_ext(15, 2, 1, 0).unwrap(), 0x6E02_7820);
        assert_eq!(encode_ext(12, 29, 30, 31).unwrap(), 0x6E1D_63DF);
        assert_eq!(encode_ext(1, 29, 30, 31).unwrap(), 0x6E1D_0BDF);
        assert_eq!(encode_ext(4, 31, 0, 17).unwrap(), 0x6E1F_2011);
        assert_eq!(encode_ext(15, 31, 0, 17).unwrap(), 0x6E1F_7811);
        assert_eq!(encode_ext(8, 11, 20, 5).unwrap(), 0x6E0B_4285);
    }

    #[test]
    fn test_ext_operand_order_is_asymmetric() {
        // EXT is NOT commutative: `Rn` (the LOW half of the concatenation) and
        // `Rm` (the HIGH half) occupy different bit fields. Swapping them is a
        // classic silent miscompile (the complementary window). Pin that the
        // swapped encoding differs and that each register lands in its field:
        //   ext v17.16b, v0.16b, v31.16b, #4 = 0x6E1F2011 (Rn=0 -> bits[9:5]=0,
        //   Rm=31 -> bits[20:16]=31); the swap encodes 0x6E043C11 instead.
        let correct = encode_ext(4, 31, 0, 17).unwrap();
        let swapped = encode_ext(4, 0, 31, 17).unwrap();
        assert_ne!(correct, swapped, "swapping Rn/Rm must change the encoding");
        assert_eq!(correct, 0x6E1F_2011);
        assert_eq!((correct >> 5) & 0x1F, 0, "Rn (LOW source) is bits [9:5]");
        assert_eq!(
            (correct >> 16) & 0x1F,
            31,
            "Rm (HIGH source) is bits [20:16]"
        );
    }

    #[test]
    fn test_ext_rejects_unproven_immediates() {
        // Hardware accepts #0..#15, but only the shifts the vectorizers emit
        // (and the SMT proofs credit) are allowed: the whole-i32-lane #4/#8/#12
        // and the single-byte-neighbor #1/#15. Everything else must fail CLOSED.
        for imm in [-1i64, 0, 2, 3, 5, 6, 7, 9, 10, 11, 13, 14, 16, 255] {
            assert_eq!(
                encode_ext(imm, 2, 1, 0),
                Err(NeonEncodeError::InvalidExtImmediate(imm)),
                "EXT #{imm} must be rejected (no proof credit)"
            );
        }
    }

    #[test]
    fn test_ext_rejects_out_of_range_registers() {
        assert!(matches!(
            encode_ext(4, 32, 1, 0),
            Err(NeonEncodeError::RegisterOutOfRange { reg: 32 })
        ));
        assert!(matches!(
            encode_ext(4, 2, 33, 0),
            Err(NeonEncodeError::RegisterOutOfRange { reg: 33 })
        ));
        assert!(matches!(
            encode_ext(4, 2, 1, 34),
            Err(NeonEncodeError::RegisterOutOfRange { reg: 34 })
        ));
    }

    // === Across-lanes reductions ===

    #[test]
    fn test_umaxv_vec_4s() {
        // UMAXV S0, V1.4S
        let enc = encode_umaxv_4s(1, 0).unwrap();
        assert_eq!((enc >> 30) & 1, 1, "Q=1");
        assert_eq!((enc >> 29) & 1, 1, "U=1 for unsigned max");
        assert_eq!((enc >> 22) & 0b11, 0b10, "size=10 for S lanes");
        assert_eq!((enc >> 17) & 0b11111, 0b11000);
        assert_eq!((enc >> 12) & 0b11111, 0b01010, "opcode=01010");
        assert_eq!((enc >> 10) & 0b11, 0b10);
        assert_eq!((enc >> 5) & 0b11111, 1, "Rn=1");
        assert_eq!(enc & 0b11111, 0, "Rd=0");
    }

    #[test]
    fn test_addp_scalar_2d() {
        // ADDP D0, V1.2D
        let enc = encode_addp_scalar_2d(1, 0).unwrap();
        assert_eq!((enc >> 30) & 1, 1, "Q=1");
        assert_eq!((enc >> 22) & 0b11, 0b11, "size=11 for D lanes");
        assert_eq!((enc >> 17) & 0b11111, 0b11000);
        assert_eq!((enc >> 12) & 0b11111, 0b11011, "opcode=11011");
        assert_eq!((enc >> 10) & 0b11, 0b10);
        assert_eq!((enc >> 5) & 0b11111, 1, "Rn=1");
        assert_eq!(enc & 0b11111, 0, "Rd=0");
    }

    // === FP vector arithmetic ===

    #[test]
    fn test_fadd_vec_4s() {
        // FADD V0.4S, V1.4S, V2.4S
        let enc = encode_fp_vec3_same(FpVectorArrangement::S4, FpVec3Op::Fadd, 2, 1, 0).unwrap();
        assert_eq!((enc >> 30) & 1, 1, "Q=1 for 4S");
        assert_eq!((enc >> 29) & 1, 0, "U=0 for FADD");
        assert_eq!((enc >> 22) & 1, 0, "sz=0 for single");
        assert_eq!((enc >> 10) & 0b111111, 0b110101, "opcode for FADD");
    }

    #[test]
    fn test_fsub_vec_4s() {
        let enc = encode_fp_vec3_same(FpVectorArrangement::S4, FpVec3Op::Fsub, 2, 1, 0).unwrap();
        assert_eq!(
            (enc >> 23) & 1,
            1,
            "bit23=1 for FSUB (distinguishes from FADD)"
        );
        assert_eq!((enc >> 10) & 0b111111, 0b110101, "opcode same as FADD");
    }

    #[test]
    fn test_fmul_vec_2d() {
        // FMUL V0.2D, V1.2D, V2.2D
        let enc = encode_fp_vec3_same(FpVectorArrangement::D2, FpVec3Op::Fmul, 2, 1, 0).unwrap();
        assert_eq!((enc >> 30) & 1, 1, "Q=1 for 2D");
        assert_eq!((enc >> 29) & 1, 1, "U=1 for FMUL");
        assert_eq!((enc >> 22) & 1, 1, "sz=1 for double");
        assert_eq!((enc >> 10) & 0b111111, 0b110111, "opcode for FMUL");
    }

    #[test]
    fn test_fdiv_vec_4s() {
        let enc = encode_fp_vec3_same(FpVectorArrangement::S4, FpVec3Op::Fdiv, 2, 1, 0).unwrap();
        assert_eq!((enc >> 29) & 1, 1, "U=1 for FDIV");
        assert_eq!((enc >> 10) & 0b111111, 0b111111, "opcode for FDIV");
    }

    #[test]
    fn test_fcmgt_vec_exact_bytes() {
        // EXACT-BYTE pins vs the system assembler (clang integrated as / llvm-mc):
        //   fcmgt v0.4s,  v1.4s,  v2.4s  = 0x6EA2E420
        //   fcmgt v0.2d,  v1.2d,  v2.2d  = 0x6EE2E420
        //   fcmgt v31.4s, v30.4s, v29.4s = 0x6EBDE7DF
        // (U=1, E(bit23)=1, opcode 111001 — FCMEQ is U=0/E=0 and FCMGE is
        // U=1/E=0 on the same opcode bits, so these pins kill the compare
        // confusions at the byte level.)
        let enc = encode_fp_vec3_same(FpVectorArrangement::S4, FpVec3Op::Fcmgt, 2, 1, 0).unwrap();
        assert_eq!(enc, 0x6EA2_E420, "fcmgt v0.4s, v1.4s, v2.4s");
        let enc = encode_fp_vec3_same(FpVectorArrangement::D2, FpVec3Op::Fcmgt, 2, 1, 0).unwrap();
        assert_eq!(enc, 0x6EE2_E420, "fcmgt v0.2d, v1.2d, v2.2d");
        let enc =
            encode_fp_vec3_same(FpVectorArrangement::S4, FpVec3Op::Fcmgt, 29, 30, 31).unwrap();
        assert_eq!(enc, 0x6EBD_E7DF, "fcmgt v31.4s, v30.4s, v29.4s");
    }

    #[test]
    fn test_fmla_lane_exact_bytes() {
        // EXACT-BYTE pins vs the system assembler (clang integrated as):
        //   fmla.4s  v0, v1, v2[0]    = 0x4F821020
        //   fmla.4s  v0, v1, v2[1]    = 0x4FA21020   (L=1)
        //   fmla.4s  v0, v1, v2[2]    = 0x4F821820   (H=1)
        //   fmla.4s  v0, v1, v2[3]    = 0x4FA21820   (H:L = 1:1)
        //   fmla.2d  v0, v1, v2[0]    = 0x4FC21020
        //   fmla.2d  v0, v1, v2[1]    = 0x4FC21820   (H=1)
        //   fmla.4s  v5, v6, v20[3]   = 0x4FB418C5   (M=1 => Vm=20 edge)
        //   fmla.2d  v7, v8, v17[1]   = 0x4FD11907   (M=1 => Vm=17 edge)
        //   fmls.4s  v0, v1, v2[2]    = 0x4F825820   (opcode 0101 polarity)
        //   fmla.4s  v31, v30, v15[1] = 0x4FAF13DF
        //   fmla.4s  v10, v11, v16[0] = 0x4F90116A   (M=1 => Vm=16 boundary)
        //   fmla.2d  v12, v13, v31[0] = 0x4FDF11AC   (M=1 => Vm=31 max)
        use FpVectorArrangement::{D2, S4};
        // .4S all four lanes (v0, v1, v2[lane])
        assert_eq!(
            encode_fmla_lane(S4, false, 0, 2, 1, 0).unwrap(),
            0x4F82_1020
        );
        assert_eq!(
            encode_fmla_lane(S4, false, 1, 2, 1, 0).unwrap(),
            0x4FA2_1020
        );
        assert_eq!(
            encode_fmla_lane(S4, false, 2, 2, 1, 0).unwrap(),
            0x4F82_1820
        );
        assert_eq!(
            encode_fmla_lane(S4, false, 3, 2, 1, 0).unwrap(),
            0x4FA2_1820
        );
        // .2D both lanes (v0, v1, v2[lane])
        assert_eq!(
            encode_fmla_lane(D2, false, 0, 2, 1, 0).unwrap(),
            0x4FC2_1020
        );
        assert_eq!(
            encode_fmla_lane(D2, false, 1, 2, 1, 0).unwrap(),
            0x4FC2_1820
        );
        // M-bit edges: Vm >= 16 (the high register bit is the encoding M bit).
        assert_eq!(
            encode_fmla_lane(S4, false, 3, 20, 6, 5).unwrap(),
            0x4FB4_18C5
        );
        assert_eq!(
            encode_fmla_lane(D2, false, 1, 17, 8, 7).unwrap(),
            0x4FD1_1907
        );
        assert_eq!(
            encode_fmla_lane(S4, false, 0, 16, 11, 10).unwrap(),
            0x4F90_116A
        );
        assert_eq!(
            encode_fmla_lane(D2, false, 0, 31, 13, 12).unwrap(),
            0x4FDF_11AC
        );
        // FMLS polarity (opcode 0101) and register-max case.
        assert_eq!(encode_fmla_lane(S4, true, 2, 2, 1, 0).unwrap(), 0x4F82_5820);
        assert_eq!(
            encode_fmla_lane(S4, false, 1, 15, 30, 31).unwrap(),
            0x4FAF_13DF
        );
    }

    #[test]
    fn test_fmla_lane_rejects_bad_lane_and_arrangement() {
        use FpVectorArrangement::{D2, S2, S4};
        // .4S: lanes 0..=3 only.
        assert!(encode_fmla_lane(S4, false, 4, 0, 0, 0).is_err());
        // .2D: lanes 0..=1 only.
        assert!(encode_fmla_lane(D2, false, 2, 0, 0, 0).is_err());
        // .2S (64-bit half) is not an emitted/proven form: fail-closed.
        assert!(encode_fmla_lane(S2, false, 0, 0, 0, 0).is_err());
        // Register out of range.
        assert!(encode_fmla_lane(S4, false, 0, 32, 0, 0).is_err());
    }

    #[test]
    fn test_dup_element_lane0_exact_bytes() {
        // The elementwise-FP vectorizer's invariant broadcast:
        //   dup v2.4s, v0.s[0] = 0x4E040402 (assembler-pinned)
        //   dup v5.2d, v1.d[0] = 0x4E080425 (assembler-pinned)
        let enc = encode_dup_element(1, ElementSize::S, 0, 0, 2).unwrap();
        assert_eq!(enc, 0x4E04_0402, "dup v2.4s, v0.s[0]");
        let enc = encode_dup_element(1, ElementSize::D, 0, 1, 5).unwrap();
        assert_eq!(enc, 0x4E08_0425, "dup v5.2d, v1.d[0]");
    }

    #[test]
    fn test_fadd_vec_2s() {
        // FADD V0.2S, V1.2S, V2.2S (64-bit register)
        let enc = encode_fp_vec3_same(FpVectorArrangement::S2, FpVec3Op::Fadd, 2, 1, 0).unwrap();
        assert_eq!((enc >> 30) & 1, 0, "Q=0 for 2S");
        assert_eq!((enc >> 22) & 1, 0, "sz=0 for single");
    }

    // === DUP ===

    #[test]
    fn test_dup_element_s() {
        // DUP V0.4S, V1.S[2]
        let enc = encode_dup_element(1, ElementSize::S, 2, 1, 0).unwrap();
        assert_eq!((enc >> 30) & 1, 1, "Q=1");
        // imm5 = (2 << 3) | 0b100 = 0b10100 = 20
        assert_eq!((enc >> 16) & 0b11111, 0b10100, "imm5 for S lane 2");
        assert_eq!((enc >> 11) & 0b1111, 0b0000, "opcode for DUP element");
    }

    #[test]
    fn test_dup_general_s() {
        // DUP V0.4S, W1
        let enc = encode_dup_general(1, ElementSize::S, 1, 0).unwrap();
        assert_eq!((enc >> 16) & 0b11111, 0b00100, "imm5 for S general");
        assert_eq!((enc >> 11) & 0b1111, 0b0001, "opcode for DUP general");
        assert_eq!(enc, 0x4E04_0C20);
    }

    #[test]
    fn test_dup_general_s_not_ins_lane_zero() {
        // DUP V30.4S, W4 uses the DUP-general opcode, not INS V30.S[0], W4.
        let dup = encode_dup_general(1, ElementSize::S, 4, 30).unwrap();
        let ins_lane0 = encode_ins_general(ElementSize::S, 0, 4, 30).unwrap();

        assert_eq!(dup, 0x4E04_0C9E);
        assert_eq!(ins_lane0, 0x4E04_1C9E);
        assert_ne!(dup, ins_lane0);
    }

    // === INS ===

    #[test]
    fn test_ins_general_s() {
        // INS V0.S[1], W2
        let enc = encode_ins_general(ElementSize::S, 1, 2, 0).unwrap();
        assert_eq!((enc >> 30) & 1, 1, "Q=1 for INS");
        // imm5 = (1 << 3) | 0b100 = 0b01100 = 12
        assert_eq!((enc >> 16) & 0b11111, 0b01100, "imm5 for S lane 1");
    }

    // === UMOV ===

    #[test]
    fn test_umov_general_b_h() {
        let b = encode_umov_general(ElementSize::B, 15, 3, 2).unwrap();
        assert_eq!((b >> 30) & 1, 0, "Q=0 for B lane extraction");
        assert_eq!((b >> 16) & 0b11111, 0b11111, "imm5 for B lane 15");
        assert_eq!(b, 0x0E1F_3C62);

        let h = encode_umov_general(ElementSize::H, 7, 7, 6).unwrap();
        assert_eq!((h >> 30) & 1, 0, "Q=0 for H lane extraction");
        assert_eq!((h >> 16) & 0b11111, 0b11110, "imm5 for H lane 7");
        assert_eq!(h, 0x0E1E_3CE6);
    }

    #[test]
    fn test_umov_general_d() {
        // UMOV X2, V3.D[1]
        let enc = encode_umov_general(ElementSize::D, 1, 3, 2).unwrap();
        assert_eq!((enc >> 30) & 1, 1, "Q=1 for D lane extraction");
        assert_eq!((enc >> 16) & 0b11111, 0b11000, "imm5 for D lane 1");
        assert_eq!(enc, 0x4E18_3C62);
    }

    #[test]
    fn test_umov_general_rejects_bad_d_lane() {
        assert!(matches!(
            encode_umov_general(ElementSize::D, 2, 3, 2),
            Err(NeonEncodeError::InvalidLane { lane: 2 })
        ));
    }

    // === MOVI ===

    #[test]
    fn test_movi_byte_16b() {
        // MOVI V0.16B, #0xAB
        let enc = encode_movi_byte(1, 0xAB, 0).unwrap();
        assert_eq!((enc >> 30) & 1, 1, "Q=1 for 16B");
        let abc = (enc >> 16) & 0b111;
        let defgh = (enc >> 5) & 0b11111;
        let reconstructed = (abc << 5) | defgh;
        assert_eq!(reconstructed, 0xAB_u32, "immediate round-trips");
    }

    #[test]
    fn test_movi_byte_8b() {
        // MOVI V5.8B, #0x42
        let enc = encode_movi_byte(0, 0x42, 5).unwrap();
        assert_eq!((enc >> 30) & 1, 0, "Q=0 for 8B");
        assert_eq!(enc & 0b11111, 5, "Rd=5");
    }

    // === LD1 / ST1 ===

    #[test]
    fn test_ld1_post_4s() {
        // LD1 {V0.4S}, [X1], #16
        let enc = encode_ld1_post_imm(VectorArrangement::S4, 1, 0).unwrap();
        assert_eq!((enc >> 30) & 1, 1, "Q=1 for 4S");
        assert_eq!((enc >> 22) & 1, 1, "L=1 for load");
        assert_eq!(
            (enc >> 16) & 0b11111,
            0b11111,
            "Rm=11111 for imm post-index"
        );
        assert_eq!((enc >> 12) & 0b1111, 0b0111, "opcode=0111 for 1 register");
    }

    #[test]
    fn test_st1_post_4s() {
        // ST1 {V0.4S}, [X1], #16
        let enc = encode_st1_post_imm(VectorArrangement::S4, 1, 0).unwrap();
        assert_eq!((enc >> 22) & 1, 0, "L=0 for store");
    }

    #[test]
    fn test_st1_post_4s_exact_bits() {
        // ST1 {V0.4S}, [X1], #16 — the vector store emitted by the `neon-map`
        // memory-map vectorizer. Cross-checked against clang's assembler
        // (`st1.4s {v0}, [x1], #16` → little-endian word 0x4C9F7820). Identical
        // to the LD1.4S encoding (0x4CDF7820) with the L (load) bit cleared.
        let enc = encode_st1_post_imm(VectorArrangement::S4, 1, 0).unwrap();
        assert_eq!(enc, 0x4C9F7820, "ST1 {{V0.4S}}, [X1], #16 = {enc:#010X}");
    }

    #[test]
    fn test_ld1_post_4s_exact_bits() {
        // LD1 {V0.4S}, [X1], #16 — the vector load emitted by the `neon-array`
        // array-reduction vectorizer. Cross-checked against clang's assembler
        // (`ld1.4s {v0}, [x1], #16` → little-endian word 0x4CDF7820).
        let enc = encode_ld1_post_imm(VectorArrangement::S4, 1, 0).unwrap();
        assert_eq!(enc, 0x4CDF7820, "LD1 {{V0.4S}}, [X1], #16 = {enc:#010X}");
    }

    #[test]
    fn test_ld1_post_2d_exact_bits() {
        // LD1 {V0.2D}, [X1], #16 — cross-checked against clang
        // (`ld1.2d {v0}, [x1], #16` → 0x4CDF7C20). Same encoder, `.2D` size.
        let enc = encode_ld1_post_imm(VectorArrangement::D2, 1, 0).unwrap();
        assert_eq!(enc, 0x4CDF7C20, "LD1 {{V0.2D}}, [X1], #16 = {enc:#010X}");
    }

    #[test]
    fn test_ld1_post_16b() {
        let enc = encode_ld1_post_imm(VectorArrangement::B16, 3, 7).unwrap();
        assert_eq!((enc >> 30) & 1, 1, "Q=1");
        assert_eq!((enc >> 10) & 0b11, 0b00, "size=00 for B");
        assert_eq!((enc >> 5) & 0b11111, 3, "Rn=3");
        assert_eq!(enc & 0b11111, 7, "Rt=7");
    }

    // === LDP Q-pair post-index — exact bytes vs llvm-mc ===
    //
    // Ground truth from `llvm-mc -triple=aarch64 -show-encoding` (little-endian
    // byte order as printed by llvm-mc, i.e. word = bytes reversed):
    //   ldp q0,  q1,  [x0],  #32  // encoding: [0x00,0x04,0xc1,0xac] = 0xACC10400
    //   ldp q2,  q3,  [x1],  #32  // encoding: [0x22,0x0c,0xc1,0xac] = 0xACC10C22
    //   ldp q30, q31, [x9],  #32  // encoding: [0x3e,0x7d,0xc1,0xac] = 0xACC17D3E
    //   ldp q4,  q5,  [x2],  #64  // encoding: [0x44,0x14,0xc2,0xac] = 0xACC21444
    //   ldp q1,  q0,  [x28], #32  // encoding: [0x81,0x03,0xc1,0xac] = 0xACC10381

    #[test]
    fn test_ldp_q_post_exact_bits_vs_llvm_mc() {
        // The exact form the NEON reduction vectorizers emit: two consecutive
        // Q registers, running pointer, #32 post-index.
        let cases: &[(i64, u8, u8, u8, u32)] = &[
            // (offset, rt2, rn, rt, expected word)
            (32, 1, 0, 0, 0xACC1_0400),   // ldp q0,  q1,  [x0],  #32
            (32, 3, 1, 2, 0xACC1_0C22),   // ldp q2,  q3,  [x1],  #32
            (32, 31, 9, 30, 0xACC1_7D3E), // ldp q30, q31, [x9],  #32
            (64, 5, 2, 4, 0xACC2_1444),   // ldp q4,  q5,  [x2],  #64
            (32, 0, 28, 1, 0xACC1_0381),  // ldp q1,  q0,  [x28], #32
        ];
        for &(offset, rt2, rn, rt, expected) in cases {
            let enc = encode_ldp_q_post_imm(offset, rt2, rn, rt).unwrap();
            assert_eq!(
                enc, expected,
                "LDP Q{rt}, Q{rt2}, [X{rn}], #{offset} = {enc:#010X}, llvm-mc says {expected:#010X}"
            );
            // Also pin the little-endian byte order (what the object file holds).
            assert_eq!(
                enc.to_le_bytes(),
                expected.to_le_bytes(),
                "little-endian byte emission mismatch"
            );
        }
    }

    #[test]
    fn test_ldp_q_post_is_simd_fp_form_not_gpr() {
        // The prior P0 in this family: pre/post-index STP/LDP hardcoded the GPR
        // form (V=0) and clobbered FPR pairs. Pin the V bit (bit 26) SET and
        // opc (bits 31-30) = 0b10 (Q, 128-bit).
        let enc = encode_ldp_q_post_imm(32, 1, 0, 0).unwrap();
        assert_eq!((enc >> 26) & 1, 1, "V=1: SIMD&FP form, never the GPR form");
        assert_eq!((enc >> 30) & 0b11, 0b10, "opc=0b10: Q (128-bit) pair");
        assert_eq!((enc >> 22) & 1, 1, "L=1: load");
        assert_eq!((enc >> 23) & 0b111, 0b001, "post-index addressing class");
    }

    #[test]
    fn test_ldp_q_post_fail_closed() {
        // Same-register destination pair is UNPREDICTABLE — rejected.
        assert!(matches!(
            encode_ldp_q_post_imm(32, 7, 0, 7),
            Err(NeonEncodeError::LdpDuplicateDest(7))
        ));
        // Offset not a multiple of the Q granule (16) — rejected, not rounded.
        assert!(matches!(
            encode_ldp_q_post_imm(24, 1, 0, 0),
            Err(NeonEncodeError::InvalidLdpQPostOffset(24))
        ));
        // Scaled offset outside signed imm7 — rejected, NOT silently truncated
        // (1024/16 = 64 > 63; a bare `& 0x7F` would encode #-1024).
        assert!(matches!(
            encode_ldp_q_post_imm(1024, 1, 0, 0),
            Err(NeonEncodeError::InvalidLdpQPostOffset(1024))
        ));
        assert!(matches!(
            encode_ldp_q_post_imm(-1040, 1, 0, 0),
            Err(NeonEncodeError::InvalidLdpQPostOffset(-1040))
        ));
        // Register indices out of range.
        assert!(encode_ldp_q_post_imm(32, 32, 0, 0).is_err());
        assert!(encode_ldp_q_post_imm(32, 1, 32, 0).is_err());
        assert!(encode_ldp_q_post_imm(32, 1, 0, 32).is_err());
        // Boundary offsets that MUST encode: +1008 (imm7=63) and -1024 (imm7=-64).
        assert!(encode_ldp_q_post_imm(1008, 1, 0, 0).is_ok());
        assert!(encode_ldp_q_post_imm(-1024, 1, 0, 0).is_ok());
    }

    // === STP (SIMD&FP, 128-bit Q pair, post-index) ===
    // Reference bytes from clang -c (arm64-apple-macos) + objdump -d:
    //   stp q0,  q1,  [x0],  #32   // ac810400
    //   stp q2,  q3,  [x1],  #32   // ac810c22
    //   stp q30, q31, [x9],  #32   // ac817d3e
    //   stp q1,  q0,  [x28], #32   // ac810381
    //   stp q7,  q0,  [x7],  #32   // ac8100e7
    //   stp q31, q30, [x5],  #-1024 // aca078bf
    //   stp q0,  q1,  [x0],  #1008 // ac9f8400
    //   stp q3,  q4,  [x9],  #-32  // acbf1123

    #[test]
    fn test_stp_q_post_exact_bits_vs_clang() {
        // The exact form the NEON map/stencil/fmap vectorizers emit: two
        // consecutive Q registers, running pointer, #32 post-index.
        let cases: &[(i64, u8, u8, u8, u32)] = &[
            // (offset, rt2, rn, rt, expected word)
            (32, 1, 0, 0, 0xAC81_0400),      // stp q0,  q1,  [x0],  #32
            (32, 3, 1, 2, 0xAC81_0C22),      // stp q2,  q3,  [x1],  #32
            (32, 31, 9, 30, 0xAC81_7D3E),    // stp q30, q31, [x9],  #32
            (32, 0, 28, 1, 0xAC81_0381),     // stp q1,  q0,  [x28], #32
            (32, 0, 7, 7, 0xAC81_00E7),      // stp q7,  q0,  [x7],  #32
            (-1024, 30, 5, 31, 0xACA0_78BF), // stp q31, q30, [x5],  #-1024
            (1008, 1, 0, 0, 0xAC9F_8400),    // stp q0,  q1,  [x0],  #1008
            (-32, 4, 9, 3, 0xACBF_1123),     // stp q3,  q4,  [x9],  #-32
        ];
        for &(offset, rt2, rn, rt, expected) in cases {
            let enc = encode_stp_q_post_imm(offset, rt2, rn, rt).unwrap();
            assert_eq!(
                enc, expected,
                "STP Q{rt}, Q{rt2}, [X{rn}], #{offset} = {enc:#010X}, clang says {expected:#010X}"
            );
            // Also pin the little-endian byte order (what the object file holds).
            assert_eq!(
                enc.to_le_bytes(),
                expected.to_le_bytes(),
                "little-endian byte emission mismatch"
            );
        }
    }

    #[test]
    fn test_stp_q_post_is_simd_fp_form_not_gpr() {
        // Same P0-guard as LDP: pin the V bit (bit 26) SET and opc (bits 31-30)
        // = 0b10 (Q, 128-bit) so we NEVER emit the GPR STP form (V=0) that
        // would clobber FPR pairs. L bit (bit 22) is CLEAR (store).
        let enc = encode_stp_q_post_imm(32, 1, 0, 0).unwrap();
        assert_eq!((enc >> 26) & 1, 1, "V=1: SIMD&FP form, never the GPR form");
        assert_eq!((enc >> 30) & 0b11, 0b10, "opc=0b10: Q (128-bit) pair");
        assert_eq!((enc >> 22) & 1, 0, "L=0: store");
        assert_eq!((enc >> 23) & 0b111, 0b001, "post-index addressing class");
        // STP is EXACTLY LDP with the L bit cleared.
        assert_eq!(
            encode_ldp_q_post_imm(32, 1, 0, 0).unwrap() & !(1 << 22),
            enc,
            "STP must equal LDP with L bit (22) cleared"
        );
    }

    #[test]
    fn test_stp_q_post_fail_closed() {
        // Offset not a multiple of the Q granule (16) — rejected, not rounded.
        assert!(matches!(
            encode_stp_q_post_imm(24, 1, 0, 0),
            Err(NeonEncodeError::InvalidStpQPostOffset(24))
        ));
        // Scaled offset outside signed imm7 — rejected, NOT silently truncated.
        assert!(matches!(
            encode_stp_q_post_imm(1024, 1, 0, 0),
            Err(NeonEncodeError::InvalidStpQPostOffset(1024))
        ));
        assert!(matches!(
            encode_stp_q_post_imm(-1040, 1, 0, 0),
            Err(NeonEncodeError::InvalidStpQPostOffset(-1040))
        ));
        // Register indices out of range.
        assert!(encode_stp_q_post_imm(32, 32, 0, 0).is_err());
        assert!(encode_stp_q_post_imm(32, 1, 32, 0).is_err());
        assert!(encode_stp_q_post_imm(32, 1, 0, 32).is_err());
        // Boundary offsets that MUST encode: +1008 (imm7=63) and -1024 (imm7=-64).
        assert!(encode_stp_q_post_imm(1008, 1, 0, 0).is_ok());
        assert!(encode_stp_q_post_imm(-1024, 1, 0, 0).is_ok());
        // Unlike LDP, a same-register store pair is VALID (stores the value
        // twice) — permitted, not rejected.
        assert!(encode_stp_q_post_imm(32, 7, 0, 7).is_ok());
    }

    // === Register validation ===

    #[test]
    fn test_register_out_of_range() {
        assert!(encode_int_vec3_same(VectorArrangement::S4, IntVec3Op::Add, 32, 0, 0).is_err());
        assert!(encode_vec_logic(1, VecLogicOp::And, 0, 32, 0).is_err());
        assert!(encode_vec_not(1, 32, 0).is_err());
        assert!(encode_fp_vec3_same(FpVectorArrangement::S4, FpVec3Op::Fadd, 0, 0, 32).is_err());
    }

    // === Full bit-pattern verification against ARM ARM ===

    #[test]
    fn test_add_vec_4s_exact_bits() {
        // ADD V0.4S, V1.4S, V2.4S
        // 0|1|0|01110|10|1|00010|10000|1|00001|00000
        // = 0100_1110_1010_0010_1000_0100_0010_0000
        // = 0x4EA28420
        let enc = encode_int_vec3_same(VectorArrangement::S4, IntVec3Op::Add, 2, 1, 0).unwrap();
        assert_eq!(enc, 0x4EA28420, "ADD V0.4S, V1.4S, V2.4S = {enc:#010X}");
    }

    #[test]
    fn test_fadd_vec_4s_exact_bits() {
        // FADD V0.4S, V1.4S, V2.4S
        // Expected: 0|1|0|01110|0|0|1|00010|110101|00001|00000
        //         = 0x4E22D420
        let enc = encode_fp_vec3_same(FpVectorArrangement::S4, FpVec3Op::Fadd, 2, 1, 0).unwrap();
        assert_eq!(enc, 0x4E22D420, "FADD V0.4S, V1.4S, V2.4S = {enc:#010X}");
    }

    #[test]
    fn test_and_vec_16b_exact_bits() {
        // AND V0.16B, V1.16B, V2.16B
        // 0|1|0|01110|00|1|00010|00011|1|00001|00000
        // = 0x4E221C20
        let enc = encode_vec_logic(1, VecLogicOp::And, 2, 1, 0).unwrap();
        assert_eq!(enc, 0x4E221C20, "AND V0.16B, V1.16B, V2.16B = {enc:#010X}");
    }

    #[test]
    fn test_not_vec_16b_exact_bits() {
        // NOT V0.16B, V1.16B
        // 0|1|1|01110|00|10000|00101|10|00001|00000
        // = 0x6E205820
        let enc = encode_vec_not(1, 1, 0).unwrap();
        assert_eq!(enc, 0x6E205820, "NOT V0.16B, V1.16B = {enc:#010X}");
    }

    #[test]
    fn test_umaxv_vec_4s_exact_bits() {
        // UMAXV S0, V1.4S
        // 0|1|1|01110|10|11000|01010|10|00001|00000
        // = 0x6EB0A820
        let enc = encode_umaxv_4s(1, 0).unwrap();
        assert_eq!(enc, 0x6EB0A820, "UMAXV S0, V1.4S = {enc:#010X}");
    }

    #[test]
    fn test_addp_scalar_2d_exact_bits() {
        // ADDP D0, V1.2D
        // Verified with `xcrun clang -target arm64-apple-macosx -x assembler`.
        let enc = encode_addp_scalar_2d(1, 0).unwrap();
        assert_eq!(enc, 0x5EF1_B820, "ADDP D0, V1.2D = {enc:#010X}");
    }

    // -- Advanced SIMD shift by immediate (SHL / USHR / SSHR) --
    //
    // All golden words below were emitted by the system assembler:
    //   clang -c -target aarch64-linux-gnu shifts.s && objdump -d
    // and cross-checked across the full 4S immediate range and edge registers.

    #[test]
    fn test_shl_4s_exact_bits() {
        let a = VectorArrangement::S4;
        use VecShiftImmOp::Shl;
        // shl v0.4s, v1.4s, #0/1/7/31
        assert_eq!(encode_vec_shift_imm(a, Shl, 0, 1, 0).unwrap(), 0x4F20_5420);
        assert_eq!(encode_vec_shift_imm(a, Shl, 1, 1, 0).unwrap(), 0x4F21_5420);
        assert_eq!(encode_vec_shift_imm(a, Shl, 7, 1, 0).unwrap(), 0x4F27_5420);
        assert_eq!(encode_vec_shift_imm(a, Shl, 31, 1, 0).unwrap(), 0x4F3F_5420);
        // shl v5.4s, v6.4s, #8 ; shl v31.4s, v31.4s, #15
        assert_eq!(encode_vec_shift_imm(a, Shl, 8, 6, 5).unwrap(), 0x4F28_54C5);
        assert_eq!(
            encode_vec_shift_imm(a, Shl, 15, 31, 31).unwrap(),
            0x4F2F_57FF
        );
    }

    #[test]
    fn test_ushr_4s_exact_bits() {
        let a = VectorArrangement::S4;
        use VecShiftImmOp::Ushr;
        // ushr v0.4s, v1.4s, #1/2/7/31
        assert_eq!(encode_vec_shift_imm(a, Ushr, 1, 1, 0).unwrap(), 0x6F3F_0420);
        assert_eq!(encode_vec_shift_imm(a, Ushr, 2, 1, 0).unwrap(), 0x6F3E_0420);
        assert_eq!(encode_vec_shift_imm(a, Ushr, 7, 1, 0).unwrap(), 0x6F39_0420);
        assert_eq!(
            encode_vec_shift_imm(a, Ushr, 31, 1, 0).unwrap(),
            0x6F21_0420
        );
        // ushr v31.4s, v30.4s, #32
        assert_eq!(
            encode_vec_shift_imm(a, Ushr, 32, 30, 31).unwrap(),
            0x6F20_07DF
        );
    }

    #[test]
    fn test_sshr_4s_exact_bits() {
        let a = VectorArrangement::S4;
        use VecShiftImmOp::Sshr;
        // sshr v0.4s, v1.4s, #1/4/31/32
        assert_eq!(encode_vec_shift_imm(a, Sshr, 1, 1, 0).unwrap(), 0x4F3F_0420);
        assert_eq!(encode_vec_shift_imm(a, Sshr, 4, 1, 0).unwrap(), 0x4F3C_0420);
        assert_eq!(
            encode_vec_shift_imm(a, Sshr, 31, 1, 0).unwrap(),
            0x4F21_0420
        );
        assert_eq!(
            encode_vec_shift_imm(a, Sshr, 32, 1, 0).unwrap(),
            0x4F20_0420
        );
    }

    // -- `.2D` (2 x i64) ops emitted by the i64 neon-array vectorizer --
    //
    // Every golden word below was produced by the system assembler
    //   clang -c -target arm64-apple-macos d2ops.s && objdump -d
    // for the exact mnemonic in the comment. These are the ONLY `.2D` arithmetic
    // / shift forms the i64 (`.2D`) array-reduction path emits.

    #[test]
    fn test_i64_neon_array_d2_ops_exact_bits() {
        use VecShiftImmOp::{Shl, Sshr, Ushr};
        use VectorArrangement::D2;
        // add.2d v0, v1, v2
        assert_eq!(
            encode_int_vec3_same(D2, IntVec3Op::Add, 2, 1, 0).unwrap(),
            0x4EE2_8420
        );
        // sub.2d v3, v4, v5
        assert_eq!(
            encode_int_vec3_same(D2, IntVec3Op::Sub, 5, 4, 3).unwrap(),
            0x6EE5_8483
        );
        // shl.2d v0, v1, #3   and   shl.2d v0, v1, #63 (max left shift)
        assert_eq!(encode_vec_shift_imm(D2, Shl, 3, 1, 0).unwrap(), 0x4F43_5420);
        assert_eq!(
            encode_vec_shift_imm(D2, Shl, 63, 1, 0).unwrap(),
            0x4F7F_5420
        );
        // ushr.2d v0, v1, #2  and  ushr.2d v0, v1, #64 (max right shift)
        assert_eq!(
            encode_vec_shift_imm(D2, Ushr, 2, 1, 0).unwrap(),
            0x6F7E_0420
        );
        assert_eq!(
            encode_vec_shift_imm(D2, Ushr, 64, 1, 0).unwrap(),
            0x6F40_0420
        );
        // sshr.2d v0, v1, #2
        assert_eq!(
            encode_vec_shift_imm(D2, Sshr, 2, 1, 0).unwrap(),
            0x4F7E_0420
        );
        // ld1.2d { v4 }, [x8], #16  (post-index vector load)
        assert_eq!(encode_ld1_post_imm(D2, 8, 4).unwrap(), 0x4CDF_7D04);
        // mov.d x6, v1[0]  and  mov.d x7, v1[1]  (UMOV both i64 lanes to GPRs)
        assert_eq!(
            encode_umov_general(ElementSize::D, 0, 1, 6).unwrap(),
            0x4E08_3C26
        );
        assert_eq!(
            encode_umov_general(ElementSize::D, 1, 1, 7).unwrap(),
            0x4E18_3C27
        );
        // movi.16b v0, #0  (zeroed .2D accumulator — all 16 bytes 0)
        assert_eq!(encode_movi_byte(1, 0, 0).unwrap(), 0x4F00_E400);
    }

    #[test]
    fn test_vec_shift_imm_out_of_range_fails_closed() {
        let a = VectorArrangement::S4;
        // Left shift by >= esize is invalid (would alias element size).
        assert!(matches!(
            encode_vec_shift_imm(a, VecShiftImmOp::Shl, 32, 1, 0),
            Err(NeonEncodeError::InvalidShiftAmount { .. })
        ));
        // Right shift by 0 has no encoding (2*esize would alias next size).
        assert!(matches!(
            encode_vec_shift_imm(a, VecShiftImmOp::Ushr, 0, 1, 0),
            Err(NeonEncodeError::InvalidShiftAmount { .. })
        ));
        assert!(matches!(
            encode_vec_shift_imm(a, VecShiftImmOp::Sshr, 0, 1, 0),
            Err(NeonEncodeError::InvalidShiftAmount { .. })
        ));
        // Right shift by > esize is invalid.
        assert!(matches!(
            encode_vec_shift_imm(a, VecShiftImmOp::Ushr, 33, 1, 0),
            Err(NeonEncodeError::InvalidShiftAmount { .. })
        ));
    }
}
