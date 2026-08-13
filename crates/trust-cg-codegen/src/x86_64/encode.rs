// trust-cg-codegen/x86_64/encode.rs - x86-64 instruction binary encoder
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: ~/llvm-project-ref/llvm/lib/Target/X86/MCTargetDesc/X86MCCodeEmitter.cpp
// Reference: Intel 64 and IA-32 Architectures SDM, Volume 2

//! x86-64 instruction binary encoder.
//!
//! Encodes `X86Opcode` instructions into variable-length machine code bytes.
//! Each encoding method produces the correct prefix, opcode, ModR/M, SIB,
//! displacement, and immediate bytes per the Intel SDM Vol 2.
//!
//! # Encoding format (general structure)
//!
//! ```text
//! [Legacy prefix] [REX prefix] [Opcode 1-3 bytes] [ModR/M] [SIB] [Disp] [Imm]
//! ```
//!
//! # REX prefix byte: `0100 WRXB`
//!
//! - W: 1 = 64-bit operand size
//! - R: extension of ModR/M reg field (bit 3)
//! - X: extension of SIB index field (bit 3)
//! - B: extension of ModR/M r/m field, SIB base, or opcode reg (bit 3)

use trust_cg_ir::x86_64_ops::{X86CondCode, X86Opcode, X86Sse2PackedOpcode};
use trust_cg_ir::x86_64_regs::{self, EAX, R10, R10B, R10D, R10W, RAX, X86PReg};

fn zero_extending_movri_alias(dst: X86PReg, imm: i64) -> Option<X86PReg> {
    (dst.is_gpr64() && (imm as u64) <= u64::from(u32::MAX))
        .then(|| x86_64_regs::x86_gpr64_to_gpr32(dst))
        .flatten()
}

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Error type for x86-64 encoding failures.
#[derive(Debug, Clone)]
pub enum X86EncodeError {
    /// The opcode is not yet supported for encoding.
    UnsupportedOpcode(X86Opcode),
    /// The operand combination is invalid.
    InvalidOperands(String),
    /// x86-64 encoding is not yet implemented for this specific form.
    NotImplemented(String),
}

impl core::fmt::Display for X86EncodeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::UnsupportedOpcode(op) => write!(f, "unsupported x86-64 opcode: {:?}", op),
            Self::InvalidOperands(msg) => write!(f, "invalid x86-64 operands: {}", msg),
            Self::NotImplemented(msg) => write!(f, "x86-64 not implemented: {}", msg),
        }
    }
}

/// FINDING #8: reject a memory displacement that does not fit in a signed
/// 32-bit field before it is narrowed to `disp as i32`. Mirrors the SSE2
/// sibling check in `require_sse2_memory_shape_impl`. Returns
/// [`X86EncodeError::InvalidOperands`] on overflow.
#[inline]
fn require_disp32(disp: i64) -> Result<(), X86EncodeError> {
    if disp < i64::from(i32::MIN) || disp > i64::from(i32::MAX) {
        return Err(X86EncodeError::InvalidOperands(format!(
            "memory displacement {disp} does not fit in disp32"
        )));
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// REX prefix builder
// ---------------------------------------------------------------------------

/// REX prefix flags for x86-64 encoding.
///
/// REX prefix byte: `0100 WRXB`
/// - W: 1 = 64-bit operand size
/// - R: extension of ModR/M reg field
/// - X: extension of SIB index field
/// - B: extension of ModR/M r/m field, SIB base, or opcode reg
#[derive(Debug, Clone, Copy, Default)]
pub struct RexPrefix {
    /// REX.W: 64-bit operand size.
    pub w: bool,
    /// REX.R: ModR/M reg extension.
    pub r: bool,
    /// REX.X: SIB index extension.
    pub x: bool,
    /// REX.B: ModR/M r/m or opcode reg extension.
    pub b: bool,
}

impl RexPrefix {
    /// Returns true if a REX prefix is needed.
    pub fn is_needed(self) -> bool {
        self.w || self.r || self.x || self.b
    }

    /// Encode the REX prefix byte.
    pub fn encode(self) -> u8 {
        let mut byte: u8 = 0x40; // REX base
        if self.w {
            byte |= 0x08;
        }
        if self.r {
            byte |= 0x04;
        }
        if self.x {
            byte |= 0x02;
        }
        if self.b {
            byte |= 0x01;
        }
        byte
    }
}

// ---------------------------------------------------------------------------
// ModR/M byte builder
// ---------------------------------------------------------------------------

/// ModR/M byte encoding helper.
///
/// ModR/M byte layout: `[mod:2][reg:3][rm:3]`
#[derive(Debug, Clone, Copy)]
pub struct ModRM {
    /// Addressing mode (0b00 = [rm], 0b01 = [rm]+disp8, 0b10 = [rm]+disp32, 0b11 = register)
    pub mode: u8,
    /// Register operand or opcode extension (3 bits, lower 3 of 4-bit encoding).
    pub reg: u8,
    /// Register/memory operand (3 bits, lower 3 of 4-bit encoding).
    pub rm: u8,
}

impl ModRM {
    /// Create a register-register ModR/M (mod=11).
    pub fn reg_reg(reg: u8, rm: u8) -> Self {
        Self {
            mode: 0b11,
            reg: reg & 0x7,
            rm: rm & 0x7,
        }
    }

    /// Create ModR/M for opcode extension with register operand (mod=11).
    pub fn ext_reg(ext: u8, rm: u8) -> Self {
        Self {
            mode: 0b11,
            reg: ext & 0x7,
            rm: rm & 0x7,
        }
    }

    /// Create ModR/M for [base] addressing (mod=00), no displacement.
    pub fn indirect(reg: u8, base: u8) -> Self {
        Self {
            mode: 0b00,
            reg: reg & 0x7,
            rm: base & 0x7,
        }
    }

    /// Create ModR/M for [base+disp8] addressing (mod=01).
    pub fn indirect_disp8(reg: u8, base: u8) -> Self {
        Self {
            mode: 0b01,
            reg: reg & 0x7,
            rm: base & 0x7,
        }
    }

    /// Create ModR/M for [base+disp32] addressing (mod=10).
    pub fn indirect_disp32(reg: u8, base: u8) -> Self {
        Self {
            mode: 0b10,
            reg: reg & 0x7,
            rm: base & 0x7,
        }
    }

    /// Encode the ModR/M byte.
    pub fn encode(self) -> u8 {
        (self.mode << 6) | (self.reg << 3) | self.rm
    }
}

// ---------------------------------------------------------------------------
// SIB byte builder
// ---------------------------------------------------------------------------

/// SIB (Scale-Index-Base) byte encoding helper.
///
/// SIB byte layout: `[scale:2][index:3][base:3]`
///
/// Used when ModR/M rm=100 (RSP encoding) to specify complex addressing modes:
/// `[base + index * scale + displacement]`
#[derive(Debug, Clone, Copy)]
pub struct Sib {
    /// Scale factor: 0=1, 1=2, 2=4, 3=8.
    pub scale: u8,
    /// Index register (3 bits, lower 3 of 4-bit encoding). 0b100 = no index.
    pub index: u8,
    /// Base register (3 bits, lower 3 of 4-bit encoding).
    pub base: u8,
}

impl Sib {
    /// Create a SIB byte for `[base]` only (no index, scale=0).
    ///
    /// This is needed when the base register encoding is 4 (RSP/R12),
    /// since ModR/M rm=100 signals "SIB follows" instead of [RSP].
    pub fn base_only(base: u8) -> Self {
        Self {
            scale: 0,
            index: 0b100, // no index
            base: base & 0x7,
        }
    }

    /// Create a SIB byte for `[base + index * scale]`.
    ///
    /// `scale_factor` must be 1, 2, 4, or 8 (encoded as 0, 1, 2, 3).
    /// `index` must not be RSP (hw_enc 4) -- index bits 100 with REX.X=0 mean
    /// "no index" in SIB; R12 is legal via REX.X=1 (the low 3 bits are masked here).
    pub fn scaled(base: u8, index: u8, scale_factor: u8) -> Self {
        let scale_bits = match scale_factor {
            1 => 0,
            2 => 1,
            4 => 2,
            8 => 3,
            _ => 0, // fallback to scale=1
        };
        Self {
            scale: scale_bits,
            index: index & 0x7,
            base: base & 0x7,
        }
    }

    /// Encode the SIB byte.
    pub fn encode(self) -> u8 {
        (self.scale << 6) | ((self.index & 0x7) << 3) | (self.base & 0x7)
    }
}

// ---------------------------------------------------------------------------
// Operand container for x86-64 instructions
// ---------------------------------------------------------------------------

/// Operands for an x86-64 instruction to be encoded.
///
/// Since the IR `MachInst` is AArch64-typed, the x86-64 encoder uses this
/// separate struct to carry operand information. The ISel or lowering pass
/// populates this before calling the encoder.
#[derive(Debug, Clone)]
pub struct X86InstOperands {
    /// Destination / first source register.
    pub dst: Option<X86PReg>,
    /// Second source register.
    pub src: Option<X86PReg>,
    /// Base register for memory operands.
    pub base: Option<X86PReg>,
    /// Index register for scaled-index (SIB) addressing.
    pub index: Option<X86PReg>,
    /// Scale factor for SIB addressing: 1, 2, 4, or 8.
    pub scale: u8,
    /// Memory displacement/offset.
    pub disp: i64,
    /// Immediate value (sign-extended to 64 bits).
    pub imm: i64,
    /// Condition code (for Jcc).
    pub cc: Option<X86CondCode>,
}

impl X86InstOperands {
    /// Create empty operands.
    pub fn none() -> Self {
        Self {
            dst: None,
            src: None,
            base: None,
            index: None,
            scale: 1,
            disp: 0,
            imm: 0,
            cc: None,
        }
    }

    /// Create operands for a register-register instruction (dst, src).
    pub fn rr(dst: X86PReg, src: X86PReg) -> Self {
        Self {
            dst: Some(dst),
            src: Some(src),
            ..Self::none()
        }
    }

    /// Create operands for a register-immediate instruction (dst, imm).
    pub fn ri(dst: X86PReg, imm: i64) -> Self {
        Self {
            dst: Some(dst),
            imm,
            ..Self::none()
        }
    }

    /// Create operands for a single register operand.
    pub fn r(reg: X86PReg) -> Self {
        Self {
            dst: Some(reg),
            ..Self::none()
        }
    }

    /// Create operands for a register-register-immediate (e.g. IMUL r,r,imm32).
    pub fn rri(dst: X86PReg, src: X86PReg, imm: i64) -> Self {
        Self {
            dst: Some(dst),
            src: Some(src),
            imm,
            ..Self::none()
        }
    }

    /// Create operands for a register-memory instruction (reg, [base+disp]).
    pub fn rm(reg: X86PReg, base: X86PReg, disp: i64) -> Self {
        Self {
            dst: Some(reg),
            base: Some(base),
            disp,
            ..Self::none()
        }
    }

    /// Create operands for a scaled-index memory operand: `[base + index*scale + disp]`.
    ///
    /// `scale` must be 1, 2, 4, or 8.
    pub fn rm_sib(reg: X86PReg, base: X86PReg, index: X86PReg, scale: u8, disp: i64) -> Self {
        Self {
            dst: Some(reg),
            base: Some(base),
            index: Some(index),
            scale,
            disp,
            ..Self::none()
        }
    }

    /// Create operands for a RIP-relative LEA: `[RIP + disp32]`.
    pub fn rip_rel(reg: X86PReg, disp: i64) -> Self {
        Self {
            dst: Some(reg),
            disp,
            ..Self::none()
        }
    }

    /// Create operands for a conditional jump (cc, rel32 displacement).
    pub fn jcc(cc: X86CondCode, disp: i64) -> Self {
        Self {
            cc: Some(cc),
            disp,
            ..Self::none()
        }
    }

    /// Create operands for an unconditional jump or call (rel32 displacement).
    pub fn rel(disp: i64) -> Self {
        Self {
            disp,
            ..Self::none()
        }
    }
}

// ---------------------------------------------------------------------------
// X86Encoder — main encoder
// ---------------------------------------------------------------------------

/// x86-64 instruction encoder.
///
/// Encodes `X86Opcode` instructions into machine code bytes.
pub struct X86Encoder {
    /// Accumulated encoded bytes.
    pub bytes: Vec<u8>,
}

impl X86Encoder {
    /// Create a new empty encoder.
    pub fn new() -> Self {
        Self { bytes: Vec::new() }
    }

    /// Returns the encoded bytes.
    pub fn finish(self) -> Vec<u8> {
        self.bytes
    }

    /// Returns the current position (number of bytes emitted).
    pub fn position(&self) -> usize {
        self.bytes.len()
    }

    /// Emit a single byte.
    pub fn emit_byte(&mut self, byte: u8) {
        self.bytes.push(byte);
    }

    /// Emit a 16-bit little-endian value.
    pub fn emit_u16_le(&mut self, value: u16) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    /// Emit a 32-bit little-endian value.
    pub fn emit_u32_le(&mut self, value: u32) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    /// Emit a 64-bit little-endian value.
    pub fn emit_u64_le(&mut self, value: u64) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    /// Emit a signed 8-bit immediate.
    pub fn emit_imm8(&mut self, value: i8) {
        self.emit_byte(value as u8);
    }

    /// Emit a signed 32-bit immediate in little-endian.
    pub fn emit_imm32(&mut self, value: i32) {
        self.emit_u32_le(value as u32);
    }

    /// Emit a signed 64-bit immediate in little-endian.
    pub fn emit_imm64(&mut self, value: i64) {
        self.emit_u64_le(value as u64);
    }

    /// Emit a REX prefix if needed.
    pub fn emit_rex(&mut self, rex: RexPrefix) {
        if rex.is_needed() {
            self.emit_byte(rex.encode());
        }
    }

    /// Emit a REX prefix even when it has no extension bits.
    ///
    /// Byte-register encodings for SPL/BPL/SIL/DIL require a bare REX prefix
    /// to avoid selecting the legacy AH/CH/DH/BH registers.
    fn emit_rex_forced(&mut self, rex: RexPrefix, force: bool) {
        if force || rex.is_needed() {
            self.emit_byte(rex.encode());
        }
    }

    /// Emit a ModR/M byte.
    pub fn emit_modrm(&mut self, modrm: ModRM) {
        self.emit_byte(modrm.encode());
    }

    /// Emit a SIB byte.
    pub fn emit_sib(&mut self, sib: Sib) {
        self.emit_byte(sib.encode());
    }

    // -----------------------------------------------------------------------
    // Internal encoding helpers
    // -----------------------------------------------------------------------

    /// Build REX prefix for a reg-reg operation with 64-bit operand size.
    /// `reg` goes into ModR/M reg field, `rm` goes into ModR/M rm field.
    fn rex_rr64(reg: X86PReg, rm: X86PReg) -> RexPrefix {
        RexPrefix {
            w: true,
            r: reg.hw_enc() >= 8,
            x: false,
            b: rm.hw_enc() >= 8,
        }
    }

    /// Build REX prefix for a reg-reg operation with configurable operand size.
    /// `reg` goes into ModR/M reg field, `rm` goes into ModR/M rm field.
    fn rex_rr(reg: X86PReg, rm: X86PReg, w: bool) -> RexPrefix {
        RexPrefix {
            w,
            r: reg.hw_enc() >= 8,
            x: false,
            b: rm.hw_enc() >= 8,
        }
    }

    /// Build REX prefix for a single register operand with 64-bit operand size.
    /// Register goes into ModR/M rm field (opcode extension in reg field).
    fn rex_m64(rm: X86PReg) -> RexPrefix {
        RexPrefix {
            w: true,
            r: false,
            x: false,
            b: rm.hw_enc() >= 8,
        }
    }

    fn low_byte_reg_needs_rex(reg: X86PReg) -> bool {
        matches!(reg.hw_enc() & 0x7, 4..=7)
    }

    fn emit_mem_reg_rex(&mut self, reg: X86PReg, base: X86PReg, w: bool, byte_reg: bool) {
        let rex = RexPrefix {
            w,
            r: reg.hw_enc() >= 8,
            x: false,
            b: base.hw_enc() >= 8,
        };
        self.emit_rex_forced(rex, byte_reg && Self::low_byte_reg_needs_rex(reg));
    }

    fn encode_mov_rm_width(
        &mut self,
        dst: X86PReg,
        base: X86PReg,
        disp: i64,
        opcode: u8,
        w: bool,
        operand_size_prefix: bool,
        byte_reg: bool,
    ) -> Result<(), X86EncodeError> {
        if operand_size_prefix {
            self.emit_byte(0x66);
        }
        self.emit_mem_reg_rex(dst, base, w, byte_reg);
        self.emit_byte(opcode);
        self.emit_mem_operand(dst.hw_enc(), base, disp)
    }

    fn encode_mov_mr_width(
        &mut self,
        src: X86PReg,
        base: X86PReg,
        disp: i64,
        opcode: u8,
        w: bool,
        operand_size_prefix: bool,
        byte_reg: bool,
    ) -> Result<(), X86EncodeError> {
        if operand_size_prefix {
            self.emit_byte(0x66);
        }
        self.emit_mem_reg_rex(src, base, w, byte_reg);
        self.emit_byte(opcode);
        self.emit_mem_operand(src.hw_enc(), base, disp)
    }

    /// Build REX prefix for opcode+rd encoding (register in low 3 bits of opcode).
    /// No REX.W needed for PUSH/POP (default 64-bit in long mode).
    fn rex_oprd(reg: X86PReg, need_w: bool) -> RexPrefix {
        RexPrefix {
            w: need_w,
            r: false,
            x: false,
            b: reg.hw_enc() >= 8,
        }
    }

    /// Encode a reg-reg ALU instruction: `REX.W + opcode /r`.
    ///
    /// ModR/M with mod=11, src in reg field, dst in rm field.
    /// This matches Intel's `/r` encoding where the reg field is the source
    /// for ADD/SUB/AND/OR/XOR/CMP (opcode byte encodes the direction).
    fn encode_alu_rr(&mut self, opcode_byte: u8, dst: X86PReg, src: X86PReg) {
        // For ADD r/m64, r64 (opcode 01): reg=src, rm=dst
        let rex = Self::rex_rr(src, dst, !(dst.is_gpr32() && src.is_gpr32()));
        self.emit_rex(rex);
        self.emit_byte(opcode_byte);
        self.emit_modrm(ModRM::reg_reg(src.hw_enc(), dst.hw_enc()));
    }

    fn atomic_rmw_narrow_alias(reg: X86PReg, width_bits: u8) -> Option<X86PReg> {
        match width_bits {
            8 => {
                if reg.is_gpr8() {
                    Some(reg)
                } else if reg.is_gpr32() {
                    x86_64_regs::x86_gpr32_to_gpr8(reg)
                } else if reg.is_gpr64() {
                    x86_64_regs::x86_gpr64_to_gpr8(reg)
                } else if reg.is_gpr16() {
                    x86_64_regs::x86_gpr16_to_gpr64(reg).and_then(x86_64_regs::x86_gpr64_to_gpr8)
                } else {
                    None
                }
            }
            16 => {
                if reg.is_gpr16() {
                    Some(reg)
                } else if reg.is_gpr32() {
                    x86_64_regs::x86_gpr32_to_gpr16(reg)
                } else if reg.is_gpr64() {
                    x86_64_regs::x86_gpr64_to_gpr16(reg)
                } else if reg.is_gpr8() {
                    x86_64_regs::x86_gpr8_to_gpr64(reg).and_then(x86_64_regs::x86_gpr64_to_gpr16)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn atomic_rmw_gpr32_alias(reg: X86PReg) -> Option<X86PReg> {
        if reg.is_gpr32() {
            Some(reg)
        } else if reg.is_gpr64() {
            x86_64_regs::x86_gpr64_to_gpr32(reg)
        } else if reg.is_gpr16() {
            x86_64_regs::x86_gpr16_to_gpr64(reg).and_then(x86_64_regs::x86_gpr64_to_gpr32)
        } else if reg.is_gpr8() {
            x86_64_regs::x86_gpr8_to_gpr64(reg).and_then(x86_64_regs::x86_gpr64_to_gpr32)
        } else {
            None
        }
    }

    fn emit_byte_reg_rex(&mut self, reg: X86PReg, rm: X86PReg, force_byte: bool) {
        let rex = Self::rex_rr(reg, rm, false);
        self.emit_rex_forced(
            rex,
            force_byte && (Self::low_byte_reg_needs_rex(reg) || Self::low_byte_reg_needs_rex(rm)),
        );
    }

    fn encode_gpr_rr_narrow(
        &mut self,
        opcode_byte: u8,
        opcode_word: u8,
        dst: X86PReg,
        src: X86PReg,
        width_bits: u8,
    ) {
        if width_bits == 16 {
            self.emit_byte(0x66);
            let rex = Self::rex_rr(src, dst, false);
            self.emit_rex(rex);
            self.emit_byte(opcode_word);
        } else {
            self.emit_byte_reg_rex(src, dst, true);
            self.emit_byte(opcode_byte);
        }
        self.emit_modrm(ModRM::reg_reg(src.hw_enc(), dst.hw_enc()));
    }

    fn encode_movzx_from_narrow(&mut self, dst: X86PReg, src: X86PReg, width_bits: u8) {
        let rex = Self::rex_rr(dst, src, false);
        self.emit_rex_forced(rex, width_bits == 8 && Self::low_byte_reg_needs_rex(src));
        self.emit_byte(0x0F);
        self.emit_byte(if width_bits == 16 { 0xB7 } else { 0xB6 });
        self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
    }

    fn encode_atomic_rmw_cas_loop(
        &mut self,
        dst: X86PReg,
        src: X86PReg,
        base: X86PReg,
        disp: i64,
        op_kind: i64,
    ) -> Result<(), X86EncodeError> {
        let (acc, scratch, w) = if dst.is_gpr32() {
            if !src.is_gpr32() {
                return Err(X86EncodeError::InvalidOperands(
                    "AtomicRmwCasLoop i32 requires a 32-bit source register".into(),
                ));
            }
            (EAX, R10D, false)
        } else if dst.is_gpr64() {
            if !src.is_gpr64() {
                return Err(X86EncodeError::InvalidOperands(
                    "AtomicRmwCasLoop i64 requires a 64-bit source register".into(),
                ));
            }
            (RAX, R10, true)
        } else {
            return Err(X86EncodeError::InvalidOperands(
                "AtomicRmwCasLoop requires a 32-bit or 64-bit destination register".into(),
            ));
        };

        if !base.is_gpr64() {
            return Err(X86EncodeError::InvalidOperands(
                "AtomicRmwCasLoop requires a 64-bit base register".into(),
            ));
        }
        if x86_64_regs::x86_regs_overlap(src, acc)
            || x86_64_regs::x86_regs_overlap(src, scratch)
            || x86_64_regs::x86_regs_overlap(base, acc)
            || x86_64_regs::x86_regs_overlap(base, scratch)
        {
            return Err(X86EncodeError::InvalidOperands(
                "AtomicRmwCasLoop source/base conflicts with fixed RAX/R10 scratch registers"
                    .into(),
            ));
        }

        let alu_opcode = match op_kind {
            0 => 0x01,  // ADD r/m, r
            1 => 0x29,  // SUB r/m, r
            2 => 0x21,  // AND r/m, r
            3 => 0x09,  // OR r/m, r
            4 => 0x31,  // XOR r/m, r
            5..=9 => 0, // XCHG or min/max via compare-select CAS loop.
            _ => {
                return Err(X86EncodeError::InvalidOperands(format!(
                    "AtomicRmwCasLoop unknown op kind {op_kind}"
                )));
            }
        };

        self.encode_mov_rm_width(acc, base, disp, 0x8B, w, false, false)?;
        let loop_start = self.position();

        if op_kind == 5 {
            self.encode_gpr_rr_width(0x89, scratch, src, w);
        } else if (6..=9).contains(&op_kind) {
            self.encode_gpr_rr_width(0x89, scratch, acc, w);
            self.encode_alu_rr(0x39, scratch, src);
            let cc = match op_kind {
                6 => X86CondCode::L, // signed max: old < src
                7 => X86CondCode::G, // signed min: old > src
                8 => X86CondCode::B, // unsigned max: old < src
                9 => X86CondCode::A, // unsigned min: old > src
                _ => unreachable!("min/max op-kind checked above"),
            };
            let rex = if w {
                Self::rex_rr64(scratch, src)
            } else {
                Self::rex_rr(scratch, src, false)
            };
            self.emit_rex(rex);
            self.emit_byte(0x0F);
            self.emit_byte(0x40 + cc.encoding());
            self.emit_modrm(ModRM::reg_reg(scratch.hw_enc(), src.hw_enc()));
        } else {
            self.encode_gpr_rr_width(0x89, scratch, acc, w);
            self.encode_alu_rr(alu_opcode, scratch, src);
        }

        self.emit_byte(0xF0); // LOCK prefix
        let rex = Self::rex_rr(scratch, base, w);
        self.emit_rex(rex);
        self.emit_byte(0x0F);
        self.emit_byte(0xB1);
        self.emit_mem_operand(scratch.hw_enc(), base, disp)?;

        self.emit_byte(0x0F);
        self.emit_byte(0x85); // JNE rel32
        let branch_end = self.position() + 4;
        let rel = loop_start as i64 - branch_end as i64;
        self.emit_imm32(rel as i32);

        self.encode_gpr_rr_width(0x89, dst, acc, w);
        Ok(())
    }

    fn encode_atomic_rmw_cas_loop_narrow(
        &mut self,
        dst: X86PReg,
        src: X86PReg,
        base: X86PReg,
        disp: i64,
        op_kind: i64,
        width_bits: u8,
    ) -> Result<(), X86EncodeError> {
        let dst32 = Self::atomic_rmw_gpr32_alias(dst).ok_or_else(|| {
            X86EncodeError::InvalidOperands(format!(
                "AtomicRmwCasLoop{width_bits} requires a 32-bit destination carrier"
            ))
        })?;
        let src_narrow = Self::atomic_rmw_narrow_alias(src, width_bits).ok_or_else(|| {
            X86EncodeError::InvalidOperands(format!(
                "AtomicRmwCasLoop{width_bits} requires a GPR source register"
            ))
        })?;
        if !base.is_gpr64() {
            return Err(X86EncodeError::InvalidOperands(format!(
                "AtomicRmwCasLoop{width_bits} requires a 64-bit base register"
            )));
        }

        let (acc, scratch) = if width_bits == 16 {
            (x86_64_regs::AX, R10W)
        } else {
            (x86_64_regs::AL, R10B)
        };
        if x86_64_regs::x86_regs_overlap(src_narrow, acc)
            || x86_64_regs::x86_regs_overlap(src_narrow, scratch)
            || x86_64_regs::x86_regs_overlap(base, acc)
            || x86_64_regs::x86_regs_overlap(base, scratch)
        {
            return Err(X86EncodeError::InvalidOperands(format!(
                "AtomicRmwCasLoop{width_bits} source/base conflicts with fixed RAX/R10 scratch registers"
            )));
        }

        let (alu_opcode_byte, alu_opcode_word) = match op_kind {
            0 => (0x00, 0x01), // ADD r/m, r
            1 => (0x28, 0x29), // SUB r/m, r
            2 => (0x20, 0x21), // AND r/m, r
            3 => (0x08, 0x09), // OR r/m, r
            4 => (0x30, 0x31), // XOR r/m, r
            5 => (0, 0),       // XCHG via CMPXCHG loop: scratch = src
            _ => {
                return Err(X86EncodeError::InvalidOperands(format!(
                    "AtomicRmwCasLoop{width_bits} unknown op kind {op_kind}"
                )));
            }
        };

        if width_bits == 16 {
            self.encode_mov_rm_width(acc, base, disp, 0x8B, false, true, false)?;
        } else {
            self.encode_mov_rm_width(acc, base, disp, 0x8A, false, false, true)?;
        }
        let loop_start = self.position();

        if op_kind == 5 {
            self.encode_gpr_rr_narrow(0x88, 0x89, scratch, src_narrow, width_bits);
        } else {
            self.encode_gpr_rr_narrow(0x88, 0x89, scratch, acc, width_bits);
            self.encode_gpr_rr_narrow(
                alu_opcode_byte,
                alu_opcode_word,
                scratch,
                src_narrow,
                width_bits,
            );
        }

        self.emit_byte(0xF0); // LOCK prefix
        if width_bits == 16 {
            self.emit_byte(0x66);
            let rex = Self::rex_rr(scratch, base, false);
            self.emit_rex(rex);
            self.emit_byte(0x0F);
            self.emit_byte(0xB1);
        } else {
            self.emit_mem_reg_rex(scratch, base, false, true);
            self.emit_byte(0x0F);
            self.emit_byte(0xB0);
        }
        self.emit_mem_operand(scratch.hw_enc(), base, disp)?;

        self.emit_byte(0x0F);
        self.emit_byte(0x85); // JNE rel32
        let branch_end = self.position() + 4;
        let rel = loop_start as i64 - branch_end as i64;
        self.emit_imm32(rel as i32);

        self.encode_movzx_from_narrow(dst32, acc, width_bits);
        Ok(())
    }

    /// Encode a reg-reg instruction: `[REX.W] + opcode /r`.
    ///
    /// ModR/M with mod=11, src in reg field, dst in rm field.
    fn encode_gpr_rr_width(&mut self, opcode_byte: u8, dst: X86PReg, src: X86PReg, w: bool) {
        let rex = Self::rex_rr(src, dst, w);
        self.emit_rex(rex);
        self.emit_byte(opcode_byte);
        self.emit_modrm(ModRM::reg_reg(src.hw_enc(), dst.hw_enc()));
    }

    /// Encode a reg-imm ALU instruction.
    ///
    /// Prefer `83 /ext ib` when the immediate has identical sign-extended
    /// imm8 semantics; otherwise use the full `81 /ext id` form.
    ///
    /// ModR/M with mod=11, opcode extension in reg field, dst in rm field.
    fn encode_alu_ri(&mut self, ext: u8, dst: X86PReg, imm: i32) {
        let rex = Self::rex_rr(X86PReg::new(0), dst, !dst.is_gpr32());
        self.emit_rex(rex);
        // INTENTIONAL MASK (by-design, not a reject-candidate): x86 is
        // variable-length; this is a lossless imm8/imm32 auto-select. The
        // `as i8` is gated by the `i32::from(imm8) == imm` round-trip equality,
        // so imm8 is emitted ONLY when it reproduces the full i32 exactly,
        // otherwise the imm32 form carries the value losslessly. (The i32 range
        // itself is range-checked upstream by require_ri / the inline i32
        // guards — FINDING #8.)
        let imm8 = imm as i8;
        let use_imm8 = i32::from(imm8) == imm;
        self.emit_byte(if use_imm8 { 0x83 } else { 0x81 });
        self.emit_modrm(ModRM::ext_reg(ext, dst.hw_enc()));
        if use_imm8 {
            self.emit_imm8(imm8);
        } else {
            self.emit_imm32(imm);
        }
    }

    /// Encode a unary instruction with opcode extension: `REX.W + opcode /ext`.
    fn encode_unary(&mut self, opcode_byte: u8, ext: u8, reg: X86PReg) {
        let rex = Self::rex_rr(X86PReg::new(0), reg, !reg.is_gpr32());
        self.emit_rex(rex);
        self.emit_byte(opcode_byte);
        self.emit_modrm(ModRM::ext_reg(ext, reg.hw_enc()));
    }

    /// Encode a shift-by-immediate instruction: `REX.W + C1 /ext ib`.
    /// Encode a shift-by-immediate instruction: `REX.W + C1 /ext ib`.
    ///
    /// INTENTIONAL MASK (by-design, not a reject-candidate): the `C1 /N ib`
    /// shift count is masked by the CPU mod operand size (& 0x3F for 64-bit,
    /// & 0x1F for 32-bit), so the architecturally-significant low 5/6 bits are
    /// what matter. The caller's `ops.imm as i8` preserves those low bits intact
    /// (defined-mod-width, exactly like the RISC-V shamt treatment), so this is
    /// a by-design narrowing, not a silent truncation of a meaningful value.
    fn encode_shift_ri(&mut self, ext: u8, dst: X86PReg, imm: i8) {
        let rex = Self::rex_rr(X86PReg::new(0), dst, !dst.is_gpr32());
        self.emit_rex(rex);
        self.emit_byte(0xC1);
        self.emit_modrm(ModRM::ext_reg(ext, dst.hw_enc()));
        self.emit_imm8(imm);
    }

    /// Encode a shift-by-CL instruction: `REX.W + D3 /ext`.
    fn encode_shift_rcl(&mut self, ext: u8, dst: X86PReg) {
        let rex = Self::rex_rr(X86PReg::new(0), dst, !dst.is_gpr32());
        self.emit_rex(rex);
        self.emit_byte(0xD3);
        self.emit_modrm(ModRM::ext_reg(ext, dst.hw_enc()));
    }

    /// Build REX prefix for XMM reg-reg (no REX.W; only need REX.R/REX.B for XMM8-15).
    fn rex_xmm_rr(reg: X86PReg, rm: X86PReg) -> RexPrefix {
        RexPrefix {
            w: false,
            r: reg.hw_enc() >= 8,
            x: false,
            b: rm.hw_enc() >= 8,
        }
    }

    /// Encode an SSE scalar instruction: `[prefix] [REX] 0F opcode /r` (reg-reg, mod=11).
    ///
    /// `prefix` is the mandatory SSE prefix (0xF3 for SS, 0xF2 for SD, 0 for none).
    /// `opcode` is the second byte after 0x0F.
    fn encode_sse_rr(&mut self, prefix: u8, opcode: u8, dst: X86PReg, src: X86PReg) {
        if prefix != 0 {
            self.emit_byte(prefix);
        }
        let rex = Self::rex_xmm_rr(dst, src);
        self.emit_rex(rex);
        self.emit_byte(0x0F);
        self.emit_byte(opcode);
        self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
    }

    /// Encode an SSE scalar instruction with an immediate byte:
    /// `[prefix] [REX] 0F opcode /r ib` (reg-reg, mod=11). Used for the
    /// compare-to-mask forms CMPSD (`F2 0F C2 /r ib`) / CMPSS (`F3 0F C2`),
    /// whose `imm8` selects the comparison predicate (3 = UNORD).
    fn encode_sse_rr_imm(&mut self, prefix: u8, opcode: u8, dst: X86PReg, src: X86PReg, imm: u8) {
        if prefix != 0 {
            self.emit_byte(prefix);
        }
        let rex = Self::rex_xmm_rr(dst, src);
        self.emit_rex(rex);
        self.emit_byte(0x0F);
        self.emit_byte(opcode);
        self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
        self.emit_imm8(imm as i8);
    }

    /// Encode an SSE scalar memory load: `[prefix] [REX] 0F opcode /r` (mem operand).
    fn encode_sse_rm(
        &mut self,
        prefix: u8,
        opcode: u8,
        dst: X86PReg,
        base: X86PReg,
        disp: i64,
    ) -> Result<(), X86EncodeError> {
        if prefix != 0 {
            self.emit_byte(prefix);
        }
        let rex = Self::rex_xmm_rr(dst, base);
        self.emit_rex(rex);
        self.emit_byte(0x0F);
        self.emit_byte(opcode);
        self.emit_mem_operand(dst.hw_enc(), base, disp)
    }

    /// Scaled-index (SIB) sibling of [`Self::encode_sse_rm`]:
    /// `<prefix> REX 0F <opcode> /r` with a `[base + index*scale + disp]`
    /// effective address.
    ///
    /// `REX.W` stays FALSE — for the scalar-FP moves the operand size is fixed
    /// by the mandatory SIMD prefix (`F2` = sd, `F3` = ss), not by REX.W. The
    /// `x` bit is what distinguishes this from the non-SIB helper: it carries
    /// the high bit of the INDEX register, which has no encoding slot in a plain
    /// ModRM memory operand.
    fn encode_sse_rm_sib(
        &mut self,
        prefix: u8,
        opcode: u8,
        dst: X86PReg,
        base: X86PReg,
        index: X86PReg,
        scale: u8,
        disp: i64,
    ) -> Result<(), X86EncodeError> {
        if prefix != 0 {
            self.emit_byte(prefix);
        }
        let rex = RexPrefix {
            w: false,
            r: dst.hw_enc() >= 8,
            x: index.hw_enc() >= 8,
            b: base.hw_enc() >= 8,
        };
        self.emit_rex(rex);
        self.emit_byte(0x0F);
        self.emit_byte(opcode);
        self.emit_sib_mem_operand(dst.hw_enc(), base, index, scale, disp)
    }

    /// Emit a 3-byte VEX (`0xC4`) prefix + opcode + reg-reg ModRM for a 256-bit
    /// (`L=1`) AVX2 packed instruction: `VEX.256.pp.map.W opcode /r`, in the
    /// non-destructive 3-operand form `dst = src1 <op> src2`
    /// (dst = ModRM.reg, src1 = VEX.vvvv, src2 = ModRM.rm).
    ///
    /// `map`: opcode map (1 = `0F`, 2 = `0F38`, 3 = `0F3A`). `pp`: mandatory SIMD
    /// prefix (0 = none, 1 = `66`, 2 = `F3`, 3 = `F2`). `w`: the `VEX.W` bit (0 for
    /// the WIG ops used here). `*_hw` are the 4-bit hardware register numbers
    /// (0..=15); their high bit goes into the inverted `R`/`B` / `vvvv` fields.
    ///
    /// FOUNDATION for the AVX2-256 vectorizer widening (memory:
    /// avx2-perf-lever-measured-2026-07-15) — the x86 vectorizer is SSE-128 only
    /// while LLVM uses AVX2-256, a ~2x width gap. This is the (unit-tested,
    /// byte-exact) VEX-prefix encoder that the 256-bit lowerings will use; it is
    /// deliberately NOT yet wired into any opcode dispatch, so it cannot affect any
    /// compiled program (zero miscompile risk) until the ymm register class +
    /// per-op proof coverage land in a dedicated follow-up.
    #[allow(dead_code)]
    fn emit_vex3_ymm_rr(
        &mut self,
        map: u8,
        pp: u8,
        w: u8,
        opcode: u8,
        dst_hw: u8,
        src1_hw: u8,
        src2_hw: u8,
    ) {
        // Byte 1: [R X B mmmmm] — R/B are the INVERTED high bits of dst/rm; there is
        // no index register in the reg-reg form, so X is the inverted 0 = 1.
        let r = 1 - ((dst_hw >> 3) & 1);
        let x = 1u8;
        let b = 1 - ((src2_hw >> 3) & 1);
        let byte1 = (r << 7) | (x << 6) | (b << 5) | (map & 0x1F);
        // Byte 2: [W vvvv L pp] — vvvv is the INVERTED src1 register (4 bits);
        // L = 1 (256-bit).
        let vvvv = (!src1_hw) & 0x0F;
        let byte2 = ((w & 1) << 7) | (vvvv << 3) | (1 << 2) | (pp & 0x03);
        self.emit_byte(0xC4);
        self.emit_byte(byte1);
        self.emit_byte(byte2);
        self.emit_byte(opcode);
        self.emit_modrm(ModRM::reg_reg(dst_hw & 7, src2_hw & 7));
    }

    /// Encode an SSE2 packed integer instruction with an `xmm, xmm/m128` source.
    fn encode_sse2_packed_xmm_rm_or_rr(
        &mut self,
        opcode: X86Opcode,
        ops: &X86InstOperands,
        opcode_byte: u8,
    ) -> Result<(), X86EncodeError> {
        self.require_no_sse2_immediate(ops, opcode)?;
        if ops.base.is_some() {
            let (dst, base, disp) = self.require_x86_sse2_xmm_rm(ops, opcode)?;
            self.encode_sse_rm(0x66, opcode_byte, dst, base, disp)?;
        } else {
            let (dst, src) = self.require_x86_sse2_xmm_rr(ops, opcode)?;
            self.encode_sse_rr(0x66, opcode_byte, dst, src);
        }
        Ok(())
    }

    /// Encode an SSE2 packed immediate shift: `66 0F 72 /ext ib` for the dword
    /// forms (PSLLD/PSRLD/PSRAD) and `66 0F 73 /ext ib` for the qword forms
    /// (PSLLQ/PSRLQ). The group opcode byte is selected from the opcode itself
    /// so a dword shift can never silently encode as a qword shift (and vice
    /// versa).
    fn encode_sse2_packed_xmm_imm_shift(
        &mut self,
        opcode: X86Opcode,
        ops: &X86InstOperands,
        ext: u8,
    ) -> Result<(), X86EncodeError> {
        let group_opcode_byte = match opcode {
            X86Opcode::Pslld | X86Opcode::Psrld | X86Opcode::Psrad => 0x72,
            X86Opcode::Psllq | X86Opcode::Psrlq => 0x73,
            _ => return Err(X86EncodeError::UnsupportedOpcode(opcode)),
        };
        let imm = self.require_sse2_imm8(ops, opcode)?;
        let dst = self.require_x86_sse2_xmm_ri(ops, opcode)?;
        self.emit_byte(0x66);
        self.emit_rex(RexPrefix {
            w: false,
            r: false,
            x: false,
            b: dst.hw_enc() >= 8,
        });
        self.emit_byte(0x0F);
        self.emit_byte(group_opcode_byte);
        self.emit_modrm(ModRM::ext_reg(ext, dst.hw_enc()));
        self.emit_imm8(imm as i8);
        Ok(())
    }

    /// Encode a 66 0F 38 packed integer instruction with an `xmm, xmm/m128` source.
    fn encode_sse_0f38_packed_xmm_rm_or_rr(
        &mut self,
        opcode: X86Opcode,
        ops: &X86InstOperands,
        opcode_byte: u8,
    ) -> Result<(), X86EncodeError> {
        self.require_no_sse2_immediate(ops, opcode)?;
        if ops.base.is_some() {
            let (dst, base, disp) = self.require_x86_sse2_xmm_rm(ops, opcode)?;
            self.emit_byte(0x66);
            self.emit_rex(Self::rex_xmm_rr(dst, base));
            self.emit_byte(0x0F);
            self.emit_byte(0x38);
            self.emit_byte(opcode_byte);
            self.emit_mem_operand(dst.hw_enc(), base, disp)?;
        } else {
            let (dst, src) = self.require_x86_sse2_xmm_rr(ops, opcode)?;
            self.emit_byte(0x66);
            self.emit_rex(Self::rex_xmm_rr(dst, src));
            self.emit_byte(0x0F);
            self.emit_byte(0x38);
            self.emit_byte(opcode_byte);
            self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
        }
        Ok(())
    }

    /// Encode a `66 0F 3A` three-byte-escape SSE4.1 scalar instruction with an
    /// `xmm, xmm, imm8` shape (reg-reg, mod=11), e.g. ROUNDSD/ROUNDSS:
    /// `66 [REX] 0F 3A opcode /r ib`. The mandatory 0x66 operand-size prefix and
    /// the 0F 3A escape distinguish the SSE4.1 round family; the trailing imm8
    /// selects the rounding mode. The XMM `dst` goes in the ModR/M reg field and
    /// `src` in the r/m field, matching the `/r` operand order.
    fn encode_sse_0f3a_rr_imm(&mut self, opcode: u8, dst: X86PReg, src: X86PReg, imm: u8) {
        self.emit_byte(0x66);
        let rex = Self::rex_xmm_rr(dst, src);
        self.emit_rex(rex);
        self.emit_byte(0x0F);
        self.emit_byte(0x3A);
        self.emit_byte(opcode);
        self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
        self.emit_imm8(imm as i8);
    }

    /// Encode an SSE scalar memory store: `[prefix] [REX] 0F opcode /r` (mem operand).
    ///
    /// For stores, the src XMM register goes into the reg field of ModR/M.
    fn encode_sse_mr(
        &mut self,
        prefix: u8,
        opcode: u8,
        src: X86PReg,
        base: X86PReg,
        disp: i64,
    ) -> Result<(), X86EncodeError> {
        if prefix != 0 {
            self.emit_byte(prefix);
        }
        let rex = Self::rex_xmm_rr(src, base);
        self.emit_rex(rex);
        self.emit_byte(0x0F);
        self.emit_byte(opcode);
        self.emit_mem_operand(src.hw_enc(), base, disp)
    }

    /// Encode an SSE scalar RIP-relative load: `[prefix] [REX] 0F opcode ModRM(00 reg 101) disp32`.
    ///
    /// Used for loading float/double constants from a constant pool via
    /// RIP-relative addressing. `disp` is the signed 32-bit displacement
    /// from RIP (the address of the next instruction after this one) to
    /// the constant pool entry.
    fn encode_sse_rip_rel(
        &mut self,
        prefix: u8,
        opcode: u8,
        dst: X86PReg,
        disp: i64,
    ) -> Result<(), X86EncodeError> {
        if prefix != 0 {
            self.emit_byte(prefix);
        }
        let rex = RexPrefix {
            w: false,
            r: dst.hw_enc() >= 8,
            x: false,
            b: false,
        };
        self.emit_rex(rex);
        self.emit_byte(0x0F);
        self.emit_byte(opcode);
        self.emit_rip_relative(dst.hw_enc(), disp)
    }

    /// Encode a two-byte opcode instruction: `REX.W + 0F + opcode /r` (reg-reg, mod=11).
    ///
    /// Used for CMOV, BSF, BSR, IMUL, etc.
    fn encode_0f_rr64(&mut self, opcode: u8, dst: X86PReg, src: X86PReg) {
        let rex = Self::rex_rr64(dst, src);
        self.emit_rex(rex);
        self.emit_byte(0x0F);
        self.emit_byte(opcode);
        self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
    }

    /// Emit ModR/M + optional SIB + displacement for a memory operand.
    ///
    /// `reg_or_ext` is the 3-bit value for the ModR/M reg field.
    /// `base` is the base register for addressing.
    /// `disp` is the signed displacement.
    ///
    /// Handles the special cases:
    /// - RSP/R12 (hw_enc & 7 == 4): must use SIB byte
    /// - RBP/R13 (hw_enc & 7 == 5) with disp=0: must use disp8=0
    fn emit_mem_operand(
        &mut self,
        reg_or_ext: u8,
        base: X86PReg,
        disp: i64,
    ) -> Result<(), X86EncodeError> {
        // FINDING #8: the disp32 path narrows `disp as i32` below. Reject any
        // displacement that does not fit in a signed 32-bit field BEFORE the
        // cast — silent truncation would encode a *different* (wrong) memory
        // offset. Mirrors the SSE2 sibling check in
        // `require_sse2_memory_shape_impl`.
        require_disp32(disp)?;
        let base_enc = base.hw_enc();
        let base_low3 = base_enc & 0x7;
        let needs_sib = base_low3 == 4; // RSP/R12 encoding

        if disp == 0 && base_low3 != 5 {
            // mod=00: [base] (no displacement)
            if needs_sib {
                self.emit_modrm(ModRM {
                    mode: 0b00,
                    reg: reg_or_ext & 0x7,
                    rm: 0b100, // SIB follows
                });
                self.emit_sib(Sib::base_only(base_enc));
            } else {
                self.emit_modrm(ModRM::indirect(reg_or_ext, base_enc));
            }
        } else if (-128..=127).contains(&disp) {
            // mod=01: [base+disp8]
            if needs_sib {
                self.emit_modrm(ModRM {
                    mode: 0b01,
                    reg: reg_or_ext & 0x7,
                    rm: 0b100,
                });
                self.emit_sib(Sib::base_only(base_enc));
            } else {
                self.emit_modrm(ModRM::indirect_disp8(reg_or_ext, base_enc));
            }
            self.emit_imm8(disp as i8);
        } else {
            // mod=10: [base+disp32]
            if needs_sib {
                self.emit_modrm(ModRM {
                    mode: 0b10,
                    reg: reg_or_ext & 0x7,
                    rm: 0b100,
                });
                self.emit_sib(Sib::base_only(base_enc));
            } else {
                self.emit_modrm(ModRM::indirect_disp32(reg_or_ext, base_enc));
            }
            self.emit_imm32(disp as i32);
        }
        Ok(())
    }

    /// Emit ModR/M + SIB + displacement for a scaled-index memory operand.
    ///
    /// Encodes `[base + index * scale + disp]` addressing mode.
    ///
    /// `reg_or_ext` is the 3-bit value for the ModR/M reg field.
    /// `base` is the base register.
    /// `index` is the index register (must not be RSP (hw_enc 4), which is the
    /// no-index sentinel; R12 is legal via REX.X=1 per Intel SDM Table 2-5).
    /// `scale` is 1, 2, 4, or 8.
    /// `disp` is the signed displacement.
    fn emit_sib_mem_operand(
        &mut self,
        reg_or_ext: u8,
        base: X86PReg,
        index: X86PReg,
        scale: u8,
        disp: i64,
    ) -> Result<(), X86EncodeError> {
        // FINDING #8: same disp32 fits-in-i32 guard as `emit_mem_operand`.
        require_disp32(disp)?;
        let base_enc = base.hw_enc();
        let base_low3 = base_enc & 0x7;
        let sib = Sib::scaled(base_enc, index.hw_enc(), scale);

        if disp == 0 && base_low3 != 5 {
            // mod=00: [base + index*scale]
            self.emit_modrm(ModRM {
                mode: 0b00,
                reg: reg_or_ext & 0x7,
                rm: 0b100, // SIB follows
            });
            self.emit_sib(sib);
        } else if (-128..=127).contains(&disp) {
            // mod=01: [base + index*scale + disp8]
            self.emit_modrm(ModRM {
                mode: 0b01,
                reg: reg_or_ext & 0x7,
                rm: 0b100,
            });
            self.emit_sib(sib);
            self.emit_imm8(disp as i8);
        } else {
            // mod=10: [base + index*scale + disp32]
            self.emit_modrm(ModRM {
                mode: 0b10,
                reg: reg_or_ext & 0x7,
                rm: 0b100,
            });
            self.emit_sib(sib);
            self.emit_imm32(disp as i32);
        }
        Ok(())
    }

    fn validate_sib_mem_operand(
        opcode: X86Opcode,
        index: X86PReg,
        scale: u8,
    ) -> Result<(), X86EncodeError> {
        if !matches!(scale, 1 | 2 | 4 | 8) {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{:?}: invalid SIB scale {} (expected 1, 2, 4, or 8)",
                opcode, scale
            )));
        }
        if index.hw_enc() == 0b100 {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{:?}: invalid SIB index {:?}; RSP (hw_enc 4) is the no-index sentinel and cannot \
                 be a SIB index (R12 is legal via REX.X=1)",
                opcode, index
            )));
        }
        Ok(())
    }

    /// Emit ModR/M for RIP-relative addressing: `[RIP + disp32]`.
    ///
    /// Uses ModR/M mod=00, rm=101 which signals RIP-relative in 64-bit mode.
    fn emit_rip_relative(&mut self, reg_or_ext: u8, disp: i64) -> Result<(), X86EncodeError> {
        // FINDING #8: the RIP-relative disp32 also narrows `disp as i32`; reject
        // out-of-range displacements before the cast.
        require_disp32(disp)?;
        self.emit_modrm(ModRM {
            mode: 0b00,
            reg: reg_or_ext & 0x7,
            rm: 0b101, // RIP-relative
        });
        self.emit_imm32(disp as i32);
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Public encoding API
    // -----------------------------------------------------------------------

    /// Encode a single x86-64 instruction.
    ///
    /// Returns the number of bytes emitted on success.
    pub fn encode_instruction(
        &mut self,
        opcode: X86Opcode,
        ops: &X86InstOperands,
    ) -> Result<usize, X86EncodeError> {
        let start = self.position();

        match opcode {
            X86Opcode::V4I32MaskExtract
            | X86Opcode::V16I8MaskExtract
            | X86Opcode::V8I16MaskExtract
            | X86Opcode::V2I64MaskExtract
            | X86Opcode::V128BoolSelect
            // Proof-only bounds-check / null-check / div-zero-check /
            // shift-range-check carriers (Sentinel S5): fail closed. A surviving
            // carrier MUST be expanded to a real CMP/TEST+Jcc+UD2 check
            // (`expand_x86_bounds_check_carriers` / `expand_x86_null_check_carriers`
            // / `expand_x86_div_zero_check_carriers` /
            // `expand_x86_shift_range_check_carriers`) or deleted under kernel
            // authorization before encoding. Reaching the encoder means the
            // expansion pass was skipped — reject rather than emit a silent NOP
            // that would drop the bounds/null/div-zero/shift-range check (miscompile).
            | X86Opcode::TrapBoundsCheckExact
            | X86Opcode::TrapNullIfZeroExact
            | X86Opcode::TrapDivZeroExact
            | X86Opcode::TrapShiftRangeExact => {
                return Err(X86EncodeError::UnsupportedOpcode(opcode));
            }

            // Pseudo-instructions: no encoding
            X86Opcode::Phi | X86Opcode::StackAlloc | X86Opcode::Nop => {
                return Ok(0);
            }

            // =================================================================
            // Multi-byte NOP (hardware encoding for alignment padding)
            // =================================================================
            // NopMulti: 0F 1F /0 variants (2-9 bytes)
            // Reference: Intel SDM Vol 2B, NOP instruction, Table 4-12
            X86Opcode::NopMulti => {
                // Clamp size to [1, 15] bytes. Real callers request 2-9 for
                // a single atomic NOP; we accept a small over-run (up to 15)
                // to cover alignment padding up to a full cache line, then
                // reject anything larger. Without this clamp, a wild `imm`
                // (e.g. `i64::MAX`) coerced through `as usize` would cause
                // `encode_multibyte_nop` to emit gigabytes of bytes and
                // exhaust memory — see #473 (panic-fuzz) for the bug that
                // surfaced this. The previous unbounded recursion path has
                // been converted to iteration in `encode_multibyte_nop`,
                // but we additionally reject pathological `imm` values at
                // the dispatch boundary so adversarial input returns a
                // typed error instead of a giant allocation.
                let requested = if ops.imm > 0 { ops.imm } else { 3 };
                if !(1..=15).contains(&requested) {
                    return Err(X86EncodeError::InvalidOperands(format!(
                        "NopMulti: imm={} out of range [1, 15]",
                        requested
                    )));
                }
                self.encode_multibyte_nop(requested as usize);
            }

            // UD2: undefined-instruction trap (0F 0B).
            X86Opcode::Ud2 => {
                self.emit_byte(0x0F);
                self.emit_byte(0x0B);
            }

            // =================================================================
            // Memory fences
            // =================================================================
            // MFENCE: 0F AE F0
            X86Opcode::Mfence => {
                self.emit_byte(0x0F);
                self.emit_byte(0xAE);
                self.emit_byte(0xF0);
            }

            // =================================================================
            // Arithmetic: reg-reg
            // =================================================================
            // ADD r/m64, r64: REX.W + 01 /r
            X86Opcode::AddRR => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_alu_rr(0x01, dst, src);
            }
            // SUB r/m64, r64: REX.W + 29 /r
            X86Opcode::SubRR => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_alu_rr(0x29, dst, src);
            }
            // ADC r/m64, r64: REX.W + 11 /r (add-with-carry, dst = dst + src + CF)
            X86Opcode::AdcRR => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_alu_rr(0x11, dst, src);
            }
            // SBB r/m64, r64: REX.W + 19 /r (subtract-with-borrow, dst = dst - src - CF)
            X86Opcode::SbbRR => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_alu_rr(0x19, dst, src);
            }
            // AND r/m64, r64: REX.W + 21 /r
            X86Opcode::AndRR => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_alu_rr(0x21, dst, src);
            }
            // OR r/m64, r64: REX.W + 09 /r
            X86Opcode::OrRR => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_alu_rr(0x09, dst, src);
            }
            // XOR r/m64, r64: REX.W + 31 /r
            X86Opcode::XorRR => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_alu_rr(0x31, dst, src);
            }
            // CMP r/m64, r64: REX.W + 39 /r
            X86Opcode::CmpRR => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_alu_rr(0x39, dst, src);
            }
            // TEST r/m64, r64: REX.W + 85 /r
            X86Opcode::TestRR => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_alu_rr(0x85, dst, src);
            }
            // MOV r/m64, r64: REX.W + 89 /r
            X86Opcode::MovRR => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_alu_rr(0x89, dst, src);
            }
            // MOV r/m32, r32: 89 /r (REX.W must be clear)
            X86Opcode::MovRR32 => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_gpr_rr_width(0x89, dst, src, false);
            }

            // =================================================================
            // Arithmetic: reg-imm32
            // =================================================================
            // ADD r/m64, imm32: REX.W + 81 /0 id
            X86Opcode::AddRI => {
                let (dst, imm) = self.require_ri(ops, opcode)?;
                self.encode_alu_ri(0, dst, imm);
            }
            // SUB r/m64, imm32: REX.W + 81 /5 id
            X86Opcode::SubRI => {
                let (dst, imm) = self.require_ri(ops, opcode)?;
                self.encode_alu_ri(5, dst, imm);
            }
            // AND r/m64, imm32: REX.W + 81 /4 id
            X86Opcode::AndRI => {
                let (dst, imm) = self.require_ri(ops, opcode)?;
                self.encode_alu_ri(4, dst, imm);
            }
            // OR r/m64, imm32: REX.W + 81 /1 id
            X86Opcode::OrRI => {
                let (dst, imm) = self.require_ri(ops, opcode)?;
                self.encode_alu_ri(1, dst, imm);
            }
            // XOR r/m64, imm32: REX.W + 81 /6 id
            X86Opcode::XorRI => {
                let (dst, imm) = self.require_ri(ops, opcode)?;
                self.encode_alu_ri(6, dst, imm);
            }
            // CMP r/m64, imm32: REX.W + 81 /7 id
            X86Opcode::CmpRI => {
                let (dst, imm) = self.require_ri(ops, opcode)?;
                self.encode_alu_ri(7, dst, imm);
            }
            // CMP r/m64, imm8 (sign-extended): REX.W + 83 /7 ib
            X86Opcode::CmpRI8 => {
                let dst = self.require_dst(ops, opcode)?;
                // FINDING #8: 0x83 sign-extends a SIGNED imm8, so the valid
                // range is i8 (-128..=127). Reject anything outside it before
                // the `as i8` narrowing rather than silently mis-encoding.
                if ops.imm < i64::from(i8::MIN) || ops.imm > i64::from(i8::MAX) {
                    return Err(X86EncodeError::InvalidOperands(format!(
                        "{:?}: immediate {} does not fit in imm8",
                        opcode, ops.imm
                    )));
                }
                let imm = ops.imm as i8;
                let rex = Self::rex_m64(dst);
                self.emit_rex(rex);
                self.emit_byte(0x83);
                self.emit_modrm(ModRM::ext_reg(7, dst.hw_enc()));
                self.emit_imm8(imm);
            }
            // TEST r/m64, imm32: REX.W + F7 /0 id
            X86Opcode::TestRI => {
                // FINDING #8: route the immediate through require_ri so an
                // out-of-i32-range value returns InvalidOperands instead of
                // being silently truncated by `as i32`, mirroring the ALU *RI
                // siblings above.
                let (dst, imm) = self.require_ri(ops, opcode)?;
                let rex = Self::rex_m64(dst);
                self.emit_rex(rex);
                self.emit_byte(0xF7);
                self.emit_modrm(ModRM::ext_reg(0, dst.hw_enc()));
                self.emit_imm32(imm);
            }
            // TEST r64, [base+disp]: REX.W + 85 /r (memory operand form)
            X86Opcode::TestRM => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                let rex = RexPrefix {
                    w: true,
                    r: dst.hw_enc() >= 8,
                    x: false,
                    b: base.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x85);
                self.emit_mem_operand(dst.hw_enc(), base, ops.disp)?;
            }

            // =================================================================
            // IMUL
            // =================================================================
            // IMUL r64/r32, r/m64/r/m32: [REX.W] + 0F AF /r
            X86Opcode::ImulRR => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                let rex = Self::rex_rr(dst, src, !(dst.is_gpr32() && src.is_gpr32()));
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0xAF);
                self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
            }
            // IMUL r64/r32, r/m64/r/m32, imm8/imm32:
            // [REX.W] + 6B /r ib (sign-extended) or [REX.W] + 69 /r id.
            X86Opcode::ImulRRI => {
                let dst = self.require_dst(ops, opcode)?;
                let src = ops.src.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing src register", opcode))
                })?;
                // FINDING #8: the immediate encodes as imm8/imm32 (sign-extended
                // by the CPU), so it must fit in i32. Mirror require_ri's range
                // check inline (require_ri only returns dst, but this arm needs
                // src too) so an out-of-range value returns InvalidOperands
                // instead of being silently truncated by `as i32`.
                if ops.imm < i64::from(i32::MIN) || ops.imm > i64::from(i32::MAX) {
                    return Err(X86EncodeError::InvalidOperands(format!(
                        "{:?}: immediate {} does not fit in imm32",
                        opcode, ops.imm
                    )));
                }
                let imm = ops.imm as i32;
                // INTENTIONAL MASK (by-design, not a reject-candidate): lossless
                // imm8/imm32 auto-select gated by the round-trip equality below;
                // the i32 range was already checked at 1534-1539 before narrowing.
                let imm8 = imm as i8;
                let use_imm8 = i32::from(imm8) == imm;
                let rex = Self::rex_rr(dst, src, !(dst.is_gpr32() && src.is_gpr32()));
                self.emit_rex(rex);
                self.emit_byte(if use_imm8 { 0x6B } else { 0x69 });
                self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
                if use_imm8 {
                    self.emit_imm8(imm8);
                } else {
                    self.emit_imm32(imm);
                }
            }
            // IMUL r64, [base+disp]: REX.W + 0F AF /r (two-operand memory form)
            X86Opcode::ImulRM => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                let rex = RexPrefix {
                    w: true,
                    r: dst.hw_enc() >= 8,
                    x: false,
                    b: base.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0xAF);
                self.emit_mem_operand(dst.hw_enc(), base, ops.disp)?;
            }
            // IMUL r64, [base+index*scale+disp]: REX.W + 0F AF /r + SIB —
            // the scaled-index sibling of ImulRM, mirroring MovRMSib's
            // operand plumbing (validate_sib_mem_operand + emit_sib_mem_operand).
            X86Opcode::ImulRMSib => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                let index = ops.index.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing index register", opcode))
                })?;
                Self::validate_sib_mem_operand(opcode, index, ops.scale)?;
                let rex = RexPrefix {
                    w: true,
                    r: dst.hw_enc() >= 8,
                    x: index.hw_enc() >= 8,
                    b: base.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0xAF);
                self.emit_sib_mem_operand(dst.hw_enc(), base, index, ops.scale, ops.disp)?;
            }

            // =================================================================
            // Unary operations
            // =================================================================
            // NEG r/m64: REX.W + F7 /3
            X86Opcode::Neg => {
                let dst = self.require_dst(ops, opcode)?;
                self.encode_unary(0xF7, 3, dst);
            }
            // NOT r/m64: REX.W + F7 /2
            X86Opcode::Not => {
                let dst = self.require_dst(ops, opcode)?;
                self.encode_unary(0xF7, 2, dst);
            }
            // INC r/m64: REX.W + FF /0
            X86Opcode::Inc => {
                let dst = self.require_dst(ops, opcode)?;
                self.encode_unary(0xFF, 0, dst);
            }
            // DEC r/m64: REX.W + FF /1
            X86Opcode::Dec => {
                let dst = self.require_dst(ops, opcode)?;
                self.encode_unary(0xFF, 1, dst);
            }
            // IDIV r/m64: REX.W + F7 /7
            X86Opcode::Idiv => {
                let dst = self.require_dst(ops, opcode)?;
                self.encode_unary(0xF7, 7, dst);
            }
            // DIV r/m64: REX.W + F7 /6
            X86Opcode::Div => {
                let dst = self.require_dst(ops, opcode)?;
                self.encode_unary(0xF7, 6, dst);
            }
            // MUL r/m64|r/m32: [REX.W] + F7 /4
            X86Opcode::Mul => {
                let dst = self.require_dst(ops, opcode)?;
                self.encode_unary(0xF7, 4, dst);
            }
            // CDQ: 99 — sign-extend EAX into EDX:EAX (32-bit, no REX.W)
            X86Opcode::Cdq => {
                self.emit_byte(0x99);
            }
            // CQO: REX.W + 99 — sign-extend RAX into RDX:RAX (64-bit)
            X86Opcode::Cqo => {
                self.emit_byte(0x48); // REX.W
                self.emit_byte(0x99);
            }

            // =================================================================
            // Shifts
            // =================================================================
            // SHL r/m64, imm8: REX.W + C1 /4 ib
            X86Opcode::ShlRI => {
                let dst = self.require_dst(ops, opcode)?;
                self.encode_shift_ri(4, dst, ops.imm as i8);
            }
            // ROL r/m64, imm8: REX.W + C1 /0 ib
            X86Opcode::RolRI => {
                let dst = self.require_dst(ops, opcode)?;
                self.encode_shift_ri(0, dst, ops.imm as i8);
            }
            // SHR r/m64, imm8: REX.W + C1 /5 ib
            X86Opcode::ShrRI => {
                let dst = self.require_dst(ops, opcode)?;
                self.encode_shift_ri(5, dst, ops.imm as i8);
            }
            // SAR r/m64, imm8: REX.W + C1 /7 ib
            X86Opcode::SarRI => {
                let dst = self.require_dst(ops, opcode)?;
                self.encode_shift_ri(7, dst, ops.imm as i8);
            }
            // SHL r/m64, CL: REX.W + D3 /4
            X86Opcode::ShlRR => {
                let dst = self.require_dst(ops, opcode)?;
                self.encode_shift_rcl(4, dst);
            }
            // SHR r/m64, CL: REX.W + D3 /5
            X86Opcode::ShrRR => {
                let dst = self.require_dst(ops, opcode)?;
                self.encode_shift_rcl(5, dst);
            }
            // SAR r/m64, CL: REX.W + D3 /7
            X86Opcode::SarRR => {
                let dst = self.require_dst(ops, opcode)?;
                self.encode_shift_rcl(7, dst);
            }

            // =================================================================
            // MOV
            // =================================================================
            // MOV r{8,16,32,64}, imm: [66] [REX.W] + B{0,8}+rd ib/iw/id/io
            X86Opcode::MovRI => {
                let dst = self.require_dst(ops, opcode)?;
                let dst = zero_extending_movri_alias(dst, ops.imm).unwrap_or(dst);
                if !dst.is_gpr() {
                    return Err(X86EncodeError::InvalidOperands(format!(
                        "{:?}: destination must be a GPR",
                        opcode
                    )));
                }
                if dst.is_gpr8() {
                    let rex = Self::rex_oprd(dst, false);
                    self.emit_rex_forced(rex, Self::low_byte_reg_needs_rex(dst));
                    self.emit_byte(0xB0 + (dst.hw_enc() & 0x7));
                    self.emit_imm8(ops.imm as i8);
                } else {
                    if dst.is_gpr16() {
                        self.emit_byte(0x66);
                    }
                    let is_gpr64 = dst.is_gpr64();
                    let rex = Self::rex_oprd(dst, is_gpr64);
                    self.emit_rex(rex);
                    self.emit_byte(0xB8 + (dst.hw_enc() & 0x7));
                    if dst.is_gpr16() {
                        self.emit_u16_le(ops.imm as u16);
                    } else if dst.is_gpr32() {
                        self.emit_imm32(ops.imm as i32);
                    } else {
                        self.emit_imm64(ops.imm);
                    }
                }
            }
            // MOV r8, [base+disp]: 8A /r
            X86Opcode::MovRM8 | X86Opcode::VolatileMovRM8 => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                self.encode_mov_rm_width(dst, base, ops.disp, 0x8A, false, false, true)?;
            }
            // MOV r16, [base+disp]: 66 + 8B /r
            X86Opcode::MovRM16 | X86Opcode::VolatileMovRM16 => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                self.encode_mov_rm_width(dst, base, ops.disp, 0x8B, false, true, false)?;
            }
            // MOV r32, [base+disp]: 8B /r
            X86Opcode::MovRM32 | X86Opcode::VolatileMovRM32 => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                self.encode_mov_rm_width(dst, base, ops.disp, 0x8B, false, false, false)?;
            }
            // MOV r64, [base+disp]: REX.W + 8B /r
            X86Opcode::MovRM | X86Opcode::VolatileMovRM => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                let rex = RexPrefix {
                    w: true,
                    r: dst.hw_enc() >= 8,
                    x: false,
                    b: base.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x8B);
                self.emit_mem_operand(dst.hw_enc(), base, ops.disp)?;
            }
            // MOV [base+disp], r8: 88 /r
            X86Opcode::MovMR8 | X86Opcode::VolatileMovMR8 => {
                let src = self.require_dst(ops, opcode)?; // dst field holds the src register for stores
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                self.encode_mov_mr_width(src, base, ops.disp, 0x88, false, false, true)?;
            }
            // MOV [base+disp], r16: 66 + 89 /r
            X86Opcode::MovMR16 | X86Opcode::VolatileMovMR16 => {
                let src = self.require_dst(ops, opcode)?; // dst field holds the src register for stores
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                self.encode_mov_mr_width(src, base, ops.disp, 0x89, false, true, false)?;
            }
            // MOV [base+disp], r32: 89 /r
            X86Opcode::MovMR32 | X86Opcode::VolatileMovMR32 => {
                let src = self.require_dst(ops, opcode)?; // dst field holds the src register for stores
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                self.encode_mov_mr_width(src, base, ops.disp, 0x89, false, false, false)?;
            }
            // MOV [base+disp], r64: REX.W + 89 /r
            X86Opcode::MovMR | X86Opcode::VolatileMovMR => {
                let src = self.require_dst(ops, opcode)?; // dst field holds the src register for stores
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                let rex = RexPrefix {
                    w: true,
                    r: src.hw_enc() >= 8,
                    x: false,
                    b: base.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x89);
                self.emit_mem_operand(src.hw_enc(), base, ops.disp)?;
            }

            // AddRM, SubRM, CmpRM: reg-memory forms
            X86Opcode::AddRM => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                let rex = RexPrefix {
                    w: true,
                    r: dst.hw_enc() >= 8,
                    x: false,
                    b: base.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x03); // ADD r64, r/m64
                self.emit_mem_operand(dst.hw_enc(), base, ops.disp)?;
            }
            X86Opcode::SubRM => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                let rex = RexPrefix {
                    w: true,
                    r: dst.hw_enc() >= 8,
                    x: false,
                    b: base.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x2B); // SUB r64, r/m64
                self.emit_mem_operand(dst.hw_enc(), base, ops.disp)?;
            }
            X86Opcode::CmpRM => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                let rex = RexPrefix {
                    w: true,
                    r: dst.hw_enc() >= 8,
                    x: false,
                    b: base.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x3B); // CMP r64, r/m64
                self.emit_mem_operand(dst.hw_enc(), base, ops.disp)?;
            }

            // =================================================================
            // Control flow
            // =================================================================
            // RET: C3
            X86Opcode::Ret => {
                self.emit_byte(0xC3);
            }
            // CALL rel32: E8 cd
            X86Opcode::Call => {
                self.emit_byte(0xE8);
                self.emit_imm32(ops.disp as i32);
            }
            // CALL r64: FF /2
            X86Opcode::CallR => {
                let dst = self.require_dst(ops, opcode)?;
                // CALL r64 does not need REX.W (default 64-bit in long mode),
                // but needs REX.B if the register is R8-R15.
                let rex = Self::rex_oprd(dst, false);
                self.emit_rex(rex);
                self.emit_byte(0xFF);
                self.emit_modrm(ModRM::ext_reg(2, dst.hw_enc()));
            }
            // CALL [base+disp]: FF /2 (indirect call through memory)
            X86Opcode::CallM => {
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                // No REX.W needed (default 64-bit in long mode),
                // but need REX.B if the base register is R8-R15.
                let rex = RexPrefix {
                    w: false,
                    r: false,
                    x: false,
                    b: base.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0xFF);
                self.emit_mem_operand(2, base, ops.disp)?;
            }
            // JMP rel32: E9 cd
            X86Opcode::Jmp => {
                self.emit_byte(0xE9);
                self.emit_imm32(ops.disp as i32);
            }
            // JMP r64: FF /4 — indirect near jump through a register.
            // Mirrors CallR (FF /2), extension field /4 instead of /2. No REX.W
            // (64-bit default in long mode), REX.B if the register is R8-R15.
            X86Opcode::JmpR => {
                let dst = self.require_dst(ops, opcode)?;
                let rex = Self::rex_oprd(dst, false);
                self.emit_rex(rex);
                self.emit_byte(0xFF);
                self.emit_modrm(ModRM::ext_reg(4, dst.hw_enc()));
            }
            // Jcc rel32: 0F 80+cc cd
            X86Opcode::Jcc => {
                let cc = ops.cc.ok_or_else(|| {
                    X86EncodeError::InvalidOperands("Jcc: missing condition code".into())
                })?;
                self.emit_byte(0x0F);
                self.emit_byte(0x80 + cc.encoding());
                self.emit_imm32(ops.disp as i32);
            }

            // =================================================================
            // Stack
            // =================================================================
            // PUSH r64: 50+rd (no REX.W, only REX.B if R8-R15)
            X86Opcode::Push => {
                let dst = self.require_dst(ops, opcode)?;
                let rex = Self::rex_oprd(dst, false);
                self.emit_rex(rex);
                self.emit_byte(0x50 + (dst.hw_enc() & 0x7));
            }
            // POP r64: 58+rd (no REX.W, only REX.B if R8-R15)
            X86Opcode::Pop => {
                let dst = self.require_dst(ops, opcode)?;
                let rex = Self::rex_oprd(dst, false);
                self.emit_rex(rex);
                self.emit_byte(0x58 + (dst.hw_enc() & 0x7));
            }

            // =================================================================
            // LEA
            // =================================================================
            // LEA r64, [base+disp]: REX.W + 8D /r
            X86Opcode::Lea => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                let rex = RexPrefix {
                    w: true,
                    r: dst.hw_enc() >= 8,
                    x: false,
                    b: base.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x8D);
                self.emit_mem_operand(dst.hw_enc(), base, ops.disp)?;
            }
            // LEA r64, [base + index*scale + disp]: REX.W + 8D /r + SIB
            X86Opcode::LeaSib => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                let index = ops.index.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing index register", opcode))
                })?;
                Self::validate_sib_mem_operand(opcode, index, ops.scale)?;
                let rex = RexPrefix {
                    w: true,
                    r: dst.hw_enc() >= 8,
                    x: index.hw_enc() >= 8,
                    b: base.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x8D);
                self.emit_sib_mem_operand(dst.hw_enc(), base, index, ops.scale, ops.disp)?;
            }

            // =================================================================
            // LEA RIP-relative
            // =================================================================
            // LEA r64, [RIP+disp32]: REX.W + 8D + ModRM(00 reg 101) + disp32
            X86Opcode::LeaRip => {
                let dst = self.require_dst(ops, opcode)?;
                let rex = RexPrefix {
                    w: true,
                    r: dst.hw_enc() >= 8,
                    x: false,
                    b: false,
                };
                self.emit_rex(rex);
                self.emit_byte(0x8D);
                self.emit_rip_relative(dst.hw_enc(), ops.disp)?;
            }
            // MOV r64, [RIP+disp32]: REX.W + 8B + ModRM(00 reg 101) + disp32
            // MovRipRelTlv is byte-identical (the Mach-O @TLVP form differs
            // only in the relocation recorded by the pipeline).
            X86Opcode::MovRipRel | X86Opcode::MovRipRelTlv => {
                let dst = self.require_dst(ops, opcode)?;
                let rex = RexPrefix {
                    w: true,
                    r: dst.hw_enc() >= 8,
                    x: false,
                    b: false,
                };
                self.emit_rex(rex);
                self.emit_byte(0x8B);
                self.emit_rip_relative(dst.hw_enc(), ops.disp)?;
            }
            // LOCK CMPXCHG r/m8, r8 (F0 [REX] 0F B0 /r) and
            // LOCK CMPXCHG r/m16, r16 (F0 66 [REX] 0F B1 /r): narrow memory
            // compare-exchange. Same operand shape as the memory form of
            // `Cmpxchg` (dst = desired-value register, base+disp = memory);
            // the register field uses the byte/word alias of the 32-bit
            // carrier (REX-extended so SIL/DIL/SPL/BPL encode correctly),
            // mirroring `encode_atomic_rmw_cas_loop_narrow`'s CMPXCHG step.
            X86Opcode::Cmpxchg8 | X86Opcode::Cmpxchg16 => {
                let width_bits: u8 = if opcode == X86Opcode::Cmpxchg16 { 16 } else { 8 };
                let src = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!(
                        "{:?}: narrow CMPXCHG requires a memory operand",
                        opcode
                    ))
                })?;
                let src_narrow = Self::atomic_rmw_narrow_alias(src, width_bits).ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!(
                        "{:?}: narrow CMPXCHG requires a GPR source register",
                        opcode
                    ))
                })?;
                if !base.is_gpr64() {
                    return Err(X86EncodeError::InvalidOperands(format!(
                        "{:?}: narrow CMPXCHG requires a 64-bit base register",
                        opcode
                    )));
                }
                let acc = if width_bits == 16 {
                    x86_64_regs::AX
                } else {
                    x86_64_regs::AL
                };
                if x86_64_regs::x86_regs_overlap(src_narrow, acc)
                    || x86_64_regs::x86_regs_overlap(base, acc)
                {
                    return Err(X86EncodeError::InvalidOperands(format!(
                        "{:?}: source/base conflicts with the fixed RAX accumulator",
                        opcode
                    )));
                }
                self.emit_byte(0xF0); // LOCK prefix
                if width_bits == 16 {
                    self.emit_byte(0x66);
                    let rex = Self::rex_rr(src_narrow, base, false);
                    self.emit_rex(rex);
                    self.emit_byte(0x0F);
                    self.emit_byte(0xB1);
                } else {
                    self.emit_mem_reg_rex(src_narrow, base, false, true);
                    self.emit_byte(0x0F);
                    self.emit_byte(0xB0);
                }
                self.emit_mem_operand(src_narrow.hw_enc(), base, ops.disp)?;
            }

            // =================================================================
            // Scaled-index (SIB) memory addressing
            // =================================================================
            // MOV r64, [base+index*scale+disp]: REX.W + 8B /r + SIB
            X86Opcode::MovRMSib => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                let index = ops.index.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing index register", opcode))
                })?;
                Self::validate_sib_mem_operand(opcode, index, ops.scale)?;
                let rex = RexPrefix {
                    w: true,
                    r: dst.hw_enc() >= 8,
                    x: index.hw_enc() >= 8,
                    b: base.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x8B);
                self.emit_sib_mem_operand(dst.hw_enc(), base, index, ops.scale, ops.disp)?;
            }
            // MOVSXD r64, [base+index*scale+disp] (m32): REX.W + 63 /r + SIB.
            // Sign-extends the 32-bit memory dword to 64 bits. Mirrors MovRMSib
            // (8B) with opcode 63 instead. Used to load a signed jump-table entry.
            X86Opcode::MovsxdRMSib => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                let index = ops.index.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing index register", opcode))
                })?;
                Self::validate_sib_mem_operand(opcode, index, ops.scale)?;
                let rex = RexPrefix {
                    w: true,
                    r: dst.hw_enc() >= 8,
                    x: index.hw_enc() >= 8,
                    b: base.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x63);
                self.emit_sib_mem_operand(dst.hw_enc(), base, index, ops.scale, ops.disp)?;
            }
            // MOV [base+index*scale+disp], r64: REX.W + 89 /r + SIB
            X86Opcode::MovMRSib => {
                let src = self.require_dst(ops, opcode)?; // dst field holds src for stores
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                let index = ops.index.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing index register", opcode))
                })?;
                Self::validate_sib_mem_operand(opcode, index, ops.scale)?;
                let rex = RexPrefix {
                    w: true,
                    r: src.hw_enc() >= 8,
                    x: index.hw_enc() >= 8,
                    b: base.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x89);
                self.emit_sib_mem_operand(src.hw_enc(), base, index, ops.scale, ops.disp)?;
            }

            // MOV r32, [base+index*scale+disp]: 8B /r + SIB (no REX.W;
            // REX only for extended regs). 32-bit sibling of MovRMSib.
            X86Opcode::MovRM32Sib => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                let index = ops.index.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing index register", opcode))
                })?;
                Self::validate_sib_mem_operand(opcode, index, ops.scale)?;
                let rex = RexPrefix {
                    w: false,
                    r: dst.hw_enc() >= 8,
                    x: index.hw_enc() >= 8,
                    b: base.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x8B);
                self.emit_sib_mem_operand(dst.hw_enc(), base, index, ops.scale, ops.disp)?;
            }
            // MOV r8, [base+index*scale+disp]: 8A /r + SIB. 8-bit sibling of
            // MovRMSib/MovRM32Sib.
            //
            // ⚑ The REX here is FORCED for dst in {SPL,BPL,SIL,DIL} (hw_enc low
            // three bits 4..=7). Without a REX byte those encodings name
            // AH/CH/DH/BH instead, so omitting it would silently read the WRONG
            // register — `low_byte_reg_needs_rex` is the shared guard, the same
            // one MovRM8 uses via `encode_mov_rm_width`.
            X86Opcode::MovRM8Sib => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                let index = ops.index.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing index register", opcode))
                })?;
                Self::validate_sib_mem_operand(opcode, index, ops.scale)?;
                let rex = RexPrefix {
                    w: false,
                    r: dst.hw_enc() >= 8,
                    x: index.hw_enc() >= 8,
                    b: base.hw_enc() >= 8,
                };
                self.emit_rex_forced(rex, Self::low_byte_reg_needs_rex(dst));
                self.emit_byte(0x8A);
                self.emit_sib_mem_operand(dst.hw_enc(), base, index, ops.scale, ops.disp)?;
            }
            // MOV [base+index*scale+disp], r8: 88 /r + SIB. Same forced-REX rule
            // as MovRM8Sib above, applied to the STORED register.
            X86Opcode::MovMR8Sib => {
                let src = self.require_dst(ops, opcode)?; // dst field holds src for stores
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                let index = ops.index.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing index register", opcode))
                })?;
                Self::validate_sib_mem_operand(opcode, index, ops.scale)?;
                let rex = RexPrefix {
                    w: false,
                    r: src.hw_enc() >= 8,
                    x: index.hw_enc() >= 8,
                    b: base.hw_enc() >= 8,
                };
                self.emit_rex_forced(rex, Self::low_byte_reg_needs_rex(src));
                self.emit_byte(0x88);
                self.emit_sib_mem_operand(src.hw_enc(), base, index, ops.scale, ops.disp)?;
            }
            // MOV [base+index*scale+disp], r32: 89 /r + SIB (no REX.W).
            X86Opcode::MovMR32Sib => {
                let src = self.require_dst(ops, opcode)?; // dst field holds src for stores
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                let index = ops.index.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing index register", opcode))
                })?;
                Self::validate_sib_mem_operand(opcode, index, ops.scale)?;
                let rex = RexPrefix {
                    w: false,
                    r: src.hw_enc() >= 8,
                    x: index.hw_enc() >= 8,
                    b: base.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x89);
                self.emit_sib_mem_operand(src.hw_enc(), base, index, ops.scale, ops.disp)?;
            }

            // =================================================================
            // MOVZX / MOVSX
            // =================================================================
            // MOVZX r64, r/m8: REX.W + 0F B6 /r (mod=11 for reg-reg)
            // MOVZX r64, r/m16: REX.W + 0F B7 /r
            // We encode the r/m8 form by default (8->64 zero-extend).
            // The ISel should pick between B6 (byte) and B7 (word) variants.
            X86Opcode::Movzx => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                let rex = Self::rex_rr64(dst, src);
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                // Use B6 for 8-bit source, B7 for 16-bit. Default to B6.
                self.emit_byte(0xB6);
                self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
            }
            // MOVSXD r64, r/m32: REX.W + 63 /r (sign-extend 32->64)
            X86Opcode::Movsx => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                let rex = Self::rex_rr64(dst, src);
                self.emit_rex(rex);
                self.emit_byte(0x63);
                self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
            }
            // MOVZX r64, r/m16: REX.W + 0F B7 /r (zero-extend word to qword)
            X86Opcode::MovzxW => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_0f_rr64(0xB7, dst, src);
            }
            // MOVSX r64, r/m8: REX.W + 0F BE /r (sign-extend byte to qword)
            X86Opcode::MovsxB => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_0f_rr64(0xBE, dst, src);
            }
            // MOVSX r64, r/m16: REX.W + 0F BF /r (sign-extend word to qword)
            X86Opcode::MovsxW => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_0f_rr64(0xBF, dst, src);
            }

            // =================================================================
            // SSE scalar double-precision (F2 0F prefix)
            // =================================================================
            // ADDSD xmm, xmm: F2 0F 58 /r
            X86Opcode::Addsd => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0xF2, 0x58, dst, src);
            }
            // SUBSD xmm, xmm: F2 0F 5C /r
            X86Opcode::Subsd => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0xF2, 0x5C, dst, src);
            }
            // MULSD xmm, xmm: F2 0F 59 /r
            X86Opcode::Mulsd => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0xF2, 0x59, dst, src);
            }
            // DIVSD xmm, xmm: F2 0F 5E /r
            X86Opcode::Divsd => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0xF2, 0x5E, dst, src);
            }
            // SQRTSD xmm, xmm: F2 0F 51 /r
            X86Opcode::Sqrtsd => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0xF2, 0x51, dst, src);
            }
            // ANDPD xmm, xmm: 66 0F 54 /r
            X86Opcode::Andpd => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0x66, 0x54, dst, src);
            }
            // ROUNDSD xmm, xmm, imm8: 66 0F 3A 0B /r ib (SSE4.1).
            // imm8 = rounding-mode selector (1=floor, 2=ceil, 3=trunc).
            X86Opcode::Roundsd => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_0f3a_rr_imm(0x0B, dst, src, ops.imm as u8);
            }
            // MINSD xmm, xmm: F2 0F 5D /r
            X86Opcode::Minsd => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0xF2, 0x5D, dst, src);
            }
            // MAXSD xmm, xmm: F2 0F 5F /r
            X86Opcode::Maxsd => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0xF2, 0x5F, dst, src);
            }
            // MINSS xmm, xmm: F3 0F 5D /r
            X86Opcode::Minss => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0xF3, 0x5D, dst, src);
            }
            // MAXSS xmm, xmm: F3 0F 5F /r
            X86Opcode::Maxss => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0xF3, 0x5F, dst, src);
            }
            // CMPSD xmm, xmm, imm8: F2 0F C2 /r ib
            X86Opcode::Cmpsd => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr_imm(0xF2, 0xC2, dst, src, ops.imm as u8);
            }
            // CMPSS xmm, xmm, imm8: F3 0F C2 /r ib
            X86Opcode::Cmpss => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr_imm(0xF3, 0xC2, dst, src, ops.imm as u8);
            }
            // MOVSD xmm, xmm: F2 0F 10 /r
            X86Opcode::MovsdRR => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0xF2, 0x10, dst, src);
            }
            // MOVSD xmm, [mem]: F2 0F 10 /r
            X86Opcode::MovsdRM | X86Opcode::VolatileMovsdRM => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                self.encode_sse_rm(0xF2, 0x10, dst, base, ops.disp)?;
            }
            // MOVSD xmm, [base+index*scale+disp]: F2 0F 10 /r + SIB
            X86Opcode::MovsdRMSib => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                let index = ops.index.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing index register", opcode))
                })?;
                Self::validate_sib_mem_operand(opcode, index, ops.scale)?;
                self.encode_sse_rm_sib(0xF2, 0x10, dst, base, index, ops.scale, ops.disp)?;
            }
            // MOVSS xmm, [base+index*scale+disp]: F3 0F 10 /r + SIB
            X86Opcode::MovssRMSib => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                let index = ops.index.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing index register", opcode))
                })?;
                Self::validate_sib_mem_operand(opcode, index, ops.scale)?;
                self.encode_sse_rm_sib(0xF3, 0x10, dst, base, index, ops.scale, ops.disp)?;
            }
            // MOVSD [mem], xmm: F2 0F 11 /r
            X86Opcode::MovsdMR | X86Opcode::VolatileMovsdMR => {
                let src = self.require_dst(ops, opcode)?; // dst field holds src for stores
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                self.encode_sse_mr(0xF2, 0x11, src, base, ops.disp)?;
            }
            // UCOMISD xmm, xmm: 66 0F 2E /r
            X86Opcode::Ucomisd => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0x66, 0x2E, dst, src);
            }
            // MOVDQU xmm, [mem]: F3 0F 6F /r
            X86Opcode::MovdquRM | X86Opcode::VolatileMovdquRM => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                self.encode_sse_rm(0xF3, 0x6F, dst, base, ops.disp)?;
            }
            // MOVDQU [mem], xmm: F3 0F 7F /r
            X86Opcode::MovdquMR | X86Opcode::VolatileMovdquMR => {
                let src = self.require_dst(ops, opcode)?; // dst field holds src for stores
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                self.encode_sse_mr(0xF3, 0x7F, src, base, ops.disp)?;
            }

            // =================================================================
            // SSE2 packed integer
            // =================================================================
            X86Opcode::Pand
            | X86Opcode::Pandn
            | X86Opcode::Por
            | X86Opcode::Pxor
            | X86Opcode::Pcmpeqb
            | X86Opcode::Pcmpeqw
            | X86Opcode::Pcmpgtb
            | X86Opcode::Pcmpgtw
            | X86Opcode::Pcmpeqd
            | X86Opcode::Pcmpgtd
            | X86Opcode::Paddb
            | X86Opcode::Paddw
            | X86Opcode::Paddd
            | X86Opcode::Psubb
            | X86Opcode::Psubw
            | X86Opcode::Psubd
            | X86Opcode::Pmullw
            | X86Opcode::Paddq
            | X86Opcode::Psubq
            | X86Opcode::Pmuludq
            | X86Opcode::Punpckldq
            | X86Opcode::Punpcklqdq
            | X86Opcode::Pmulld
            | X86Opcode::Psadbw
            | X86Opcode::Pcmpeqq
            | X86Opcode::Pcmpgtq
            | X86Opcode::Ptest
            | X86Opcode::Pblendvb
            | X86Opcode::Pshufd
            | X86Opcode::Pslld
            | X86Opcode::Psrld
            | X86Opcode::Psrad
            | X86Opcode::Psllq
            | X86Opcode::Psrlq
            | X86Opcode::Punpcklbw
            | X86Opcode::Punpckhbw
            | X86Opcode::Packuswb
            | X86Opcode::Pmovmskb
            | X86Opcode::MovdqaRR
            | X86Opcode::MovdqaRM
            | X86Opcode::MovdqaMR
            | X86Opcode::VolatileMovdqaRM
            | X86Opcode::VolatileMovdqaMR => {
                self.encode_sse2_packed_x86_opcode(opcode, ops)?;
            }

            // =================================================================
            // SSE packed single-precision FP arithmetic (`<4 x f32>`)
            //
            // ADDPS/SUBPS/MULPS/DIVPS use the legacy SSE two-byte map with NO
            // mandatory prefix: `0F 58/5C/59/5E /r`. XMM register-register only.
            // =================================================================
            X86Opcode::Addps => {
                let (dst, src) = self.require_x86_sse2_xmm_rr(ops, opcode)?;
                self.encode_sse_rr(0x00, 0x58, dst, src);
            }
            X86Opcode::Subps => {
                let (dst, src) = self.require_x86_sse2_xmm_rr(ops, opcode)?;
                self.encode_sse_rr(0x00, 0x5C, dst, src);
            }
            X86Opcode::Mulps => {
                let (dst, src) = self.require_x86_sse2_xmm_rr(ops, opcode)?;
                self.encode_sse_rr(0x00, 0x59, dst, src);
            }
            X86Opcode::Divps => {
                let (dst, src) = self.require_x86_sse2_xmm_rr(ops, opcode)?;
                self.encode_sse_rr(0x00, 0x5E, dst, src);
            }

            // =================================================================
            // SSE2 packed double-precision FP arithmetic (`<2 x f64>`)
            //
            // ADDPD/SUBPD/MULPD/DIVPD share the same second opcode bytes as the
            // single-precision forms but carry the mandatory 66 operand-size
            // prefix: `66 0F 58/5C/59/5E /r`. XMM register-register only.
            // =================================================================
            X86Opcode::Addpd => {
                let (dst, src) = self.require_x86_sse2_xmm_rr(ops, opcode)?;
                self.encode_sse_rr(0x66, 0x58, dst, src);
            }
            X86Opcode::Subpd => {
                let (dst, src) = self.require_x86_sse2_xmm_rr(ops, opcode)?;
                self.encode_sse_rr(0x66, 0x5C, dst, src);
            }
            X86Opcode::Mulpd => {
                let (dst, src) = self.require_x86_sse2_xmm_rr(ops, opcode)?;
                self.encode_sse_rr(0x66, 0x59, dst, src);
            }
            X86Opcode::Divpd => {
                let (dst, src) = self.require_x86_sse2_xmm_rr(ops, opcode)?;
                self.encode_sse_rr(0x66, 0x5E, dst, src);
            }

            // =================================================================
            // SSE4.1 packed lane insert/extract
            // =================================================================
            X86Opcode::Pinsrd | X86Opcode::Pextrd | X86Opcode::Pinsrq | X86Opcode::Pextrq => {
                self.encode_sse41_lane_x86_opcode(opcode, ops)?;
            }

            // =================================================================
            // SSE scalar single-precision (F3 0F prefix)
            // =================================================================
            // ADDSS xmm, xmm: F3 0F 58 /r
            X86Opcode::Addss => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0xF3, 0x58, dst, src);
            }
            // SUBSS xmm, xmm: F3 0F 5C /r
            X86Opcode::Subss => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0xF3, 0x5C, dst, src);
            }
            // MULSS xmm, xmm: F3 0F 59 /r
            X86Opcode::Mulss => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0xF3, 0x59, dst, src);
            }
            // DIVSS xmm, xmm: F3 0F 5E /r
            X86Opcode::Divss => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0xF3, 0x5E, dst, src);
            }
            // SQRTSS xmm, xmm: F3 0F 51 /r
            X86Opcode::Sqrtss => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0xF3, 0x51, dst, src);
            }
            // ANDPS xmm, xmm: 0F 54 /r
            X86Opcode::Andps => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0, 0x54, dst, src);
            }
            // ROUNDSS xmm, xmm, imm8: 66 0F 3A 0A /r ib (SSE4.1).
            // imm8 = rounding-mode selector (1=floor, 2=ceil, 3=trunc).
            X86Opcode::Roundss => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_0f3a_rr_imm(0x0A, dst, src, ops.imm as u8);
            }
            // MOVSS xmm, xmm: F3 0F 10 /r
            X86Opcode::MovssRR => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0xF3, 0x10, dst, src);
            }
            // MOVSS xmm, [mem]: F3 0F 10 /r
            X86Opcode::MovssRM | X86Opcode::VolatileMovssRM => {
                let dst = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                self.encode_sse_rm(0xF3, 0x10, dst, base, ops.disp)?;
            }
            // MOVSS [mem], xmm: F3 0F 11 /r
            X86Opcode::MovssMR | X86Opcode::VolatileMovssMR => {
                let src = self.require_dst(ops, opcode)?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                self.encode_sse_mr(0xF3, 0x11, src, base, ops.disp)?;
            }
            // UCOMISS xmm, xmm: 0F 2E /r (no prefix)
            X86Opcode::Ucomiss => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0, 0x2E, dst, src);
            }

            // =================================================================
            // SSE RIP-relative constant pool loads
            // =================================================================
            // MOVSS xmm, [RIP+disp32]: F3 [REX] 0F 10 ModRM(00 reg 101) disp32
            X86Opcode::MovssRipRel => {
                let dst = self.require_dst(ops, opcode)?;
                self.encode_sse_rip_rel(0xF3, 0x10, dst, ops.disp)?;
            }
            // MOVSD xmm, [RIP+disp32]: F2 [REX] 0F 10 ModRM(00 reg 101) disp32
            X86Opcode::MovsdRipRel => {
                let dst = self.require_dst(ops, opcode)?;
                self.encode_sse_rip_rel(0xF2, 0x10, dst, ops.disp)?;
            }

            // =================================================================
            // SSE type conversion
            // =================================================================
            // CVTSI2SD xmm, r64: F2 REX.W 0F 2A /r
            X86Opcode::Cvtsi2sd => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.emit_byte(0xF2);
                let rex = RexPrefix {
                    w: true,
                    r: dst.hw_enc() >= 8,
                    x: false,
                    b: src.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0x2A);
                self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
            }
            // CVTSD2SI r64, xmm: F2 REX.W 0F 2D /r (MXCSR rounding mode)
            X86Opcode::Cvtsd2si => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.emit_byte(0xF2);
                let rex = RexPrefix {
                    w: true,
                    r: dst.hw_enc() >= 8,
                    x: false,
                    b: src.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0x2D);
                self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
            }
            // CVTTSD2SI r64, xmm: F2 REX.W 0F 2C /r (truncate)
            X86Opcode::Cvttsd2si => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.emit_byte(0xF2);
                let rex = Self::rex_rr64(dst, src);
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0x2C);
                self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
            }
            // CVTSI2SS xmm, r64: F3 REX.W 0F 2A /r
            X86Opcode::Cvtsi2ss => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.emit_byte(0xF3);
                let rex = RexPrefix {
                    w: true,
                    r: dst.hw_enc() >= 8,
                    x: false,
                    b: src.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0x2A);
                self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
            }
            // CVTSS2SI r64, xmm: F3 REX.W 0F 2D /r (MXCSR rounding mode)
            X86Opcode::Cvtss2si => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.emit_byte(0xF3);
                let rex = RexPrefix {
                    w: true,
                    r: dst.hw_enc() >= 8,
                    x: false,
                    b: src.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0x2D);
                self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
            }
            // CVTTSS2SI r64, xmm: F3 REX.W 0F 2C /r (truncate)
            X86Opcode::Cvttss2si => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.emit_byte(0xF3);
                let rex = Self::rex_rr64(dst, src);
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0x2C);
                self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
            }
            // CVTSD2SS xmm, xmm: F2 0F 5A /r
            X86Opcode::Cvtsd2ss => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0xF2, 0x5A, dst, src);
            }
            // CVTSS2SD xmm, xmm: F3 0F 5A /r
            X86Opcode::Cvtss2sd => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_sse_rr(0xF3, 0x5A, dst, src);
            }

            // =================================================================
            // CMOVcc — conditional move
            // =================================================================
            // CMOVcc r64, r64: REX.W + 0F 40+cc /r
            X86Opcode::Cmovcc => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                let cc = ops.cc.ok_or_else(|| {
                    X86EncodeError::InvalidOperands("CMOVcc: missing condition code".into())
                })?;
                let rex = Self::rex_rr64(dst, src);
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0x40 + cc.encoding());
                self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
            }
            // CMOVcc r32, r32: 0F 40+cc /r, optional REX.R/B but no REX.W.
            X86Opcode::Cmovcc32 => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                let cc = ops.cc.ok_or_else(|| {
                    X86EncodeError::InvalidOperands("CMOVcc32: missing condition code".into())
                })?;
                let rex = Self::rex_rr(dst, src, false);
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0x40 + cc.encoding());
                self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
            }

            // =================================================================
            // SETcc — set byte on condition
            // =================================================================
            // SETcc r/m8: 0F 90+cc /0 (ModR/M mod=11, reg=0, rm=reg)
            // Needs REX prefix if dst is R8-R15 or SPL/BPL/SIL/DIL.
            X86Opcode::Setcc => {
                let dst = self.require_dst(ops, opcode)?;
                let cc = ops.cc.ok_or_else(|| {
                    X86EncodeError::InvalidOperands("SETcc: missing condition code".into())
                })?;
                // SETcc operates on 8-bit register, no REX.W.
                // Need REX.B if destination encoding >= 8.
                let rex = RexPrefix {
                    w: false,
                    r: false,
                    x: false,
                    b: dst.hw_enc() >= 8,
                };
                self.emit_rex_forced(rex, Self::low_byte_reg_needs_rex(dst));
                self.emit_byte(0x0F);
                self.emit_byte(0x90 + cc.encoding());
                self.emit_modrm(ModRM::ext_reg(0, dst.hw_enc()));
            }

            // =================================================================
            // Bit manipulation
            // =================================================================
            // BSF r64, r64: REX.W + 0F BC /r
            X86Opcode::Bsf => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_0f_rr64(0xBC, dst, src);
            }
            // BSR r64, r64: REX.W + 0F BD /r
            X86Opcode::Bsr => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_0f_rr64(0xBD, dst, src);
            }
            // TZCNT r64, r64: F3 REX.W + 0F BC /r (rep-prefixed BSF)
            X86Opcode::Tzcnt => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.emit_byte(0xF3); // REP prefix
                let rex = Self::rex_rr64(dst, src);
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0xBC);
                self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
            }
            // LZCNT r64, r64: F3 REX.W + 0F BD /r (rep-prefixed BSR)
            X86Opcode::Lzcnt => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.emit_byte(0xF3); // REP prefix
                let rex = Self::rex_rr64(dst, src);
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0xBD);
                self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
            }
            // POPCNT r64/r32, r64/r32: F3 [REX.W] + 0F B8 /r
            X86Opcode::Popcnt => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.emit_byte(0xF3); // REP prefix
                let rex = Self::rex_rr(dst, src, !(dst.is_gpr32() && src.is_gpr32()));
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0xB8);
                self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
            }
            // BT r/m64, imm8: REX.W + 0F BA /4 ib
            X86Opcode::BtRI => {
                let dst = self.require_dst(ops, opcode)?;
                // FINDING #8: imm8 here is a BIT INDEX into a 64-bit operand, so
                // the only valid range is 0..=63. Only a single imm8 byte is
                // emitted, so an i32 guard would still let e.g. 300 truncate;
                // bound the bit index directly, mirroring require_sse41_dword_lane.
                if !(0..=63).contains(&ops.imm) {
                    return Err(X86EncodeError::InvalidOperands(format!(
                        "{:?}: bit index {} outside 0..63",
                        opcode, ops.imm
                    )));
                }
                let rex = Self::rex_m64(dst);
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0xBA);
                self.emit_modrm(ModRM::ext_reg(4, dst.hw_enc()));
                self.emit_imm8(ops.imm as i8);
            }
            // BSWAP r64: REX.W + 0F C8+rd
            X86Opcode::Bswap => {
                let dst = self.require_dst(ops, opcode)?;
                let rex = Self::rex_oprd(dst, true);
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0xC8 + (dst.hw_enc() & 0x7));
            }

            // =================================================================
            // Atomic / exchange
            // =================================================================
            // XCHG r/m64, r64: REX.W + 87 /r
            X86Opcode::Xchg => {
                if let Some(base) = ops.base {
                    let dst = self.require_dst(ops, opcode)?;
                    if !(dst.is_gpr32() || dst.is_gpr64()) {
                        return Err(X86EncodeError::InvalidOperands(format!(
                            "{:?}: memory XCHG requires a 32-bit or 64-bit GPR",
                            opcode
                        )));
                    }
                    let rex = Self::rex_rr(dst, base, !dst.is_gpr32());
                    self.emit_rex(rex);
                    self.emit_byte(0x87);
                    self.emit_mem_operand(dst.hw_enc(), base, ops.disp)?;
                    return Ok(self.position() - start);
                }
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.encode_alu_rr(0x87, dst, src);
            }
            // LOCK CMPXCHG r/m64, r64: F0 + REX.W + 0F B1 /r
            // Compare RAX with r/m64; if equal, ZF is set and r64 is
            // stored into r/m64. Otherwise, r/m64 is loaded into RAX.
            X86Opcode::Cmpxchg => {
                if let Some(base) = ops.base {
                    let src = self.require_dst(ops, opcode)?;
                    if !(src.is_gpr32() || src.is_gpr64()) {
                        return Err(X86EncodeError::InvalidOperands(format!(
                            "{:?}: memory CMPXCHG requires a 32-bit or 64-bit GPR source",
                            opcode
                        )));
                    }
                    self.emit_byte(0xF0); // LOCK prefix
                    let rex = Self::rex_rr(src, base, !src.is_gpr32());
                    self.emit_rex(rex);
                    self.emit_byte(0x0F);
                    self.emit_byte(0xB1);
                    self.emit_mem_operand(src.hw_enc(), base, ops.disp)?;
                    return Ok(self.position() - start);
                }
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.emit_byte(0xF0); // LOCK prefix
                let rex = Self::rex_rr64(src, dst);
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0xB1);
                self.emit_modrm(ModRM::reg_reg(src.hw_enc(), dst.hw_enc()));
            }
            // Pseudo expansion:
            //   mov   acc, [base+disp]
            // retry:
            //   mov   r10, acc
            //   op    r10, src
            //   lock cmpxchg [base+disp], r10
            //   jne   retry
            //   mov   dst, acc
            X86Opcode::AtomicRmwCasLoop => {
                let dst = self.require_dst(ops, opcode)?;
                let src = ops.src.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!(
                        "{:?}: missing source register",
                        opcode
                    ))
                })?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                self.encode_atomic_rmw_cas_loop(dst, src, base, ops.disp, ops.imm)?;
            }
            X86Opcode::AtomicRmwCasLoop8 | X86Opcode::AtomicRmwCasLoop16 => {
                let dst = self.require_dst(ops, opcode)?;
                let src = ops.src.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!(
                        "{:?}: missing source register",
                        opcode
                    ))
                })?;
                let base = ops.base.ok_or_else(|| {
                    X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
                })?;
                let width_bits = if opcode == X86Opcode::AtomicRmwCasLoop16 {
                    16
                } else {
                    8
                };
                self.encode_atomic_rmw_cas_loop_narrow(
                    dst, src, base, ops.disp, ops.imm, width_bits,
                )?;
            }

            // =================================================================
            // GPR <-> XMM transfers
            // =================================================================
            // MOVD xmm, r/m32: 66 0F 6E /r (no REX.W, 32-bit)
            X86Opcode::MovdToXmm => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.emit_byte(0x66);
                let rex = Self::rex_xmm_rr(dst, src);
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0x6E);
                self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
            }
            // MOVD r/m32, xmm: 66 0F 7E /r (no REX.W, 32-bit)
            X86Opcode::MovdFromXmm => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                // dst=GPR (in rm), src=XMM (in reg)
                self.emit_byte(0x66);
                let rex = Self::rex_xmm_rr(src, dst);
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0x7E);
                self.emit_modrm(ModRM::reg_reg(src.hw_enc(), dst.hw_enc()));
            }
            // MOVQ xmm, r/m64: 66 REX.W 0F 6E /r (64-bit with REX.W)
            X86Opcode::MovqToXmm => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                self.emit_byte(0x66);
                let rex = RexPrefix {
                    w: true,
                    r: dst.hw_enc() >= 8,
                    x: false,
                    b: src.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0x6E);
                self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
            }
            // MOVQ r/m64, xmm: 66 REX.W 0F 7E /r (64-bit with REX.W)
            X86Opcode::MovqFromXmm => {
                let (dst, src) = self.require_rr(ops, opcode)?;
                // dst=GPR (in rm), src=XMM (in reg)
                self.emit_byte(0x66);
                let rex = RexPrefix {
                    w: true,
                    r: src.hw_enc() >= 8,
                    x: false,
                    b: dst.hw_enc() >= 8,
                };
                self.emit_rex(rex);
                self.emit_byte(0x0F);
                self.emit_byte(0x7E);
                self.emit_modrm(ModRM::reg_reg(src.hw_enc(), dst.hw_enc()));
            }
        }

        Ok(self.position() - start)
    }

    /// Encode a standalone SSE2 packed integer instruction.
    ///
    /// This is retained for direct encoder users. Pipeline callers dispatch
    /// the same encodings through the corresponding [`X86Opcode`] variants.
    pub fn encode_sse2_packed_instruction(
        &mut self,
        opcode: X86Sse2PackedOpcode,
        ops: &X86InstOperands,
    ) -> Result<usize, X86EncodeError> {
        let start = self.position();
        self.encode_sse2_packed_x86_opcode(opcode.to_x86_opcode(), ops)?;
        Ok(self.position() - start)
    }

    fn encode_sse2_packed_x86_opcode(
        &mut self,
        opcode: X86Opcode,
        ops: &X86InstOperands,
    ) -> Result<(), X86EncodeError> {
        match opcode {
            // PAND xmm, xmm: 66 0F DB /r
            X86Opcode::Pand => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0xDB)?;
            }
            // PANDN xmm, xmm: 66 0F DF /r
            X86Opcode::Pandn => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0xDF)?;
            }
            // POR xmm, xmm: 66 0F EB /r
            X86Opcode::Por => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0xEB)?;
            }
            // PXOR xmm, xmm: 66 0F EF /r
            X86Opcode::Pxor => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0xEF)?;
            }
            // PCMPEQB xmm, xmm/m128: 66 0F 74 /r
            X86Opcode::Pcmpeqb => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0x74)?;
            }
            // PCMPEQW xmm, xmm/m128: 66 0F 75 /r
            X86Opcode::Pcmpeqw => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0x75)?;
            }
            // PCMPGTB xmm, xmm/m128: 66 0F 64 /r
            X86Opcode::Pcmpgtb => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0x64)?;
            }
            // PCMPGTW xmm, xmm/m128: 66 0F 65 /r
            X86Opcode::Pcmpgtw => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0x65)?;
            }
            // PCMPEQD xmm, xmm: 66 0F 76 /r
            X86Opcode::Pcmpeqd => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0x76)?;
            }
            // PCMPGTD xmm, xmm: 66 0F 66 /r
            X86Opcode::Pcmpgtd => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0x66)?;
            }
            // PADDB xmm, xmm: 66 0F FC /r
            X86Opcode::Paddb => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0xFC)?;
            }
            // PADDW xmm, xmm: 66 0F FD /r
            X86Opcode::Paddw => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0xFD)?;
            }
            // PADDD xmm, xmm: 66 0F FE /r
            X86Opcode::Paddd => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0xFE)?;
            }
            // PSUBB xmm, xmm: 66 0F F8 /r
            X86Opcode::Psubb => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0xF8)?;
            }
            // PSUBW xmm, xmm: 66 0F F9 /r
            X86Opcode::Psubw => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0xF9)?;
            }
            // PMULLW xmm, xmm: 66 0F D5 /r
            X86Opcode::Pmullw => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0xD5)?;
            }
            // PSUBD xmm, xmm: 66 0F FA /r
            X86Opcode::Psubd => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0xFA)?;
            }
            // PADDQ xmm, xmm: 66 0F D4 /r
            X86Opcode::Paddq => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0xD4)?;
            }
            // PSADBW xmm, xmm/m128: 66 0F F6 /r — sum-of-absolute-differences of
            // unsigned bytes into two u64 lanes (SAD-vs-zero = byte-sum).
            X86Opcode::Psadbw => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0xF6)?;
            }
            // PSUBQ xmm, xmm: 66 0F FB /r
            X86Opcode::Psubq => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0xFB)?;
            }
            // PMULUDQ xmm, xmm: 66 0F F4 /r
            X86Opcode::Pmuludq => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0xF4)?;
            }
            // PUNPCKLDQ xmm, xmm: 66 0F 62 /r
            X86Opcode::Punpckldq => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0x62)?;
            }
            // PUNPCKLQDQ xmm, xmm: 66 0F 6C /r
            X86Opcode::Punpcklqdq => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0x6C)?;
            }
            // PUNPCKLBW xmm, xmm: 66 0F 60 /r
            X86Opcode::Punpcklbw => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0x60)?;
            }
            // PUNPCKHBW xmm, xmm: 66 0F 68 /r
            X86Opcode::Punpckhbw => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0x68)?;
            }
            // PACKUSWB xmm, xmm: 66 0F 67 /r
            X86Opcode::Packuswb => {
                self.encode_sse2_packed_xmm_rm_or_rr(opcode, ops, 0x67)?;
            }
            // PSLLD xmm, imm8: 66 0F 72 /6 ib
            X86Opcode::Pslld => {
                self.encode_sse2_packed_xmm_imm_shift(opcode, ops, 6)?;
            }
            // PSRLD xmm, imm8: 66 0F 72 /2 ib
            X86Opcode::Psrld => {
                self.encode_sse2_packed_xmm_imm_shift(opcode, ops, 2)?;
            }
            // PSRAD xmm, imm8: 66 0F 72 /4 ib
            X86Opcode::Psrad => {
                self.encode_sse2_packed_xmm_imm_shift(opcode, ops, 4)?;
            }
            // PSLLQ xmm, imm8: 66 0F 73 /6 ib
            X86Opcode::Psllq => {
                self.encode_sse2_packed_xmm_imm_shift(opcode, ops, 6)?;
            }
            // PSRLQ xmm, imm8: 66 0F 73 /2 ib
            X86Opcode::Psrlq => {
                self.encode_sse2_packed_xmm_imm_shift(opcode, ops, 2)?;
            }
            // PMULLD xmm, xmm: 66 0F 38 40 /r
            X86Opcode::Pmulld => {
                self.encode_sse_0f38_packed_xmm_rm_or_rr(opcode, ops, 0x40)?;
            }
            // PCMPEQQ xmm, xmm: 66 0F 38 29 /r
            X86Opcode::Pcmpeqq => {
                self.encode_sse_0f38_packed_xmm_rm_or_rr(opcode, ops, 0x29)?;
            }
            // PCMPGTQ xmm, xmm: 66 0F 38 37 /r
            X86Opcode::Pcmpgtq => {
                self.encode_sse_0f38_packed_xmm_rm_or_rr(opcode, ops, 0x37)?;
            }
            // PTEST xmm, xmm/m128: 66 0F 38 17 /r
            X86Opcode::Ptest => {
                self.require_no_sse2_immediate(ops, opcode)?;
                if ops.base.is_some() {
                    let (dst, base, disp) = self.require_x86_sse2_xmm_rm(ops, opcode)?;
                    self.emit_byte(0x66);
                    self.emit_rex(Self::rex_xmm_rr(dst, base));
                    self.emit_byte(0x0F);
                    self.emit_byte(0x38);
                    self.emit_byte(0x17);
                    self.emit_mem_operand(dst.hw_enc(), base, disp)?;
                } else {
                    let (dst, src) = self.require_x86_sse2_xmm_rr(ops, opcode)?;
                    self.require_no_sse2_immediate(ops, opcode)?;
                    self.emit_byte(0x66);
                    self.emit_rex(Self::rex_xmm_rr(dst, src));
                    self.emit_byte(0x0F);
                    self.emit_byte(0x38);
                    self.emit_byte(0x17);
                    self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
                }
            }
            // PBLENDVB xmm, xmm: 66 0F 38 10 /r, implicit mask in XMM0.
            X86Opcode::Pblendvb => {
                let (dst, src) = self.require_x86_sse2_xmm_rr(ops, opcode)?;
                self.require_no_sse2_immediate(ops, opcode)?;
                self.emit_byte(0x66);
                self.emit_rex(Self::rex_xmm_rr(dst, src));
                self.emit_byte(0x0F);
                self.emit_byte(0x38);
                self.emit_byte(0x10);
                self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
            }
            // PSHUFD xmm, xmm, imm8: 66 0F 70 /r ib
            X86Opcode::Pshufd => {
                let imm = self.require_sse2_imm8(ops, opcode)?;
                if ops.base.is_some() {
                    let (dst, base, disp) = self.require_x86_sse2_xmm_rm_with_imm(ops, opcode)?;
                    self.encode_sse_rm(0x66, 0x70, dst, base, disp)?;
                } else {
                    let (dst, src) = self.require_x86_sse2_xmm_rr(ops, opcode)?;
                    self.encode_sse_rr(0x66, 0x70, dst, src);
                }
                self.emit_imm8(imm as i8);
            }
            // PMOVMSKB r32, xmm: 66 0F D7 /r
            X86Opcode::Pmovmskb => {
                let (dst, src) = self.require_x86_sse2_gpr32_xmm_rr(ops, opcode)?;
                self.require_no_sse2_immediate(ops, opcode)?;
                self.encode_sse_rr(0x66, 0xD7, dst, src);
            }
            // MOVDQA xmm, xmm: 66 0F 6F /r
            X86Opcode::MovdqaRR => {
                let (dst, src) = self.require_x86_sse2_xmm_rr(ops, opcode)?;
                self.require_no_sse2_immediate(ops, opcode)?;
                self.encode_sse_rr(0x66, 0x6F, dst, src);
            }
            // MOVDQA xmm, [mem]: 66 0F 6F /r
            X86Opcode::MovdqaRM | X86Opcode::VolatileMovdqaRM => {
                let (dst, base, disp) = self.require_x86_sse2_xmm_rm(ops, opcode)?;
                self.encode_sse_rm(0x66, 0x6F, dst, base, disp)?;
            }
            // MOVDQA [mem], xmm: 66 0F 7F /r
            X86Opcode::MovdqaMR | X86Opcode::VolatileMovdqaMR => {
                let (src, base, disp) = self.require_x86_sse2_xmm_mr(ops, opcode)?;
                self.encode_sse_mr(0x66, 0x7F, src, base, disp)?;
            }
            other => return Err(X86EncodeError::UnsupportedOpcode(other)),
        }

        Ok(())
    }

    fn encode_sse41_lane_x86_opcode(
        &mut self,
        opcode: X86Opcode,
        ops: &X86InstOperands,
    ) -> Result<(), X86EncodeError> {
        match opcode {
            // PINSRD xmm, r32, imm8: 66 0F 3A 22 /r ib
            X86Opcode::Pinsrd => {
                let (dst, src) = self.require_x86_sse41_xmm_gpr32_rr(ops, opcode)?;
                let imm = self.require_sse41_dword_lane(ops, opcode)?;
                self.emit_byte(0x66);
                self.emit_rex(Self::rex_xmm_rr(dst, src));
                self.emit_byte(0x0F);
                self.emit_byte(0x3A);
                self.emit_byte(0x22);
                self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
                self.emit_imm8(imm as i8);
            }
            // PEXTRD r32, xmm, imm8: 66 0F 3A 16 /r ib
            X86Opcode::Pextrd => {
                let (dst, src) = self.require_x86_sse41_gpr32_xmm_rr(ops, opcode)?;
                let imm = self.require_sse41_dword_lane(ops, opcode)?;
                self.emit_byte(0x66);
                self.emit_rex(Self::rex_xmm_rr(src, dst));
                self.emit_byte(0x0F);
                self.emit_byte(0x3A);
                self.emit_byte(0x16);
                self.emit_modrm(ModRM::reg_reg(src.hw_enc(), dst.hw_enc()));
                self.emit_imm8(imm as i8);
            }
            // PINSRQ xmm, r64, imm8: 66 REX.W 0F 3A 22 /r ib
            X86Opcode::Pinsrq => {
                let (dst, src) = self.require_x86_sse41_xmm_gpr64_rr(ops, opcode)?;
                let imm = self.require_sse41_qword_lane(ops, opcode)?;
                self.emit_byte(0x66);
                self.emit_rex(Self::rex_rr(dst, src, true));
                self.emit_byte(0x0F);
                self.emit_byte(0x3A);
                self.emit_byte(0x22);
                self.emit_modrm(ModRM::reg_reg(dst.hw_enc(), src.hw_enc()));
                self.emit_imm8(imm as i8);
            }
            // PEXTRQ r64, xmm, imm8: 66 REX.W 0F 3A 16 /r ib
            X86Opcode::Pextrq => {
                let (dst, src) = self.require_x86_sse41_gpr64_xmm_rr(ops, opcode)?;
                let imm = self.require_sse41_qword_lane(ops, opcode)?;
                self.emit_byte(0x66);
                self.emit_rex(Self::rex_rr(src, dst, true));
                self.emit_byte(0x0F);
                self.emit_byte(0x3A);
                self.emit_byte(0x16);
                self.emit_modrm(ModRM::reg_reg(src.hw_enc(), dst.hw_enc()));
                self.emit_imm8(imm as i8);
            }
            other => return Err(X86EncodeError::UnsupportedOpcode(other)),
        }

        Ok(())
    }

    // -----------------------------------------------------------------------
    // Operand extraction helpers
    // -----------------------------------------------------------------------

    fn require_dst(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<X86PReg, X86EncodeError> {
        ops.dst.ok_or_else(|| {
            X86EncodeError::InvalidOperands(format!("{:?}: missing dst register", opcode))
        })
    }

    fn require_rr(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<(X86PReg, X86PReg), X86EncodeError> {
        let dst = ops.dst.ok_or_else(|| {
            X86EncodeError::InvalidOperands(format!("{:?}: missing dst register", opcode))
        })?;
        let src = ops.src.ok_or_else(|| {
            X86EncodeError::InvalidOperands(format!("{:?}: missing src register", opcode))
        })?;
        Ok((dst, src))
    }

    fn require_ri(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<(X86PReg, i32), X86EncodeError> {
        let dst = ops.dst.ok_or_else(|| {
            X86EncodeError::InvalidOperands(format!("{:?}: missing dst register", opcode))
        })?;
        // FINDING #8: `ops.imm` is an i64 (sign-extended to 64 bits) but the ALU
        // r/imm forms encode an imm8/imm32 (sign-extended by the CPU). A value
        // outside i32 range (e.g. 0x1_0000_0000 -> 0, or 0xFFFF_FFFF -> -1) was
        // silently truncated by `as i32`, encoding a *different* immediate.
        // Reject it before the cast, mirroring the SSE2 disp32 sibling check.
        if ops.imm < i64::from(i32::MIN) || ops.imm > i64::from(i32::MAX) {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{:?}: immediate {} does not fit in imm32",
                opcode, ops.imm
            )));
        }
        Ok((dst, ops.imm as i32))
    }

    fn require_x86_sse2_rr(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<(X86PReg, X86PReg), X86EncodeError> {
        self.require_no_sse2_memory_shape(ops, opcode)?;
        let dst = ops.dst.ok_or_else(|| {
            X86EncodeError::InvalidOperands(format!("{:?}: missing dst register", opcode))
        })?;
        let src = ops.src.ok_or_else(|| {
            X86EncodeError::InvalidOperands(format!("{:?}: missing src register", opcode))
        })?;
        Ok((dst, src))
    }

    fn require_x86_sse2_xmm_rr(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<(X86PReg, X86PReg), X86EncodeError> {
        let (dst, src) = self.require_x86_sse2_rr(ops, opcode)?;
        if !dst.is_xmm() || !src.is_xmm() {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{:?}: expected dst/src XMM registers, got dst={:?}, src={:?}",
                opcode, dst, src
            )));
        }
        Ok((dst, src))
    }

    fn require_x86_sse2_xmm_ri(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<X86PReg, X86EncodeError> {
        self.require_no_sse2_memory_shape(ops, opcode)?;
        if ops.src.is_some() {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{:?}: expected dst XMM register and imm8 only, got src={:?}",
                opcode, ops.src
            )));
        }
        let dst = self.require_dst(ops, opcode)?;
        if !dst.is_xmm() {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{:?}: expected dst XMM register, got dst={:?}",
                opcode, dst
            )));
        }
        Ok(dst)
    }

    fn require_x86_sse2_gpr32_xmm_rr(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<(X86PReg, X86PReg), X86EncodeError> {
        let (dst, src) = self.require_x86_sse2_rr(ops, opcode)?;
        if !dst.is_gpr32() || !src.is_xmm() {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{:?}: expected dst GPR32 and src XMM register, got dst={:?}, src={:?}",
                opcode, dst, src
            )));
        }
        Ok((dst, src))
    }

    fn require_x86_sse41_xmm_gpr32_rr(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<(X86PReg, X86PReg), X86EncodeError> {
        let (dst, src) = self.require_x86_sse2_rr(ops, opcode)?;
        if !dst.is_xmm() || !src.is_gpr32() {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{:?}: expected dst XMM register and src GPR32 register, got dst={:?}, src={:?}",
                opcode, dst, src
            )));
        }
        Ok((dst, src))
    }

    fn require_x86_sse41_gpr32_xmm_rr(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<(X86PReg, X86PReg), X86EncodeError> {
        let (dst, src) = self.require_x86_sse2_rr(ops, opcode)?;
        if !dst.is_gpr32() || !src.is_xmm() {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{:?}: expected dst GPR32 register and src XMM register, got dst={:?}, src={:?}",
                opcode, dst, src
            )));
        }
        Ok((dst, src))
    }

    fn require_x86_sse41_xmm_gpr64_rr(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<(X86PReg, X86PReg), X86EncodeError> {
        let (dst, src) = self.require_x86_sse2_rr(ops, opcode)?;
        if !dst.is_xmm() || !src.is_gpr64() {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{opcode:?}: expected dst XMM and src GPR64, got {dst:?}, {src:?}"
            )));
        }
        Ok((dst, src))
    }

    fn require_x86_sse41_gpr64_xmm_rr(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<(X86PReg, X86PReg), X86EncodeError> {
        let (dst, src) = self.require_x86_sse2_rr(ops, opcode)?;
        if !dst.is_gpr64() || !src.is_xmm() {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{opcode:?}: expected dst GPR64 and src XMM, got {dst:?}, {src:?}"
            )));
        }
        Ok((dst, src))
    }

    fn require_x86_sse2_xmm_rm(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<(X86PReg, X86PReg, i64), X86EncodeError> {
        self.require_sse2_memory_shape(ops, opcode)?;
        let dst = self.require_dst(ops, opcode)?;
        let base = ops.base.ok_or_else(|| {
            X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
        })?;
        if !dst.is_xmm() || !base.is_gpr64() {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{:?}: expected dst XMM register and base GPR64 register, got dst={:?}, base={:?}",
                opcode, dst, base
            )));
        }
        Ok((dst, base, ops.disp))
    }

    fn require_x86_sse2_xmm_rm_with_imm(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<(X86PReg, X86PReg, i64), X86EncodeError> {
        self.require_sse2_memory_shape_with_imm(ops, opcode)?;
        let dst = self.require_dst(ops, opcode)?;
        let base = ops.base.ok_or_else(|| {
            X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
        })?;
        if !dst.is_xmm() || !base.is_gpr64() {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{:?}: expected dst XMM register and base GPR64 register, got dst={:?}, base={:?}",
                opcode, dst, base
            )));
        }
        Ok((dst, base, ops.disp))
    }

    fn require_x86_sse2_xmm_mr(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<(X86PReg, X86PReg, i64), X86EncodeError> {
        self.require_sse2_memory_shape(ops, opcode)?;
        let src = self.require_dst(ops, opcode)?;
        let base = ops.base.ok_or_else(|| {
            X86EncodeError::InvalidOperands(format!("{:?}: missing base register", opcode))
        })?;
        if !src.is_xmm() || !base.is_gpr64() {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{:?}: expected src XMM register and base GPR64 register, got src={:?}, base={:?}",
                opcode, src, base
            )));
        }
        Ok((src, base, ops.disp))
    }

    fn require_no_sse2_memory_shape(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<(), X86EncodeError> {
        if ops.base.is_some() || ops.index.is_some() || ops.disp != 0 || ops.scale != 1 {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{:?}: expected register operands only, got base={:?}, index={:?}, scale={}, disp={}",
                opcode, ops.base, ops.index, ops.scale, ops.disp
            )));
        }
        if ops.cc.is_some() {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{:?}: unexpected condition code {:?}",
                opcode, ops.cc
            )));
        }
        Ok(())
    }

    fn require_sse2_memory_shape(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<(), X86EncodeError> {
        self.require_sse2_memory_shape_impl(ops, opcode, false)
    }

    fn require_sse2_memory_shape_with_imm(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<(), X86EncodeError> {
        self.require_sse2_memory_shape_impl(ops, opcode, true)
    }

    fn require_sse2_memory_shape_impl(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
        allow_imm: bool,
    ) -> Result<(), X86EncodeError> {
        let unexpected_imm = !allow_imm && ops.imm != 0;
        if ops.src.is_some() || ops.index.is_some() || ops.scale != 1 || unexpected_imm {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{:?}: expected base+disp memory operand with dst/src in dst field, got src={:?}, index={:?}, scale={}, imm={}",
                opcode, ops.src, ops.index, ops.scale, ops.imm
            )));
        }
        if ops.cc.is_some() {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{:?}: unexpected condition code {:?}",
                opcode, ops.cc
            )));
        }
        if ops.disp < i64::from(i32::MIN) || ops.disp > i64::from(i32::MAX) {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{:?}: memory displacement {} does not fit in disp32",
                opcode, ops.disp
            )));
        }
        Ok(())
    }

    fn require_no_sse2_immediate(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<(), X86EncodeError> {
        if ops.imm != 0 {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{:?}: unexpected immediate {}",
                opcode, ops.imm
            )));
        }
        Ok(())
    }

    fn require_sse2_imm8(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<u8, X86EncodeError> {
        if !(0..=255).contains(&ops.imm) {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{:?}: immediate {} does not fit in imm8",
                opcode, ops.imm
            )));
        }
        Ok(ops.imm as u8)
    }

    fn require_sse41_dword_lane(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<u8, X86EncodeError> {
        if !(0..=3).contains(&ops.imm) {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{:?}: dword lane immediate {} outside 0..3",
                opcode, ops.imm
            )));
        }
        Ok(ops.imm as u8)
    }

    fn require_sse41_qword_lane(
        &self,
        ops: &X86InstOperands,
        opcode: X86Opcode,
    ) -> Result<u8, X86EncodeError> {
        if !(0..=1).contains(&ops.imm) {
            return Err(X86EncodeError::InvalidOperands(format!(
                "{opcode:?}: lane immediate must be in 0..=1, got {}",
                ops.imm
            )));
        }
        Ok(ops.imm as u8)
    }

    /// Encode a hardware NOP instruction (0x90).
    ///
    /// Note: `X86Opcode::Nop` is a pseudo with no encoding. Call this
    /// directly when you need a real 1-byte NOP in the output stream.
    pub fn encode_nop(&mut self) {
        self.emit_byte(0x90);
    }

    /// Encode a multi-byte NOP of the given size (0-9 bytes).
    ///
    /// Reference: Intel SDM Vol 2B, NOP instruction, Table 4-12.
    /// Recommended multi-byte NOP sequences for each length:
    /// - 1 byte: 90
    /// - 2 bytes: 66 90
    /// - 3 bytes: 0F 1F 00
    /// - 4 bytes: 0F 1F 40 00
    /// - 5 bytes: 0F 1F 44 00 00
    /// - 6 bytes: 66 0F 1F 44 00 00
    /// - 7 bytes: 0F 1F 80 00 00 00 00
    /// - 8 bytes: 0F 1F 84 00 00 00 00 00
    /// - 9 bytes: 66 0F 1F 84 00 00 00 00 00
    ///
    /// For sizes > 9, emits multiple 9-byte NOP sequences iteratively. The
    /// original implementation recursed via `encode_multibyte_nop(size - 9)`,
    /// which overflowed the stack for adversarial callers (e.g. a wild
    /// `ops.imm` of `i64::MAX` coerced through `NopMulti`). The panic-fuzz
    /// harness `panic_fuzz_encode_x86_64.rs` (#473) surfaced this as a real
    /// SIGABRT on macOS aarch64; converting to iteration removes the
    /// unbounded-recursion vector without changing the emitted byte sequence
    /// for any `size`.
    pub fn encode_multibyte_nop(&mut self, size: usize) {
        // Emit 9-byte NOP sequences until the remaining size fits in one
        // atomic NOP emission. This preserves bit-identical output with the
        // previous recursive implementation but bounds stack depth to O(1).
        let mut remaining = size;
        while remaining > 9 {
            // 9 bytes: 66 NOP DWORD ptr [RAX + RAX*1 + 00000000]
            self.emit_byte(0x66);
            self.emit_byte(0x0F);
            self.emit_byte(0x1F);
            self.emit_byte(0x84);
            self.emit_byte(0x00);
            self.emit_byte(0x00);
            self.emit_byte(0x00);
            self.emit_byte(0x00);
            self.emit_byte(0x00);
            remaining -= 9;
        }
        match remaining {
            0 => {}
            1 => {
                self.emit_byte(0x90);
            }
            2 => {
                self.emit_byte(0x66);
                self.emit_byte(0x90);
            }
            3 => {
                // NOP DWORD ptr [RAX]
                self.emit_byte(0x0F);
                self.emit_byte(0x1F);
                self.emit_byte(0x00);
            }
            4 => {
                // NOP DWORD ptr [RAX + 00]
                self.emit_byte(0x0F);
                self.emit_byte(0x1F);
                self.emit_byte(0x40);
                self.emit_byte(0x00);
            }
            5 => {
                // NOP DWORD ptr [RAX + RAX*1 + 00]
                self.emit_byte(0x0F);
                self.emit_byte(0x1F);
                self.emit_byte(0x44);
                self.emit_byte(0x00);
                self.emit_byte(0x00);
            }
            6 => {
                // 66 NOP DWORD ptr [RAX + RAX*1 + 00]
                self.emit_byte(0x66);
                self.emit_byte(0x0F);
                self.emit_byte(0x1F);
                self.emit_byte(0x44);
                self.emit_byte(0x00);
                self.emit_byte(0x00);
            }
            7 => {
                // NOP DWORD ptr [RAX + 00000000]
                self.emit_byte(0x0F);
                self.emit_byte(0x1F);
                self.emit_byte(0x80);
                self.emit_byte(0x00);
                self.emit_byte(0x00);
                self.emit_byte(0x00);
                self.emit_byte(0x00);
            }
            8 => {
                // NOP DWORD ptr [RAX + RAX*1 + 00000000]
                self.emit_byte(0x0F);
                self.emit_byte(0x1F);
                self.emit_byte(0x84);
                self.emit_byte(0x00);
                self.emit_byte(0x00);
                self.emit_byte(0x00);
                self.emit_byte(0x00);
                self.emit_byte(0x00);
            }
            _ => {
                // Unreachable under the loop above (remaining is in 0..=9
                // after the while-loop exits). Kept as a defensive 9-byte
                // emission to preserve behaviour if remaining ever somehow
                // equals exactly 9.
                self.emit_byte(0x66);
                self.emit_byte(0x0F);
                self.emit_byte(0x1F);
                self.emit_byte(0x84);
                self.emit_byte(0x00);
                self.emit_byte(0x00);
                self.emit_byte(0x00);
                self.emit_byte(0x00);
                self.emit_byte(0x00);
            }
        }
    }
}

impl Default for X86Encoder {
    fn default() -> Self {
        Self::new()
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::x86_64_ops::{X86CondCode, X86Opcode, X86Sse2PackedOpcode};
    use trust_cg_ir::x86_64_regs::{
        AL, AX, CL, CX, EAX, ECX, EDX, R8, R8B, R8D, R9, R9D, R10, R10B, R11, R12, R13, R14, R14D,
        R14W, R15, R15D, RAX, RBP, RBX, RCX, RDI, RDX, RSI, RSP, SIL, XMM0, XMM1, XMM8, XMM15,
    };

    // Helper to encode an instruction and return the bytes.
    fn encode(opcode: X86Opcode, ops: &X86InstOperands) -> Vec<u8> {
        let mut enc = X86Encoder::new();
        enc.encode_instruction(opcode, ops).unwrap();
        enc.finish()
    }

    fn encode_sse2_packed(opcode: X86Sse2PackedOpcode, ops: &X86InstOperands) -> Vec<u8> {
        let mut enc = X86Encoder::new();
        enc.encode_sse2_packed_instruction(opcode, ops).unwrap();
        enc.finish()
    }

    // AVX2-256 foundation: byte-exact VEX 3-byte (C4) prefix encoding for the ymm
    // ops the future vectorizer widening will emit. Verified against the
    // Intel SDM VEX layout `VEX.256.pp.map.W opcode /r`. (The helper is not yet
    // wired into opcode dispatch, so these tests are its only consumer today.)
    #[test]
    fn vex3_ymm_encoding_is_byte_exact() {
        // VPADDQ ymm0, ymm0, ymm0  = VEX.256.66.0F.WIG D4 /r = C4 E1 7D D4 C0
        let mut e = X86Encoder::new();
        e.emit_vex3_ymm_rr(1, 1, 0, 0xD4, 0, 0, 0);
        assert_eq!(
            e.finish(),
            vec![0xC4, 0xE1, 0x7D, 0xD4, 0xC0],
            "VPADDQ ymm0,ymm0,ymm0"
        );
        // VPMULUDQ ymm0, ymm0, ymm0 = VEX.256.66.0F.WIG F4 /r = C4 E1 7D F4 C0
        let mut e = X86Encoder::new();
        e.emit_vex3_ymm_rr(1, 1, 0, 0xF4, 0, 0, 0);
        assert_eq!(
            e.finish(),
            vec![0xC4, 0xE1, 0x7D, 0xF4, 0xC0],
            "VPMULUDQ ymm0,ymm0,ymm0"
        );
        // VMULPD ymm0, ymm0, ymm0   = VEX.256.66.0F.WIG 59 /r = C4 E1 7D 59 C0
        let mut e = X86Encoder::new();
        e.emit_vex3_ymm_rr(1, 1, 0, 0x59, 0, 0, 0);
        assert_eq!(
            e.finish(),
            vec![0xC4, 0xE1, 0x7D, 0x59, 0xC0],
            "VMULPD ymm0,ymm0,ymm0"
        );
        // VADDPD ymm0, ymm0, ymm0   = VEX.256.66.0F.WIG 58 /r = C4 E1 7D 58 C0
        let mut e = X86Encoder::new();
        e.emit_vex3_ymm_rr(1, 1, 0, 0x58, 0, 0, 0);
        assert_eq!(
            e.finish(),
            vec![0xC4, 0xE1, 0x7D, 0x58, 0xC0],
            "VADDPD ymm0,ymm0,ymm0"
        );
        // HIGH registers: VPADDQ ymm8, ymm1, ymm9 exercises the inverted R (dst>=8),
        // B (rm>=8), and vvvv (src1) fields. byte1=0x41, byte2=0x75, ModRM=0xC1.
        let mut e = X86Encoder::new();
        e.emit_vex3_ymm_rr(1, 1, 0, 0xD4, 8, 1, 9);
        assert_eq!(
            e.finish(),
            vec![0xC4, 0x41, 0x75, 0xD4, 0xC1],
            "VPADDQ ymm8,ymm1,ymm9"
        );
        // W=1 sets byte2 bit 7 (a W1-form op).
        let mut e = X86Encoder::new();
        e.emit_vex3_ymm_rr(1, 1, 1, 0xD4, 0, 0, 0);
        assert_eq!(
            e.finish(),
            vec![0xC4, 0xE1, 0xFD, 0xD4, 0xC0],
            "VEX.W=1 sets byte2 bit7"
        );
    }

    // -----------------------------------------------------------------------
    // REX prefix tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_rex_prefix_not_needed() {
        let rex = RexPrefix::default();
        assert!(!rex.is_needed());
    }

    #[test]
    fn test_rex_prefix_w() {
        let rex = RexPrefix {
            w: true,
            ..Default::default()
        };
        assert!(rex.is_needed());
        assert_eq!(rex.encode(), 0x48);
    }

    #[test]
    fn test_rex_prefix_all() {
        let rex = RexPrefix {
            w: true,
            r: true,
            x: true,
            b: true,
        };
        assert_eq!(rex.encode(), 0x4F);
    }

    #[test]
    fn test_rex_prefix_b_only() {
        let rex = RexPrefix {
            b: true,
            ..Default::default()
        };
        assert_eq!(rex.encode(), 0x41);
    }

    // -----------------------------------------------------------------------
    // ModR/M tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_modrm_reg_reg() {
        // MOV RAX, RBX: mod=11, reg=RAX(0), rm=RBX(3)
        let modrm = ModRM::reg_reg(0, 3);
        assert_eq!(modrm.encode(), 0b11_000_011);
    }

    #[test]
    fn test_modrm_encode() {
        // mod=10, reg=5, rm=4 (SIB follows)
        let modrm = ModRM {
            mode: 0b10,
            reg: 5,
            rm: 4,
        };
        assert_eq!(modrm.encode(), 0b10_101_100);
    }

    // -----------------------------------------------------------------------
    // SIB tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_sib_base_only_rsp() {
        // SIB for [RSP]: scale=0, index=none(4), base=RSP(4)
        let sib = Sib::base_only(4);
        assert_eq!(sib.encode(), 0b00_100_100);
    }

    #[test]
    fn test_sib_base_only_r12() {
        // SIB for [R12]: same low 3 bits as RSP
        let sib = Sib::base_only(12); // 12 & 7 = 4
        assert_eq!(sib.encode(), 0b00_100_100);
    }

    // -----------------------------------------------------------------------
    // Encoder basic tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_encoder_new() {
        let enc = X86Encoder::new();
        assert_eq!(enc.position(), 0);
        assert!(enc.bytes.is_empty());
    }

    #[test]
    fn test_encoder_emit_bytes() {
        let mut enc = X86Encoder::new();
        enc.emit_byte(0x90);
        enc.emit_byte(0xC3);
        assert_eq!(enc.position(), 2);
        assert_eq!(enc.finish(), vec![0x90, 0xC3]);
    }

    #[test]
    fn test_encoder_emit_u32() {
        let mut enc = X86Encoder::new();
        enc.emit_u32_le(0xDEADBEEF);
        assert_eq!(enc.finish(), vec![0xEF, 0xBE, 0xAD, 0xDE]);
    }

    #[test]
    fn test_encoder_emit_u64() {
        let mut enc = X86Encoder::new();
        enc.emit_u64_le(0x0102030405060708);
        assert_eq!(
            enc.finish(),
            vec![0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]
        );
    }

    // -----------------------------------------------------------------------
    // Pseudo-instruction tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_encode_pseudo_succeeds() {
        let ops = X86InstOperands::none();
        let empty: Vec<u8> = vec![];
        assert_eq!(encode(X86Opcode::Phi, &ops), empty);
        assert_eq!(encode(X86Opcode::Nop, &ops), empty);
        assert_eq!(encode(X86Opcode::StackAlloc, &ops), empty);
    }

    // -----------------------------------------------------------------------
    // NOP (hardware)
    // -----------------------------------------------------------------------

    #[test]
    fn test_encode_nop() {
        let mut enc = X86Encoder::new();
        enc.encode_nop();
        assert_eq!(enc.finish(), vec![0x90]);
    }

    // -----------------------------------------------------------------------
    // ADD tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_add_rax_rcx() {
        // ADD RAX, RCX: REX.W(48) + 01 + ModRM(11 001 000) = C8
        let bytes = encode(X86Opcode::AddRR, &X86InstOperands::rr(RAX, RCX));
        assert_eq!(bytes, vec![0x48, 0x01, 0xC8]);
    }

    #[test]
    fn test_add_rbx_rdx() {
        // ADD RBX, RDX: REX.W(48) + 01 + ModRM(11 010 011) = D3
        let bytes = encode(X86Opcode::AddRR, &X86InstOperands::rr(RBX, RDX));
        assert_eq!(bytes, vec![0x48, 0x01, 0xD3]);
    }

    #[test]
    fn test_add_r8_r9() {
        // ADD R8, R9: REX.WRB(4D) + 01 + ModRM(11 001 000) = C8
        // src=R9(hw=9, bit3=1 -> REX.R), dst=R8(hw=8, bit3=1 -> REX.B)
        let bytes = encode(X86Opcode::AddRR, &X86InstOperands::rr(R8, R9));
        assert_eq!(bytes, vec![0x4D, 0x01, 0xC8]);
    }

    #[test]
    fn test_add_rax_r8() {
        // ADD RAX, R8: src=R8(hw=8, bit3=1 -> REX.R), dst=RAX(hw=0)
        // REX.WR(4C) + 01 + ModRM(11 000 000) = C0
        let bytes = encode(X86Opcode::AddRR, &X86InstOperands::rr(RAX, R8));
        assert_eq!(bytes, vec![0x4C, 0x01, 0xC0]);
    }

    #[test]
    fn test_add_r15_rax() {
        // ADD R15, RAX: src=RAX(hw=0), dst=R15(hw=15, bit3=1 -> REX.B)
        // REX.WB(49) + 01 + ModRM(11 000 111) = C7
        let bytes = encode(X86Opcode::AddRR, &X86InstOperands::rr(R15, RAX));
        assert_eq!(bytes, vec![0x49, 0x01, 0xC7]);
    }

    #[test]
    fn test_add_rax_imm_uses_short_form() {
        // ADD RAX, 42: REX.W(48) + 83 + ModRM(11 000 000) + imm8(2A)
        let bytes = encode(X86Opcode::AddRI, &X86InstOperands::ri(RAX, 42));
        assert_eq!(bytes, vec![0x48, 0x83, 0xC0, 0x2A]);
    }

    #[test]
    fn test_add_r12_imm_uses_short_form_with_rex_b() {
        // ADD R12, 100: REX.WB(49) + 83 + ModRM(11 000 100) + imm8
        let bytes = encode(X86Opcode::AddRI, &X86InstOperands::ri(R12, 100));
        assert_eq!(bytes, vec![0x49, 0x83, 0xC4, 0x64]);
    }

    // Helper to encode an instruction and return the raw Result (for error cases).
    fn try_encode(opcode: X86Opcode, ops: &X86InstOperands) -> Result<usize, X86EncodeError> {
        let mut enc = X86Encoder::new();
        enc.encode_instruction(opcode, ops)
    }

    #[test]
    fn test_alu_ri_immediate_out_of_i32_range_returns_err() {
        // FINDING #8: a 64-bit ALU immediate that does not fit in imm32 was
        // silently truncated by `ops.imm as i32` (0x1_0000_0000 -> 0,
        // 0xFFFF_FFFF -> -1). It must now return InvalidOperands.
        for &imm in &[0x1_0000_0000_i64, 0xFFFF_FFFF_i64, i64::MAX, i64::MIN] {
            let res = try_encode(X86Opcode::AddRI, &X86InstOperands::ri(RAX, imm));
            assert!(
                matches!(res, Err(X86EncodeError::InvalidOperands(_))),
                "AddRI imm {imm:#x} must be rejected, got {res:?}"
            );
        }
        // Other ALU r/imm forms route through the same require_ri guard.
        for opcode in [
            X86Opcode::SubRI,
            X86Opcode::AndRI,
            X86Opcode::OrRI,
            X86Opcode::XorRI,
            X86Opcode::CmpRI,
        ] {
            let res = try_encode(opcode, &X86InstOperands::ri(RAX, 0x1_0000_0000));
            assert!(
                matches!(res, Err(X86EncodeError::InvalidOperands(_))),
                "{opcode:?} out-of-range imm must be rejected, got {res:?}"
            );
        }
    }

    #[test]
    fn test_alu_ri_immediate_in_range_boundaries_still_encode() {
        // FINDING #8 boundary: the extreme in-range imm32 values still encode
        // byte-identically (imm32 sign-extended to 64 by the CPU).
        // ADD RAX, i32::MAX -> REX.W + 81 /0 id
        assert_eq!(
            encode(X86Opcode::AddRI, &X86InstOperands::ri(RAX, i32::MAX as i64)),
            vec![0x48, 0x81, 0xC0, 0xFF, 0xFF, 0xFF, 0x7F]
        );
        // ADD RAX, -1 -> REX.W + 83 /0 ib (short form, sign-extended imm8)
        assert_eq!(
            encode(X86Opcode::AddRI, &X86InstOperands::ri(RAX, -1)),
            vec![0x48, 0x83, 0xC0, 0xFF]
        );
        // ADD RAX, i32::MIN -> REX.W + 81 /0 id
        assert_eq!(
            encode(X86Opcode::AddRI, &X86InstOperands::ri(RAX, i32::MIN as i64)),
            vec![0x48, 0x81, 0xC0, 0x00, 0x00, 0x00, 0x80]
        );
    }

    #[test]
    fn test_imm_arm_out_of_range_returns_err() {
        // FINDING #8 (defense-in-depth): TestRI/ImulRRI/CmpRI8/BtRI narrowed
        // ops.imm with a raw `as` cast and no range check. An out-of-range
        // immediate must now return InvalidOperands instead of silently
        // mis-encoding.
        // TestRI: imm32 form -> reject outside i32.
        for &imm in &[0x1_0000_0000_i64, i64::MAX, i64::MIN] {
            let res = try_encode(X86Opcode::TestRI, &X86InstOperands::ri(RAX, imm));
            assert!(
                matches!(res, Err(X86EncodeError::InvalidOperands(_))),
                "TestRI imm {imm:#x} must be rejected, got {res:?}"
            );
        }
        // ImulRRI: imm8/imm32 form -> reject outside i32.
        for &imm in &[0x1_0000_0000_i64, i64::MAX, i64::MIN] {
            let res = try_encode(X86Opcode::ImulRRI, &X86InstOperands::rri(RAX, RCX, imm));
            assert!(
                matches!(res, Err(X86EncodeError::InvalidOperands(_))),
                "ImulRRI imm {imm:#x} must be rejected, got {res:?}"
            );
        }
        // CmpRI8: sign-extended imm8 form -> reject outside i8 (-128..=127).
        for &imm in &[128_i64, 200_i64, -129_i64, 0x1_0000_0000_i64] {
            let res = try_encode(X86Opcode::CmpRI8, &X86InstOperands::ri(RAX, imm));
            assert!(
                matches!(res, Err(X86EncodeError::InvalidOperands(_))),
                "CmpRI8 imm {imm} must be rejected, got {res:?}"
            );
        }
        // BtRI: bit-index imm8 (0..=63) -> reject outside that range.
        for &imm in &[64_i64, 300_i64, -1_i64] {
            let res = try_encode(X86Opcode::BtRI, &X86InstOperands::ri(RAX, imm));
            assert!(
                matches!(res, Err(X86EncodeError::InvalidOperands(_))),
                "BtRI imm {imm} must be rejected, got {res:?}"
            );
        }
    }

    #[test]
    fn test_imm_arm_in_range_boundaries_still_encode() {
        // FINDING #8 boundary: the extreme in-range immediates each arm already
        // accepts must still encode byte-identically (no behavior change).
        // TestRI RAX, i32::MAX/i32::MIN: REX.W + F7 /0 id.
        assert_eq!(
            encode(
                X86Opcode::TestRI,
                &X86InstOperands::ri(RAX, i32::MAX as i64)
            ),
            vec![0x48, 0xF7, 0xC0, 0xFF, 0xFF, 0xFF, 0x7F]
        );
        assert_eq!(
            encode(
                X86Opcode::TestRI,
                &X86InstOperands::ri(RAX, i32::MIN as i64)
            ),
            vec![0x48, 0xF7, 0xC0, 0x00, 0x00, 0x00, 0x80]
        );
        // ImulRRI RAX, RCX, i32::MAX: REX.W + 69 /r id (imm32, no imm8 fit).
        assert_eq!(
            encode(
                X86Opcode::ImulRRI,
                &X86InstOperands::rri(RAX, RCX, i32::MAX as i64)
            ),
            vec![0x48, 0x69, 0xC1, 0xFF, 0xFF, 0xFF, 0x7F]
        );
        // CmpRI8 RAX, 127 (i8::MAX) and -128 (i8::MIN): REX.W + 83 /7 ib.
        assert_eq!(
            encode(X86Opcode::CmpRI8, &X86InstOperands::ri(RAX, 127)),
            vec![0x48, 0x83, 0xF8, 0x7F]
        );
        assert_eq!(
            encode(X86Opcode::CmpRI8, &X86InstOperands::ri(RAX, -128)),
            vec![0x48, 0x83, 0xF8, 0x80]
        );
        // BtRI RAX, 0 and R15, 63: REX.W + 0F BA /4 ib (bit-index extremes).
        assert_eq!(
            encode(X86Opcode::BtRI, &X86InstOperands::ri(RAX, 0)),
            vec![0x48, 0x0F, 0xBA, 0xE0, 0x00]
        );
        assert_eq!(
            encode(X86Opcode::BtRI, &X86InstOperands::ri(R15, 63)),
            vec![0x49, 0x0F, 0xBA, 0xE7, 0x3F]
        );
    }

    #[test]
    fn test_mem_displacement_out_of_i32_range_returns_err() {
        // FINDING #8: a memory displacement that does not fit in disp32 was
        // silently truncated by `disp as i32`. Must now return InvalidOperands
        // across the GPR mem (rm), SIB (rm_sib), and RIP-relative paths.
        let big = 0x1_0000_0000_i64;
        let res = try_encode(X86Opcode::MovRM, &X86InstOperands::rm(RAX, RBX, big));
        assert!(
            matches!(res, Err(X86EncodeError::InvalidOperands(_))),
            "MovRM disp {big:#x} must be rejected, got {res:?}"
        );
        let res = try_encode(
            X86Opcode::MovMR,
            &X86InstOperands::rm(RAX, RBX, -0x1_0000_0001),
        );
        assert!(matches!(res, Err(X86EncodeError::InvalidOperands(_))));

        let res = try_encode(
            X86Opcode::MovRMSib,
            &X86InstOperands::rm_sib(RAX, RBX, RCX, 8, big),
        );
        assert!(matches!(res, Err(X86EncodeError::InvalidOperands(_))));

        let res = try_encode(X86Opcode::LeaRip, &X86InstOperands::rip_rel(RAX, big));
        assert!(matches!(res, Err(X86EncodeError::InvalidOperands(_))));
    }

    #[test]
    fn test_mem_displacement_in_range_boundaries_still_encode() {
        // FINDING #8 boundary: the extreme in-range disp32 values and a small
        // disp8 still encode byte-identically.
        // MOV RAX, [RBX + i32::MAX]: REX.W + 8B + ModRM(10 000 011) + disp32
        assert_eq!(
            encode(
                X86Opcode::MovRM,
                &X86InstOperands::rm(RAX, RBX, i32::MAX as i64)
            ),
            vec![0x48, 0x8B, 0x83, 0xFF, 0xFF, 0xFF, 0x7F]
        );
        // MOV RAX, [RBX + i32::MIN]: disp32
        assert_eq!(
            encode(
                X86Opcode::MovRM,
                &X86InstOperands::rm(RAX, RBX, i32::MIN as i64)
            ),
            vec![0x48, 0x8B, 0x83, 0x00, 0x00, 0x00, 0x80]
        );
        // MOV RAX, [RBX + 0x10]: disp8 short form unchanged.
        assert_eq!(
            encode(X86Opcode::MovRM, &X86InstOperands::rm(RAX, RBX, 0x10)),
            vec![0x48, 0x8B, 0x43, 0x10]
        );
    }

    // -----------------------------------------------------------------------
    // SUB tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_sub_rax_rcx() {
        // SUB RAX, RCX: REX.W(48) + 29 + ModRM(11 001 000) = C8
        let bytes = encode(X86Opcode::SubRR, &X86InstOperands::rr(RAX, RCX));
        assert_eq!(bytes, vec![0x48, 0x29, 0xC8]);
    }

    #[test]
    fn test_sub_rax_imm_uses_short_form() {
        // SUB RAX, 10: REX.W(48) + 83 + ModRM(11 101 000) = E8 + imm8
        let bytes = encode(X86Opcode::SubRI, &X86InstOperands::ri(RAX, 10));
        assert_eq!(bytes, vec![0x48, 0x83, 0xE8, 0x0A]);
    }

    // -----------------------------------------------------------------------
    // ADC / SBB tests (i128 add-with-carry / subtract-with-borrow)
    // -----------------------------------------------------------------------

    #[test]
    fn test_adc_rax_rcx() {
        // ADC RAX, RCX: REX.W(48) + 11 /r + ModRM(11 001 000) = C8.
        // Verified against Intel SDM: ADC r/m64, r64 is REX.W + 11 /r.
        let bytes = encode(X86Opcode::AdcRR, &X86InstOperands::rr(RAX, RCX));
        assert_eq!(bytes, vec![0x48, 0x11, 0xC8]);
    }

    #[test]
    fn test_adc_rdx_rax() {
        // ADC RDX, RAX: REX.W(48) + 11 /r + ModRM(11 000 010) = C2.
        // This is the canonical i128 high-half add (dst_hi += src_hi + CF).
        let bytes = encode(X86Opcode::AdcRR, &X86InstOperands::rr(RDX, RAX));
        assert_eq!(bytes, vec![0x48, 0x11, 0xC2]);
    }

    #[test]
    fn test_adc_r8_r9() {
        // ADC R8, R9: REX.WRB(4D) + 11 /r + ModRM(11 001 000) = C8.
        let bytes = encode(X86Opcode::AdcRR, &X86InstOperands::rr(R8, R9));
        assert_eq!(bytes, vec![0x4D, 0x11, 0xC8]);
    }

    #[test]
    fn test_sbb_rax_rcx() {
        // SBB RAX, RCX: REX.W(48) + 19 /r + ModRM(11 001 000) = C8.
        // Verified against Intel SDM: SBB r/m64, r64 is REX.W + 19 /r.
        let bytes = encode(X86Opcode::SbbRR, &X86InstOperands::rr(RAX, RCX));
        assert_eq!(bytes, vec![0x48, 0x19, 0xC8]);
    }

    #[test]
    fn test_sbb_rdx_rax() {
        // SBB RDX, RAX: REX.W(48) + 19 /r + ModRM(11 000 010) = C2.
        // This is the canonical i128 high-half sub (dst_hi -= src_hi + CF).
        let bytes = encode(X86Opcode::SbbRR, &X86InstOperands::rr(RDX, RAX));
        assert_eq!(bytes, vec![0x48, 0x19, 0xC2]);
    }

    // -----------------------------------------------------------------------
    // AND/OR/XOR tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_and_rax_rcx() {
        // AND RAX, RCX: REX.W + 21 + ModRM(11 001 000)
        let bytes = encode(X86Opcode::AndRR, &X86InstOperands::rr(RAX, RCX));
        assert_eq!(bytes, vec![0x48, 0x21, 0xC8]);
    }

    #[test]
    fn test_or_rax_rdx() {
        // OR RAX, RDX: REX.W + 09 + ModRM(11 010 000)
        let bytes = encode(X86Opcode::OrRR, &X86InstOperands::rr(RAX, RDX));
        assert_eq!(bytes, vec![0x48, 0x09, 0xD0]);
    }

    #[test]
    fn test_xor_rax_rax() {
        // XOR RAX, RAX: REX.W + 31 + ModRM(11 000 000) = C0
        let bytes = encode(X86Opcode::XorRR, &X86InstOperands::rr(RAX, RAX));
        assert_eq!(bytes, vec![0x48, 0x31, 0xC0]);
    }

    #[test]
    fn test_and_rcx_imm32() {
        // AND RCX, 0xFF: REX.W + 81 + ModRM(11 100 001) + imm32
        let bytes = encode(X86Opcode::AndRI, &X86InstOperands::ri(RCX, 0xFF));
        assert_eq!(bytes, vec![0x48, 0x81, 0xE1, 0xFF, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_or_rdx_imm_uses_short_form() {
        // OR RDX, 1: REX.W + 83 + ModRM(11 001 010) + imm8
        let bytes = encode(X86Opcode::OrRI, &X86InstOperands::ri(RDX, 1));
        assert_eq!(bytes, vec![0x48, 0x83, 0xCA, 0x01]);
    }

    #[test]
    fn test_xor_rbx_imm32() {
        // XOR RBX, 0xDEAD: REX.W + 81 + ModRM(11 110 011) + imm32
        let bytes = encode(X86Opcode::XorRI, &X86InstOperands::ri(RBX, 0xDEAD));
        assert_eq!(bytes, vec![0x48, 0x81, 0xF3, 0xAD, 0xDE, 0x00, 0x00]);
    }

    // -----------------------------------------------------------------------
    // CMP / TEST tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_cmp_rax_rcx() {
        // CMP RAX, RCX: REX.W + 39 + ModRM(11 001 000) = C8
        let bytes = encode(X86Opcode::CmpRR, &X86InstOperands::rr(RAX, RCX));
        assert_eq!(bytes, vec![0x48, 0x39, 0xC8]);
    }

    #[test]
    fn test_cmp_rax_imm_uses_short_form() {
        // CMP RAX, 0: REX.W + 83 + ModRM(11 111 000) + imm8
        let bytes = encode(X86Opcode::CmpRI, &X86InstOperands::ri(RAX, 0));
        assert_eq!(bytes, vec![0x48, 0x83, 0xF8, 0x00]);
    }

    #[test]
    fn test_test_rax_rcx() {
        // TEST RAX, RCX: REX.W + 85 + ModRM(11 001 000)
        let bytes = encode(X86Opcode::TestRR, &X86InstOperands::rr(RAX, RCX));
        assert_eq!(bytes, vec![0x48, 0x85, 0xC8]);
    }

    #[test]
    fn test_test_rax_imm32() {
        // TEST RAX, 1: REX.W + F7 + ModRM(11 000 000) + imm32
        let bytes = encode(X86Opcode::TestRI, &X86InstOperands::ri(RAX, 1));
        assert_eq!(bytes, vec![0x48, 0xF7, 0xC0, 0x01, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_gpr32_alu_forms_do_not_emit_rex_w() {
        assert_eq!(
            encode(X86Opcode::AddRR, &X86InstOperands::rr(EAX, ECX)),
            vec![0x01, 0xC8]
        );
        assert_eq!(
            encode(X86Opcode::AddRI, &X86InstOperands::ri(EAX, 7)),
            vec![0x83, 0xC0, 0x07]
        );
        assert_eq!(
            encode(X86Opcode::XorRR, &X86InstOperands::rr(EDX, EDX)),
            vec![0x31, 0xD2]
        );
    }

    // -----------------------------------------------------------------------
    // MOV tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_mov_rax_rcx() {
        // MOV RAX, RCX: REX.W + 89 + ModRM(11 001 000) = C8
        let bytes = encode(X86Opcode::MovRR, &X86InstOperands::rr(RAX, RCX));
        assert_eq!(bytes, vec![0x48, 0x89, 0xC8]);
    }

    #[test]
    fn test_mov_r15_r14() {
        // MOV R15, R14: REX.WRB(4D) + 89 + ModRM(11 110 111) = F7
        let bytes = encode(X86Opcode::MovRR, &X86InstOperands::rr(R15, R14));
        assert_eq!(bytes, vec![0x4D, 0x89, 0xF7]);
    }

    #[test]
    fn test_movrr32_eax_ecx_has_no_rex_w() {
        // MOV EAX, ECX: 89 + ModRM(11 001 000) = C8.
        let bytes = encode(X86Opcode::MovRR32, &X86InstOperands::rr(EAX, ECX));
        assert_eq!(bytes, vec![0x89, 0xC8]);
    }

    #[test]
    fn test_movrr32_extended_regs_has_rex_without_w() {
        // MOV R15D, R14D: REX.RB(45) + 89 + ModRM(11 110 111) = F7.
        let bytes = encode(X86Opcode::MovRR32, &X86InstOperands::rr(R15D, R14D));
        assert_eq!(bytes, vec![0x45, 0x89, 0xF7]);
    }

    #[test]
    fn test_movabs_rax_imm64() {
        // MOV RAX, 0x123456789ABCDEF0: REX.W + B8 + imm64
        let bytes = encode(
            X86Opcode::MovRI,
            &X86InstOperands::ri(RAX, 0x123456789ABCDEF0u64 as i64),
        );
        assert_eq!(
            bytes,
            vec![0x48, 0xB8, 0xF0, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12]
        );
    }

    #[test]
    fn test_movri_rax_small_u32_uses_zero_extending_r32() {
        // MOV EAX, 42: B8 + imm32, zero-extending into RAX.
        let bytes = encode(X86Opcode::MovRI, &X86InstOperands::ri(RAX, 42));
        assert_eq!(bytes, vec![0xB8, 0x2A, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_movri_rax_high_u32_uses_zero_extending_r32() {
        // MOV EAX, 0x80000001: B8 + imm32, producing 0x0000000080000001 in RAX.
        let bytes = encode(
            X86Opcode::MovRI,
            &X86InstOperands::ri(RAX, 0x80000001u32 as i64),
        );
        assert_eq!(bytes, vec![0xB8, 0x01, 0x00, 0x00, 0x80]);
    }

    #[test]
    fn test_movri_r8_small_u32_uses_zero_extending_r32() {
        // MOV R8D, 42: REX.B(41) + B8 + imm32, zero-extending into R8.
        let bytes = encode(X86Opcode::MovRI, &X86InstOperands::ri(R8, 42));
        assert_eq!(bytes, vec![0x41, 0xB8, 0x2A, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_movabs_r8_wide_imm64() {
        // MOV R8, 0x100000000: REX.WB(49) + B8 + imm64.
        let bytes = encode(X86Opcode::MovRI, &X86InstOperands::ri(R8, 0x1_0000_0000));
        assert_eq!(
            bytes,
            vec![0x49, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00]
        );
    }

    #[test]
    fn test_movabs_rax_negative_imm64() {
        // MOV RAX, -1: must stay movabs to preserve all 64 one bits.
        let bytes = encode(X86Opcode::MovRI, &X86InstOperands::ri(RAX, -1));
        assert_eq!(
            bytes,
            vec![0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]
        );
    }

    #[test]
    fn test_movri_eax_imm32_has_no_rex_w() {
        // MOV EAX, 0x80000001: B8 + imm32.
        let bytes = encode(
            X86Opcode::MovRI,
            &X86InstOperands::ri(EAX, 0x80000001u32 as i64),
        );
        assert_eq!(bytes, vec![0xB8, 0x01, 0x00, 0x00, 0x80]);
    }

    #[test]
    fn test_movri_r8d_imm32_has_rex_without_w() {
        // MOV R8D, 42: REX.B(41) + B8 + imm32.
        let bytes = encode(X86Opcode::MovRI, &X86InstOperands::ri(R8D, 42));
        assert_eq!(bytes, vec![0x41, 0xB8, 0x2A, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_movri_al_imm8_uses_byte_opcode() {
        // MOV AL, 7: B0 + imm8.
        let bytes = encode(X86Opcode::MovRI, &X86InstOperands::ri(AL, 7));
        assert_eq!(bytes, vec![0xB0, 0x07]);
    }

    #[test]
    fn test_movri_r8b_imm8_has_rex_without_w() {
        // MOV R8B, 7: REX.B(41) + B0 + imm8.
        let bytes = encode(X86Opcode::MovRI, &X86InstOperands::ri(R8B, 7));
        assert_eq!(bytes, vec![0x41, 0xB0, 0x07]);
    }

    #[test]
    fn test_movri_ax_imm16_has_operand_size_prefix() {
        // MOV AX, 0x1234: 66 + B8 + imm16.
        let bytes = encode(X86Opcode::MovRI, &X86InstOperands::ri(AX, 0x1234));
        assert_eq!(bytes, vec![0x66, 0xB8, 0x34, 0x12]);
    }

    #[test]
    fn test_movri_r14w_imm16_has_rex_without_w() {
        // MOV R14W, 0x1234: 66 + REX.B(41) + BE + imm16.
        let bytes = encode(X86Opcode::MovRI, &X86InstOperands::ri(R14W, 0x1234));
        assert_eq!(bytes, vec![0x66, 0x41, 0xBE, 0x34, 0x12]);
    }

    // -----------------------------------------------------------------------
    // MOV memory tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_mov_rax_mem_rbx() {
        // MOV RAX, [RBX]: REX.W + 8B + ModRM(00 000 011)
        let bytes = encode(X86Opcode::MovRM, &X86InstOperands::rm(RAX, RBX, 0));
        assert_eq!(bytes, vec![0x48, 0x8B, 0x03]);
    }

    #[test]
    fn test_mov_width_specific_loads_from_mem() {
        assert_eq!(
            encode(X86Opcode::MovRM8, &X86InstOperands::rm(RAX, RBX, 0)),
            vec![0x8A, 0x03]
        );
        assert_eq!(
            encode(X86Opcode::MovRM16, &X86InstOperands::rm(RAX, RBX, 0)),
            vec![0x66, 0x8B, 0x03]
        );
        assert_eq!(
            encode(X86Opcode::MovRM32, &X86InstOperands::rm(RAX, RBX, 0)),
            vec![0x8B, 0x03]
        );
        assert_eq!(
            encode(X86Opcode::MovRM, &X86InstOperands::rm(RAX, RBX, 0)),
            vec![0x48, 0x8B, 0x03]
        );
    }

    #[test]
    fn test_mov_width_specific_stores_to_mem() {
        assert_eq!(
            encode(X86Opcode::MovMR8, &X86InstOperands::rm(RAX, RBX, 0)),
            vec![0x88, 0x03]
        );
        assert_eq!(
            encode(X86Opcode::MovMR16, &X86InstOperands::rm(RAX, RBX, 0)),
            vec![0x66, 0x89, 0x03]
        );
        assert_eq!(
            encode(X86Opcode::MovMR32, &X86InstOperands::rm(RAX, RBX, 0)),
            vec![0x89, 0x03]
        );
        assert_eq!(
            encode(X86Opcode::MovMR, &X86InstOperands::rm(RAX, RBX, 0)),
            vec![0x48, 0x89, 0x03]
        );
    }

    #[test]
    fn test_mov_byte_memory_ops_force_rex_for_sil_dil() {
        assert_eq!(
            encode(X86Opcode::MovRM8, &X86InstOperands::rm(RSI, RBX, 0)),
            vec![0x40, 0x8A, 0x33]
        );
        assert_eq!(
            encode(X86Opcode::MovMR8, &X86InstOperands::rm(RDI, RBX, 0)),
            vec![0x40, 0x88, 0x3B]
        );
    }

    #[test]
    fn test_mov_rax_mem_rbx_disp8() {
        // MOV RAX, [RBX+16]: REX.W + 8B + ModRM(01 000 011) + disp8(10)
        let bytes = encode(X86Opcode::MovRM, &X86InstOperands::rm(RAX, RBX, 16));
        assert_eq!(bytes, vec![0x48, 0x8B, 0x43, 0x10]);
    }

    #[test]
    fn test_mov_rax_mem_rbx_disp32() {
        // MOV RAX, [RBX+256]: REX.W + 8B + ModRM(10 000 011) + disp32
        let bytes = encode(X86Opcode::MovRM, &X86InstOperands::rm(RAX, RBX, 256));
        assert_eq!(bytes, vec![0x48, 0x8B, 0x83, 0x00, 0x01, 0x00, 0x00]);
    }

    #[test]
    fn test_mov_rax_mem_rsp() {
        // MOV RAX, [RSP]: REX.W + 8B + ModRM(00 000 100) + SIB(00 100 100)
        // RSP as base requires SIB byte
        let bytes = encode(X86Opcode::MovRM, &X86InstOperands::rm(RAX, RSP, 0));
        assert_eq!(bytes, vec![0x48, 0x8B, 0x04, 0x24]);
    }

    #[test]
    fn test_mov_rax_mem_rsp_disp8() {
        // MOV RAX, [RSP+8]: REX.W + 8B + ModRM(01 000 100) + SIB(00 100 100) + disp8(08)
        let bytes = encode(X86Opcode::MovRM, &X86InstOperands::rm(RAX, RSP, 8));
        assert_eq!(bytes, vec![0x48, 0x8B, 0x44, 0x24, 0x08]);
    }

    #[test]
    fn test_mov_rax_mem_rbp() {
        // MOV RAX, [RBP+0]: RBP as base with disp=0 requires disp8=0
        // REX.W + 8B + ModRM(01 000 101) + disp8(00)
        let bytes = encode(X86Opcode::MovRM, &X86InstOperands::rm(RAX, RBP, 0));
        assert_eq!(bytes, vec![0x48, 0x8B, 0x45, 0x00]);
    }

    #[test]
    fn test_mov_mem_rbx_rax() {
        // MOV [RBX], RAX: REX.W + 89 + ModRM(00 000 011)
        // For MovMR, dst field holds the source register
        let bytes = encode(
            X86Opcode::MovMR,
            &X86InstOperands {
                dst: Some(RAX),
                base: Some(RBX),
                disp: 0,
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0x48, 0x89, 0x03]);
    }

    // -----------------------------------------------------------------------
    // IMUL tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_imul_rax_rcx() {
        // IMUL RAX, RCX: REX.W + 0F AF + ModRM(11 000 001)
        let bytes = encode(X86Opcode::ImulRR, &X86InstOperands::rr(RAX, RCX));
        assert_eq!(bytes, vec![0x48, 0x0F, 0xAF, 0xC1]);
    }

    #[test]
    fn test_imul_r8_r9() {
        // IMUL R8, R9: REX.WRB(4D) + 0F AF + ModRM(11 000 001)
        let bytes = encode(X86Opcode::ImulRR, &X86InstOperands::rr(R8, R9));
        assert_eq!(bytes, vec![0x4D, 0x0F, 0xAF, 0xC1]);
    }

    #[test]
    fn test_imul_rax_rcx_imm32() {
        // IMUL RAX, RCX, 128: REX.W + 69 + ModRM(11 000 001) + imm32
        let bytes = encode(X86Opcode::ImulRRI, &X86InstOperands::rri(RAX, RCX, 128));
        assert_eq!(bytes, vec![0x48, 0x69, 0xC1, 0x80, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_imul_rax_rcx_imm8_uses_short_encoding() {
        // IMUL RAX, RCX, 42: REX.W + 6B + ModRM(11 000 001) + imm8
        let bytes = encode(X86Opcode::ImulRRI, &X86InstOperands::rri(RAX, RCX, 42));
        assert_eq!(bytes, vec![0x48, 0x6B, 0xC1, 0x2A]);
    }

    #[test]
    fn test_imul_rax_rcx_negative_imm8_uses_short_encoding() {
        // IMUL RAX, RCX, -7: REX.W + 6B + ModRM(11 000 001) + imm8
        let bytes = encode(X86Opcode::ImulRRI, &X86InstOperands::rri(RAX, RCX, -7));
        assert_eq!(bytes, vec![0x48, 0x6B, 0xC1, 0xF9]);
    }

    #[test]
    fn test_imul_r8_r9_imm8_keeps_extended_register_rex() {
        // IMUL R8, R9, -1: REX.WRB + 6B + ModRM(11 000 001) + imm8
        let bytes = encode(X86Opcode::ImulRRI, &X86InstOperands::rri(R8, R9, -1));
        assert_eq!(bytes, vec![0x4D, 0x6B, 0xC1, 0xFF]);
    }

    #[test]
    fn test_imul_eax_ecx_has_no_rex_w() {
        // IMUL EAX, ECX: 0F AF + ModRM(11 000 001)
        let bytes = encode(X86Opcode::ImulRR, &X86InstOperands::rr(EAX, ECX));
        assert_eq!(bytes, vec![0x0F, 0xAF, 0xC1]);
    }

    #[test]
    fn test_imul_r8d_r9d_has_rex_without_w() {
        // IMUL R8D, R9D: REX.RB(45) + 0F AF + ModRM(11 000 001)
        let bytes = encode(X86Opcode::ImulRR, &X86InstOperands::rr(R8D, R9D));
        assert_eq!(bytes, vec![0x45, 0x0F, 0xAF, 0xC1]);
    }

    #[test]
    fn test_imul_eax_ecx_imm32_has_no_rex_w() {
        // IMUL EAX, ECX, 128: 69 + ModRM(11 000 001) + imm32
        let bytes = encode(X86Opcode::ImulRRI, &X86InstOperands::rri(EAX, ECX, 128));
        assert_eq!(bytes, vec![0x69, 0xC1, 0x80, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_imul_eax_ecx_imm8_has_no_rex_w() {
        // IMUL EAX, ECX, 42: 6B + ModRM(11 000 001) + imm8
        let bytes = encode(X86Opcode::ImulRRI, &X86InstOperands::rri(EAX, ECX, 42));
        assert_eq!(bytes, vec![0x6B, 0xC1, 0x2A]);
    }

    // -----------------------------------------------------------------------
    // Unary tests: NEG, NOT, INC, DEC, IDIV
    // -----------------------------------------------------------------------

    #[test]
    fn test_neg_rax() {
        // NEG RAX: REX.W + F7 + ModRM(11 011 000)
        let bytes = encode(X86Opcode::Neg, &X86InstOperands::r(RAX));
        assert_eq!(bytes, vec![0x48, 0xF7, 0xD8]);
    }

    #[test]
    fn test_neg_r15() {
        // NEG R15: REX.WB(49) + F7 + ModRM(11 011 111)
        let bytes = encode(X86Opcode::Neg, &X86InstOperands::r(R15));
        assert_eq!(bytes, vec![0x49, 0xF7, 0xDF]);
    }

    #[test]
    fn test_not_rcx() {
        // NOT RCX: REX.W + F7 + ModRM(11 010 001)
        let bytes = encode(X86Opcode::Not, &X86InstOperands::r(RCX));
        assert_eq!(bytes, vec![0x48, 0xF7, 0xD1]);
    }

    #[test]
    fn test_inc_rax() {
        // INC RAX: REX.W + FF + ModRM(11 000 000)
        let bytes = encode(X86Opcode::Inc, &X86InstOperands::r(RAX));
        assert_eq!(bytes, vec![0x48, 0xFF, 0xC0]);
    }

    #[test]
    fn test_dec_rcx() {
        // DEC RCX: REX.W + FF + ModRM(11 001 001)
        let bytes = encode(X86Opcode::Dec, &X86InstOperands::r(RCX));
        assert_eq!(bytes, vec![0x48, 0xFF, 0xC9]);
    }

    #[test]
    fn test_idiv_rcx() {
        // IDIV RCX: REX.W + F7 + ModRM(11 111 001)
        let bytes = encode(X86Opcode::Idiv, &X86InstOperands::r(RCX));
        assert_eq!(bytes, vec![0x48, 0xF7, 0xF9]);
    }

    #[test]
    fn test_div_rcx() {
        // DIV RCX: REX.W + F7 + ModRM(11 110 001)
        // ModR/M: mod=11, reg=/6(110), rm=RCX(001) = 0xF1
        let bytes = encode(X86Opcode::Div, &X86InstOperands::r(RCX));
        assert_eq!(bytes, vec![0x48, 0xF7, 0xF1]);
    }

    #[test]
    fn test_div_r8() {
        // DIV R8: REX.WB(49) + F7 + ModRM(11 110 000)
        // R8 hw_enc=8, bit3=1 -> REX.B. ModR/M rm=R8(0 low3)
        let bytes = encode(X86Opcode::Div, &X86InstOperands::r(R8));
        assert_eq!(bytes, vec![0x49, 0xF7, 0xF0]);
    }

    #[test]
    fn test_mul_rcx() {
        // MUL RCX: REX.W + F7 + ModRM(11 100 001)
        let bytes = encode(X86Opcode::Mul, &X86InstOperands::r(RCX));
        assert_eq!(bytes, vec![0x48, 0xF7, 0xE1]);
    }

    #[test]
    fn test_div_idiv_gpr32_do_not_emit_rex_w() {
        assert_eq!(
            encode(X86Opcode::Idiv, &X86InstOperands::r(ECX)),
            vec![0xF7, 0xF9]
        );
        assert_eq!(
            encode(X86Opcode::Div, &X86InstOperands::r(ECX)),
            vec![0xF7, 0xF1]
        );
        assert_eq!(
            encode(X86Opcode::Mul, &X86InstOperands::r(ECX)),
            vec![0xF7, 0xE1]
        );
    }

    #[test]
    fn test_ud2() {
        let bytes = encode(X86Opcode::Ud2, &X86InstOperands::none());
        assert_eq!(bytes, vec![0x0F, 0x0B]);
    }

    // -----------------------------------------------------------------------
    // Shift tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_shl_rax_imm() {
        // SHL RAX, 4: REX.W + C1 + ModRM(11 100 000) + ib(04)
        let bytes = encode(X86Opcode::ShlRI, &X86InstOperands::ri(RAX, 4));
        assert_eq!(bytes, vec![0x48, 0xC1, 0xE0, 0x04]);
    }

    /// ROL r/m64, imm8 = `REX.W + C1 /0 ib`. Byte-for-byte against the system
    /// assembler: `rolq $9, %rcx` assembles to `48 c1 c1 09`, and
    /// `rolq $63, %r11` to `49 c1 c3 3f` (REX.WB for the extended register).
    #[test]
    fn test_rol_ri_matches_assembler_bytes() {
        assert_eq!(
            encode(X86Opcode::RolRI, &X86InstOperands::ri(RCX, 9)),
            vec![0x48, 0xC1, 0xC1, 0x09],
            "rolq $9, %rcx"
        );
        assert_eq!(
            encode(X86Opcode::RolRI, &X86InstOperands::ri(R11, 63)),
            vec![0x49, 0xC1, 0xC3, 0x3F],
            "rolq $63, %r11"
        );
        // 32-bit form takes no REX.W, exactly as for the shifts.
        assert_eq!(
            encode(X86Opcode::RolRI, &X86InstOperands::ri(ECX, 9)),
            vec![0xC1, 0xC1, 0x09],
            "roll $9, %ecx"
        );
    }

    /// ROL and SHL differ ONLY in the ModRM extension field (/0 vs /4). If that
    /// ever collapses, a rotate would silently encode as a shift.
    #[test]
    fn test_rol_ri_is_not_shl_ri() {
        let rol = encode(X86Opcode::RolRI, &X86InstOperands::ri(RAX, 4));
        let shl = encode(X86Opcode::ShlRI, &X86InstOperands::ri(RAX, 4));
        assert_ne!(rol, shl, "ROL must not encode identically to SHL");
        assert_eq!(rol, vec![0x48, 0xC1, 0xC0, 0x04]);
        assert_eq!(shl, vec![0x48, 0xC1, 0xE0, 0x04]);
    }

    #[test]
    fn test_shl_eax_imm_has_no_rex_w() {
        let bytes = encode(X86Opcode::ShlRI, &X86InstOperands::ri(EAX, 4));
        assert_eq!(bytes, vec![0xC1, 0xE0, 0x04]);
    }

    #[test]
    fn test_shr_rdx_imm() {
        // SHR RDX, 8: REX.W + C1 + ModRM(11 101 010) + ib(08)
        let bytes = encode(X86Opcode::ShrRI, &X86InstOperands::ri(RDX, 8));
        assert_eq!(bytes, vec![0x48, 0xC1, 0xEA, 0x08]);
    }

    #[test]
    fn test_sar_rcx_imm() {
        // SAR RCX, 1: REX.W + C1 + ModRM(11 111 001) + ib(01)
        let bytes = encode(X86Opcode::SarRI, &X86InstOperands::ri(RCX, 1));
        assert_eq!(bytes, vec![0x48, 0xC1, 0xF9, 0x01]);
    }

    #[test]
    fn test_shl_rax_cl() {
        // SHL RAX, CL: REX.W + D3 + ModRM(11 100 000)
        let bytes = encode(X86Opcode::ShlRR, &X86InstOperands::r(RAX));
        assert_eq!(bytes, vec![0x48, 0xD3, 0xE0]);
    }

    #[test]
    fn test_shr_rdx_cl() {
        // SHR RDX, CL: REX.W + D3 + ModRM(11 101 010)
        let bytes = encode(X86Opcode::ShrRR, &X86InstOperands::r(RDX));
        assert_eq!(bytes, vec![0x48, 0xD3, 0xEA]);
    }

    #[test]
    fn test_sar_r15_cl() {
        // SAR R15, CL: REX.WB(49) + D3 + ModRM(11 111 111)
        let bytes = encode(X86Opcode::SarRR, &X86InstOperands::r(R15));
        assert_eq!(bytes, vec![0x49, 0xD3, 0xFF]);
    }

    // -----------------------------------------------------------------------
    // Control flow tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_ret() {
        let bytes = encode(X86Opcode::Ret, &X86InstOperands::none());
        assert_eq!(bytes, vec![0xC3]);
    }

    #[test]
    fn test_call_rel32() {
        // CALL +0: E8 00000000
        let bytes = encode(X86Opcode::Call, &X86InstOperands::rel(0));
        assert_eq!(bytes, vec![0xE8, 0x00, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_call_rel32_offset() {
        // CALL +256: E8 00010000
        let bytes = encode(X86Opcode::Call, &X86InstOperands::rel(256));
        assert_eq!(bytes, vec![0xE8, 0x00, 0x01, 0x00, 0x00]);
    }

    #[test]
    fn test_call_r_rax() {
        // CALL RAX: FF + ModRM(11 010 000) = D0
        let bytes = encode(X86Opcode::CallR, &X86InstOperands::r(RAX));
        assert_eq!(bytes, vec![0xFF, 0xD0]);
    }

    #[test]
    fn test_call_r_r15() {
        // CALL R15: REX.B(41) + FF + ModRM(11 010 111) = D7
        let bytes = encode(X86Opcode::CallR, &X86InstOperands::r(R15));
        assert_eq!(bytes, vec![0x41, 0xFF, 0xD7]);
    }

    // --- Indirect JMP r64 (FF /4) — jump-table dispatch. Mirrors CallR (FF /2)
    //     with the ModRM.reg extension field = /4 instead of /2. ---
    #[test]
    fn test_jmp_r_rax() {
        // JMP RAX: FF + ModRM(11 100 000) = E0  (mod=11, /4, rm=RAX(000))
        let bytes = encode(X86Opcode::JmpR, &X86InstOperands::r(RAX));
        assert_eq!(bytes, vec![0xFF, 0xE0]);
    }

    #[test]
    fn test_jmp_r_r8() {
        // JMP R8: REX.B(41) + FF + ModRM(11 100 000) = E0  (rm=000 + REX.B -> R8)
        let bytes = encode(X86Opcode::JmpR, &X86InstOperands::r(R8));
        assert_eq!(bytes, vec![0x41, 0xFF, 0xE0]);
    }

    #[test]
    fn test_jmp_r_r15() {
        // JMP R15: REX.B(41) + FF + ModRM(11 100 111) = E7  (rm=111 + REX.B -> R15)
        let bytes = encode(X86Opcode::JmpR, &X86InstOperands::r(R15));
        assert_eq!(bytes, vec![0x41, 0xFF, 0xE7]);
    }

    // --- MOVSXD r64, [base + index*4] (REX.W 63 /r + SIB) — signed jump-table
    //     entry load. Identical to MovRMSib except opcode 63 instead of 8B. ---
    #[test]
    fn test_movsxd_rm_sib_rax_rbx_rcx_scale4_nodisp() {
        // MOVSXD RAX, [RBX + RCX*4]: REX.W(48) + 63 + ModRM(00 000 100) + SIB(10 001 011)
        let bytes = encode(
            X86Opcode::MovsxdRMSib,
            &X86InstOperands::rm_sib(RAX, RBX, RCX, 4, 0),
        );
        assert_eq!(bytes, vec![0x48, 0x63, 0x04, 0x8B]);
    }

    #[test]
    fn test_movsxd_rm_sib_extended_regs() {
        // MOVSXD R8, [R12 + R9*4]: REX.WRXB(4F) + 63 + ModRM(00 000 100) + SIB(10 001 100)
        // dst=R8(REX.R), base=R12(REX.B), index=R9(REX.X); SIB scale=4(10) idx=R9(001) base=R12(100)
        let bytes = encode(
            X86Opcode::MovsxdRMSib,
            &X86InstOperands::rm_sib(R8, R12, R9, 4, 0),
        );
        assert_eq!(bytes, vec![0x4F, 0x63, 0x04, 0x8C]);
    }

    #[test]
    fn test_jmp_rel32() {
        // JMP +0: E9 00000000
        let bytes = encode(X86Opcode::Jmp, &X86InstOperands::rel(0));
        assert_eq!(bytes, vec![0xE9, 0x00, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_jcc_je() {
        // JE +0: 0F 84 00000000
        let bytes = encode(X86Opcode::Jcc, &X86InstOperands::jcc(X86CondCode::E, 0));
        assert_eq!(bytes, vec![0x0F, 0x84, 0x00, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_jcc_jne() {
        // JNE +100: 0F 85 64000000
        let bytes = encode(X86Opcode::Jcc, &X86InstOperands::jcc(X86CondCode::NE, 100));
        assert_eq!(bytes, vec![0x0F, 0x85, 0x64, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_jcc_jl() {
        // JL -16: 0F 8C F0FFFFFF
        let bytes = encode(X86Opcode::Jcc, &X86InstOperands::jcc(X86CondCode::L, -16));
        assert_eq!(bytes, vec![0x0F, 0x8C, 0xF0, 0xFF, 0xFF, 0xFF]);
    }

    #[test]
    fn test_jcc_jg() {
        // JG +0: 0F 8F 00000000
        let bytes = encode(X86Opcode::Jcc, &X86InstOperands::jcc(X86CondCode::G, 0));
        assert_eq!(bytes, vec![0x0F, 0x8F, 0x00, 0x00, 0x00, 0x00]);
    }

    // -----------------------------------------------------------------------
    // Stack tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_push_rax() {
        // PUSH RAX: 50
        let bytes = encode(X86Opcode::Push, &X86InstOperands::r(RAX));
        assert_eq!(bytes, vec![0x50]);
    }

    #[test]
    fn test_push_rbx() {
        // PUSH RBX: 53
        let bytes = encode(X86Opcode::Push, &X86InstOperands::r(RBX));
        assert_eq!(bytes, vec![0x53]);
    }

    #[test]
    fn test_push_r8() {
        // PUSH R8: REX.B(41) + 50
        let bytes = encode(X86Opcode::Push, &X86InstOperands::r(R8));
        assert_eq!(bytes, vec![0x41, 0x50]);
    }

    #[test]
    fn test_push_r15() {
        // PUSH R15: REX.B(41) + 57
        let bytes = encode(X86Opcode::Push, &X86InstOperands::r(R15));
        assert_eq!(bytes, vec![0x41, 0x57]);
    }

    #[test]
    fn test_pop_rax() {
        // POP RAX: 58
        let bytes = encode(X86Opcode::Pop, &X86InstOperands::r(RAX));
        assert_eq!(bytes, vec![0x58]);
    }

    #[test]
    fn test_pop_r15() {
        // POP R15: REX.B(41) + 5F
        let bytes = encode(X86Opcode::Pop, &X86InstOperands::r(R15));
        assert_eq!(bytes, vec![0x41, 0x5F]);
    }

    // -----------------------------------------------------------------------
    // Extended register encoding correctness
    // -----------------------------------------------------------------------

    #[test]
    fn test_mov_r13_r14() {
        // MOV R13, R14: REX.WRB(4D) + 89 + ModRM(11 110 101)
        let bytes = encode(X86Opcode::MovRR, &X86InstOperands::rr(R13, R14));
        assert_eq!(bytes, vec![0x4D, 0x89, 0xF5]);
    }

    #[test]
    fn test_xor_r10_r11() {
        // XOR R10, R11: REX.WRB(4D) + 31 + ModRM(11 011 010)
        let bytes = encode(X86Opcode::XorRR, &X86InstOperands::rr(R10, R11));
        assert_eq!(bytes, vec![0x4D, 0x31, 0xDA]);
    }

    #[test]
    fn test_sub_rsi_rdi() {
        // SUB RSI, RDI: REX.W(48) + 29 + ModRM(11 111 110) = FE
        let bytes = encode(X86Opcode::SubRR, &X86InstOperands::rr(RSI, RDI));
        assert_eq!(bytes, vec![0x48, 0x29, 0xFE]);
    }

    // -----------------------------------------------------------------------
    // Error handling tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_missing_dst_error() {
        let mut enc = X86Encoder::new();
        let result = enc.encode_instruction(X86Opcode::AddRR, &X86InstOperands::none());
        assert!(result.is_err());
    }

    #[test]
    fn test_missing_src_error() {
        let mut enc = X86Encoder::new();
        let result = enc.encode_instruction(X86Opcode::AddRR, &X86InstOperands::r(RAX));
        assert!(result.is_err());
    }

    #[test]
    fn test_missing_cc_error() {
        let mut enc = X86Encoder::new();
        let result = enc.encode_instruction(X86Opcode::Jcc, &X86InstOperands::rel(0));
        assert!(result.is_err());
    }

    #[test]
    fn test_encode_error_display() {
        let e1 = X86EncodeError::UnsupportedOpcode(X86Opcode::Ret);
        assert!(format!("{}", e1).contains("Ret"));

        let e2 = X86EncodeError::InvalidOperands("bad combo".into());
        assert!(format!("{}", e2).contains("bad combo"));

        let e3 = X86EncodeError::NotImplemented("stub".into());
        assert!(format!("{}", e3).contains("stub"));
    }

    // -----------------------------------------------------------------------
    // Memory encoding with extended registers
    // -----------------------------------------------------------------------

    #[test]
    fn test_mov_r8_mem_r12() {
        // MOV R8, [R12]: REX.WRB(4D) + 8B + ModRM(00 000 100) + SIB(00 100 100)
        // R12 base uses SIB (hw_enc & 7 == 4)
        let bytes = encode(X86Opcode::MovRM, &X86InstOperands::rm(R8, R12, 0));
        assert_eq!(bytes, vec![0x4D, 0x8B, 0x04, 0x24]);
    }

    #[test]
    fn test_mov_r8_mem_r13() {
        // MOV R8, [R13+0]: R13 base with disp=0 requires disp8=0 (hw_enc & 7 == 5)
        // REX.WRB(4D) + 8B + ModRM(01 000 101) + disp8(00)
        let bytes = encode(X86Opcode::MovRM, &X86InstOperands::rm(R8, R13, 0));
        assert_eq!(bytes, vec![0x4D, 0x8B, 0x45, 0x00]);
    }

    // -----------------------------------------------------------------------
    // AddRM, SubRM, CmpRM tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_add_rax_mem_rbx() {
        // ADD RAX, [RBX]: REX.W + 03 + ModRM(00 000 011)
        let bytes = encode(X86Opcode::AddRM, &X86InstOperands::rm(RAX, RBX, 0));
        assert_eq!(bytes, vec![0x48, 0x03, 0x03]);
    }

    #[test]
    fn test_sub_rcx_mem_rdx_disp() {
        // SUB RCX, [RDX+16]: REX.W + 2B + ModRM(01 001 010) + disp8(10)
        let bytes = encode(X86Opcode::SubRM, &X86InstOperands::rm(RCX, RDX, 16));
        assert_eq!(bytes, vec![0x48, 0x2B, 0x4A, 0x10]);
    }

    #[test]
    fn test_cmp_rdi_mem_rsi() {
        // CMP RDI, [RSI]: REX.W + 3B + ModRM(00 111 110)
        let bytes = encode(X86Opcode::CmpRM, &X86InstOperands::rm(RDI, RSI, 0));
        assert_eq!(bytes, vec![0x48, 0x3B, 0x3E]);
    }

    // -----------------------------------------------------------------------
    // Instruction size tests (verify correct byte counts)
    // -----------------------------------------------------------------------

    #[test]
    fn test_instruction_sizes() {
        let mut enc = X86Encoder::new();

        // RET = 1 byte
        let n = enc
            .encode_instruction(X86Opcode::Ret, &X86InstOperands::none())
            .unwrap();
        assert_eq!(n, 1);

        // PUSH RAX = 1 byte (no REX needed)
        let n = enc
            .encode_instruction(X86Opcode::Push, &X86InstOperands::r(RAX))
            .unwrap();
        assert_eq!(n, 1);

        // PUSH R8 = 2 bytes (REX.B + opcode)
        let n = enc
            .encode_instruction(X86Opcode::Push, &X86InstOperands::r(R8))
            .unwrap();
        assert_eq!(n, 2);

        // ADD RAX, RCX = 3 bytes (REX.W + opcode + ModRM)
        let n = enc
            .encode_instruction(X86Opcode::AddRR, &X86InstOperands::rr(RAX, RCX))
            .unwrap();
        assert_eq!(n, 3);

        // CALL rel32 = 5 bytes (opcode + imm32)
        let n = enc
            .encode_instruction(X86Opcode::Call, &X86InstOperands::rel(0))
            .unwrap();
        assert_eq!(n, 5);

        // Jcc rel32 = 6 bytes (0F + opcode + imm32)
        let n = enc
            .encode_instruction(X86Opcode::Jcc, &X86InstOperands::jcc(X86CondCode::E, 0))
            .unwrap();
        assert_eq!(n, 6);

        // ADD RAX, imm8 = 4 bytes (REX.W + opcode + ModRM + imm8)
        let n = enc
            .encode_instruction(X86Opcode::AddRI, &X86InstOperands::ri(RAX, 42))
            .unwrap();
        assert_eq!(n, 4);

        // ADD RAX, imm32 = 7 bytes when imm8 sign-extension would change the value.
        let n = enc
            .encode_instruction(X86Opcode::AddRI, &X86InstOperands::ri(RAX, 128))
            .unwrap();
        assert_eq!(n, 7);

        // MOV RAX, imm64 = 10 bytes (REX.W + opcode + imm64).
        // Use a value that overflows u32 so the encoder cannot fold the
        // instruction to the 5-byte `MOV EAX, imm32` zero-extending alias
        // (see `zero_extending_movri_alias`).
        let n = enc
            .encode_instruction(X86Opcode::MovRI, &X86InstOperands::ri(RAX, -1))
            .unwrap();
        assert_eq!(n, 10);
    }

    // -----------------------------------------------------------------------
    // LEA tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_lea_rax_rbx() {
        // LEA RAX, [RBX]: REX.W(48) + 8D + ModRM(00 000 011)
        let bytes = encode(X86Opcode::Lea, &X86InstOperands::rm(RAX, RBX, 0));
        assert_eq!(bytes, vec![0x48, 0x8D, 0x03]);
    }

    #[test]
    fn test_lea_rax_rbx_disp8() {
        // LEA RAX, [RBX+16]: REX.W + 8D + ModRM(01 000 011) + disp8
        let bytes = encode(X86Opcode::Lea, &X86InstOperands::rm(RAX, RBX, 16));
        assert_eq!(bytes, vec![0x48, 0x8D, 0x43, 0x10]);
    }

    #[test]
    fn test_lea_rax_rbx_disp32() {
        // LEA RAX, [RBX+256]: REX.W + 8D + ModRM(10 000 011) + disp32
        let bytes = encode(X86Opcode::Lea, &X86InstOperands::rm(RAX, RBX, 256));
        assert_eq!(bytes, vec![0x48, 0x8D, 0x83, 0x00, 0x01, 0x00, 0x00]);
    }

    #[test]
    fn test_lea_r15_rsp_disp8() {
        // LEA R15, [RSP+8]: REX.WRB(4C) + 8D + ModRM(01 111 100) + SIB(00 100 100) + disp8
        let bytes = encode(X86Opcode::Lea, &X86InstOperands::rm(R15, RSP, 8));
        assert_eq!(bytes, vec![0x4C, 0x8D, 0x7C, 0x24, 0x08]);
    }

    // -----------------------------------------------------------------------
    // MOVZX / MOVSX tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_movzx_rax_cl() {
        // MOVZX RAX, CL: REX.W(48) + 0F B6 + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Movzx, &X86InstOperands::rr(RAX, RCX));
        assert_eq!(bytes, vec![0x48, 0x0F, 0xB6, 0xC1]);
    }

    #[test]
    fn test_movzx_r8_al() {
        // MOVZX R8, AL: REX.WR(4C) + 0F B6 + ModRM(11 000 000)
        let bytes = encode(X86Opcode::Movzx, &X86InstOperands::rr(R8, RAX));
        assert_eq!(bytes, vec![0x4C, 0x0F, 0xB6, 0xC0]);
    }

    #[test]
    fn test_movsx_rax_ecx() {
        // MOVSXD RAX, ECX: REX.W(48) + 63 + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Movsx, &X86InstOperands::rr(RAX, RCX));
        assert_eq!(bytes, vec![0x48, 0x63, 0xC1]);
    }

    #[test]
    fn test_movsx_r15_r14() {
        // MOVSXD R15, R14: REX.WRB(4D) + 63 + ModRM(11 111 110)
        let bytes = encode(X86Opcode::Movsx, &X86InstOperands::rr(R15, R14));
        assert_eq!(bytes, vec![0x4D, 0x63, 0xFE]);
    }

    // -----------------------------------------------------------------------
    // SSE scalar double-precision tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_addsd_xmm0_xmm1() {
        // ADDSD XMM0, XMM1: F2 0F 58 + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Addsd, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0xF2, 0x0F, 0x58, 0xC1]);
    }

    #[test]
    fn test_subsd_xmm0_xmm1() {
        // SUBSD XMM0, XMM1: F2 0F 5C + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Subsd, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0xF2, 0x0F, 0x5C, 0xC1]);
    }

    #[test]
    fn test_mulsd_xmm0_xmm1() {
        // MULSD XMM0, XMM1: F2 0F 59 + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Mulsd, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0xF2, 0x0F, 0x59, 0xC1]);
    }

    #[test]
    fn test_divsd_xmm0_xmm1() {
        // DIVSD XMM0, XMM1: F2 0F 5E + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Divsd, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0xF2, 0x0F, 0x5E, 0xC1]);
    }

    #[test]
    fn test_addsd_xmm8_xmm15() {
        // ADDSD XMM8, XMM15: F2 REX.RB(45) 0F 58 + ModRM(11 000 111)
        let bytes = encode(X86Opcode::Addsd, &X86InstOperands::rr(XMM8, XMM15));
        assert_eq!(bytes, vec![0xF2, 0x45, 0x0F, 0x58, 0xC7]);
    }

    #[test]
    fn test_sqrtsd_xmm0_xmm1() {
        // SQRTSD XMM0, XMM1: F2 0F 51 + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Sqrtsd, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0xF2, 0x0F, 0x51, 0xC1]);
    }

    #[test]
    fn test_sqrtsd_xmm8_xmm15() {
        // SQRTSD XMM8, XMM15: F2 REX.RB(45) 0F 51 + ModRM(11 000 111)
        let bytes = encode(X86Opcode::Sqrtsd, &X86InstOperands::rr(XMM8, XMM15));
        assert_eq!(bytes, vec![0xF2, 0x45, 0x0F, 0x51, 0xC7]);
    }

    // --- Packed floating-point arithmetic (ADDPS/ADDPD families) ---

    #[test]
    fn test_addps_xmm0_xmm1() {
        // ADDPS XMM0, XMM1: 0F 58 + ModRM(11 000 001). No mandatory prefix.
        let bytes = encode(X86Opcode::Addps, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0x0F, 0x58, 0xC1]);
    }

    #[test]
    fn test_subps_xmm0_xmm1() {
        // SUBPS XMM0, XMM1: 0F 5C + ModRM(11 000 001).
        let bytes = encode(X86Opcode::Subps, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0x0F, 0x5C, 0xC1]);
    }

    #[test]
    fn test_mulps_xmm0_xmm1() {
        // MULPS XMM0, XMM1: 0F 59 + ModRM(11 000 001).
        let bytes = encode(X86Opcode::Mulps, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0x0F, 0x59, 0xC1]);
    }

    #[test]
    fn test_divps_xmm0_xmm1() {
        // DIVPS XMM0, XMM1: 0F 5E + ModRM(11 000 001).
        let bytes = encode(X86Opcode::Divps, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0x0F, 0x5E, 0xC1]);
    }

    #[test]
    fn test_addps_xmm8_xmm15() {
        // ADDPS XMM8, XMM15: REX.RB(45) 0F 58 + ModRM(11 000 111). No 66 prefix.
        let bytes = encode(X86Opcode::Addps, &X86InstOperands::rr(XMM8, XMM15));
        assert_eq!(bytes, vec![0x45, 0x0F, 0x58, 0xC7]);
    }

    #[test]
    fn test_addpd_xmm0_xmm1() {
        // ADDPD XMM0, XMM1: 66 0F 58 + ModRM(11 000 001). Mandatory 66 prefix.
        let bytes = encode(X86Opcode::Addpd, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0x66, 0x0F, 0x58, 0xC1]);
    }

    #[test]
    fn test_subpd_xmm0_xmm1() {
        // SUBPD XMM0, XMM1: 66 0F 5C + ModRM(11 000 001).
        let bytes = encode(X86Opcode::Subpd, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0x66, 0x0F, 0x5C, 0xC1]);
    }

    #[test]
    fn test_mulpd_xmm0_xmm1() {
        // MULPD XMM0, XMM1: 66 0F 59 + ModRM(11 000 001).
        let bytes = encode(X86Opcode::Mulpd, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0x66, 0x0F, 0x59, 0xC1]);
    }

    #[test]
    fn test_divpd_xmm0_xmm1() {
        // DIVPD XMM0, XMM1: 66 0F 5E + ModRM(11 000 001).
        let bytes = encode(X86Opcode::Divpd, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0x66, 0x0F, 0x5E, 0xC1]);
    }

    #[test]
    fn test_addpd_xmm8_xmm15() {
        // ADDPD XMM8, XMM15: 66 REX.RB(45) 0F 58 + ModRM(11 000 111).
        let bytes = encode(X86Opcode::Addpd, &X86InstOperands::rr(XMM8, XMM15));
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0x58, 0xC7]);
    }

    // Scalar-FP scaled-index loads. Every expected byte string below is GROUND
    // TRUTH from an independent assembler (`llvm-mc -show-encoding`), not from
    // re-deriving this encoder's own arithmetic — an X==X test would pin nothing.
    #[test]
    fn test_movsd_rm_sib_basic() {
        // llvm-mc: movsd 16(%rbx,%rcx,8), %xmm0 => [f2,0f,10,44,cb,10]
        // No REX byte: every register is low, and REX.W stays 0 (the F2 prefix
        // fixes the operand size, not REX.W).
        let bytes = encode(
            X86Opcode::MovsdRMSib,
            &X86InstOperands::rm_sib(XMM0, RBX, RCX, 8, 16),
        );
        assert_eq!(bytes, vec![0xF2, 0x0F, 0x10, 0x44, 0xCB, 0x10]);
    }

    #[test]
    fn test_movss_rm_sib_basic() {
        // llvm-mc: movss 16(%rbx,%rcx,8), %xmm0 => [f3,0f,10,44,cb,10]
        // Identical to MOVSD except the mandatory prefix (F3 vs F2).
        let bytes = encode(
            X86Opcode::MovssRMSib,
            &X86InstOperands::rm_sib(XMM0, RBX, RCX, 8, 16),
        );
        assert_eq!(bytes, vec![0xF3, 0x0F, 0x10, 0x44, 0xCB, 0x10]);
    }

    #[test]
    fn test_movsd_rm_sib_high_base_rex_b() {
        // llvm-mc: movsd (%r8,%rdx,8), %xmm1 => [f2,41,0f,10,0c,d0]
        // Pins that the mandatory SIMD prefix precedes REX (0xF2 then 0x41).
        let bytes = encode(
            X86Opcode::MovsdRMSib,
            &X86InstOperands::rm_sib(XMM1, R8, RDX, 8, 0),
        );
        assert_eq!(bytes, vec![0xF2, 0x41, 0x0F, 0x10, 0x0C, 0xD0]);
    }

    #[test]
    fn test_movsd_rm_sib_all_high_regs_disp32() {
        // llvm-mc: movsd 128(%r15,%r10,4), %xmm8
        //       => [f2,47,0f,10,84,97,80,00,00,00]
        // REX 0x47 = R|X|B: the X bit carries the INDEX high bit, which has no
        // slot in a plain ModRM memory operand — the whole reason this form
        // needs its own encoder helper. Also the 10-byte worst case that
        // `estimate_inst_size` must not under-report.
        let bytes = encode(
            X86Opcode::MovsdRMSib,
            &X86InstOperands::rm_sib(XMM8, R15, R10, 4, 128),
        );
        assert_eq!(
            bytes,
            vec![0xF2, 0x47, 0x0F, 0x10, 0x84, 0x97, 0x80, 0x00, 0x00, 0x00]
        );
        assert_eq!(bytes.len(), 10);
    }

    #[test]
    fn test_andpd_xmm0_xmm1() {
        // ANDPD XMM0, XMM1: 66 0F 54 + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Andpd, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0x66, 0x0F, 0x54, 0xC1]);
    }

    #[test]
    fn test_andpd_xmm8_xmm15() {
        // ANDPD XMM8, XMM15: 66 REX.RB(45) 0F 54 + ModRM(11 000 111)
        let bytes = encode(X86Opcode::Andpd, &X86InstOperands::rr(XMM8, XMM15));
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0x54, 0xC7]);
    }

    #[test]
    fn test_movsd_xmm0_xmm1() {
        // MOVSD XMM0, XMM1: F2 0F 10 + ModRM(11 000 001)
        let bytes = encode(X86Opcode::MovsdRR, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0xF2, 0x0F, 0x10, 0xC1]);
    }

    #[test]
    fn test_movsd_rm_xmm0_rbx() {
        // MOVSD XMM0, [RBX]: F2 0F 10 + ModRM(00 000 011)
        let bytes = encode(X86Opcode::MovsdRM, &X86InstOperands::rm(XMM0, RBX, 0));
        assert_eq!(bytes, vec![0xF2, 0x0F, 0x10, 0x03]);
    }

    #[test]
    fn test_movsd_rm_xmm0_rbx_disp8() {
        // MOVSD XMM0, [RBX+8]: F2 0F 10 + ModRM(01 000 011) + disp8
        let bytes = encode(X86Opcode::MovsdRM, &X86InstOperands::rm(XMM0, RBX, 8));
        assert_eq!(bytes, vec![0xF2, 0x0F, 0x10, 0x43, 0x08]);
    }

    #[test]
    fn test_movsd_mr_rbx_xmm0() {
        // MOVSD [RBX], XMM0: F2 0F 11 + ModRM(00 000 011)
        // For MovsdMR, dst field holds the source XMM register.
        let bytes = encode(
            X86Opcode::MovsdMR,
            &X86InstOperands {
                dst: Some(XMM0),
                base: Some(RBX),
                disp: 0,
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0xF2, 0x0F, 0x11, 0x03]);
    }

    #[test]
    fn test_ucomisd_xmm0_xmm1() {
        // UCOMISD XMM0, XMM1: 66 0F 2E + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Ucomisd, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0x66, 0x0F, 0x2E, 0xC1]);
    }

    // -----------------------------------------------------------------------
    // SSE2 packed integer direct encoder tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_sse2_packed_xmm_rr_low_regs() {
        use X86Sse2PackedOpcode::*;

        for (opcode, opcode_byte) in [
            (Pand, 0xDB),
            (Pandn, 0xDF),
            (Por, 0xEB),
            (Pxor, 0xEF),
            (Pcmpeqb, 0x74),
            (Pcmpeqw, 0x75),
            (Pcmpgtb, 0x64),
            (Pcmpgtw, 0x65),
            (Pcmpeqd, 0x76),
            (MovdqaRR, 0x6F),
            (Pcmpgtd, 0x66),
            (Paddb, 0xFC),
            (Paddw, 0xFD),
            (Paddd, 0xFE),
            (Psubb, 0xF8),
            (Psubw, 0xF9),
            (Psubd, 0xFA),
            (Pmullw, 0xD5),
            (Paddq, 0xD4),
            (Psubq, 0xFB),
            (Pmuludq, 0xF4),
            (Punpcklbw, 0x60),
            (Punpckldq, 0x62),
            (Packuswb, 0x67),
            (Punpckhbw, 0x68),
            (Punpcklqdq, 0x6C),
        ] {
            let bytes = encode_sse2_packed(opcode, &X86InstOperands::rr(XMM0, XMM1));
            assert_eq!(bytes, vec![0x66, 0x0F, opcode_byte, 0xC1]);
        }

        let bytes = encode_sse2_packed(Pcmpeqq, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0x66, 0x0F, 0x38, 0x29, 0xC1]);
        let bytes = encode_sse2_packed(Pcmpgtq, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0x66, 0x0F, 0x38, 0x37, 0xC1]);
    }

    #[test]
    fn test_sse2_packed_xmm_rr_high_regs() {
        use X86Sse2PackedOpcode::*;

        for (opcode, opcode_byte) in [
            (Pand, 0xDB),
            (Pandn, 0xDF),
            (Por, 0xEB),
            (Pxor, 0xEF),
            (Pcmpeqb, 0x74),
            (Pcmpeqw, 0x75),
            (Pcmpgtb, 0x64),
            (Pcmpgtw, 0x65),
            (Pcmpeqd, 0x76),
            (MovdqaRR, 0x6F),
            (Pcmpgtd, 0x66),
            (Paddb, 0xFC),
            (Paddw, 0xFD),
            (Paddd, 0xFE),
            (Psubb, 0xF8),
            (Psubw, 0xF9),
            (Psubd, 0xFA),
            (Pmullw, 0xD5),
            (Paddq, 0xD4),
            (Psubq, 0xFB),
            (Pmuludq, 0xF4),
            (Punpcklbw, 0x60),
            (Punpckldq, 0x62),
            (Packuswb, 0x67),
            (Punpckhbw, 0x68),
            (Punpcklqdq, 0x6C),
        ] {
            let bytes = encode_sse2_packed(opcode, &X86InstOperands::rr(XMM8, XMM15));
            assert_eq!(bytes, vec![0x66, 0x45, 0x0F, opcode_byte, 0xC7]);
        }

        let bytes = encode_sse2_packed(Pcmpeqq, &X86InstOperands::rr(XMM8, XMM15));
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0x38, 0x29, 0xC7]);
        let bytes = encode_sse2_packed(Pcmpgtq, &X86InstOperands::rr(XMM8, XMM15));
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0x38, 0x37, 0xC7]);
    }

    #[test]
    fn test_sse2_packed_pshufd_low_and_high_regs() {
        let bytes = encode_sse2_packed(
            X86Sse2PackedOpcode::Pshufd,
            &X86InstOperands::rri(XMM0, XMM1, 0x1B),
        );
        assert_eq!(bytes, vec![0x66, 0x0F, 0x70, 0xC1, 0x1B]);

        let bytes = encode_sse2_packed(
            X86Sse2PackedOpcode::Pshufd,
            &X86InstOperands::rri(XMM8, XMM15, 0x4E),
        );
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0x70, 0xC7, 0x4E]);
    }

    #[test]
    fn test_sse2_packed_dword_imm_shifts_low_and_high_regs() {
        use X86Sse2PackedOpcode::*;

        for (opcode, ext, imm, expected_modrm) in [
            (Pslld, 6, 7, 0xF0),
            (Psrld, 2, 31, 0xD0),
            (Psrad, 4, 1, 0xE0),
        ] {
            let bytes = encode_sse2_packed(opcode, &X86InstOperands::ri(XMM0, imm));
            assert_eq!(bytes, vec![0x66, 0x0F, 0x72, expected_modrm, imm as u8]);

            let bytes = encode_sse2_packed(opcode, &X86InstOperands::ri(XMM15, imm));
            assert_eq!(
                bytes,
                vec![0x66, 0x41, 0x0F, 0x72, expected_modrm | 0x07, imm as u8],
                "high-register /{} encoding for {:?}",
                ext,
                opcode
            );
        }
    }

    #[test]
    fn test_sse2_packed_qword_imm_shifts_low_and_high_regs() {
        use X86Sse2PackedOpcode::*;

        // PSLLQ/PSRLQ share group-13 opcode byte 0x73 (the dword shifts use
        // 0x72 — group 12); a 0x72-encoded qword shift would be a silent
        // dword shift, so the group byte is asserted per-opcode here.
        for (opcode, ext, imm, expected_modrm) in [(Psllq, 6, 32, 0xF0), (Psrlq, 2, 32, 0xD0)] {
            let bytes = encode_sse2_packed(opcode, &X86InstOperands::ri(XMM0, imm));
            assert_eq!(bytes, vec![0x66, 0x0F, 0x73, expected_modrm, imm as u8]);

            let bytes = encode_sse2_packed(opcode, &X86InstOperands::ri(XMM15, imm));
            assert_eq!(
                bytes,
                vec![0x66, 0x41, 0x0F, 0x73, expected_modrm | 0x07, imm as u8],
                "high-register /{} encoding for {:?}",
                ext,
                opcode
            );
        }
    }

    #[test]
    fn test_sse2_packed_xmm_memory_low_and_high_regs() {
        use X86Sse2PackedOpcode::*;

        for (opcode, opcode_byte) in [
            (Pand, 0xDB),
            (Por, 0xEB),
            (Pxor, 0xEF),
            (Pcmpeqb, 0x74),
            (Pcmpeqw, 0x75),
            (Pcmpgtb, 0x64),
            (Pcmpgtw, 0x65),
            (Pcmpeqd, 0x76),
            (Paddb, 0xFC),
            (Paddw, 0xFD),
            (Psubb, 0xF8),
            (Psubw, 0xF9),
        ] {
            let bytes = encode_sse2_packed(opcode, &X86InstOperands::rm(XMM0, RBX, 0));
            assert_eq!(bytes, vec![0x66, 0x0F, opcode_byte, 0x03]);

            let bytes = encode_sse2_packed(opcode, &X86InstOperands::rm(XMM8, R12, 32));
            assert_eq!(bytes, vec![0x66, 0x45, 0x0F, opcode_byte, 0x44, 0x24, 0x20]);
        }

        let bytes = encode_sse2_packed(Pxor, &X86InstOperands::rm(XMM15, R13, 0));
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0xEF, 0x7D, 0x00]);

        let mut ops = X86InstOperands::rm(XMM8, R12, 32);
        ops.imm = 0x4E;
        let bytes = encode_sse2_packed(X86Sse2PackedOpcode::Pshufd, &ops);
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0x70, 0x44, 0x24, 0x20, 0x4E]);
    }

    #[test]
    fn test_sse2_packed_pmovmskb_low_and_high_regs() {
        let bytes = encode_sse2_packed(
            X86Sse2PackedOpcode::Pmovmskb,
            &X86InstOperands::rr(EAX, XMM1),
        );
        assert_eq!(bytes, vec![0x66, 0x0F, 0xD7, 0xC1]);

        let bytes = encode_sse2_packed(
            X86Sse2PackedOpcode::Pmovmskb,
            &X86InstOperands::rr(R8D, XMM15),
        );
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0xD7, 0xC7]);
    }

    #[test]
    fn test_sse2_packed_rejects_wrong_register_classes() {
        use X86Sse2PackedOpcode::*;

        for opcode in [
            Pand, Pandn, Por, Pxor, Pcmpeqb, Pcmpeqw, Pcmpgtb, Pcmpgtw, Pcmpeqd, Pcmpgtd, Paddb,
            Paddw, Paddd, Psubb, Psubw, Psubd, Pmullw, Paddq, Psubq, Pcmpeqq, Pcmpgtq, Pshufd,
            Punpcklbw, Punpckldq, Packuswb, Punpckhbw, Punpcklqdq, Pslld, Psrld, Psrad, Psllq,
            Psrlq, MovdqaRR,
        ] {
            let mut enc = X86Encoder::new();
            let err = enc
                .encode_sse2_packed_instruction(opcode, &X86InstOperands::rr(EAX, XMM1))
                .expect_err("packed XMM ops require XMM dst/src registers");
            assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
            assert!(enc.finish().is_empty());
        }

        let mut enc = X86Encoder::new();
        let err = enc
            .encode_sse2_packed_instruction(
                X86Sse2PackedOpcode::Pmovmskb,
                &X86InstOperands::rr(XMM0, XMM1),
            )
            .expect_err("PMOVMSKB requires a GPR32 dst and XMM src");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());
    }

    #[test]
    fn test_sse2_packed_rejects_bad_operand_shapes() {
        let mut enc = X86Encoder::new();
        let err = enc
            .encode_sse2_packed_instruction(
                X86Sse2PackedOpcode::Pshufd,
                &X86InstOperands::rri(XMM0, XMM1, 256),
            )
            .expect_err("PSHUFD immediate must fit in imm8");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());

        let mut enc = X86Encoder::new();
        let err = enc
            .encode_sse2_packed_instruction(
                X86Sse2PackedOpcode::Pslld,
                &X86InstOperands::ri(XMM0, 256),
            )
            .expect_err("PSLLD immediate must fit in imm8");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());

        let mut ops = X86InstOperands::rr(XMM0, XMM1);
        ops.base = Some(RBX);
        let mut enc = X86Encoder::new();
        let err = enc
            .encode_sse2_packed_instruction(X86Sse2PackedOpcode::Pand, &ops)
            .expect_err("packed ops must reject mixed register and memory sources");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());
    }

    #[test]
    fn test_x86_opcode_sse2_packed_xmm_rr_low_regs() {
        use X86Opcode::*;

        for (opcode, opcode_byte) in [
            (Pand, 0xDB),
            (Pandn, 0xDF),
            (Por, 0xEB),
            (Pxor, 0xEF),
            (Pcmpeqb, 0x74),
            (Pcmpeqw, 0x75),
            (Pcmpgtb, 0x64),
            (Pcmpgtw, 0x65),
            (Pcmpeqd, 0x76),
            (MovdqaRR, 0x6F),
            (Pcmpgtd, 0x66),
            (Paddb, 0xFC),
            (Paddw, 0xFD),
            (Paddd, 0xFE),
            (Psubb, 0xF8),
            (Psubw, 0xF9),
            (Psubd, 0xFA),
            (Pmullw, 0xD5),
            (Paddq, 0xD4),
            (Psubq, 0xFB),
            (Pmuludq, 0xF4),
            (Punpcklbw, 0x60),
            (Punpckldq, 0x62),
            (Packuswb, 0x67),
            (Punpckhbw, 0x68),
            (Punpcklqdq, 0x6C),
            // PSADBW: 66 0F F6 /r — byte sum-of-absolute-differences.
            (Psadbw, 0xF6),
        ] {
            let bytes = encode(opcode, &X86InstOperands::rr(XMM0, XMM1));
            assert_eq!(bytes, vec![0x66, 0x0F, opcode_byte, 0xC1]);
        }

        let bytes = encode(Pmulld, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0x66, 0x0F, 0x38, 0x40, 0xC1]);
        let bytes = encode(Pcmpeqq, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0x66, 0x0F, 0x38, 0x29, 0xC1]);
        let bytes = encode(Pcmpgtq, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0x66, 0x0F, 0x38, 0x37, 0xC1]);
        let bytes = encode(Ptest, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0x66, 0x0F, 0x38, 0x17, 0xC1]);
        let bytes = encode(Pblendvb, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0x66, 0x0F, 0x38, 0x10, 0xC1]);
    }

    #[test]
    fn test_x86_opcode_sse2_packed_xmm_rr_high_regs() {
        use X86Opcode::*;

        for (opcode, opcode_byte) in [
            (Pand, 0xDB),
            (Pandn, 0xDF),
            (Por, 0xEB),
            (Pxor, 0xEF),
            (Pcmpeqb, 0x74),
            (Pcmpeqw, 0x75),
            (Pcmpgtb, 0x64),
            (Pcmpgtw, 0x65),
            (Pcmpeqd, 0x76),
            (MovdqaRR, 0x6F),
            (Pcmpgtd, 0x66),
            (Paddb, 0xFC),
            (Paddw, 0xFD),
            (Paddd, 0xFE),
            (Psubb, 0xF8),
            (Psubw, 0xF9),
            (Psubd, 0xFA),
            (Pmullw, 0xD5),
            (Paddq, 0xD4),
            (Psubq, 0xFB),
            (Pmuludq, 0xF4),
            (Punpcklbw, 0x60),
            (Punpckldq, 0x62),
            (Packuswb, 0x67),
            (Punpckhbw, 0x68),
            (Punpcklqdq, 0x6C),
            // PSADBW: 66 45 0F F6 /r with REX.RB for xmm8-15.
            (Psadbw, 0xF6),
        ] {
            let bytes = encode(opcode, &X86InstOperands::rr(XMM8, XMM15));
            assert_eq!(bytes, vec![0x66, 0x45, 0x0F, opcode_byte, 0xC7]);
        }

        let bytes = encode(Pmulld, &X86InstOperands::rr(XMM8, XMM15));
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0x38, 0x40, 0xC7]);
        let bytes = encode(Pcmpeqq, &X86InstOperands::rr(XMM8, XMM15));
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0x38, 0x29, 0xC7]);
        let bytes = encode(Pcmpgtq, &X86InstOperands::rr(XMM8, XMM15));
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0x38, 0x37, 0xC7]);
        let bytes = encode(Ptest, &X86InstOperands::rr(XMM8, XMM15));
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0x38, 0x17, 0xC7]);
        let bytes = encode(Pblendvb, &X86InstOperands::rr(XMM8, XMM15));
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0x38, 0x10, 0xC7]);
    }

    #[test]
    fn test_x86_opcode_sse2_packed_pshufd_and_pmovmskb() {
        let bytes = encode(X86Opcode::Pshufd, &X86InstOperands::rri(XMM0, XMM1, 0x1B));
        assert_eq!(bytes, vec![0x66, 0x0F, 0x70, 0xC1, 0x1B]);

        let bytes = encode(X86Opcode::Pmovmskb, &X86InstOperands::rr(R8D, XMM15));
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0xD7, 0xC7]);
    }

    #[test]
    fn test_x86_opcode_sse2_packed_dword_imm_shifts_low_and_high_regs() {
        for (opcode, imm, expected_low_modrm) in [
            (X86Opcode::Pslld, 7, 0xF0),
            (X86Opcode::Psrld, 31, 0xD0),
            (X86Opcode::Psrad, 1, 0xE0),
        ] {
            let bytes = encode(opcode, &X86InstOperands::ri(XMM0, imm));
            assert_eq!(bytes, vec![0x66, 0x0F, 0x72, expected_low_modrm, imm as u8]);

            let bytes = encode(opcode, &X86InstOperands::ri(XMM15, imm));
            assert_eq!(
                bytes,
                vec![0x66, 0x41, 0x0F, 0x72, expected_low_modrm | 0x07, imm as u8]
            );
        }
    }

    #[test]
    fn test_x86_opcode_sse2_packed_qword_imm_shifts_low_and_high_regs() {
        // Group-13 byte 0x73 (qword), NOT the dword group 0x72 — a swapped
        // group byte silently reinterprets the shift at the wrong lane width.
        for (opcode, imm, expected_low_modrm) in
            [(X86Opcode::Psllq, 32, 0xF0), (X86Opcode::Psrlq, 32, 0xD0)]
        {
            let bytes = encode(opcode, &X86InstOperands::ri(XMM0, imm));
            assert_eq!(bytes, vec![0x66, 0x0F, 0x73, expected_low_modrm, imm as u8]);

            let bytes = encode(opcode, &X86InstOperands::ri(XMM15, imm));
            assert_eq!(
                bytes,
                vec![0x66, 0x41, 0x0F, 0x73, expected_low_modrm | 0x07, imm as u8]
            );
        }
    }

    #[test]
    fn test_x86_opcode_sse2_packed_xmm_memory_low_and_high_regs() {
        use X86Opcode::*;

        for (opcode, opcode_byte) in [
            (Pand, 0xDB),
            (Por, 0xEB),
            (Pxor, 0xEF),
            (Pcmpeqb, 0x74),
            (Pcmpeqw, 0x75),
            (Pcmpgtb, 0x64),
            (Pcmpgtw, 0x65),
            (Pcmpeqd, 0x76),
            (Paddb, 0xFC),
            (Paddw, 0xFD),
            (Psubb, 0xF8),
            (Psubw, 0xF9),
        ] {
            let bytes = encode(opcode, &X86InstOperands::rm(XMM0, RBX, 0));
            assert_eq!(bytes, vec![0x66, 0x0F, opcode_byte, 0x03]);

            let bytes = encode(opcode, &X86InstOperands::rm(XMM8, R12, 32));
            assert_eq!(bytes, vec![0x66, 0x45, 0x0F, opcode_byte, 0x44, 0x24, 0x20]);
        }

        let bytes = encode(X86Opcode::Pxor, &X86InstOperands::rm(XMM15, R13, 0));
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0xEF, 0x7D, 0x00]);

        let mut ops = X86InstOperands::rm(XMM8, R12, 32);
        ops.imm = 0x4E;
        let bytes = encode(X86Opcode::Pshufd, &ops);
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0x70, 0x44, 0x24, 0x20, 0x4E]);
    }

    #[test]
    fn test_vector_pseudos_are_pipeline_only() {
        for opcode in [
            X86Opcode::V4I32MaskExtract,
            X86Opcode::V16I8MaskExtract,
            X86Opcode::V8I16MaskExtract,
            X86Opcode::V2I64MaskExtract,
            X86Opcode::V128BoolSelect,
        ] {
            let mut enc = X86Encoder::new();
            let err = enc
                .encode_instruction(opcode, &X86InstOperands::rr(EAX, XMM0))
                .expect_err("vector pseudo must be expanded by the x86 pipeline");
            assert!(matches!(err, X86EncodeError::UnsupportedOpcode(op) if op == opcode));
            assert!(enc.finish().is_empty());
        }
    }

    #[test]
    fn test_x86_opcode_movdqa_load_store_low_and_high_regs() {
        let bytes = encode(X86Opcode::MovdqaRM, &X86InstOperands::rm(XMM0, RBX, 0));
        assert_eq!(bytes, vec![0x66, 0x0F, 0x6F, 0x03]);

        let bytes = encode(X86Opcode::MovdqaMR, &X86InstOperands::rm(XMM0, RBX, 0));
        assert_eq!(bytes, vec![0x66, 0x0F, 0x7F, 0x03]);

        let bytes = encode(X86Opcode::MovdqaRM, &X86InstOperands::rm(XMM8, R12, 32));
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0x6F, 0x44, 0x24, 0x20]);

        let bytes = encode(X86Opcode::MovdqaMR, &X86InstOperands::rm(XMM15, R13, 0));
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0x7F, 0x7D, 0x00]);

        let bytes = encode(X86Opcode::Ptest, &X86InstOperands::rm(XMM0, RBX, 0));
        assert_eq!(bytes, vec![0x66, 0x0F, 0x38, 0x17, 0x03]);

        let bytes = encode(X86Opcode::Ptest, &X86InstOperands::rm(XMM8, R12, 32));
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0x38, 0x17, 0x44, 0x24, 0x20]);
    }

    #[test]
    fn test_x86_opcode_sse2_packed_rejects_wrong_register_classes() {
        for opcode in [
            X86Opcode::Pand,
            X86Opcode::Pandn,
            X86Opcode::Por,
            X86Opcode::Pxor,
            X86Opcode::Pcmpeqb,
            X86Opcode::Pcmpeqw,
            X86Opcode::Pcmpgtb,
            X86Opcode::Pcmpgtw,
            X86Opcode::Pcmpeqd,
            X86Opcode::Pcmpgtd,
            X86Opcode::Paddb,
            X86Opcode::Paddw,
            X86Opcode::Paddd,
            X86Opcode::Psubb,
            X86Opcode::Psubw,
            X86Opcode::Psubd,
            X86Opcode::Paddq,
            X86Opcode::Psubq,
            X86Opcode::Pmuludq,
            X86Opcode::Punpcklbw,
            X86Opcode::Punpckhbw,
            X86Opcode::Punpckldq,
            X86Opcode::Punpcklqdq,
            X86Opcode::Packuswb,
            X86Opcode::Pmulld,
            X86Opcode::Pcmpeqq,
            X86Opcode::Pcmpgtq,
            X86Opcode::Ptest,
            X86Opcode::Pblendvb,
            X86Opcode::Pshufd,
            X86Opcode::Pslld,
            X86Opcode::Psrld,
            X86Opcode::Psrad,
            X86Opcode::Psllq,
            X86Opcode::Psrlq,
            X86Opcode::MovdqaRR,
        ] {
            let mut enc = X86Encoder::new();
            let err = enc
                .encode_instruction(opcode, &X86InstOperands::rr(EAX, XMM1))
                .expect_err("packed XMM ops require XMM dst/src registers");
            assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
            assert!(enc.finish().is_empty());
        }

        let mut enc = X86Encoder::new();
        let err = enc
            .encode_instruction(X86Opcode::Pmovmskb, &X86InstOperands::rr(XMM0, XMM1))
            .expect_err("PMOVMSKB requires a GPR32 dst and XMM src");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());
    }

    #[test]
    fn test_x86_opcode_sse2_packed_rejects_bad_operand_shapes() {
        let mut enc = X86Encoder::new();
        let err = enc
            .encode_instruction(X86Opcode::Pshufd, &X86InstOperands::rri(XMM0, XMM1, 256))
            .expect_err("PSHUFD immediate must fit in imm8");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());

        let mut enc = X86Encoder::new();
        let err = enc
            .encode_instruction(X86Opcode::Psrld, &X86InstOperands::ri(XMM0, 256))
            .expect_err("PSRLD immediate must fit in imm8");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());

        let mut ops = X86InstOperands::rr(XMM0, XMM1);
        ops.base = Some(RBX);
        let mut enc = X86Encoder::new();
        let err = enc
            .encode_instruction(X86Opcode::Pand, &ops)
            .expect_err("packed ops must reject mixed register and memory sources");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());

        let mut ops = X86InstOperands::rr(XMM0, XMM1);
        ops.imm = 1;
        let mut enc = X86Encoder::new();
        let err = enc
            .encode_instruction(X86Opcode::Ptest, &ops)
            .expect_err("PTEST must reject immediate operands");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());

        let mut ops = X86InstOperands::rr(XMM0, XMM1);
        ops.base = Some(RBX);
        let mut enc = X86Encoder::new();
        let err = enc
            .encode_instruction(X86Opcode::Pblendvb, &ops)
            .expect_err("PBLENDVB must reject memory-shaped operands");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());

        let mut ops = X86InstOperands::rm(XMM0, RBX, 0);
        ops.imm = 1;
        let mut enc = X86Encoder::new();
        let err = enc
            .encode_instruction(X86Opcode::Ptest, &ops)
            .expect_err("PTEST memory form must reject immediate operands");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());

        let mut enc = X86Encoder::new();
        let err = enc
            .encode_instruction(X86Opcode::MovdqaRM, &X86InstOperands::rm(EAX, RBX, 0))
            .expect_err("MOVDQA load requires XMM dst");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());

        let mut enc = X86Encoder::new();
        let err = enc
            .encode_instruction(X86Opcode::MovdqaMR, &X86InstOperands::rm(XMM0, XMM1, 0))
            .expect_err("MOVDQA store requires GPR64 memory base");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());

        let mut ops = X86InstOperands::rm(XMM0, RBX, i64::from(i32::MAX) + 1);
        let mut enc = X86Encoder::new();
        let err = enc
            .encode_instruction(X86Opcode::MovdqaRM, &ops)
            .expect_err("MOVDQA load displacement must fit in disp32");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());

        ops = X86InstOperands::rm_sib(XMM0, RBX, RAX, 2, 0);
        let mut enc = X86Encoder::new();
        let err = enc
            .encode_instruction(X86Opcode::MovdqaRM, &ops)
            .expect_err("MOVDQA load currently accepts base+disp only");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());
    }

    // -----------------------------------------------------------------------
    // SSE scalar single-precision tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_addss_xmm0_xmm1() {
        // ADDSS XMM0, XMM1: F3 0F 58 + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Addss, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0xF3, 0x0F, 0x58, 0xC1]);
    }

    #[test]
    fn test_subss_xmm0_xmm1() {
        // SUBSS XMM0, XMM1: F3 0F 5C + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Subss, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0xF3, 0x0F, 0x5C, 0xC1]);
    }

    #[test]
    fn test_mulss_xmm0_xmm1() {
        // MULSS XMM0, XMM1: F3 0F 59 + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Mulss, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0xF3, 0x0F, 0x59, 0xC1]);
    }

    #[test]
    fn test_divss_xmm0_xmm1() {
        // DIVSS XMM0, XMM1: F3 0F 5E + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Divss, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0xF3, 0x0F, 0x5E, 0xC1]);
    }

    #[test]
    fn test_addss_xmm8_xmm15() {
        // ADDSS XMM8, XMM15: F3 REX.RB(45) 0F 58 + ModRM(11 000 111)
        let bytes = encode(X86Opcode::Addss, &X86InstOperands::rr(XMM8, XMM15));
        assert_eq!(bytes, vec![0xF3, 0x45, 0x0F, 0x58, 0xC7]);
    }

    #[test]
    fn test_sqrtss_xmm0_xmm1() {
        // SQRTSS XMM0, XMM1: F3 0F 51 + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Sqrtss, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0xF3, 0x0F, 0x51, 0xC1]);
    }

    #[test]
    fn test_sqrtss_xmm8_xmm15() {
        // SQRTSS XMM8, XMM15: F3 REX.RB(45) 0F 51 + ModRM(11 000 111)
        let bytes = encode(X86Opcode::Sqrtss, &X86InstOperands::rr(XMM8, XMM15));
        assert_eq!(bytes, vec![0xF3, 0x45, 0x0F, 0x51, 0xC7]);
    }

    // ROUNDSD/ROUNDSS encodings cross-checked against clang/objdump ground truth:
    //   roundsd $1, %xmm1, %xmm0      -> 66 0f 3a 0b c1 01
    //   roundss $2, %xmm1, %xmm0      -> 66 0f 3a 0a c1 02
    //   roundsd $3, %xmm15, %xmm8     -> 66 45 0f 3a 0b c7 03
    #[test]
    fn test_roundsd_xmm0_xmm1_floor() {
        // ROUNDSD XMM0, XMM1, 0x09 (floor): 66 0F 3A 0B + ModRM(11 000 001) + ib
        let bytes = encode(X86Opcode::Roundsd, &X86InstOperands::rri(XMM0, XMM1, 0x09));
        assert_eq!(bytes, vec![0x66, 0x0F, 0x3A, 0x0B, 0xC1, 0x09]);
    }

    #[test]
    fn test_roundsd_xmm8_xmm15_trunc() {
        // ROUNDSD XMM8, XMM15, 0x0B (trunc): 66 REX.RB(45) 0F 3A 0B + ModRM(11 000 111) + ib
        let bytes = encode(X86Opcode::Roundsd, &X86InstOperands::rri(XMM8, XMM15, 0x0B));
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0x3A, 0x0B, 0xC7, 0x0B]);
    }

    #[test]
    fn test_roundss_xmm0_xmm1_ceil() {
        // ROUNDSS XMM0, XMM1, 0x0A (ceil): 66 0F 3A 0A + ModRM(11 000 001) + ib
        let bytes = encode(X86Opcode::Roundss, &X86InstOperands::rri(XMM0, XMM1, 0x0A));
        assert_eq!(bytes, vec![0x66, 0x0F, 0x3A, 0x0A, 0xC1, 0x0A]);
    }

    #[test]
    fn test_roundss_xmm8_xmm15_floor() {
        // ROUNDSS XMM8, XMM15, 0x09 (floor): 66 REX.RB(45) 0F 3A 0A + ModRM(11 000 111) + ib
        let bytes = encode(X86Opcode::Roundss, &X86InstOperands::rri(XMM8, XMM15, 0x09));
        assert_eq!(bytes, vec![0x66, 0x45, 0x0F, 0x3A, 0x0A, 0xC7, 0x09]);
    }

    #[test]
    fn test_andps_xmm0_xmm1() {
        // ANDPS XMM0, XMM1: 0F 54 + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Andps, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0x0F, 0x54, 0xC1]);
    }

    #[test]
    fn test_andps_xmm8_xmm15() {
        // ANDPS XMM8, XMM15: REX.RB(45) 0F 54 + ModRM(11 000 111)
        let bytes = encode(X86Opcode::Andps, &X86InstOperands::rr(XMM8, XMM15));
        assert_eq!(bytes, vec![0x45, 0x0F, 0x54, 0xC7]);
    }

    #[test]
    fn test_movss_xmm0_xmm1() {
        // MOVSS XMM0, XMM1: F3 0F 10 + ModRM(11 000 001)
        let bytes = encode(X86Opcode::MovssRR, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0xF3, 0x0F, 0x10, 0xC1]);
    }

    #[test]
    fn test_movss_rm_xmm0_rbx() {
        // MOVSS XMM0, [RBX]: F3 0F 10 + ModRM(00 000 011)
        let bytes = encode(X86Opcode::MovssRM, &X86InstOperands::rm(XMM0, RBX, 0));
        assert_eq!(bytes, vec![0xF3, 0x0F, 0x10, 0x03]);
    }

    #[test]
    fn test_movss_mr_rbx_xmm0() {
        // MOVSS [RBX], XMM0: F3 0F 11 + ModRM(00 000 011)
        let bytes = encode(
            X86Opcode::MovssMR,
            &X86InstOperands {
                dst: Some(XMM0),
                base: Some(RBX),
                disp: 0,
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0xF3, 0x0F, 0x11, 0x03]);
    }

    #[test]
    fn test_ucomiss_xmm0_xmm1() {
        // UCOMISS XMM0, XMM1: 0F 2E + ModRM(11 000 001) (no prefix)
        let bytes = encode(X86Opcode::Ucomiss, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0x0F, 0x2E, 0xC1]);
    }

    #[test]
    fn test_ucomiss_xmm8_xmm15() {
        // UCOMISS XMM8, XMM15: REX.RB(45) 0F 2E + ModRM(11 000 111)
        let bytes = encode(X86Opcode::Ucomiss, &X86InstOperands::rr(XMM8, XMM15));
        assert_eq!(bytes, vec![0x45, 0x0F, 0x2E, 0xC7]);
    }

    // -----------------------------------------------------------------------
    // CMOVcc tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_cmove_rax_rcx() {
        // CMOVE RAX, RCX: REX.W(48) + 0F 44 + ModRM(11 000 001)
        let bytes = encode(
            X86Opcode::Cmovcc,
            &X86InstOperands {
                dst: Some(RAX),
                src: Some(RCX),
                cc: Some(X86CondCode::E),
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0x48, 0x0F, 0x44, 0xC1]);
    }

    #[test]
    fn test_cmovne_rbx_rdx() {
        // CMOVNE RBX, RDX: REX.W(48) + 0F 45 + ModRM(11 011 010)
        let bytes = encode(
            X86Opcode::Cmovcc,
            &X86InstOperands {
                dst: Some(RBX),
                src: Some(RDX),
                cc: Some(X86CondCode::NE),
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0x48, 0x0F, 0x45, 0xDA]);
    }

    #[test]
    fn test_cmovl_r8_r9() {
        // CMOVL R8, R9: REX.WRB(4D) + 0F 4C + ModRM(11 000 001)
        let bytes = encode(
            X86Opcode::Cmovcc,
            &X86InstOperands {
                dst: Some(R8),
                src: Some(R9),
                cc: Some(X86CondCode::L),
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0x4D, 0x0F, 0x4C, 0xC1]);
    }

    #[test]
    fn test_cmovg_rax_r15() {
        // CMOVG RAX, R15: REX.WB(49) + 0F 4F + ModRM(11 000 111)
        let bytes = encode(
            X86Opcode::Cmovcc,
            &X86InstOperands {
                dst: Some(RAX),
                src: Some(R15),
                cc: Some(X86CondCode::G),
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0x49, 0x0F, 0x4F, 0xC7]);
    }

    #[test]
    fn test_cmovne32_eax_ecx() {
        // CMOVNE EAX, ECX: 0F 45 + ModRM(11 000 001), no REX.W.
        let bytes = encode(
            X86Opcode::Cmovcc32,
            &X86InstOperands {
                dst: Some(EAX),
                src: Some(ECX),
                cc: Some(X86CondCode::NE),
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0x0F, 0x45, 0xC1]);
    }

    #[test]
    fn test_cmovl32_r8d_r9d() {
        // CMOVL R8D, R9D: REX.RB(45) + 0F 4C + ModRM(11 000 001), no REX.W.
        let bytes = encode(
            X86Opcode::Cmovcc32,
            &X86InstOperands {
                dst: Some(R8D),
                src: Some(R9D),
                cc: Some(X86CondCode::L),
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0x45, 0x0F, 0x4C, 0xC1]);
    }

    // -----------------------------------------------------------------------
    // SETcc tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_sete_al() {
        // SETE AL: 0F 94 + ModRM(11 000 000)
        let bytes = encode(
            X86Opcode::Setcc,
            &X86InstOperands {
                dst: Some(AL),
                cc: Some(X86CondCode::E),
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0x0F, 0x94, 0xC0]);
    }

    #[test]
    fn test_setne_cl() {
        // SETNE CL: 0F 95 + ModRM(11 000 001)
        let bytes = encode(
            X86Opcode::Setcc,
            &X86InstOperands {
                dst: Some(CL),
                cc: Some(X86CondCode::NE),
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0x0F, 0x95, 0xC1]);
    }

    #[test]
    fn test_setl_r8b() {
        // SETL R8B: REX.B(41) + 0F 9C + ModRM(11 000 000)
        let bytes = encode(
            X86Opcode::Setcc,
            &X86InstOperands {
                dst: Some(R8B),
                cc: Some(X86CondCode::L),
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0x41, 0x0F, 0x9C, 0xC0]);
    }

    #[test]
    fn test_sete_sil_forces_rex() {
        // SETE SIL: forced REX(40) selects SIL instead of legacy DH.
        let bytes = encode(
            X86Opcode::Setcc,
            &X86InstOperands {
                dst: Some(SIL),
                cc: Some(X86CondCode::E),
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0x40, 0x0F, 0x94, 0xC6]);
    }

    #[test]
    fn test_setg_al() {
        // SETG AL: 0F 9F + ModRM(11 000 000)
        let bytes = encode(
            X86Opcode::Setcc,
            &X86InstOperands {
                dst: Some(AL),
                cc: Some(X86CondCode::G),
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0x0F, 0x9F, 0xC0]);
    }

    // -----------------------------------------------------------------------
    // Bit manipulation tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_bsf_rax_rcx() {
        // BSF RAX, RCX: REX.W(48) + 0F BC + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Bsf, &X86InstOperands::rr(RAX, RCX));
        assert_eq!(bytes, vec![0x48, 0x0F, 0xBC, 0xC1]);
    }

    #[test]
    fn test_bsf_r8_r9() {
        // BSF R8, R9: REX.WRB(4D) + 0F BC + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Bsf, &X86InstOperands::rr(R8, R9));
        assert_eq!(bytes, vec![0x4D, 0x0F, 0xBC, 0xC1]);
    }

    #[test]
    fn test_bsr_rax_rcx() {
        // BSR RAX, RCX: REX.W(48) + 0F BD + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Bsr, &X86InstOperands::rr(RAX, RCX));
        assert_eq!(bytes, vec![0x48, 0x0F, 0xBD, 0xC1]);
    }

    #[test]
    fn test_bsr_r15_rax() {
        // BSR R15, RAX: REX.WR(4C) + 0F BD + ModRM(11 111 000)
        let bytes = encode(X86Opcode::Bsr, &X86InstOperands::rr(R15, RAX));
        assert_eq!(bytes, vec![0x4C, 0x0F, 0xBD, 0xF8]);
    }

    #[test]
    fn test_tzcnt_rax_rcx() {
        // TZCNT RAX, RCX: F3 REX.W(48) + 0F BC + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Tzcnt, &X86InstOperands::rr(RAX, RCX));
        assert_eq!(bytes, vec![0xF3, 0x48, 0x0F, 0xBC, 0xC1]);
    }

    #[test]
    fn test_tzcnt_r8_r9() {
        // TZCNT R8, R9: F3 REX.WRB(4D) + 0F BC + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Tzcnt, &X86InstOperands::rr(R8, R9));
        assert_eq!(bytes, vec![0xF3, 0x4D, 0x0F, 0xBC, 0xC1]);
    }

    #[test]
    fn test_lzcnt_rax_rcx() {
        // LZCNT RAX, RCX: F3 REX.W(48) + 0F BD + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Lzcnt, &X86InstOperands::rr(RAX, RCX));
        assert_eq!(bytes, vec![0xF3, 0x48, 0x0F, 0xBD, 0xC1]);
    }

    #[test]
    fn test_lzcnt_r15_rax() {
        // LZCNT R15, RAX: F3 REX.WR(4C) + 0F BD + ModRM(11 111 000)
        let bytes = encode(X86Opcode::Lzcnt, &X86InstOperands::rr(R15, RAX));
        assert_eq!(bytes, vec![0xF3, 0x4C, 0x0F, 0xBD, 0xF8]);
    }

    #[test]
    fn test_popcnt_rax_rcx() {
        // POPCNT RAX, RCX: F3 REX.W(48) + 0F B8 + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Popcnt, &X86InstOperands::rr(RAX, RCX));
        assert_eq!(bytes, vec![0xF3, 0x48, 0x0F, 0xB8, 0xC1]);
    }

    #[test]
    fn test_popcnt_r8_r9() {
        // POPCNT R8, R9: F3 REX.WRB(4D) + 0F B8 + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Popcnt, &X86InstOperands::rr(R8, R9));
        assert_eq!(bytes, vec![0xF3, 0x4D, 0x0F, 0xB8, 0xC1]);
    }

    #[test]
    fn test_popcnt_eax_ecx_has_no_rex_w() {
        // POPCNT EAX, ECX: F3 + 0F B8 + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Popcnt, &X86InstOperands::rr(EAX, ECX));
        assert_eq!(bytes, vec![0xF3, 0x0F, 0xB8, 0xC1]);
    }

    #[test]
    fn test_popcnt_r8d_r9d_has_rex_without_w() {
        // POPCNT R8D, R9D: F3 + REX.RB(45) + 0F B8 + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Popcnt, &X86InstOperands::rr(R8D, R9D));
        assert_eq!(bytes, vec![0xF3, 0x45, 0x0F, 0xB8, 0xC1]);
    }

    // -----------------------------------------------------------------------
    // Mixed encoding size tests for new instructions
    // -----------------------------------------------------------------------

    #[test]
    fn test_new_instruction_sizes() {
        let mut enc = X86Encoder::new();

        // SSE scalar: prefix(1) + 0F(1) + opcode(1) + ModRM(1) = 4 bytes
        let n = enc
            .encode_instruction(X86Opcode::Addsd, &X86InstOperands::rr(XMM0, XMM1))
            .unwrap();
        assert_eq!(n, 4);

        // SSE scalar with extended regs: prefix(1) + REX(1) + 0F(1) + opcode(1) + ModRM(1) = 5 bytes
        let n = enc
            .encode_instruction(X86Opcode::Addsd, &X86InstOperands::rr(XMM8, XMM15))
            .unwrap();
        assert_eq!(n, 5);

        // CMOVcc: REX.W(1) + 0F(1) + opcode(1) + ModRM(1) = 4 bytes
        let n = enc
            .encode_instruction(
                X86Opcode::Cmovcc,
                &X86InstOperands {
                    dst: Some(RAX),
                    src: Some(RCX),
                    cc: Some(X86CondCode::E),
                    ..X86InstOperands::none()
                },
            )
            .unwrap();
        assert_eq!(n, 4);

        // SETcc (no REX): 0F(1) + opcode(1) + ModRM(1) = 3 bytes
        let n = enc
            .encode_instruction(
                X86Opcode::Setcc,
                &X86InstOperands {
                    dst: Some(AL),
                    cc: Some(X86CondCode::E),
                    ..X86InstOperands::none()
                },
            )
            .unwrap();
        assert_eq!(n, 3);

        // SETcc with REX.B: REX(1) + 0F(1) + opcode(1) + ModRM(1) = 4 bytes
        let n = enc
            .encode_instruction(
                X86Opcode::Setcc,
                &X86InstOperands {
                    dst: Some(R8B),
                    cc: Some(X86CondCode::E),
                    ..X86InstOperands::none()
                },
            )
            .unwrap();
        assert_eq!(n, 4);

        // BSF: REX.W(1) + 0F(1) + opcode(1) + ModRM(1) = 4 bytes
        let n = enc
            .encode_instruction(X86Opcode::Bsf, &X86InstOperands::rr(RAX, RCX))
            .unwrap();
        assert_eq!(n, 4);

        // TZCNT: F3(1) + REX.W(1) + 0F(1) + opcode(1) + ModRM(1) = 5 bytes
        let n = enc
            .encode_instruction(X86Opcode::Tzcnt, &X86InstOperands::rr(RAX, RCX))
            .unwrap();
        assert_eq!(n, 5);

        // POPCNT: F3(1) + REX.W(1) + 0F(1) + opcode(1) + ModRM(1) = 5 bytes
        let n = enc
            .encode_instruction(X86Opcode::Popcnt, &X86InstOperands::rr(RAX, RCX))
            .unwrap();
        assert_eq!(n, 5);

        // LEA [base+0] = 3 bytes (REX.W + 8D + ModRM)
        let n = enc
            .encode_instruction(X86Opcode::Lea, &X86InstOperands::rm(RAX, RBX, 0))
            .unwrap();
        assert_eq!(n, 3);

        // MOVZX = 4 bytes (REX.W + 0F + B6 + ModRM)
        let n = enc
            .encode_instruction(X86Opcode::Movzx, &X86InstOperands::rr(RAX, RCX))
            .unwrap();
        assert_eq!(n, 4);

        // MOVSXD = 3 bytes (REX.W + 63 + ModRM)
        let n = enc
            .encode_instruction(X86Opcode::Movsx, &X86InstOperands::rr(RAX, RCX))
            .unwrap();
        assert_eq!(n, 3);
    }

    // -----------------------------------------------------------------------
    // CMOVcc / SETcc missing cc errors
    // -----------------------------------------------------------------------

    #[test]
    fn test_cmovcc_missing_cc_error() {
        let mut enc = X86Encoder::new();
        let result = enc.encode_instruction(X86Opcode::Cmovcc, &X86InstOperands::rr(RAX, RCX));
        assert!(result.is_err());
    }

    #[test]
    fn test_cmovcc32_missing_cc_error() {
        let mut enc = X86Encoder::new();
        let result = enc.encode_instruction(X86Opcode::Cmovcc32, &X86InstOperands::rr(EAX, ECX));
        assert!(result.is_err());
    }

    #[test]
    fn test_setcc_missing_cc_error() {
        let mut enc = X86Encoder::new();
        let result = enc.encode_instruction(X86Opcode::Setcc, &X86InstOperands::r(AL));
        assert!(result.is_err());
    }

    // -----------------------------------------------------------------------
    // All CMOVcc condition codes
    // -----------------------------------------------------------------------

    #[test]
    fn test_cmovcc_all_conditions() {
        let all_cc = [
            (X86CondCode::O, 0x40u8),
            (X86CondCode::NO, 0x41),
            (X86CondCode::B, 0x42),
            (X86CondCode::AE, 0x43),
            (X86CondCode::E, 0x44),
            (X86CondCode::NE, 0x45),
            (X86CondCode::BE, 0x46),
            (X86CondCode::A, 0x47),
            (X86CondCode::S, 0x48),
            (X86CondCode::NS, 0x49),
            (X86CondCode::P, 0x4A),
            (X86CondCode::NP, 0x4B),
            (X86CondCode::L, 0x4C),
            (X86CondCode::GE, 0x4D),
            (X86CondCode::LE, 0x4E),
            (X86CondCode::G, 0x4F),
        ];
        for (cc, expected_byte) in &all_cc {
            let bytes = encode(
                X86Opcode::Cmovcc,
                &X86InstOperands {
                    dst: Some(RAX),
                    src: Some(RCX),
                    cc: Some(*cc),
                    ..X86InstOperands::none()
                },
            );
            // REX.W(48) + 0F + cc_byte + ModRM
            assert_eq!(bytes[2], *expected_byte, "CMOVcc {:?}", cc);
        }
    }

    // -----------------------------------------------------------------------
    // SSE memory with extended registers
    // -----------------------------------------------------------------------

    #[test]
    fn test_movsd_rm_xmm8_rsp_disp8() {
        // MOVSD XMM8, [RSP+16]: F2 REX.R(44) 0F 10 + ModRM(01 000 100) + SIB(00 100 100) + disp8
        let bytes = encode(X86Opcode::MovsdRM, &X86InstOperands::rm(XMM8, RSP, 16));
        assert_eq!(bytes, vec![0xF2, 0x44, 0x0F, 0x10, 0x44, 0x24, 0x10]);
    }

    #[test]
    fn test_movss_rm_xmm8_rbp() {
        // MOVSS XMM8, [RBP+0]: F3 REX.R(44) 0F 10 + ModRM(01 000 101) + disp8(00)
        let bytes = encode(X86Opcode::MovssRM, &X86InstOperands::rm(XMM8, RBP, 0));
        assert_eq!(bytes, vec![0xF3, 0x44, 0x0F, 0x10, 0x45, 0x00]);
    }

    // -----------------------------------------------------------------------
    // RIP-relative LEA tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_lea_rip_rax_disp0() {
        // LEA RAX, [RIP+0]: REX.W(48) + 8D + ModRM(00 000 101) + disp32(00000000)
        let bytes = encode(X86Opcode::LeaRip, &X86InstOperands::rip_rel(RAX, 0));
        assert_eq!(bytes, vec![0x48, 0x8D, 0x05, 0x00, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_lea_rip_rcx_disp256() {
        // LEA RCX, [RIP+256]: REX.W(48) + 8D + ModRM(00 001 101) + disp32
        let bytes = encode(X86Opcode::LeaRip, &X86InstOperands::rip_rel(RCX, 256));
        assert_eq!(bytes, vec![0x48, 0x8D, 0x0D, 0x00, 0x01, 0x00, 0x00]);
    }

    #[test]
    fn test_lea_rip_r8_negative() {
        // LEA R8, [RIP-16]: REX.WR(4C) + 8D + ModRM(00 000 101) + disp32(F0FFFFFF)
        let bytes = encode(X86Opcode::LeaRip, &X86InstOperands::rip_rel(R8, -16));
        assert_eq!(bytes, vec![0x4C, 0x8D, 0x05, 0xF0, 0xFF, 0xFF, 0xFF]);
    }

    #[test]
    fn test_mov_rip_rel_rax_disp0() {
        // MOV RAX, [RIP+0]: REX.W(48) + 8B + ModRM(00 000 101) + disp32(00000000)
        let bytes = encode(X86Opcode::MovRipRel, &X86InstOperands::rip_rel(RAX, 0));
        assert_eq!(bytes, vec![0x48, 0x8B, 0x05, 0x00, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_mov_rip_rel_r8_negative() {
        // MOV R8, [RIP-16]: REX.WR(4C) + 8B + ModRM(00 000 101) + disp32(F0FFFFFF)
        let bytes = encode(X86Opcode::MovRipRel, &X86InstOperands::rip_rel(R8, -16));
        assert_eq!(bytes, vec![0x4C, 0x8B, 0x05, 0xF0, 0xFF, 0xFF, 0xFF]);
    }

    // -----------------------------------------------------------------------
    // Scaled-index (SIB) memory tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_sib_scaled_encode() {
        // SIB for [RAX + RCX*4]: scale=2(4x), index=RCX(1), base=RAX(0)
        let sib = Sib::scaled(0, 1, 4);
        // scale=2(0b10), index=1(0b001), base=0(0b000) -> 10_001_000 = 0x88
        assert_eq!(sib.encode(), 0x88);
    }

    #[test]
    fn test_sib_scaled_encode_scale8() {
        // SIB for [RBX + RDX*8]: scale=3(8x), index=RDX(2), base=RBX(3)
        let sib = Sib::scaled(3, 2, 8);
        // scale=3(0b11), index=2(0b010), base=3(0b011) -> 11_010_011 = 0xD3
        assert_eq!(sib.encode(), 0xD3);
    }

    #[test]
    fn test_mov_rm_sib_rax_rbx_rcx_scale4_nodisp() {
        // MOV RAX, [RBX + RCX*4]: REX.W(48) + 8B + ModRM(00 000 100) + SIB(10 001 011)
        // reg=RAX(0), rm=100(SIB), SIB: scale=4(2), index=RCX(1), base=RBX(3)
        let bytes = encode(
            X86Opcode::MovRMSib,
            &X86InstOperands::rm_sib(RAX, RBX, RCX, 4, 0),
        );
        assert_eq!(bytes, vec![0x48, 0x8B, 0x04, 0x8B]);
    }

    #[test]
    fn test_mov_rm_sib_rax_rbx_rcx_scale4_disp8() {
        // MOV RAX, [RBX + RCX*4 + 16]: REX.W(48) + 8B + ModRM(01 000 100) + SIB + disp8
        let bytes = encode(
            X86Opcode::MovRMSib,
            &X86InstOperands::rm_sib(RAX, RBX, RCX, 4, 16),
        );
        assert_eq!(bytes, vec![0x48, 0x8B, 0x44, 0x8B, 0x10]);
    }

    #[test]
    fn test_mov_rm_sib_rax_rbx_rcx_scale8_disp32() {
        // MOV RAX, [RBX + RCX*8 + 256]: REX.W(48) + 8B + ModRM(10 000 100) + SIB + disp32
        let bytes = encode(
            X86Opcode::MovRMSib,
            &X86InstOperands::rm_sib(RAX, RBX, RCX, 8, 256),
        );
        assert_eq!(bytes, vec![0x48, 0x8B, 0x84, 0xCB, 0x00, 0x01, 0x00, 0x00]);
    }

    #[test]
    fn test_mov_rm_sib_r8_r12_r9_scale2() {
        // MOV R8, [R12 + R9*2]: REX.WRX.B(4F) + 8B + ModRM(00 000 100) + SIB
        // dst=R8(8, REX.R), base=R12(12, REX.B), index=R9(9, REX.X)
        let bytes = encode(
            X86Opcode::MovRMSib,
            &X86InstOperands::rm_sib(R8, R12, R9, 2, 0),
        );
        // REX: W=1, R=1(R8), X=1(R9), B=1(R12) -> 0x4F
        // ModRM: mod=00, reg=000(R8&7), rm=100(SIB)
        // SIB: scale=1(2x), index=001(R9&7), base=100(R12&7)
        assert_eq!(bytes, vec![0x4F, 0x8B, 0x04, 0x4C]);
    }

    #[test]
    fn test_sib_r12_index_encodes_with_rex_x() {
        // R12 (hw_enc 12) is a LEGAL SIB index: low 3 bits are 100 but REX.X=1
        // disambiguates it from the no-index sentinel (Intel SDM Table 2-5).
        // Byte expectations cross-checked against LLVM output.

        // MOV RAX, [RAX + R12*8]: REX(W=1,X=1)=4A + 8B + ModRM(00 000 100) + SIB(11 100 000)
        let bytes = encode(
            X86Opcode::MovRMSib,
            &X86InstOperands::rm_sib(RAX, RAX, R12, 8, 0),
        );
        assert_eq!(bytes, vec![0x4A, 0x8B, 0x04, 0xE0]);

        // MOV [RAX + R12*8], RAX: REX(W=1,X=1)=4A + 89 + ModRM + SIB
        let bytes = encode(
            X86Opcode::MovMRSib,
            &X86InstOperands::rm_sib(RAX, RAX, R12, 8, 0),
        );
        assert_eq!(bytes, vec![0x4A, 0x89, 0x04, 0xE0]);

        // LEA RAX, [RAX + R12*8]: REX(W=1,X=1)=4A + 8D + ModRM + SIB
        let bytes = encode(
            X86Opcode::LeaSib,
            &X86InstOperands::rm_sib(RAX, RAX, R12, 8, 0),
        );
        assert_eq!(bytes, vec![0x4A, 0x8D, 0x04, 0xE0]);

        // MOV RAX, [R12 + R12*1]: REX(W=1,X=1,B=1)=4B + 8B + ModRM + SIB(00 100 100)
        let bytes = encode(
            X86Opcode::MovRMSib,
            &X86InstOperands::rm_sib(RAX, R12, R12, 1, 0),
        );
        assert_eq!(bytes, vec![0x4B, 0x8B, 0x04, 0x24]);
    }

    #[test]
    fn test_mov_mr_sib_store() {
        // MOV [RBX + RCX*4], RAX: REX.W(48) + 89 + ModRM(00 000 100) + SIB
        let bytes = encode(
            X86Opcode::MovMRSib,
            &X86InstOperands {
                dst: Some(RAX), // src register stored in dst field for stores
                base: Some(RBX),
                index: Some(RCX),
                scale: 4,
                disp: 0,
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0x48, 0x89, 0x04, 0x8B]);
    }

    /// 8-bit SIB store/load bytes, cross-checked instruction-by-instruction
    /// against the SYSTEM ASSEMBLER (`clang -c` + `llvm-objdump`) rather than
    /// against my own reading of the manual.
    ///
    /// ⚑ Cases 2 and 6 are the reason `low_byte_reg_needs_rex` exists and are
    /// the whole point of this test: `%sil` assembles to `40 88 34 10` — a REX
    /// byte with EVERY FIELD ZERO. Without it the same ModRM reg value 6 names
    /// `%dh`, so dropping the "useless" prefix would silently store the WRONG
    /// REGISTER. A negative control below pins that.
    #[test]
    fn test_mov_8bit_sib_matches_assembler_bytes() {
        let st = |src, base, index, scale, disp| {
            encode(
                X86Opcode::MovMR8Sib,
                &X86InstOperands {
                    dst: Some(src), // stores keep the value register in `dst`
                    base: Some(base),
                    index: Some(index),
                    scale,
                    disp,
                    ..X86InstOperands::none()
                },
            )
        };
        let ld = |dst, base, index, scale, disp| {
            encode(
                X86Opcode::MovRM8Sib,
                &X86InstOperands {
                    dst: Some(dst),
                    base: Some(base),
                    index: Some(index),
                    scale,
                    disp,
                    ..X86InstOperands::none()
                },
            )
        };

        // movb %cl, -1064(%rbp,%rdx)   -> 88 8c 15 d8 fb ff ff   (no REX)
        assert_eq!(
            st(CL, RBP, RDX, 1, -1064),
            vec![0x88, 0x8C, 0x15, 0xD8, 0xFB, 0xFF, 0xFF]
        );
        // movb %sil, (%rax,%rdx)       -> 40 88 34 10            (FORCED empty REX)
        assert_eq!(st(SIL, RAX, RDX, 1, 0), vec![0x40, 0x88, 0x34, 0x10]);
        // movb %r10b, -1064(%rbp,%rcx) -> 44 88 94 0d d8 fb ff ff (REX.R)
        assert_eq!(
            st(R10B, RBP, RCX, 1, -1064),
            vec![0x44, 0x88, 0x94, 0x0D, 0xD8, 0xFB, 0xFF, 0xFF]
        );
        // movb %al, 16(%r9,%r11,4)     -> 43 88 44 99 10          (REX.X|REX.B)
        assert_eq!(st(AL, R9, R11, 4, 16), vec![0x43, 0x88, 0x44, 0x99, 0x10]);

        // movb (%rax,%rdx), %cl        -> 8a 0c 10
        assert_eq!(ld(CL, RAX, RDX, 1, 0), vec![0x8A, 0x0C, 0x10]);
        // movb (%rax,%rdx), %sil       -> 40 8a 34 10             (FORCED empty REX)
        assert_eq!(ld(SIL, RAX, RDX, 1, 0), vec![0x40, 0x8A, 0x34, 0x10]);
        // movb -1064(%rbp,%rcx), %r10b -> 44 8a 94 0d d8 fb ff ff
        assert_eq!(
            ld(R10B, RBP, RCX, 1, -1064),
            vec![0x44, 0x8A, 0x94, 0x0D, 0xD8, 0xFB, 0xFF, 0xFF]
        );
        // movb 16(%r9,%r11,4), %al     -> 43 8a 44 99 10
        assert_eq!(ld(AL, R9, R11, 4, 16), vec![0x43, 0x8A, 0x44, 0x99, 0x10]);
    }

    /// Negative controls: the 8-bit SIB forms must not collapse into their
    /// 32/64-bit siblings, and the forced REX must actually be emitted.
    #[test]
    fn test_mov_8bit_sib_is_not_the_wider_sibling() {
        let ops = X86InstOperands {
            dst: Some(RAX),
            base: Some(RBX),
            index: Some(RCX),
            scale: 4,
            disp: 0,
            ..X86InstOperands::none()
        };
        let b8 = encode(X86Opcode::MovMR8Sib, &ops);
        let b32 = encode(X86Opcode::MovMR32Sib, &ops);
        let b64 = encode(X86Opcode::MovMRSib, &ops);
        // 88 (r8) vs 89 (r32/r64), and no REX.W on the 8-bit form.
        assert_eq!(b8, vec![0x88, 0x04, 0x8B]);
        assert_ne!(b8, b32);
        assert_ne!(b8, b64);
        assert_eq!(b64, vec![0x48, 0x89, 0x04, 0x8B]);

        // The forced REX is a real byte, not a no-op: SIL differs from CL by
        // exactly the 0x40 prefix, and MUST NOT encode identically to DH.
        let sil = encode(
            X86Opcode::MovMR8Sib,
            &X86InstOperands {
                dst: Some(SIL),
                ..ops.clone()
            },
        );
        assert_eq!(sil.first(), Some(&0x40));
        assert_eq!(sil.len(), b8.len() + 1);
    }

    #[test]
    fn test_mov_mr_sib_store_disp8() {
        // MOV [RBX + RDX*8 + 32], RCX: REX.W(48) + 89 + ModRM(01 001 100) + SIB + disp8
        let bytes = encode(
            X86Opcode::MovMRSib,
            &X86InstOperands {
                dst: Some(RCX),
                base: Some(RBX),
                index: Some(RDX),
                scale: 8,
                disp: 32,
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0x48, 0x89, 0x4C, 0xD3, 0x20]);
    }

    // -----------------------------------------------------------------------
    // SSE conversion instruction tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_cvtsi2sd_xmm0_rax() {
        // CVTSI2SD XMM0, RAX: F2 REX.W(48) 0F 2A + ModRM(11 000 000)
        let bytes = encode(X86Opcode::Cvtsi2sd, &X86InstOperands::rr(XMM0, RAX));
        assert_eq!(bytes, vec![0xF2, 0x48, 0x0F, 0x2A, 0xC0]);
    }

    #[test]
    fn test_cvtsi2sd_xmm8_r15() {
        // CVTSI2SD XMM8, R15: F2 REX.WRB(4D) 0F 2A + ModRM(11 000 111)
        let bytes = encode(X86Opcode::Cvtsi2sd, &X86InstOperands::rr(XMM8, R15));
        assert_eq!(bytes, vec![0xF2, 0x4D, 0x0F, 0x2A, 0xC7]);
    }

    #[test]
    fn test_cvtsd2si_rax_xmm0() {
        // CVTSD2SI RAX, XMM0: F2 REX.W(48) 0F 2D + ModRM(11 000 000)
        let bytes = encode(X86Opcode::Cvtsd2si, &X86InstOperands::rr(RAX, XMM0));
        assert_eq!(bytes, vec![0xF2, 0x48, 0x0F, 0x2D, 0xC0]);
    }

    #[test]
    fn test_cvtsd2si_r8_xmm15() {
        // CVTSD2SI R8, XMM15: F2 REX.WRB(4D) 0F 2D + ModRM(11 000 111)
        let bytes = encode(X86Opcode::Cvtsd2si, &X86InstOperands::rr(R8, XMM15));
        assert_eq!(bytes, vec![0xF2, 0x4D, 0x0F, 0x2D, 0xC7]);
    }

    #[test]
    fn test_cvttsd2si_rax_xmm0() {
        // CVTTSD2SI RAX, XMM0: F2 REX.W(48) 0F 2C + ModRM(11 000 000)
        let bytes = encode(X86Opcode::Cvttsd2si, &X86InstOperands::rr(RAX, XMM0));
        assert_eq!(bytes, vec![0xF2, 0x48, 0x0F, 0x2C, 0xC0]);
    }

    #[test]
    fn test_cvttsd2si_r8_xmm15() {
        // CVTTSD2SI R8, XMM15: F2 REX.WRB(4D) 0F 2C + ModRM(11 000 111)
        let bytes = encode(X86Opcode::Cvttsd2si, &X86InstOperands::rr(R8, XMM15));
        assert_eq!(bytes, vec![0xF2, 0x4D, 0x0F, 0x2C, 0xC7]);
    }

    #[test]
    fn test_cvtsi2ss_xmm0_rax() {
        // CVTSI2SS XMM0, RAX: F3 REX.W(48) 0F 2A + ModRM(11 000 000)
        let bytes = encode(X86Opcode::Cvtsi2ss, &X86InstOperands::rr(XMM0, RAX));
        assert_eq!(bytes, vec![0xF3, 0x48, 0x0F, 0x2A, 0xC0]);
    }

    #[test]
    fn test_cvtss2si_rax_xmm0() {
        // CVTSS2SI RAX, XMM0: F3 REX.W(48) 0F 2D + ModRM(11 000 000)
        let bytes = encode(X86Opcode::Cvtss2si, &X86InstOperands::rr(RAX, XMM0));
        assert_eq!(bytes, vec![0xF3, 0x48, 0x0F, 0x2D, 0xC0]);
    }

    #[test]
    fn test_cvttss2si_rax_xmm0() {
        // CVTTSS2SI RAX, XMM0: F3 REX.W(48) 0F 2C + ModRM(11 000 000)
        let bytes = encode(X86Opcode::Cvttss2si, &X86InstOperands::rr(RAX, XMM0));
        assert_eq!(bytes, vec![0xF3, 0x48, 0x0F, 0x2C, 0xC0]);
    }

    #[test]
    fn test_cvttss2si_r8_xmm15() {
        // CVTTSS2SI R8, XMM15: F3 REX.WRB(4D) 0F 2C + ModRM(11 000 111)
        let bytes = encode(X86Opcode::Cvttss2si, &X86InstOperands::rr(R8, XMM15));
        assert_eq!(bytes, vec![0xF3, 0x4D, 0x0F, 0x2C, 0xC7]);
    }

    #[test]
    fn test_cvtsd2ss_xmm0_xmm1() {
        // CVTSD2SS XMM0, XMM1: F2 0F 5A + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Cvtsd2ss, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0xF2, 0x0F, 0x5A, 0xC1]);
    }

    #[test]
    fn test_cvtss2sd_xmm0_xmm1() {
        // CVTSS2SD XMM0, XMM1: F3 0F 5A + ModRM(11 000 001)
        let bytes = encode(X86Opcode::Cvtss2sd, &X86InstOperands::rr(XMM0, XMM1));
        assert_eq!(bytes, vec![0xF3, 0x0F, 0x5A, 0xC1]);
    }

    #[test]
    fn test_cvtsd2ss_xmm8_xmm15() {
        // CVTSD2SS XMM8, XMM15: F2 REX.RB(45) 0F 5A + ModRM(11 000 111)
        let bytes = encode(X86Opcode::Cvtsd2ss, &X86InstOperands::rr(XMM8, XMM15));
        assert_eq!(bytes, vec![0xF2, 0x45, 0x0F, 0x5A, 0xC7]);
    }

    #[test]
    fn test_cvtss2sd_xmm8_xmm15() {
        // CVTSS2SD XMM8, XMM15: F3 REX.RB(45) 0F 5A + ModRM(11 000 111)
        let bytes = encode(X86Opcode::Cvtss2sd, &X86InstOperands::rr(XMM8, XMM15));
        assert_eq!(bytes, vec![0xF3, 0x45, 0x0F, 0x5A, 0xC7]);
    }

    // -----------------------------------------------------------------------
    // New instruction size tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_new_instruction_sizes_v2() {
        let mut enc = X86Encoder::new();

        // LEA RIP: REX.W(1) + 8D(1) + ModRM(1) + disp32(4) = 7 bytes
        let n = enc
            .encode_instruction(X86Opcode::LeaRip, &X86InstOperands::rip_rel(RAX, 0))
            .unwrap();
        assert_eq!(n, 7);

        // CVTSI2SD: F2(1) + REX.W(1) + 0F(1) + 2A(1) + ModRM(1) = 5 bytes
        let n = enc
            .encode_instruction(X86Opcode::Cvtsi2sd, &X86InstOperands::rr(XMM0, RAX))
            .unwrap();
        assert_eq!(n, 5);

        // CVTSD2SI: F2(1) + REX.W(1) + 0F(1) + 2D(1) + ModRM(1) = 5 bytes
        let n = enc
            .encode_instruction(X86Opcode::Cvtsd2si, &X86InstOperands::rr(RAX, XMM0))
            .unwrap();
        assert_eq!(n, 5);

        // CVTTSD2SI: F2(1) + REX.W(1) + 0F(1) + 2C(1) + ModRM(1) = 5 bytes
        let n = enc
            .encode_instruction(X86Opcode::Cvttsd2si, &X86InstOperands::rr(RAX, XMM0))
            .unwrap();
        assert_eq!(n, 5);

        // CVTTSS2SI: F3(1) + REX.W(1) + 0F(1) + 2C(1) + ModRM(1) = 5 bytes
        let n = enc
            .encode_instruction(X86Opcode::Cvttss2si, &X86InstOperands::rr(RAX, XMM0))
            .unwrap();
        assert_eq!(n, 5);

        // CVTSD2SS: F2(1) + 0F(1) + 5A(1) + ModRM(1) = 4 bytes
        let n = enc
            .encode_instruction(X86Opcode::Cvtsd2ss, &X86InstOperands::rr(XMM0, XMM1))
            .unwrap();
        assert_eq!(n, 4);

        // CVTSS2SD: F3(1) + 0F(1) + 5A(1) + ModRM(1) = 4 bytes
        let n = enc
            .encode_instruction(X86Opcode::Cvtss2sd, &X86InstOperands::rr(XMM0, XMM1))
            .unwrap();
        assert_eq!(n, 4);

        // MovRMSib [base + index*scale]: REX.W(1) + 8B(1) + ModRM(1) + SIB(1) = 4 bytes
        let n = enc
            .encode_instruction(
                X86Opcode::MovRMSib,
                &X86InstOperands::rm_sib(RAX, RBX, RCX, 4, 0),
            )
            .unwrap();
        assert_eq!(n, 4);

        // MovRMSib [base + index*scale + disp8]: 5 bytes
        let n = enc
            .encode_instruction(
                X86Opcode::MovRMSib,
                &X86InstOperands::rm_sib(RAX, RBX, RCX, 4, 16),
            )
            .unwrap();
        assert_eq!(n, 5);

        // MovRMSib [base + index*scale + disp32]: 8 bytes
        let n = enc
            .encode_instruction(
                X86Opcode::MovRMSib,
                &X86InstOperands::rm_sib(RAX, RBX, RCX, 8, 256),
            )
            .unwrap();
        assert_eq!(n, 8);
    }

    // -----------------------------------------------------------------------
    // SIB error handling
    // -----------------------------------------------------------------------

    #[test]
    fn test_mov_rm_sib_missing_base_error() {
        let mut enc = X86Encoder::new();
        let ops = X86InstOperands {
            dst: Some(RAX),
            index: Some(RCX),
            scale: 4,
            ..X86InstOperands::none()
        };
        let result = enc.encode_instruction(X86Opcode::MovRMSib, &ops);
        assert!(result.is_err());
    }

    #[test]
    fn test_mov_rm_sib_missing_index_error() {
        let mut enc = X86Encoder::new();
        let ops = X86InstOperands {
            dst: Some(RAX),
            base: Some(RBX),
            scale: 4,
            ..X86InstOperands::none()
        };
        let result = enc.encode_instruction(X86Opcode::MovRMSib, &ops);
        assert!(result.is_err());
    }

    fn expect_invalid_sib_operand(opcode: X86Opcode, ops: X86InstOperands, expected: &str) {
        let mut enc = X86Encoder::new();
        let err = enc.encode_instruction(opcode, &ops).unwrap_err();
        let msg = err.to_string();
        assert!(
            msg.contains(expected),
            "expected {opcode:?} error to contain {expected:?}, got {msg:?}"
        );
        assert!(
            enc.finish().is_empty(),
            "SIB validation must reject before emitting bytes"
        );
    }

    #[test]
    fn test_sib_rejects_invalid_scale_before_emitting_bytes() {
        for opcode in [X86Opcode::MovRMSib, X86Opcode::MovMRSib, X86Opcode::LeaSib] {
            expect_invalid_sib_operand(
                opcode,
                X86InstOperands::rm_sib(RAX, RBX, RCX, 3, 0),
                "invalid SIB scale",
            );
        }
    }

    #[test]
    fn test_sib_rejects_no_index_aliases_before_emitting_bytes() {
        // Only RSP (hw_enc 4) is the true no-index sentinel; R12 is a legal
        // SIB index via REX.X=1 and must NOT be rejected.
        for opcode in [X86Opcode::MovRMSib, X86Opcode::MovMRSib, X86Opcode::LeaSib] {
            expect_invalid_sib_operand(
                opcode,
                X86InstOperands::rm_sib(RAX, RBX, RSP, 4, 0),
                "no-index sentinel",
            );
        }
    }

    #[test]
    fn test_lea_rip_missing_dst_error() {
        let mut enc = X86Encoder::new();
        let result = enc.encode_instruction(X86Opcode::LeaRip, &X86InstOperands::none());
        assert!(result.is_err());
    }

    // ===================================================================
    // Cross-reference encoding verification
    //
    // These tests systematically verify byte-level encoding against the
    // Intel 64 and IA-32 Architectures SDM Volume 2 (Instruction Set
    // Reference). Each test cites the relevant SDM instruction family.
    // ===================================================================

    // -------------------------------------------------------------------
    // 1. MOV reg,reg for all 16 GPRs -- verify REX bits
    // Intel SDM Vol 2, MOV instruction: opcode 89 /r (MOV r/m64, r64)
    // REX prefix 0100_WRXB: W=1 (64-bit), R=src>>3, B=dst>>3
    // ModRM = 11_src[2:0]_dst[2:0]
    // -------------------------------------------------------------------

    #[test]
    fn test_mov_all_16_gprs() {
        // Pairs: (dst, src, expected_bytes)
        // Format: REX.W prefix + 0x89 + ModRM(11, src[2:0], dst[2:0])
        let cases: &[(X86PReg, X86PReg, &[u8])] = &[
            // Legacy-to-legacy (no extended regs): REX.W = 0x48
            (RAX, RAX, &[0x48, 0x89, 0xC0]), // MOV RAX,RAX: ModRM=11_000_000=C0
            (RCX, RAX, &[0x48, 0x89, 0xC1]), // MOV RCX,RAX: ModRM=11_000_001=C1
            (RDX, RBX, &[0x48, 0x89, 0xDA]), // MOV RDX,RBX: ModRM=11_011_010=DA
            (RSP, RBP, &[0x48, 0x89, 0xEC]), // MOV RSP,RBP: ModRM=11_101_100=EC
            (RSI, RDI, &[0x48, 0x89, 0xFE]), // MOV RSI,RDI: ModRM=11_111_110=FE
            (RDI, RSI, &[0x48, 0x89, 0xF7]), // MOV RDI,RSI: ModRM=11_110_111=F7
            // Extended dst only: REX.WB = 0x49 (W=1, B=1)
            (R8, RAX, &[0x49, 0x89, 0xC0]), // MOV R8,RAX:  ModRM=11_000_000=C0
            (R12, RCX, &[0x49, 0x89, 0xCC]), // MOV R12,RCX: ModRM=11_001_100=CC
            (R15, RDI, &[0x49, 0x89, 0xFF]), // MOV R15,RDI: ModRM=11_111_111=FF
            // Extended src only: REX.WR = 0x4C (W=1, R=1)
            (RAX, R8, &[0x4C, 0x89, 0xC0]), // MOV RAX,R8:  ModRM=11_000_000=C0
            (RCX, R12, &[0x4C, 0x89, 0xE1]), // MOV RCX,R12: ModRM=11_100_001=E1
            (RDI, R15, &[0x4C, 0x89, 0xFF]), // MOV RDI,R15: ModRM=11_111_111=FF
            // Both extended: REX.WRB = 0x4D (W=1, R=1, B=1)
            (R8, R9, &[0x4D, 0x89, 0xC8]), // MOV R8,R9:   ModRM=11_001_000=C8
            (R10, R11, &[0x4D, 0x89, 0xDA]), // MOV R10,R11: ModRM=11_011_010=DA
            (R14, R13, &[0x4D, 0x89, 0xEE]), // MOV R14,R13: ModRM=11_101_110=EE
            (R15, R15, &[0x4D, 0x89, 0xFF]), // MOV R15,R15: ModRM=11_111_111=FF
        ];

        for (i, (dst, src, expected)) in cases.iter().enumerate() {
            let bytes = encode(X86Opcode::MovRR, &X86InstOperands::rr(*dst, *src));
            assert_eq!(
                bytes,
                expected.to_vec(),
                "MOV case {}: dst={:?}, src={:?}",
                i,
                dst,
                src
            );
        }
    }

    // -------------------------------------------------------------------
    // 2. PUSH/POP for all 16 GPRs
    // Intel SDM Vol 2, PUSH: opcode 50+rd (no REX.W needed for PUSH r64)
    //   R8-R15 need REX.B prefix (0x41) to extend the opcode register field
    // Intel SDM Vol 2, POP:  opcode 58+rd (same REX.B rule)
    // -------------------------------------------------------------------

    #[test]
    fn test_push_pop_all_16_gprs() {
        // PUSH register tests: (reg, expected_bytes)
        let push_cases: &[(X86PReg, &[u8])] = &[
            (RAX, &[0x50]),       // 50+0
            (RCX, &[0x51]),       // 50+1
            (RDX, &[0x52]),       // 50+2
            (RBX, &[0x53]),       // 50+3
            (RSP, &[0x54]),       // 50+4
            (RBP, &[0x55]),       // 50+5
            (RSI, &[0x56]),       // 50+6
            (RDI, &[0x57]),       // 50+7
            (R8, &[0x41, 0x50]),  // REX.B + 50+0
            (R9, &[0x41, 0x51]),  // REX.B + 50+1
            (R10, &[0x41, 0x52]), // REX.B + 50+2
            (R11, &[0x41, 0x53]), // REX.B + 50+3
            (R12, &[0x41, 0x54]), // REX.B + 50+4
            (R13, &[0x41, 0x55]), // REX.B + 50+5
            (R14, &[0x41, 0x56]), // REX.B + 50+6
            (R15, &[0x41, 0x57]), // REX.B + 50+7
        ];

        for (i, (reg, expected)) in push_cases.iter().enumerate() {
            let bytes = encode(X86Opcode::Push, &X86InstOperands::r(*reg));
            assert_eq!(bytes, expected.to_vec(), "PUSH case {}: reg={:?}", i, reg);
        }

        // POP register tests: (reg, expected_bytes)
        let pop_cases: &[(X86PReg, &[u8])] = &[
            (RAX, &[0x58]),       // 58+0
            (RCX, &[0x59]),       // 58+1
            (RDX, &[0x5A]),       // 58+2
            (RBX, &[0x5B]),       // 58+3
            (RSP, &[0x5C]),       // 58+4
            (RBP, &[0x5D]),       // 58+5
            (RSI, &[0x5E]),       // 58+6
            (RDI, &[0x5F]),       // 58+7
            (R8, &[0x41, 0x58]),  // REX.B + 58+0
            (R9, &[0x41, 0x59]),  // REX.B + 58+1
            (R10, &[0x41, 0x5A]), // REX.B + 58+2
            (R11, &[0x41, 0x5B]), // REX.B + 58+3
            (R12, &[0x41, 0x5C]), // REX.B + 58+4
            (R13, &[0x41, 0x5D]), // REX.B + 58+5
            (R14, &[0x41, 0x5E]), // REX.B + 58+6
            (R15, &[0x41, 0x5F]), // REX.B + 58+7
        ];

        for (i, (reg, expected)) in pop_cases.iter().enumerate() {
            let bytes = encode(X86Opcode::Pop, &X86InstOperands::r(*reg));
            assert_eq!(bytes, expected.to_vec(), "POP case {}: reg={:?}", i, reg);
        }
    }

    // -------------------------------------------------------------------
    // 3. Negative displacement: MOV RAX, [RBX-8]
    // Intel SDM Vol 2, MOV: opcode 8B /r (MOV r64, r/m64)
    // disp=-8 fits in signed byte (0xF8), so mod=01 (disp8)
    // -------------------------------------------------------------------

    #[test]
    fn test_negative_displacement() {
        // MOV RAX, [RBX-8]: REX.W(48) + 8B + ModRM(01_000_011=43) + disp8(F8)
        // -8 as signed byte = 0xF8
        let bytes = encode(X86Opcode::MovRM, &X86InstOperands::rm(RAX, RBX, -8));
        assert_eq!(bytes, vec![0x48, 0x8B, 0x43, 0xF8]);

        // MOV RCX, [RDX-1]: REX.W(48) + 8B + ModRM(01_001_010=4A) + disp8(FF)
        let bytes = encode(X86Opcode::MovRM, &X86InstOperands::rm(RCX, RDX, -1));
        assert_eq!(bytes, vec![0x48, 0x8B, 0x4A, 0xFF]);

        // MOV RDI, [RSI-128]: disp=-128 still fits in disp8 (0x80)
        // REX.W(48) + 8B + ModRM(01_111_110=7E) + disp8(80)
        let bytes = encode(X86Opcode::MovRM, &X86InstOperands::rm(RDI, RSI, -128));
        assert_eq!(bytes, vec![0x48, 0x8B, 0x7E, 0x80]);

        // MOV RAX, [RBX-129]: disp=-129 does NOT fit in disp8, needs disp32
        // REX.W(48) + 8B + ModRM(10_000_011=83) + disp32(FFFFFF7F in LE)
        let bytes = encode(X86Opcode::MovRM, &X86InstOperands::rm(RAX, RBX, -129));
        assert_eq!(bytes, vec![0x48, 0x8B, 0x83, 0x7F, 0xFF, 0xFF, 0xFF]);
    }

    // -------------------------------------------------------------------
    // 4. RSP and RBP base addressing special cases
    // Intel SDM Vol 2, Table 2-2 (ModRM with SIB):
    //   rm=100 (RSP/R12) always emits SIB byte
    //   rm=101 (RBP/R13) with mod=00 is RIP-relative, so disp=0 needs mod=01+disp8(00)
    // -------------------------------------------------------------------

    #[test]
    fn test_rsp_rbp_addressing() {
        // MOV RAX, [RSP+0]: needs SIB byte (base=RSP, no index)
        // REX.W(48) + 8B + ModRM(00_000_100=04) + SIB(00_100_100=24)
        let bytes = encode(X86Opcode::MovRM, &X86InstOperands::rm(RAX, RSP, 0));
        assert_eq!(bytes, vec![0x48, 0x8B, 0x04, 0x24]);

        // MOV RAX, [RSP+8]: SIB + disp8
        // REX.W(48) + 8B + ModRM(01_000_100=44) + SIB(00_100_100=24) + disp8(08)
        let bytes = encode(X86Opcode::MovRM, &X86InstOperands::rm(RAX, RSP, 8));
        assert_eq!(bytes, vec![0x48, 0x8B, 0x44, 0x24, 0x08]);

        // MOV RAX, [RSP+256]: SIB + disp32
        // REX.W(48) + 8B + ModRM(10_000_100=84) + SIB(00_100_100=24) + disp32
        let bytes = encode(X86Opcode::MovRM, &X86InstOperands::rm(RAX, RSP, 256));
        assert_eq!(bytes, vec![0x48, 0x8B, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00]);

        // MOV RAX, [RBP+0]: RBP base with no displacement needs disp8=0
        // REX.W(48) + 8B + ModRM(01_000_101=45) + disp8(00)
        let bytes = encode(X86Opcode::MovRM, &X86InstOperands::rm(RAX, RBP, 0));
        assert_eq!(bytes, vec![0x48, 0x8B, 0x45, 0x00]);

        // MOV RAX, [RBP+16]: normal disp8
        // REX.W(48) + 8B + ModRM(01_000_101=45) + disp8(10)
        let bytes = encode(X86Opcode::MovRM, &X86InstOperands::rm(RAX, RBP, 16));
        assert_eq!(bytes, vec![0x48, 0x8B, 0x45, 0x10]);

        // MOV R8, [R12+0]: R12 (hw=4) behaves like RSP -- needs SIB
        // REX.WRB(4D) + 8B + ModRM(00_000_100=04) + SIB(00_100_100=24)
        let bytes = encode(X86Opcode::MovRM, &X86InstOperands::rm(R8, R12, 0));
        assert_eq!(bytes, vec![0x4D, 0x8B, 0x04, 0x24]);

        // MOV R8, [R13+0]: R13 (hw=5) behaves like RBP -- needs disp8=0
        // REX.WRB(4D) + 8B + ModRM(01_000_101=45) + disp8(00)
        let bytes = encode(X86Opcode::MovRM, &X86InstOperands::rm(R8, R13, 0));
        assert_eq!(bytes, vec![0x4D, 0x8B, 0x45, 0x00]);
    }

    // -------------------------------------------------------------------
    // 5. Jcc condition codes -- verify 0F 80+cc rel32 encoding
    // Intel SDM Vol 2, Jcc: 0F 80+cc cd (near jump with 32-bit displacement)
    // cc values: O=0, NO=1, B=2, AE=3, E=4, NE=5, BE=6, A=7,
    //            S=8, NS=9, P=A, NP=B, L=C, GE=D, LE=E, G=F
    // -------------------------------------------------------------------

    #[test]
    fn test_all_jcc_condition_codes() {
        // Each Jcc with disp=0 should produce: 0F (80+cc) 00 00 00 00
        let cases: &[(X86CondCode, u8)] = &[
            (X86CondCode::O, 0x80),
            (X86CondCode::NO, 0x81),
            (X86CondCode::B, 0x82),
            (X86CondCode::AE, 0x83),
            (X86CondCode::E, 0x84),
            (X86CondCode::NE, 0x85),
            (X86CondCode::BE, 0x86),
            (X86CondCode::A, 0x87),
            (X86CondCode::S, 0x88),
            (X86CondCode::NS, 0x89),
            (X86CondCode::P, 0x8A),
            (X86CondCode::NP, 0x8B),
            (X86CondCode::L, 0x8C),
            (X86CondCode::GE, 0x8D),
            (X86CondCode::LE, 0x8E),
            (X86CondCode::G, 0x8F),
        ];

        for (cc, expected_opcode2) in cases {
            let bytes = encode(X86Opcode::Jcc, &X86InstOperands::jcc(*cc, 0));
            assert_eq!(bytes.len(), 6, "Jcc {:?} should be 6 bytes", cc);
            assert_eq!(bytes[0], 0x0F, "Jcc {:?} first byte", cc);
            assert_eq!(bytes[1], *expected_opcode2, "Jcc {:?} second byte", cc);
            // disp32=0 -> 00 00 00 00
            assert_eq!(&bytes[2..], &[0x00, 0x00, 0x00, 0x00], "Jcc {:?} disp", cc);
        }

        // Verify a nonzero displacement: JNE +100
        // 0F 85 64 00 00 00  (100 = 0x64)
        let bytes = encode(X86Opcode::Jcc, &X86InstOperands::jcc(X86CondCode::NE, 100));
        assert_eq!(bytes, vec![0x0F, 0x85, 0x64, 0x00, 0x00, 0x00]);

        // Verify negative displacement: JL -16
        // 0F 8C F0 FF FF FF  (-16 as i32 = 0xFFFF_FFF0)
        let bytes = encode(X86Opcode::Jcc, &X86InstOperands::jcc(X86CondCode::L, -16));
        assert_eq!(bytes, vec![0x0F, 0x8C, 0xF0, 0xFF, 0xFF, 0xFF]);
    }

    // -------------------------------------------------------------------
    // 6. XOR reg,reg zero idiom
    // Intel SDM Vol 2, XOR: opcode 31 /r (XOR r/m64, r64)
    // REX.W(48) + 31 + ModRM(11, src[2:0], dst[2:0])
    // -------------------------------------------------------------------

    #[test]
    fn test_xor_zero_idiom() {
        // XOR RAX, RAX: REX.W(48) + 31 + ModRM(11_000_000=C0)
        let bytes = encode(X86Opcode::XorRR, &X86InstOperands::rr(RAX, RAX));
        assert_eq!(bytes, vec![0x48, 0x31, 0xC0]);

        // XOR RCX, RCX: REX.W(48) + 31 + ModRM(11_001_001=C9)
        let bytes = encode(X86Opcode::XorRR, &X86InstOperands::rr(RCX, RCX));
        assert_eq!(bytes, vec![0x48, 0x31, 0xC9]);

        // XOR RDX, RDX: REX.W(48) + 31 + ModRM(11_010_010=D2)
        let bytes = encode(X86Opcode::XorRR, &X86InstOperands::rr(RDX, RDX));
        assert_eq!(bytes, vec![0x48, 0x31, 0xD2]);

        // XOR R8, R8: REX.WRB(4D) + 31 + ModRM(11_000_000=C0)
        let bytes = encode(X86Opcode::XorRR, &X86InstOperands::rr(R8, R8));
        assert_eq!(bytes, vec![0x4D, 0x31, 0xC0]);

        // XOR R15, R15: REX.WRB(4D) + 31 + ModRM(11_111_111=FF)
        let bytes = encode(X86Opcode::XorRR, &X86InstOperands::rr(R15, R15));
        assert_eq!(bytes, vec![0x4D, 0x31, 0xFF]);

        // XOR R10, R10: REX.WRB(4D) + 31 + ModRM(11_010_010=D2)
        let bytes = encode(X86Opcode::XorRR, &X86InstOperands::rr(R10, R10));
        assert_eq!(bytes, vec![0x4D, 0x31, 0xD2]);
    }

    // -------------------------------------------------------------------
    // 7. SUB RSP, imm -- common prologue stack frame allocation
    // Intel SDM Vol 2, SUB: opcode 83 /5 ib or 81 /5 id.
    // The encoder uses the shorter sign-extended imm8 form when possible.
    // RSP hw_enc=4, /5 means reg field=5 in ModRM
    // -------------------------------------------------------------------

    #[test]
    fn test_sub_rsp_imm_uses_shortest_sign_extended_encoding() {
        // SUB RSP, 32: REX.W(48) + 83 + ModRM(11_101_100=EC) + imm8(20)
        let bytes = encode(X86Opcode::SubRI, &X86InstOperands::ri(RSP, 32));
        assert_eq!(bytes, vec![0x48, 0x83, 0xEC, 0x20]);

        // SUB RSP, 128: REX.W(48) + 81 + EC + imm32(80 00 00 00)
        let bytes = encode(X86Opcode::SubRI, &X86InstOperands::ri(RSP, 128));
        assert_eq!(bytes, vec![0x48, 0x81, 0xEC, 0x80, 0x00, 0x00, 0x00]);

        // ADD RSP, 32 (epilogue counterpart):
        // REX.W(48) + 83 + ModRM(11_000_100=C4) + imm8(20)
        // /0 means reg field=0 in ModRM for ADD
        let bytes = encode(X86Opcode::AddRI, &X86InstOperands::ri(RSP, 32));
        assert_eq!(bytes, vec![0x48, 0x83, 0xC4, 0x20]);
    }

    // -------------------------------------------------------------------
    // 8. Complete prologue/epilogue sequence
    // Verifies concatenated bytes for a standard System V AMD64 ABI
    // function frame setup and teardown.
    //
    //   PUSH RBP           ; 55
    //   MOV RBP, RSP       ; 48 89 E5 (REX.W + 89 + ModRM 11_100_101)
    //   SUB RSP, 32        ; 48 83 EC 20
    //   ADD RSP, 32        ; 48 83 C4 20
    //   POP RBP            ; 5D
    //   RET                ; C3
    //
    // Total: 1 + 3 + 4 + 4 + 1 + 1 = 14 bytes
    // -------------------------------------------------------------------

    #[test]
    fn test_prologue_epilogue_sequence() {
        let mut enc = X86Encoder::new();

        // PUSH RBP
        enc.encode_instruction(X86Opcode::Push, &X86InstOperands::r(RBP))
            .unwrap();
        // MOV RBP, RSP
        enc.encode_instruction(X86Opcode::MovRR, &X86InstOperands::rr(RBP, RSP))
            .unwrap();
        // SUB RSP, 32
        enc.encode_instruction(X86Opcode::SubRI, &X86InstOperands::ri(RSP, 32))
            .unwrap();
        // ADD RSP, 32
        enc.encode_instruction(X86Opcode::AddRI, &X86InstOperands::ri(RSP, 32))
            .unwrap();
        // POP RBP
        enc.encode_instruction(X86Opcode::Pop, &X86InstOperands::r(RBP))
            .unwrap();
        // RET
        enc.encode_instruction(X86Opcode::Ret, &X86InstOperands::none())
            .unwrap();

        let bytes = enc.finish();

        let expected: Vec<u8> = vec![
            0x55, // PUSH RBP
            0x48, 0x89, 0xE5, // MOV RBP, RSP
            0x48, 0x83, 0xEC, 0x20, // SUB RSP, 32
            0x48, 0x83, 0xC4, 0x20, // ADD RSP, 32
            0x5D, // POP RBP
            0xC3, // RET
        ];

        assert_eq!(bytes.len(), 14, "prologue/epilogue should be 14 bytes");
        assert_eq!(bytes, expected);
    }

    // -----------------------------------------------------------------------
    // MovzxW tests (MOVZX r64, r/m16 -- 0F B7)
    // -----------------------------------------------------------------------

    #[test]
    fn test_movzxw_rax_cx() {
        // MOVZX RAX, CX: REX.W(48) + 0F B7 + ModRM(11 000 001)
        let bytes = encode(X86Opcode::MovzxW, &X86InstOperands::rr(RAX, CX));
        assert_eq!(bytes, vec![0x48, 0x0F, 0xB7, 0xC1]);
    }

    #[test]
    fn test_movzxw_r8_ax() {
        // MOVZX R8, AX: REX.WR(4C) + 0F B7 + ModRM(11 000 000)
        let bytes = encode(X86Opcode::MovzxW, &X86InstOperands::rr(R8, AX));
        assert_eq!(bytes, vec![0x4C, 0x0F, 0xB7, 0xC0]);
    }

    // -----------------------------------------------------------------------
    // MovsxB tests (MOVSX r64, r/m8 -- 0F BE)
    // -----------------------------------------------------------------------

    #[test]
    fn test_movsxb_rax_cl() {
        // MOVSX RAX, CL: REX.W(48) + 0F BE + ModRM(11 000 001)
        let bytes = encode(X86Opcode::MovsxB, &X86InstOperands::rr(RAX, CL));
        assert_eq!(bytes, vec![0x48, 0x0F, 0xBE, 0xC1]);
    }

    #[test]
    fn test_movsxb_r8_al() {
        // MOVSX R8, AL: REX.WR(4C) + 0F BE + ModRM(11 000 000)
        let bytes = encode(X86Opcode::MovsxB, &X86InstOperands::rr(R8, AL));
        assert_eq!(bytes, vec![0x4C, 0x0F, 0xBE, 0xC0]);
    }

    // -----------------------------------------------------------------------
    // MovsxW tests (MOVSX r64, r/m16 -- 0F BF)
    // -----------------------------------------------------------------------

    #[test]
    fn test_movsxw_rax_cx() {
        // MOVSX RAX, CX: REX.W(48) + 0F BF + ModRM(11 000 001)
        let bytes = encode(X86Opcode::MovsxW, &X86InstOperands::rr(RAX, CX));
        assert_eq!(bytes, vec![0x48, 0x0F, 0xBF, 0xC1]);
    }

    #[test]
    fn test_movsxw_r15_r14w() {
        // MOVSX R15, R14W: REX.WRB(4D) + 0F BF + ModRM(11 111 110)
        let bytes = encode(X86Opcode::MovsxW, &X86InstOperands::rr(R15, R14W));
        assert_eq!(bytes, vec![0x4D, 0x0F, 0xBF, 0xFE]);
    }

    // -----------------------------------------------------------------------
    // LeaSib tests (LEA r64, [base + index*scale + disp])
    // -----------------------------------------------------------------------

    #[test]
    fn test_lea_sib_rax_rbx_rcx_scale4() {
        // LEA RAX, [RBX + RCX*4]: REX.W(48) + 8D + ModRM(00 000 100) + SIB(10 001 011)
        let bytes = encode(
            X86Opcode::LeaSib,
            &X86InstOperands::rm_sib(RAX, RBX, RCX, 4, 0),
        );
        assert_eq!(bytes, vec![0x48, 0x8D, 0x04, 0x8B]);
    }

    #[test]
    fn test_lea_sib_rax_rbx_rcx_scale4_disp8() {
        // LEA RAX, [RBX + RCX*4 + 16]: REX.W(48) + 8D + ModRM(01 000 100) + SIB(10 001 011) + disp8(10)
        let bytes = encode(
            X86Opcode::LeaSib,
            &X86InstOperands::rm_sib(RAX, RBX, RCX, 4, 16),
        );
        assert_eq!(bytes, vec![0x48, 0x8D, 0x44, 0x8B, 0x10]);
    }

    #[test]
    fn test_lea_sib_r8_r12_r9_scale2() {
        // LEA R8, [R12 + R9*2]: REX.WRXB(4F) + 8D + ModRM(00 000 100) + SIB(01 001 100)
        let bytes = encode(
            X86Opcode::LeaSib,
            &X86InstOperands::rm_sib(R8, R12, R9, 2, 0),
        );
        assert_eq!(bytes, vec![0x4F, 0x8D, 0x04, 0x4C]);
    }

    // -----------------------------------------------------------------------
    // ImulRM tests (IMUL r64, [base+disp] -- 0F AF)
    // -----------------------------------------------------------------------

    #[test]
    fn test_imul_rax_mem_rbx() {
        // IMUL RAX, [RBX]: REX.W(48) + 0F AF + ModRM(00 000 011)
        let bytes = encode(X86Opcode::ImulRM, &X86InstOperands::rm(RAX, RBX, 0));
        assert_eq!(bytes, vec![0x48, 0x0F, 0xAF, 0x03]);
    }

    #[test]
    fn test_imul_rax_mem_rbx_disp8() {
        // IMUL RAX, [RBX+16]: REX.W(48) + 0F AF + ModRM(01 000 011) + disp8(10)
        let bytes = encode(X86Opcode::ImulRM, &X86InstOperands::rm(RAX, RBX, 16));
        assert_eq!(bytes, vec![0x48, 0x0F, 0xAF, 0x43, 0x10]);
    }

    #[test]
    fn test_imul_r8_mem_r13() {
        // IMUL R8, [R13+0]: REX.WRB(4D) + 0F AF + ModRM(01 000 101) + disp8(00)
        // R13 base (hw_enc & 7 == 5) with disp=0 requires disp8=0
        let bytes = encode(X86Opcode::ImulRM, &X86InstOperands::rm(R8, R13, 0));
        assert_eq!(bytes, vec![0x4D, 0x0F, 0xAF, 0x45, 0x00]);
    }

    // -----------------------------------------------------------------------
    // ImulRMSib tests (IMUL r64, [base+index*scale+disp] -- 0F AF + SIB)
    // -----------------------------------------------------------------------

    #[test]
    fn test_imul_rax_sib_rbx_rcx4_disp8() {
        // IMUL RAX, [RBX+RCX*4+8]: REX.W(48) + 0F AF + ModRM(01 000 100) +
        // SIB(10 001 011) + disp8(08)
        let bytes = encode(
            X86Opcode::ImulRMSib,
            &X86InstOperands::rm_sib(RAX, RBX, RCX, 4, 8),
        );
        assert_eq!(bytes, vec![0x48, 0x0F, 0xAF, 0x44, 0x8B, 0x08]);
    }

    #[test]
    fn test_imul_r8_sib_r13_r14_scale1() {
        // IMUL R8, [R13+R14*1+0]: REX.WRXB(4F) + 0F AF + ModRM(01 000 100) +
        // SIB(00 110 101) + disp8(00) — the R13 base (enc&7 == 5) forces the
        // explicit disp8=0, exactly like the base+disp form.
        let bytes = encode(
            X86Opcode::ImulRMSib,
            &X86InstOperands::rm_sib(R8, R13, R14, 1, 0),
        );
        assert_eq!(bytes, vec![0x4F, 0x0F, 0xAF, 0x44, 0x35, 0x00]);
    }

    // -----------------------------------------------------------------------
    // TestRM tests (TEST r64, [base+disp] -- 85)
    // -----------------------------------------------------------------------

    #[test]
    fn test_test_rax_mem_rbx() {
        // TEST RAX, [RBX]: REX.W(48) + 85 + ModRM(00 000 011)
        let bytes = encode(X86Opcode::TestRM, &X86InstOperands::rm(RAX, RBX, 0));
        assert_eq!(bytes, vec![0x48, 0x85, 0x03]);
    }

    #[test]
    fn test_test_rcx_mem_rdx_disp8() {
        // TEST RCX, [RDX+16]: REX.W(48) + 85 + ModRM(01 001 010) + disp8(10)
        let bytes = encode(X86Opcode::TestRM, &X86InstOperands::rm(RCX, RDX, 16));
        assert_eq!(bytes, vec![0x48, 0x85, 0x4A, 0x10]);
    }

    // -----------------------------------------------------------------------
    // CallM tests (CALL [base+disp] -- FF /2)
    // -----------------------------------------------------------------------

    #[test]
    fn test_call_mem_rax() {
        // CALL [RAX]: FF + ModRM(00 010 000) = 0x10
        let bytes = encode(
            X86Opcode::CallM,
            &X86InstOperands {
                base: Some(RAX),
                disp: 0,
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0xFF, 0x10]);
    }

    #[test]
    fn test_call_mem_rbx_disp8() {
        // CALL [RBX+8]: FF + ModRM(01 010 011) + disp8(08)
        let bytes = encode(
            X86Opcode::CallM,
            &X86InstOperands {
                base: Some(RBX),
                disp: 8,
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0xFF, 0x53, 0x08]);
    }

    #[test]
    fn test_call_mem_r15() {
        // CALL [R15]: REX.B(41) + FF + ModRM(00 010 111)
        let bytes = encode(
            X86Opcode::CallM,
            &X86InstOperands {
                base: Some(R15),
                disp: 0,
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0x41, 0xFF, 0x17]);
    }

    #[test]
    fn test_call_mem_rsp() {
        // CALL [RSP]: FF + ModRM(00 010 100) + SIB(00 100 100)
        // RSP base requires SIB byte
        let bytes = encode(
            X86Opcode::CallM,
            &X86InstOperands {
                base: Some(RSP),
                disp: 0,
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0xFF, 0x14, 0x24]);
    }

    // -----------------------------------------------------------------------
    // CMP r/m64, imm8 (CmpRI8) tests
    // Intel SDM Vol 2: CMP r/m64, imm8: REX.W + 83 /7 ib
    // -----------------------------------------------------------------------

    #[test]
    fn test_cmp_rax_imm8() {
        // CMP RAX, 1: REX.W(48) + 83 + ModRM(11 111 000) + imm8(01)
        let bytes = encode(X86Opcode::CmpRI8, &X86InstOperands::ri(RAX, 1));
        assert_eq!(bytes, vec![0x48, 0x83, 0xF8, 0x01]);
    }

    #[test]
    fn test_cmp_rcx_imm8_negative() {
        // CMP RCX, -1: REX.W(48) + 83 + ModRM(11 111 001) + imm8(FF)
        let bytes = encode(X86Opcode::CmpRI8, &X86InstOperands::ri(RCX, -1));
        assert_eq!(bytes, vec![0x48, 0x83, 0xF9, 0xFF]);
    }

    #[test]
    fn test_cmp_r15_imm8() {
        // CMP R15, 42: REX.WB(49) + 83 + ModRM(11 111 111) + imm8(2A)
        let bytes = encode(X86Opcode::CmpRI8, &X86InstOperands::ri(R15, 42));
        assert_eq!(bytes, vec![0x49, 0x83, 0xFF, 0x2A]);
    }

    #[test]
    fn test_cmp_r8_imm8_zero() {
        // CMP R8, 0: REX.WB(49) + 83 + ModRM(11 111 000) + imm8(00)
        let bytes = encode(X86Opcode::CmpRI8, &X86InstOperands::ri(R8, 0));
        assert_eq!(bytes, vec![0x49, 0x83, 0xF8, 0x00]);
    }

    #[test]
    fn test_cmpri_uses_short_form_when_semantics_match() {
        let mut enc = X86Encoder::new();
        let n8 = enc
            .encode_instruction(X86Opcode::CmpRI8, &X86InstOperands::ri(RAX, 1))
            .unwrap();
        assert_eq!(n8, 4); // REX.W + 83 + ModRM + imm8
        let n_short = enc
            .encode_instruction(X86Opcode::CmpRI, &X86InstOperands::ri(RAX, 1))
            .unwrap();
        assert_eq!(n_short, 4); // CmpRI also selects the short form when equivalent.
        let n_long = enc
            .encode_instruction(X86Opcode::CmpRI, &X86InstOperands::ri(RAX, 128))
            .unwrap();
        assert_eq!(n_long, 7); // REX.W + 81 + ModRM + imm32
    }

    // -----------------------------------------------------------------------
    // CDQ / CQO tests
    // Intel SDM Vol 2: CDQ: 99, CQO: REX.W + 99
    // -----------------------------------------------------------------------

    #[test]
    fn test_cdq() {
        // CDQ: 99 (sign-extend EAX into EDX:EAX, 32-bit)
        let bytes = encode(X86Opcode::Cdq, &X86InstOperands::none());
        assert_eq!(bytes, vec![0x99]);
    }

    #[test]
    fn test_cqo() {
        // CQO: REX.W(48) + 99 (sign-extend RAX into RDX:RAX, 64-bit)
        let bytes = encode(X86Opcode::Cqo, &X86InstOperands::none());
        assert_eq!(bytes, vec![0x48, 0x99]);
    }

    #[test]
    fn test_cdq_cqo_sizes() {
        let mut enc = X86Encoder::new();
        let n = enc
            .encode_instruction(X86Opcode::Cdq, &X86InstOperands::none())
            .unwrap();
        assert_eq!(n, 1);
        let n = enc
            .encode_instruction(X86Opcode::Cqo, &X86InstOperands::none())
            .unwrap();
        assert_eq!(n, 2);
    }

    // -----------------------------------------------------------------------
    // Multi-byte NOP tests
    // Intel SDM Vol 2B, NOP instruction, Table 4-12
    // -----------------------------------------------------------------------

    #[test]
    fn test_multibyte_nop_0() {
        let mut enc = X86Encoder::new();
        enc.encode_multibyte_nop(0);
        assert_eq!(enc.finish(), vec![] as Vec<u8>);
    }

    #[test]
    fn test_multibyte_nop_1() {
        let mut enc = X86Encoder::new();
        enc.encode_multibyte_nop(1);
        assert_eq!(enc.finish(), vec![0x90]);
    }

    #[test]
    fn test_multibyte_nop_2() {
        let mut enc = X86Encoder::new();
        enc.encode_multibyte_nop(2);
        assert_eq!(enc.finish(), vec![0x66, 0x90]);
    }

    #[test]
    fn test_multibyte_nop_3() {
        let mut enc = X86Encoder::new();
        enc.encode_multibyte_nop(3);
        assert_eq!(enc.finish(), vec![0x0F, 0x1F, 0x00]);
    }

    #[test]
    fn test_multibyte_nop_4() {
        let mut enc = X86Encoder::new();
        enc.encode_multibyte_nop(4);
        assert_eq!(enc.finish(), vec![0x0F, 0x1F, 0x40, 0x00]);
    }

    #[test]
    fn test_multibyte_nop_5() {
        let mut enc = X86Encoder::new();
        enc.encode_multibyte_nop(5);
        assert_eq!(enc.finish(), vec![0x0F, 0x1F, 0x44, 0x00, 0x00]);
    }

    #[test]
    fn test_multibyte_nop_6() {
        let mut enc = X86Encoder::new();
        enc.encode_multibyte_nop(6);
        assert_eq!(enc.finish(), vec![0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00]);
    }

    #[test]
    fn test_multibyte_nop_7() {
        let mut enc = X86Encoder::new();
        enc.encode_multibyte_nop(7);
        assert_eq!(enc.finish(), vec![0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_multibyte_nop_8() {
        let mut enc = X86Encoder::new();
        enc.encode_multibyte_nop(8);
        assert_eq!(
            enc.finish(),
            vec![0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]
        );
    }

    #[test]
    fn test_multibyte_nop_9() {
        let mut enc = X86Encoder::new();
        enc.encode_multibyte_nop(9);
        assert_eq!(
            enc.finish(),
            vec![0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]
        );
    }

    #[test]
    fn test_multibyte_nop_11_recurse() {
        // 11 bytes = 9-byte NOP + 2-byte NOP
        let mut enc = X86Encoder::new();
        enc.encode_multibyte_nop(11);
        let bytes = enc.finish();
        assert_eq!(bytes.len(), 11);
        // First 9 bytes: 66 0F 1F 84 00 00 00 00 00
        assert_eq!(
            &bytes[0..9],
            &[0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]
        );
        // Last 2 bytes: 66 90
        assert_eq!(&bytes[9..11], &[0x66, 0x90]);
    }

    #[test]
    fn test_nopmulti_via_instruction_default() {
        // NopMulti with imm=0 defaults to 3-byte NOP
        let bytes = encode(X86Opcode::NopMulti, &X86InstOperands::none());
        assert_eq!(bytes, vec![0x0F, 0x1F, 0x00]);
    }

    #[test]
    fn test_nopmulti_via_instruction_size_5() {
        // NopMulti with imm=5 produces 5-byte NOP
        let bytes = encode(
            X86Opcode::NopMulti,
            &X86InstOperands {
                imm: 5,
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0x0F, 0x1F, 0x44, 0x00, 0x00]);
    }

    #[test]
    fn test_nopmulti_via_instruction_size_8() {
        // NopMulti with imm=8 produces 8-byte NOP
        let bytes = encode(
            X86Opcode::NopMulti,
            &X86InstOperands {
                imm: 8,
                ..X86InstOperands::none()
            },
        );
        assert_eq!(bytes, vec![0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]);
    }

    // -----------------------------------------------------------------------
    // New instruction size tests (wave 38)
    // -----------------------------------------------------------------------

    #[test]
    fn test_new_instruction_sizes_v3() {
        let mut enc = X86Encoder::new();

        // CDQ = 1 byte (99)
        let n = enc
            .encode_instruction(X86Opcode::Cdq, &X86InstOperands::none())
            .unwrap();
        assert_eq!(n, 1);

        // CQO = 2 bytes (REX.W + 99)
        let n = enc
            .encode_instruction(X86Opcode::Cqo, &X86InstOperands::none())
            .unwrap();
        assert_eq!(n, 2);

        // CMP r64, imm8 = 4 bytes (REX.W + 83 + ModRM + imm8)
        let n = enc
            .encode_instruction(X86Opcode::CmpRI8, &X86InstOperands::ri(RAX, 1))
            .unwrap();
        assert_eq!(n, 4);

        // CMP R15, imm8 = 4 bytes (REX.WB + 83 + ModRM + imm8)
        let n = enc
            .encode_instruction(X86Opcode::CmpRI8, &X86InstOperands::ri(R15, 1))
            .unwrap();
        assert_eq!(n, 4);

        // NopMulti default = 3 bytes (0F 1F 00)
        let n = enc
            .encode_instruction(X86Opcode::NopMulti, &X86InstOperands::none())
            .unwrap();
        assert_eq!(n, 3);

        // NopMulti size=9 = 9 bytes
        let n = enc
            .encode_instruction(
                X86Opcode::NopMulti,
                &X86InstOperands {
                    imm: 9,
                    ..X86InstOperands::none()
                },
            )
            .unwrap();
        assert_eq!(n, 9);
    }

    // -----------------------------------------------------------------------
    // All SETcc condition codes (comprehensive)
    // Intel SDM Vol 2: SETcc: 0F 90+cc /0
    // -----------------------------------------------------------------------

    #[test]
    fn test_setcc_all_conditions() {
        let all_cc = [
            (X86CondCode::O, 0x90u8),
            (X86CondCode::NO, 0x91),
            (X86CondCode::B, 0x92),
            (X86CondCode::AE, 0x93),
            (X86CondCode::E, 0x94),
            (X86CondCode::NE, 0x95),
            (X86CondCode::BE, 0x96),
            (X86CondCode::A, 0x97),
            (X86CondCode::S, 0x98),
            (X86CondCode::NS, 0x99),
            (X86CondCode::P, 0x9A),
            (X86CondCode::NP, 0x9B),
            (X86CondCode::L, 0x9C),
            (X86CondCode::GE, 0x9D),
            (X86CondCode::LE, 0x9E),
            (X86CondCode::G, 0x9F),
        ];
        for (cc, expected_byte) in &all_cc {
            let bytes = encode(
                X86Opcode::Setcc,
                &X86InstOperands {
                    dst: Some(AL),
                    cc: Some(*cc),
                    ..X86InstOperands::none()
                },
            );
            // 0F + cc_byte + ModRM(11 000 000)
            assert_eq!(bytes[0], 0x0F, "SETcc {:?} prefix", cc);
            assert_eq!(bytes[1], *expected_byte, "SETcc {:?} opcode byte", cc);
            assert_eq!(bytes[2], 0xC0, "SETcc {:?} ModRM", cc);
        }
    }

    // -----------------------------------------------------------------------
    // Fence encoding
    // -----------------------------------------------------------------------

    #[test]
    fn test_mfence() {
        let bytes = encode(X86Opcode::Mfence, &X86InstOperands::none());
        assert_eq!(bytes, &[0x0F, 0xAE, 0xF0]);
    }

    // -----------------------------------------------------------------------
    // XCHG encoding (Intel SDM: 87 /r)
    // -----------------------------------------------------------------------

    #[test]
    fn test_xchg_rax_rcx() {
        // XCHG RAX, RCX: REX.W + 87 + ModRM(11_001_000)
        // encode_alu_rr puts src(RCX=1) in reg, dst(RAX=0) in rm
        // REX: W=1,R=0,X=0,B=0 = 0x48
        // ModRM: mod=11, reg=001, rm=000 = 0xC8
        let bytes = encode(X86Opcode::Xchg, &X86InstOperands::rr(RAX, RCX));
        assert_eq!(bytes, &[0x48, 0x87, 0xC8]);
    }

    #[test]
    fn test_xchg_r8_rdx() {
        // XCHG R8, RDX: src=RDX(2) in reg, dst=R8(8) in rm
        // REX: W=1,R=0,X=0,B=1(R8>=8) = 0x49
        // ModRM: mod=11, reg=010, rm=000(R8&7=0) = 0xD0
        let bytes = encode(X86Opcode::Xchg, &X86InstOperands::rr(R8, RDX));
        assert_eq!(bytes, &[0x49, 0x87, 0xD0]);
    }

    #[test]
    fn test_xchg_r15_r14() {
        // XCHG R15, R14: src=R14(14) in reg, dst=R15(15) in rm
        // REX: W=1,R=1(R14>=8),X=0,B=1(R15>=8) = 0x4D
        // ModRM: mod=11, reg=110(R14&7=6), rm=111(R15&7=7) = 0xF7
        let bytes = encode(X86Opcode::Xchg, &X86InstOperands::rr(R15, R14));
        assert_eq!(bytes, &[0x4D, 0x87, 0xF7]);
    }

    #[test]
    fn test_xchg_mem_rbx_rax_i64() {
        // XCHG [RBX], RAX: REX.W + 87 + ModRM(00_000_011)
        let bytes = encode(X86Opcode::Xchg, &X86InstOperands::rm(RAX, RBX, 0));
        assert_eq!(bytes, &[0x48, 0x87, 0x03]);
    }

    #[test]
    fn test_xchg_mem_r13_r8_i64() {
        // XCHG [R13+0], R8: REX.WRB + 87 + ModRM(01_000_101) + disp8(0)
        let bytes = encode(X86Opcode::Xchg, &X86InstOperands::rm(R8, R13, 0));
        assert_eq!(bytes, &[0x4D, 0x87, 0x45, 0x00]);
    }

    #[test]
    fn test_xchg_mem_rbx_eax_i32_does_not_emit_rex_w() {
        // XCHG [RBX+16], EAX: 87 + ModRM(01_000_011) + disp8(16)
        let bytes = encode(X86Opcode::Xchg, &X86InstOperands::rm(EAX, RBX, 16));
        assert_eq!(bytes, &[0x87, 0x43, 0x10]);
    }

    // -----------------------------------------------------------------------
    // CMPXCHG encoding (Intel SDM: F0 + 0F B1 /r)
    // -----------------------------------------------------------------------

    #[test]
    fn test_cmpxchg_rcx_rdx() {
        // LOCK CMPXCHG RCX, RDX
        // F0(LOCK) + REX.W(0x48) + 0F B1 + ModRM
        // src=RDX(2) in reg, dst=RCX(1) in rm
        // ModRM: mod=11, reg=010, rm=001 = 0xD1
        let bytes = encode(X86Opcode::Cmpxchg, &X86InstOperands::rr(RCX, RDX));
        assert_eq!(bytes, &[0xF0, 0x48, 0x0F, 0xB1, 0xD1]);
    }

    #[test]
    fn test_cmpxchg_r8_r9() {
        // LOCK CMPXCHG R8, R9
        // F0 + REX(W=1,R=1(R9>=8),B=1(R8>=8)) = REX 0x4D
        // 0F B1 + ModRM: mod=11, reg=001(R9&7=1), rm=000(R8&7=0) = 0xC8
        let bytes = encode(X86Opcode::Cmpxchg, &X86InstOperands::rr(R8, R9));
        assert_eq!(bytes, &[0xF0, 0x4D, 0x0F, 0xB1, 0xC8]);
    }

    #[test]
    fn test_cmpxchg_mem_rbx_rdx_i64() {
        // LOCK CMPXCHG [RBX], RDX: F0 + REX.W + 0F B1 + ModRM(00_010_011)
        let bytes = encode(X86Opcode::Cmpxchg, &X86InstOperands::rm(RDX, RBX, 0));
        assert_eq!(bytes, &[0xF0, 0x48, 0x0F, 0xB1, 0x13]);
    }

    #[test]
    fn test_cmpxchg_mem_r13_r8_i64() {
        // LOCK CMPXCHG [R13+0], R8: F0 + REX.WRB + 0F B1 + ModRM + disp8(0)
        let bytes = encode(X86Opcode::Cmpxchg, &X86InstOperands::rm(R8, R13, 0));
        assert_eq!(bytes, &[0xF0, 0x4D, 0x0F, 0xB1, 0x45, 0x00]);
    }

    #[test]
    fn test_cmpxchg_mem_rbx_edx_i32_does_not_emit_rex_w() {
        // LOCK CMPXCHG [RBX], EDX: F0 + 0F B1 + ModRM(00_010_011)
        let bytes = encode(X86Opcode::Cmpxchg, &X86InstOperands::rm(EDX, RBX, 0));
        assert_eq!(bytes, &[0xF0, 0x0F, 0xB1, 0x13]);
    }

    #[test]
    fn test_atomic_rmw_cas_loop_add_i64_expands_to_locked_cmpxchg_loop() {
        let bytes = encode(
            X86Opcode::AtomicRmwCasLoop,
            &X86InstOperands {
                dst: Some(RCX),
                src: Some(RDX),
                base: Some(RBX),
                imm: 0,
                ..X86InstOperands::none()
            },
        );
        assert_eq!(
            bytes,
            &[
                0x48, 0x8B, 0x03, // mov rax, [rbx]
                0x49, 0x89, 0xC2, // mov r10, rax
                0x49, 0x01, 0xD2, // add r10, rdx
                0xF0, 0x4C, 0x0F, 0xB1, 0x13, // lock cmpxchg [rbx], r10
                0x0F, 0x85, 0xEF, 0xFF, 0xFF, 0xFF, // jne retry
                0x48, 0x89, 0xC1, // mov rcx, rax
            ]
        );
    }

    #[test]
    fn test_atomic_rmw_cas_loop_xor_i32_expands_without_rex_w() {
        let bytes = encode(
            X86Opcode::AtomicRmwCasLoop,
            &X86InstOperands {
                dst: Some(EDX),
                src: Some(ECX),
                base: Some(RBX),
                imm: 4,
                ..X86InstOperands::none()
            },
        );
        assert_eq!(
            bytes,
            &[
                0x8B, 0x03, // mov eax, [rbx]
                0x41, 0x89, 0xC2, // mov r10d, eax
                0x41, 0x31, 0xCA, // xor r10d, ecx
                0xF0, 0x44, 0x0F, 0xB1, 0x13, // lock cmpxchg [rbx], r10d
                0x0F, 0x85, 0xEF, 0xFF, 0xFF, 0xFF, // jne retry
                0x89, 0xC2, // mov edx, eax
            ]
        );
    }

    #[test]
    fn test_atomic_rmw_cas_loop_add_i8_expands_to_byte_locked_cmpxchg_loop() {
        let bytes = encode(
            X86Opcode::AtomicRmwCasLoop8,
            &X86InstOperands {
                dst: Some(EAX),
                src: Some(EDX),
                base: Some(RBX),
                imm: 0,
                ..X86InstOperands::none()
            },
        );
        assert_eq!(
            bytes,
            &[
                0x8A, 0x03, // mov al, [rbx]
                0x41, 0x88, 0xC2, // mov r10b, al
                0x41, 0x00, 0xD2, // add r10b, dl
                0xF0, 0x44, 0x0F, 0xB0, 0x13, // lock cmpxchg byte ptr [rbx], r10b
                0x0F, 0x85, 0xEF, 0xFF, 0xFF, 0xFF, // jne retry
                0x0F, 0xB6, 0xC0, // movzx eax, al
            ]
        );
    }

    #[test]
    fn test_atomic_rmw_cas_loop_xor_i16_expands_to_word_locked_cmpxchg_loop() {
        let bytes = encode(
            X86Opcode::AtomicRmwCasLoop16,
            &X86InstOperands {
                dst: Some(EDX),
                src: Some(ECX),
                base: Some(RBX),
                imm: 4,
                ..X86InstOperands::none()
            },
        );
        assert_eq!(
            bytes,
            &[
                0x66, 0x8B, 0x03, // mov ax, [rbx]
                0x66, 0x41, 0x89, 0xC2, // mov r10w, ax
                0x66, 0x41, 0x31, 0xCA, // xor r10w, cx
                0xF0, 0x66, 0x44, 0x0F, 0xB1, 0x13, // lock cmpxchg word ptr [rbx], r10w
                0x0F, 0x85, 0xEC, 0xFF, 0xFF, 0xFF, // jne retry
                0x0F, 0xB7, 0xD0, // movzx edx, ax
            ]
        );
    }

    #[test]
    fn test_atomic_rmw_cas_loop_xchg_i8_uses_source_as_new_value() {
        let bytes = encode(
            X86Opcode::AtomicRmwCasLoop8,
            &X86InstOperands {
                dst: Some(ECX),
                src: Some(EDX),
                base: Some(RBX),
                imm: 5,
                ..X86InstOperands::none()
            },
        );
        assert_eq!(
            bytes,
            &[
                0x8A, 0x03, // mov al, [rbx]
                0x41, 0x88, 0xD2, // mov r10b, dl
                0xF0, 0x44, 0x0F, 0xB0, 0x13, // lock cmpxchg byte ptr [rbx], r10b
                0x0F, 0x85, 0xF2, 0xFF, 0xFF, 0xFF, // jne retry
                0x0F, 0xB6, 0xC8, // movzx ecx, al
            ]
        );
    }

    #[test]
    fn test_atomic_rmw_cas_loop_max_i64_uses_signed_cmov() {
        let bytes = encode(
            X86Opcode::AtomicRmwCasLoop,
            &X86InstOperands {
                dst: Some(RCX),
                src: Some(RDX),
                base: Some(RBX),
                imm: 6,
                ..X86InstOperands::none()
            },
        );
        assert_eq!(
            bytes,
            &[
                0x48, 0x8B, 0x03, // mov rax, [rbx]
                0x49, 0x89, 0xC2, // mov r10, rax
                0x49, 0x39, 0xD2, // cmp r10, rdx
                0x4C, 0x0F, 0x4C, 0xD2, // cmovl r10, rdx
                0xF0, 0x4C, 0x0F, 0xB1, 0x13, // lock cmpxchg [rbx], r10
                0x0F, 0x85, 0xEB, 0xFF, 0xFF, 0xFF, // jne retry
                0x48, 0x89, 0xC1, // mov rcx, rax
            ]
        );
    }

    #[test]
    fn test_atomic_rmw_cas_loop_umin_i32_uses_unsigned_cmov() {
        let bytes = encode(
            X86Opcode::AtomicRmwCasLoop,
            &X86InstOperands {
                dst: Some(EDX),
                src: Some(ECX),
                base: Some(RBX),
                imm: 9,
                ..X86InstOperands::none()
            },
        );
        assert_eq!(
            bytes,
            &[
                0x8B, 0x03, // mov eax, [rbx]
                0x41, 0x89, 0xC2, // mov r10d, eax
                0x41, 0x39, 0xCA, // cmp r10d, ecx
                0x44, 0x0F, 0x47, 0xD1, // cmova r10d, ecx
                0xF0, 0x44, 0x0F, 0xB1, 0x13, // lock cmpxchg [rbx], r10d
                0x0F, 0x85, 0xEB, 0xFF, 0xFF, 0xFF, // jne retry
                0x89, 0xC2, // mov edx, eax
            ]
        );
    }

    // -----------------------------------------------------------------------
    // BT encoding (Intel SDM: 0F BA /4 ib)
    // -----------------------------------------------------------------------

    #[test]
    fn test_bt_rax_imm5() {
        // BT RAX, 5: REX.W(0x48) + 0F BA + ModRM(11_100_000) + 05
        // ModRM ext_reg(4, RAX=0): mod=11, reg=100, rm=000 = 0xE0
        let bytes = encode(X86Opcode::BtRI, &X86InstOperands::ri(RAX, 5));
        assert_eq!(bytes, &[0x48, 0x0F, 0xBA, 0xE0, 0x05]);
    }

    #[test]
    fn test_bt_r15_imm63() {
        // BT R15, 63: REX.WB(0x49) + 0F BA + ModRM(11_100_111) + 3F
        // ModRM ext_reg(4, R15&7=7): mod=11, reg=100, rm=111 = 0xE7
        let bytes = encode(X86Opcode::BtRI, &X86InstOperands::ri(R15, 63));
        assert_eq!(bytes, &[0x49, 0x0F, 0xBA, 0xE7, 0x3F]);
    }

    // -----------------------------------------------------------------------
    // BSWAP encoding (Intel SDM: 0F C8+rd)
    // -----------------------------------------------------------------------

    #[test]
    fn test_bswap_rax() {
        // BSWAP RAX: REX.W(0x48) + 0F + C8+0 = [0x48, 0x0F, 0xC8]
        let bytes = encode(X86Opcode::Bswap, &X86InstOperands::r(RAX));
        assert_eq!(bytes, &[0x48, 0x0F, 0xC8]);
    }

    #[test]
    fn test_bswap_rbx() {
        // BSWAP RBX: REX.W(0x48) + 0F + C8+3 = [0x48, 0x0F, 0xCB]
        let bytes = encode(X86Opcode::Bswap, &X86InstOperands::r(RBX));
        assert_eq!(bytes, &[0x48, 0x0F, 0xCB]);
    }

    #[test]
    fn test_bswap_r12() {
        // BSWAP R12: REX.WB(0x49) + 0F + C8+4(R12&7=4) = [0x49, 0x0F, 0xCC]
        let bytes = encode(X86Opcode::Bswap, &X86InstOperands::r(R12));
        assert_eq!(bytes, &[0x49, 0x0F, 0xCC]);
    }

    // -----------------------------------------------------------------------
    // MOVD/MOVQ xmm<->gpr encoding (Intel SDM: 66 0F 6E/7E)
    // -----------------------------------------------------------------------

    #[test]
    fn test_movd_to_xmm_xmm0_rax() {
        // MOVD XMM0, EAX: 66 0F 6E ModRM(11_000_000)=0xC0
        // No REX needed (both < 8)
        let bytes = encode(X86Opcode::MovdToXmm, &X86InstOperands::rr(XMM0, RAX));
        assert_eq!(bytes, &[0x66, 0x0F, 0x6E, 0xC0]);
    }

    #[test]
    fn test_movd_to_xmm8_rcx() {
        // MOVD XMM8, ECX: 66 REX.R(XMM8>=8)(0x44) 0F 6E ModRM(11_000_001)=0xC1
        // REX: W=0,R=1(XMM8>=8),X=0,B=0 = 0x44
        let bytes = encode(X86Opcode::MovdToXmm, &X86InstOperands::rr(XMM8, RCX));
        assert_eq!(bytes, &[0x66, 0x44, 0x0F, 0x6E, 0xC1]);
    }

    #[test]
    fn test_movd_from_xmm_rax_xmm0() {
        // MOVD EAX, XMM0: 66 0F 7E ModRM(11_000_000)=0xC0
        // src=XMM0 in reg, dst=RAX in rm
        let bytes = encode(X86Opcode::MovdFromXmm, &X86InstOperands::rr(RAX, XMM0));
        assert_eq!(bytes, &[0x66, 0x0F, 0x7E, 0xC0]);
    }

    #[test]
    fn test_movq_to_xmm_xmm0_rax() {
        // MOVQ XMM0, RAX: 66 REX.W(0x48) 0F 6E ModRM(11_000_000)=0xC0
        let bytes = encode(X86Opcode::MovqToXmm, &X86InstOperands::rr(XMM0, RAX));
        assert_eq!(bytes, &[0x66, 0x48, 0x0F, 0x6E, 0xC0]);
    }

    #[test]
    fn test_movq_from_xmm_rax_xmm0() {
        // MOVQ RAX, XMM0: 66 REX.W(0x48) 0F 7E ModRM(11_000_000)=0xC0
        let bytes = encode(X86Opcode::MovqFromXmm, &X86InstOperands::rr(RAX, XMM0));
        assert_eq!(bytes, &[0x66, 0x48, 0x0F, 0x7E, 0xC0]);
    }

    #[test]
    fn test_movq_to_xmm15_r15() {
        // MOVQ XMM15, R15: 66 REX.WRB(0x4D) 0F 6E ModRM(11_111_111)=0xFF
        // REX: W=1, R=1(XMM15>=8), X=0, B=1(R15>=8) = 0x4D
        // ModRM: mod=11, reg=111(XMM15&7=7), rm=111(R15&7=7) = 0xFF
        let bytes = encode(X86Opcode::MovqToXmm, &X86InstOperands::rr(XMM15, R15));
        assert_eq!(bytes, &[0x66, 0x4D, 0x0F, 0x6E, 0xFF]);
    }

    #[test]
    fn test_movq_from_xmm15_r15() {
        // MOVQ R15, XMM15: 66 REX.WRB(0x4D) 0F 7E ModRM(11_111_111)=0xFF
        // src=XMM15 in reg, dst=R15 in rm
        // REX: W=1, R=1(XMM15>=8), X=0, B=1(R15>=8) = 0x4D
        let bytes = encode(X86Opcode::MovqFromXmm, &X86InstOperands::rr(R15, XMM15));
        assert_eq!(bytes, &[0x66, 0x4D, 0x0F, 0x7E, 0xFF]);
    }

    // -----------------------------------------------------------------------
    // SSE4.1 PINSRD/PEXTRD lane insert/extract encoding
    // -----------------------------------------------------------------------

    #[test]
    fn test_pinsrd_xmm0_eax_lane2() {
        // PINSRD XMM0, EAX, 2: 66 0F 3A 22 /r ib, ModRM(11_000_000)=0xC0
        let bytes = encode(X86Opcode::Pinsrd, &X86InstOperands::rri(XMM0, EAX, 2));
        assert_eq!(bytes, &[0x66, 0x0F, 0x3A, 0x22, 0xC0, 0x02]);
    }

    #[test]
    fn test_pinsrd_xmm8_r9d_lane3() {
        // REX.RB extends dst XMM8 in ModRM.reg and src R9D in ModRM.rm.
        let bytes = encode(X86Opcode::Pinsrd, &X86InstOperands::rri(XMM8, R9D, 3));
        assert_eq!(bytes, &[0x66, 0x45, 0x0F, 0x3A, 0x22, 0xC1, 0x03]);
    }

    #[test]
    fn test_pextrd_eax_xmm1_lane2() {
        // PEXTRD EAX, XMM1, 2: source XMM1 is ModRM.reg, dest EAX is ModRM.rm.
        let bytes = encode(X86Opcode::Pextrd, &X86InstOperands::rri(EAX, XMM1, 2));
        assert_eq!(bytes, &[0x66, 0x0F, 0x3A, 0x16, 0xC8, 0x02]);
    }

    #[test]
    fn test_pextrd_r9d_xmm15_lane0() {
        // REX.RB extends src XMM15 in ModRM.reg and dst R9D in ModRM.rm.
        let bytes = encode(X86Opcode::Pextrd, &X86InstOperands::rri(R9D, XMM15, 0));
        assert_eq!(bytes, &[0x66, 0x45, 0x0F, 0x3A, 0x16, 0xF9, 0x00]);
    }

    #[test]
    fn test_pinsrq_xmm0_rax_lane1() {
        // PINSRQ XMM0, RAX, 1: mandatory REX.W plus ModRM(11_000_000)=0xC0.
        let bytes = encode(X86Opcode::Pinsrq, &X86InstOperands::rri(XMM0, RAX, 1));
        assert_eq!(bytes, &[0x66, 0x48, 0x0F, 0x3A, 0x22, 0xC0, 0x01]);
    }

    #[test]
    fn test_pinsrq_xmm8_r9_lane0() {
        // REX.WRB extends dst XMM8 in ModRM.reg and src R9 in ModRM.rm.
        let bytes = encode(X86Opcode::Pinsrq, &X86InstOperands::rri(XMM8, R9, 0));
        assert_eq!(bytes, &[0x66, 0x4D, 0x0F, 0x3A, 0x22, 0xC1, 0x00]);
    }

    #[test]
    fn test_pextrq_rax_xmm1_lane1() {
        // PEXTRQ RAX, XMM1, 1: source XMM1 is ModRM.reg, dest RAX is ModRM.rm.
        let bytes = encode(X86Opcode::Pextrq, &X86InstOperands::rri(RAX, XMM1, 1));
        assert_eq!(bytes, &[0x66, 0x48, 0x0F, 0x3A, 0x16, 0xC8, 0x01]);
    }

    #[test]
    fn test_pextrq_r9_xmm15_lane0() {
        // REX.WRB extends src XMM15 in ModRM.reg and dst R9 in ModRM.rm.
        let bytes = encode(X86Opcode::Pextrq, &X86InstOperands::rri(R9, XMM15, 0));
        assert_eq!(bytes, &[0x66, 0x4D, 0x0F, 0x3A, 0x16, 0xF9, 0x00]);
    }

    #[test]
    fn test_pinsrd_pextrd_reject_wrong_register_classes_and_lanes() {
        let mut enc = X86Encoder::new();
        let err = enc
            .encode_instruction(X86Opcode::Pinsrd, &X86InstOperands::rri(XMM0, RAX, 0))
            .expect_err("PINSRD must require a 32-bit GPR source");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());

        let mut enc = X86Encoder::new();
        let err = enc
            .encode_instruction(X86Opcode::Pextrd, &X86InstOperands::rri(XMM0, XMM1, 0))
            .expect_err("PEXTRD must require a 32-bit GPR destination");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());

        let mut enc = X86Encoder::new();
        let err = enc
            .encode_instruction(X86Opcode::Pextrd, &X86InstOperands::rri(EAX, XMM1, 4))
            .expect_err("PEXTRD dword lane must fail closed outside 0..3");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());
    }

    #[test]
    fn test_pinsrq_pextrq_reject_wrong_register_classes_and_lanes() {
        let mut enc = X86Encoder::new();
        let err = enc
            .encode_instruction(X86Opcode::Pinsrq, &X86InstOperands::rri(XMM0, EAX, 0))
            .expect_err("PINSRQ must require a 64-bit GPR source");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());

        let mut enc = X86Encoder::new();
        let err = enc
            .encode_instruction(X86Opcode::Pextrq, &X86InstOperands::rri(R9D, XMM1, 0))
            .expect_err("PEXTRQ must require a 64-bit GPR destination");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());

        let mut enc = X86Encoder::new();
        let err = enc
            .encode_instruction(X86Opcode::Pinsrq, &X86InstOperands::rri(XMM0, RAX, 2))
            .expect_err("PINSRQ qword lane must fail closed outside 0..1");
        assert!(matches!(err, X86EncodeError::InvalidOperands(_)));
        assert!(enc.finish().is_empty());
    }

    // -----------------------------------------------------------------------
    // Instruction size sanity checks for new opcodes
    // -----------------------------------------------------------------------

    #[test]
    fn test_new_instruction_sizes_v4() {
        let mut enc = X86Encoder::new();

        // XCHG RAX,RCX = 3 bytes (REX.W + 87 + ModRM)
        let n = enc
            .encode_instruction(X86Opcode::Xchg, &X86InstOperands::rr(RAX, RCX))
            .unwrap();
        assert_eq!(n, 3, "XCHG RAX,RCX size");

        // CMPXCHG RCX,RDX = 5 bytes (LOCK + REX.W + 0F + B1 + ModRM)
        let n = enc
            .encode_instruction(X86Opcode::Cmpxchg, &X86InstOperands::rr(RCX, RDX))
            .unwrap();
        assert_eq!(n, 5, "CMPXCHG RCX,RDX size");

        // BT RAX,5 = 5 bytes (REX.W + 0F + BA + ModRM + imm8)
        let n = enc
            .encode_instruction(X86Opcode::BtRI, &X86InstOperands::ri(RAX, 5))
            .unwrap();
        assert_eq!(n, 5, "BT RAX,5 size");

        // BSWAP RAX = 3 bytes (REX.W + 0F + C8)
        let n = enc
            .encode_instruction(X86Opcode::Bswap, &X86InstOperands::r(RAX))
            .unwrap();
        assert_eq!(n, 3, "BSWAP RAX size");

        // MOVD XMM0,EAX = 4 bytes (66 + 0F + 6E + ModRM)
        let n = enc
            .encode_instruction(X86Opcode::MovdToXmm, &X86InstOperands::rr(XMM0, RAX))
            .unwrap();
        assert_eq!(n, 4, "MOVD XMM0,EAX size");

        // MOVQ XMM0,RAX = 5 bytes (66 + REX.W + 0F + 6E + ModRM)
        let n = enc
            .encode_instruction(X86Opcode::MovqToXmm, &X86InstOperands::rr(XMM0, RAX))
            .unwrap();
        assert_eq!(n, 5, "MOVQ XMM0,RAX size");

        // PUNPCKLDQ XMM0,XMM1 = 4 bytes (66 + 0F + opcode + ModRM)
        let n = enc
            .encode_instruction(X86Opcode::Punpckldq, &X86InstOperands::rr(XMM0, XMM1))
            .unwrap();
        assert_eq!(n, 4, "PUNPCKLDQ XMM0,XMM1 size");

        // PUNPCKLQDQ XMM0,XMM1 = 4 bytes (66 + 0F + opcode + ModRM)
        let n = enc
            .encode_instruction(X86Opcode::Punpcklqdq, &X86InstOperands::rr(XMM0, XMM1))
            .unwrap();
        assert_eq!(n, 4, "PUNPCKLQDQ XMM0,XMM1 size");

        // PSLLD XMM0,7 = 5 bytes (66 + 0F + 72 + ModRM + imm8)
        let n = enc
            .encode_instruction(X86Opcode::Pslld, &X86InstOperands::ri(XMM0, 7))
            .unwrap();
        assert_eq!(n, 5, "PSLLD XMM0,7 size");

        // PSRAD XMM15,1 = 6 bytes (66 + REX.B + 0F + 72 + ModRM + imm8)
        let n = enc
            .encode_instruction(X86Opcode::Psrad, &X86InstOperands::ri(XMM15, 1))
            .unwrap();
        assert_eq!(n, 6, "PSRAD XMM15,1 size");

        // PINSRD XMM8,R9D,3 = 7 bytes (66 + REX.RB + 0F 3A + opcode + ModRM + imm8)
        let n = enc
            .encode_instruction(X86Opcode::Pinsrd, &X86InstOperands::rri(XMM8, R9D, 3))
            .unwrap();
        assert_eq!(n, 7, "PINSRD XMM8,R9D,3 size");

        // PEXTRD R9D,XMM15,0 = 7 bytes (66 + REX.RB + 0F 3A + opcode + ModRM + imm8)
        let n = enc
            .encode_instruction(X86Opcode::Pextrd, &X86InstOperands::rri(R9D, XMM15, 0))
            .unwrap();
        assert_eq!(n, 7, "PEXTRD R9D,XMM15,0 size");

        // PINSRQ XMM0,RAX,1 = 7 bytes (66 + REX.W + 0F 3A + opcode + ModRM + imm8)
        let n = enc
            .encode_instruction(X86Opcode::Pinsrq, &X86InstOperands::rri(XMM0, RAX, 1))
            .unwrap();
        assert_eq!(n, 7, "PINSRQ XMM0,RAX,1 size");

        // PEXTRQ R9,XMM15,0 = 7 bytes (66 + REX.WRB + 0F 3A + opcode + ModRM + imm8)
        let n = enc
            .encode_instruction(X86Opcode::Pextrq, &X86InstOperands::rri(R9, XMM15, 0))
            .unwrap();
        assert_eq!(n, 7, "PEXTRQ R9,XMM15,0 size");

        // PTEST XMM0,XMM1 = 5 bytes (66 + 0F 38 + opcode + ModRM)
        let n = enc
            .encode_instruction(X86Opcode::Ptest, &X86InstOperands::rr(XMM0, XMM1))
            .unwrap();
        assert_eq!(n, 5, "PTEST XMM0,XMM1 size");

        // PTEST XMM8,[R12+32] = 8 bytes (66 + REX.RB + 0F 38 + opcode + ModRM + SIB + disp8)
        let n = enc
            .encode_instruction(X86Opcode::Ptest, &X86InstOperands::rm(XMM8, R12, 32))
            .unwrap();
        assert_eq!(n, 8, "PTEST XMM8,[R12+32] size");

        // PMULLD XMM8,[R12+32] = 8 bytes (66 + REX.RB + 0F 38 + opcode + ModRM + SIB + disp8)
        let n = enc
            .encode_instruction(X86Opcode::Pmulld, &X86InstOperands::rm(XMM8, R12, 32))
            .unwrap();
        assert_eq!(n, 8, "PMULLD XMM8,[R12+32] size");

        // PCMPEQQ XMM8,[R12+32] = 8 bytes (66 + REX.RB + 0F 38 + opcode + ModRM + SIB + disp8)
        let n = enc
            .encode_instruction(X86Opcode::Pcmpeqq, &X86InstOperands::rm(XMM8, R12, 32))
            .unwrap();
        assert_eq!(n, 8, "PCMPEQQ XMM8,[R12+32] size");

        // PCMPGTQ XMM8,[R12+32] = 8 bytes (66 + REX.RB + 0F 38 + opcode + ModRM + SIB + disp8)
        let n = enc
            .encode_instruction(X86Opcode::Pcmpgtq, &X86InstOperands::rm(XMM8, R12, 32))
            .unwrap();
        assert_eq!(n, 8, "PCMPGTQ XMM8,[R12+32] size");
    }

    // -----------------------------------------------------------------------
    // RIP-relative SSE load tests (MOVSS/MOVSD [RIP+disp32])
    //
    // Intel SDM Vol 2:
    //   MOVSS xmm, m32: F3 0F 10 /r
    //   MOVSD xmm, m64: F2 0F 10 /r
    // RIP-relative: ModRM mod=00, rm=101 signals [RIP+disp32] in 64-bit mode
    // REX.R needed for XMM8-XMM15 (extends ModRM reg field)
    // -----------------------------------------------------------------------

    #[test]
    fn test_movss_rip_rel_xmm0_disp0() {
        // MOVSS XMM0, [RIP+0]: F3 0F 10 ModRM(00 000 101) disp32(00000000)
        // No REX needed (XMM0 hw_enc=0)
        let bytes = encode(X86Opcode::MovssRipRel, &X86InstOperands::rip_rel(XMM0, 0));
        assert_eq!(bytes, vec![0xF3, 0x0F, 0x10, 0x05, 0x00, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_movsd_rip_rel_xmm0_disp0() {
        // MOVSD XMM0, [RIP+0]: F2 0F 10 ModRM(00 000 101) disp32(00000000)
        // No REX needed (XMM0 hw_enc=0)
        let bytes = encode(X86Opcode::MovsdRipRel, &X86InstOperands::rip_rel(XMM0, 0));
        assert_eq!(bytes, vec![0xF2, 0x0F, 0x10, 0x05, 0x00, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_movsd_rip_rel_xmm1_disp256() {
        // MOVSD XMM1, [RIP+256]: F2 0F 10 ModRM(00 001 101) disp32
        // XMM1 reg=001 -> ModRM = 00_001_101 = 0x0D
        let bytes = encode(X86Opcode::MovsdRipRel, &X86InstOperands::rip_rel(XMM1, 256));
        assert_eq!(bytes, vec![0xF2, 0x0F, 0x10, 0x0D, 0x00, 0x01, 0x00, 0x00]);
    }

    #[test]
    fn test_movss_rip_rel_xmm8_disp0() {
        // MOVSS XMM8, [RIP+0]: F3 REX.R(44) 0F 10 ModRM(00 000 101) disp32
        // XMM8 hw_enc=8, needs REX.R: 0100 0100 = 0x44
        let bytes = encode(X86Opcode::MovssRipRel, &X86InstOperands::rip_rel(XMM8, 0));
        assert_eq!(
            bytes,
            vec![0xF3, 0x44, 0x0F, 0x10, 0x05, 0x00, 0x00, 0x00, 0x00]
        );
    }

    #[test]
    fn test_movsd_rip_rel_xmm8_negative_disp() {
        // MOVSD XMM8, [RIP-16]: F2 REX.R(44) 0F 10 ModRM(00 000 101) disp32(F0FFFFFF)
        let bytes = encode(X86Opcode::MovsdRipRel, &X86InstOperands::rip_rel(XMM8, -16));
        assert_eq!(
            bytes,
            vec![0xF2, 0x44, 0x0F, 0x10, 0x05, 0xF0, 0xFF, 0xFF, 0xFF]
        );
    }

    #[test]
    fn test_movss_rip_rel_xmm15_disp128() {
        // MOVSS XMM15, [RIP+128]: F3 REX.R(44) 0F 10 ModRM(00 111 101) disp32
        // XMM15 hw_enc=15, reg&7=7 -> ModRM = 00_111_101 = 0x3D
        let bytes = encode(
            X86Opcode::MovssRipRel,
            &X86InstOperands::rip_rel(XMM15, 128),
        );
        assert_eq!(
            bytes,
            vec![0xF3, 0x44, 0x0F, 0x10, 0x3D, 0x80, 0x00, 0x00, 0x00]
        );
    }

    #[test]
    fn test_movss_rip_rel_size_no_rex() {
        // MOVSS XMM0, [RIP+0] should be 8 bytes (no REX)
        // F3(1) + 0F(1) + 10(1) + ModRM(1) + disp32(4) = 8
        let mut enc = X86Encoder::new();
        let n = enc
            .encode_instruction(X86Opcode::MovssRipRel, &X86InstOperands::rip_rel(XMM0, 0))
            .unwrap();
        assert_eq!(n, 8, "MOVSS XMM0,[RIP+0] size without REX");
    }

    #[test]
    fn test_movsd_rip_rel_size_with_rex() {
        // MOVSD XMM8, [RIP+0] should be 9 bytes (with REX.R)
        // F2(1) + REX(1) + 0F(1) + 10(1) + ModRM(1) + disp32(4) = 9
        let mut enc = X86Encoder::new();
        let n = enc
            .encode_instruction(X86Opcode::MovsdRipRel, &X86InstOperands::rip_rel(XMM8, 0))
            .unwrap();
        assert_eq!(n, 9, "MOVSD XMM8,[RIP+0] size with REX.R");
    }

    #[test]
    fn test_movss_rip_rel_missing_dst_error() {
        let mut enc = X86Encoder::new();
        let result = enc.encode_instruction(X86Opcode::MovssRipRel, &X86InstOperands::none());
        assert!(result.is_err(), "MovssRipRel without dst should fail");
    }

    #[test]
    fn test_movsd_rip_rel_missing_dst_error() {
        let mut enc = X86Encoder::new();
        let result = enc.encode_instruction(X86Opcode::MovsdRipRel, &X86InstOperands::none());
        assert!(result.is_err(), "MovsdRipRel without dst should fail");
    }
}
