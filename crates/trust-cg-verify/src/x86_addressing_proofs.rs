// trust-cg-verify/src/x86_addressing_proofs.rs - byte-level ADDRESS obligations for the x86-64 memory MOV family
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The EFFECTIVE ADDRESS of an emitted memory MOV, proven from the REAL BYTES.
//!
//! # Why this module exists
//!
//! The x86 coverage gate credited its memory rows through
//! `x86_64_function_verifier::x86_reconstruct_effective_address`, whose two
//! halves are built from the SAME `X86ISelOperand` with structurally identical
//! encoders (`encode_trust_ir_binop(Iadd) == bvadd == encode_lea_base_disp`).
//! The obligation was therefore `X == X`, and the audit
//! `report_which_credited_opcodes_have_no_address_teeth` pinned the consequence
//! when it landed (f001a11e8): of the 39 memory opcodes then credited, only
//! `Cmpxchg8`/`Cmpxchg16` can refute an address error at all. For the other 37
//! no address error of ANY kind — wrong base, wrong index, base/index swap,
//! wrong scale, wrong displacement — can be refuted, while roughly thirty
//! `coverage_gate` comments claimed exactly the opposite. The sixteen volatile
//! forms, which reconstruct since 88de9e199, are toothless the same way; the
//! audit pins all 53 by name and requires this lane to carry each of them.
//!
//! # The two sides, and why they are independent
//!
//! SOURCE is the INTENT: what the instruction's addressing operand says the
//! address is, read as `base + index*scale + disp` with the INTENDED register
//! roots as leaves.
//!
//! MACHINE is the DECODE: the same address read back out of the bytes the live
//! encoder produced, through [`sdm_decode_memory_mov`] — an SDM-derived decoder
//! that shares no code with the encoder — as
//! `base + (index << shift) + disp` with the DECODED register roots as leaves.
//!
//! The two are structurally DISTINCT on purpose. The SIB byte encodes a SHIFT,
//! not a scale factor (SDM Vol 2A 2.1.5, Table 2-3), so the machine reading is
//! a `bvshl` where the intent is a `bvmul`. They denote the same address only
//! when `scale == 1 << shift` AND every decoded root equals its intended root
//! AND the displacement round-tripped. Each of those is a way for the encoder
//! to be wrong, and each one REFUTES.
//!
//! This is the same shape as `x86_movsxd_sib_proofs` and the wasm lane: the
//! machine side is rebuilt from what was actually emitted, never from the typed
//! operand the emitter was handed.
//!
//! # What this does NOT prove
//!
//! It proves the ENCODING of the address, not its SELECTION. Nothing here says
//! the lowering chose the right base or index in the first place, because this
//! layer runs post-isel and has no trust_ir input: `X86ProofOrigin` carries only
//! atomics, so a machine memory instruction has no link back to the trust_ir
//! address chain it came from. That is true of every reconstruction credit on
//! every architecture in this tree, and it is stated here rather than implied.

use crate::smt::{EvalEnv, SmtExpr};

/// Address width for every 64-bit-mode effective address.
pub const ADDR_BITS: u32 = 64;

/// SDM Vol 2A Table 2-3: the SIB `scale` field is a SHIFT amount, and the
/// scale factor is `1 << shift`.
pub const SDM_SIB_SCALE_FACTOR: [u32; 4] = [1, 2, 4, 8];

/// A displacement exactly as the bytes carry it.
///
/// The encoding matters, not just the value: x86 stores a displacement as a
/// SIGN-EXTENDED 8- or 32-bit field selected by `ModR/M.mod` (SDM Vol 2A
/// Table 2-2), or omits it entirely. Modelling that faithfully is what keeps
/// the machine reading structurally distinct from the intent's plain `i64`,
/// and it is what lets a displacement that does not round-trip through its
/// encoded width REFUTE.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DispField {
    /// Width in bits of the encoded field: 0 (absent), 8, or 32.
    pub encoded_bits: u32,
    /// The raw little-endian field bytes, as emitted.
    pub bytes: Vec<u8>,
    /// The value after sign-extension.
    pub value: i64,
}

impl DispField {
    /// The absent displacement (`mod = 00`).
    #[must_use]
    pub fn absent() -> Self {
        DispField {
            encoded_bits: 0,
            bytes: Vec::new(),
            value: 0,
        }
    }

    /// The displacement as the BYTES denote it: the raw field, sign-extended to
    /// the address width.
    ///
    /// Returns `None` when `mod = 00` selects NO displacement field at all.
    /// That is not the same as a displacement of zero, and the difference is
    /// load-bearing twice over. It is more faithful — the bytes carry no
    /// displacement, so the address is just the base — and it is what keeps the
    /// machine reading structurally DISTINCT from an intent that says `+0`.
    /// Denoting an absent field as `bv_const(0)` made the two sides the same
    /// tree for `[base]`, so the anti-vacuity guard refuted a CORRECT encoding
    /// (`MovRM rax,[rbx]` = `48 8B 03`) as `Degenerate`. The corpus hid it,
    /// because its only zero-displacement base was `rbp`, which cannot use
    /// `mod = 00` and is forced to a disp8.
    #[must_use]
    pub fn denotation(&self) -> Option<SmtExpr> {
        match self.encoded_bits {
            0 => None,
            bits => {
                let mut raw = 0u64;
                for (i, b) in self.bytes.iter().enumerate() {
                    raw |= u64::from(*b) << (8 * i);
                }
                Some(SmtExpr::bv_const(raw, bits).sign_ext(ADDR_BITS - bits))
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The decoder
// ---------------------------------------------------------------------------

/// Which REGISTER FILE the ModR/M.reg operand names.
///
/// Carried because the root NUMBER alone cannot distinguish `xmm3` from `rbx`:
/// both are ModR/M.reg = 011. Without the file, a decode naming an XMM
/// register would compare equal to an intent naming the GPR with the same
/// number, and the register facet would have no teeth on the SSE and packed
/// families.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegFile {
    /// A general-purpose register.
    Gpr,
    /// An XMM register.
    Xmm,
}

/// Which memory production a byte string decoded to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemMovMnemonic {
    /// `8B /r` — load a GPR from memory.
    LoadGpr,
    /// `89 /r` — store a GPR to memory.
    StoreGpr,
    /// `8A /r` — load a byte.
    LoadGpr8,
    /// `0F B6 /r` (byte) / `0F B7 /r` (word) — MOVZX r32/r64, m8/m16: a
    /// ZERO-EXTENDING load. The access width is fixed by the opcode byte, and
    /// the destination is written WHOLE: a 32-bit destination write
    /// zero-extends to 64 bits (SDM Vol 1 3.4.1.1), so bits `access_bits..64`
    /// are zero. A `0x66` prefix (`movzx r16, m8`, which writes only 16 bits
    /// and keeps the rest) is refused, not decoded.
    LoadGprZeroExtend,
    /// `0F BE /r` (byte) / `0F BF /r` (word) — MOVSX r32/r64, m8/m16: a
    /// SIGN-EXTENDING load. The backend emits no memory MOVSX; this production
    /// is decoded so that a zero-extending encoding corrupted into it
    /// (`B6 -> BE`, one bit) refutes as an EXTENSION error rather than as an
    /// unknown opcode.
    LoadGprSignExtend,
    /// `88 /r` — store a byte.
    StoreGpr8,
    /// `F3 0F 10 /r` (MOVSS) / `F2 0F 10 /r` (MOVSD) — scalar FP load.
    LoadScalarFp,
    /// `F3 0F 11 /r` / `F2 0F 11 /r` — scalar FP store.
    StoreScalarFp,
    /// `66 0F 6F /r` (MOVDQA) / `F3 0F 6F /r` (MOVDQU) — 128-bit load.
    LoadPacked,
    /// `66 0F 7F /r` / `F3 0F 7F /r` — 128-bit store.
    StorePacked,
    /// `03`/`2B`/`3B` `/r` and `0F AF /r` — an ALU form reading memory into
    /// the register operand (ADD/SUB/CMP/IMUL r, r/m).
    AluRegMem,
    /// `01`/`31` `/r` — an ALU form whose DESTINATION is memory
    /// (ADD/XOR r/m, r).
    AluMemReg,
    /// `8D /r` — LEA. COMPUTES the effective address into the register operand
    /// and touches NO memory at all.
    ///
    /// For this production the address IS the value, which makes it the
    /// cleanest member of the family: there is no access width to get wrong and
    /// no direction, so the obligation reduces to exactly the question this
    /// module answers. `access_bits` here is the DESTINATION operand width
    /// (REX.W / 0x66 select it), not the width of any access.
    ComputeAddress,
    /// `F0 0F B0 /r` (byte) / `F0 [66] 0F B1 /r` — LOCK CMPXCHG r/m, r. Memory
    /// is the DESTINATION (read, and written in both branches); the register
    /// operand is the replacement value. Only the LOCK-prefixed form is
    /// accepted: it is the only one the backend emits.
    CompareExchange,
    /// `F0 [REX.W] 0F C7 /1` — LOCK CMPXCHG8B m64 (no REX.W) / LOCK CMPXCHG16B
    /// m128 (REX.W). Memory is the DESTINATION. There is NO register operand:
    /// the ModR/M.reg field is the `/1` opcode extension, reported (with
    /// REX.R) as `reg_root`, so an intent names it as `1`. Only the
    /// LOCK-prefixed form is accepted.
    CompareExchangeBytes,
}

impl MemMovMnemonic {
    /// Whether the memory operand is the DESTINATION.
    ///
    /// `AluMemReg` reads AND writes memory; it is a store for the purpose of
    /// the direction facet, which asks which operand the memory one is.
    #[must_use]
    pub const fn is_store(self) -> bool {
        matches!(
            self,
            MemMovMnemonic::StoreGpr
                | MemMovMnemonic::StoreGpr8
                | MemMovMnemonic::StoreScalarFp
                | MemMovMnemonic::StorePacked
                | MemMovMnemonic::AluMemReg
                | MemMovMnemonic::CompareExchange
                | MemMovMnemonic::CompareExchangeBytes
        )
    }

    /// Whether this production is a compare-exchange, the only family whose
    /// encoding carries (and here REQUIRES) the `F0` LOCK prefix.
    #[must_use]
    pub const fn is_compare_exchange(self) -> bool {
        matches!(
            self,
            MemMovMnemonic::CompareExchange | MemMovMnemonic::CompareExchangeBytes
        )
    }

    /// Whether this production actually touches memory. LEA does not.
    #[must_use]
    pub const fn accesses_memory(self) -> bool {
        !matches!(self, MemMovMnemonic::ComputeAddress)
    }

    /// Whether this production is the ZERO-EXTENDING load (`0F B6`/`0F B7`).
    #[must_use]
    pub const fn zero_extends(self) -> bool {
        matches!(self, MemMovMnemonic::LoadGprZeroExtend)
    }

    /// Which register file the ModR/M.reg operand names.
    #[must_use]
    pub const fn reg_file(self) -> RegFile {
        match self {
            MemMovMnemonic::LoadScalarFp
            | MemMovMnemonic::StoreScalarFp
            | MemMovMnemonic::LoadPacked
            | MemMovMnemonic::StorePacked => RegFile::Xmm,
            _ => RegFile::Gpr,
        }
    }
}

/// The addressing form read out of ModR/M (+SIB, +displacement).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecodedAddress {
    /// `mod = 11` — register-direct. Not an address at all; refused.
    RegisterDirect { rm_root: u8 },
    /// `[base + disp]`, no SIB byte.
    BaseDisp { base_root: u8, disp: DispField },
    /// RIP-relative `[rip + disp32]`.
    RipRelative { disp: DispField },
    /// `[base + (index << shift) + disp]` through a SIB byte. `base_root` is
    /// `None` for the no-base (`mod = 00`, `base = 101`) disp32 form, and
    /// `index_root` is `None` when the index field encodes "no index".
    Sib {
        base_root: Option<u8>,
        index_root: Option<u8>,
        shift: u8,
        disp: DispField,
    },
}

/// A fully decoded memory MOV.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedMemoryMov {
    /// Legacy prefixes ahead of the REX, in order, except `F0`. Only `0x66` is
    /// expected.
    pub legacy_prefixes: Vec<u8>,
    /// Whether the `F0` LOCK prefix is present. Required for a
    /// compare-exchange and refused for every other production.
    pub lock: bool,
    /// The REX byte, when present.
    pub rex: Option<u8>,
    /// Which production matched.
    pub mnemonic: MemMovMnemonic,
    /// The raw ModR/M byte.
    pub modrm: u8,
    /// The raw SIB byte, when `ModR/M.rm = 100`.
    pub sib: Option<u8>,
    /// The register operand's 64-bit root (`ModR/M.reg` + `REX.R << 3`).
    pub reg_root: u8,
    /// True when this is a BYTE form (`88`/`8A`) with NO REX byte and a
    /// `ModR/M.reg` of 4..7, which names AH/CH/DH/BH — the legacy high-byte
    /// registers — and NOT SPL/BPL/SIL/DIL (SDM Vol 2A Table 2-2, note on
    /// byte registers without REX).
    ///
    /// Without this the decode would map both spellings to root 4..7 and could
    /// not tell them apart, which is exactly the defect the encoder forces a
    /// REX byte to avoid (`low_byte_reg_needs_rex`): drop that forced REX and
    /// `MOV dil, [..]` silently becomes `MOV bh, [..]`. A decode that flattens
    /// them would leave the obligation blind to it.
    pub reg_is_legacy_high_byte: bool,
    /// The decoded address.
    pub address: DecodedAddress,
    /// Width in bits of the memory ACCESS.
    pub access_bits: u32,
    /// Bytes consumed.
    pub len: usize,
}

/// Why a byte string is not a canonical memory MOV.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MemMovDecodeError {
    /// No bytes.
    Empty,
    /// Ran out of bytes mid-instruction.
    Truncated { field: &'static str },
    /// A second REX prefix.
    DoubledRex,
    /// A legacy prefix AFTER the REX — non-canonical (SDM Vol 2A 2.2.1).
    PrefixAfterRex(u8),
    /// A legacy prefix this family never emits.
    UnexpectedPrefix(u8),
    /// Not one of `8B`/`89`/`8A`/`88`.
    UnknownOpcode(u8),
    /// `mod = 11`: a register-direct form, which has no effective address.
    RegisterDirect,
    /// Bytes left over after a complete instruction.
    TrailingBytes { consumed: usize, total: usize },
    /// A compare-exchange without the `F0` LOCK prefix. The backend emits only
    /// the locked form, so an unlocked one is not a canonical encoding here.
    MissingLock,
    /// `0F C7` with a ModR/M.reg opcode extension other than `/1` (CMPXCHG8B /
    /// CMPXCHG16B), e.g. `/6` (RDRAND).
    OpcodeExtension { opcode: u8, extension: u8 },
}

impl std::fmt::Display for MemMovDecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MemMovDecodeError::Empty => write!(f, "empty byte string"),
            MemMovDecodeError::Truncated { field } => write!(f, "truncated at {field}"),
            MemMovDecodeError::DoubledRex => write!(f, "a second REX prefix"),
            MemMovDecodeError::PrefixAfterRex(b) => {
                write!(f, "legacy prefix {b:#04x} after the REX")
            }
            MemMovDecodeError::UnexpectedPrefix(b) => write!(f, "unexpected prefix {b:#04x}"),
            MemMovDecodeError::UnknownOpcode(b) => write!(f, "opcode {b:#04x} is not a memory MOV"),
            MemMovDecodeError::RegisterDirect => write!(f, "mod=11: no effective address"),
            MemMovDecodeError::TrailingBytes { consumed, total } => {
                write!(f, "{} trailing byte(s)", total - consumed)
            }
            MemMovDecodeError::MissingLock => {
                write!(f, "a compare-exchange without the F0 LOCK prefix")
            }
            MemMovDecodeError::OpcodeExtension { opcode, extension } => {
                write!(f, "0F {opcode:02X} /{extension} is not CMPXCHG8B/16B")
            }
        }
    }
}

const fn is_rex(byte: u8) -> bool {
    byte & 0xF0 == 0x40
}

/// Decode one canonical memory-MOV encoding, per Intel SDM Vol 2A.
///
/// Written from the manual, not from the encoder: the encoder's tables are the
/// object under test, so nothing here may consult them.
pub fn sdm_decode_memory_mov(bytes: &[u8]) -> Result<DecodedMemoryMov, MemMovDecodeError> {
    if bytes.is_empty() {
        return Err(MemMovDecodeError::Empty);
    }
    let mut i = 0usize;

    // Prefixes. `0x66` is an operand-size override for the integer forms and a
    // MANDATORY prefix for the packed ones; `0xF2`/`0xF3` are mandatory
    // prefixes selecting the SSE production (SDM Vol 2A 2.1.1). Which role a
    // byte plays is decided by the OPCODE below, not here.
    // `0xF0` (LOCK) may appear in any position among them (SDM Vol 2A 2.1.1:
    // the legacy prefix groups have no required order); it is recorded rather
    // than kept in `legacy_prefixes`, and whether it is ALLOWED is decided by
    // the opcode too — required for a compare-exchange, refused otherwise.
    let mut legacy_prefixes = Vec::new();
    let mut lock = false;
    while i < bytes.len() && matches!(bytes[i], 0x66 | 0xF2 | 0xF3 | 0xF0) {
        if bytes[i] == 0xF0 {
            if lock {
                return Err(MemMovDecodeError::UnexpectedPrefix(0xF0));
            }
            lock = true;
        } else {
            legacy_prefixes.push(bytes[i]);
        }
        i += 1;
    }
    // Every other prefix is refused by name rather than silently skipped.
    if i < bytes.len() && matches!(bytes[i], 0x2E | 0x36 | 0x3E | 0x26 | 0x64 | 0x65 | 0x67) {
        return Err(MemMovDecodeError::UnexpectedPrefix(bytes[i]));
    }
    if legacy_prefixes.len() > 1 {
        return Err(MemMovDecodeError::UnexpectedPrefix(legacy_prefixes[1]));
    }

    let mut rex = None;
    if i < bytes.len() && is_rex(bytes[i]) {
        rex = Some(bytes[i]);
        i += 1;
        if i < bytes.len() && is_rex(bytes[i]) {
            return Err(MemMovDecodeError::DoubledRex);
        }
        if i < bytes.len() && matches!(bytes[i], 0x66 | 0xF0) {
            return Err(MemMovDecodeError::PrefixAfterRex(bytes[i]));
        }
    }
    let rex_bit = |shift: u32| rex.is_some_and(|r| (r >> shift) & 1 == 1);
    let (rex_w, rex_r, rex_x, rex_b) = (rex_bit(3), rex_bit(2), rex_bit(1), rex_bit(0));

    let has_66 = legacy_prefixes.contains(&0x66);
    let has_f2 = legacy_prefixes.contains(&0xF2);
    let has_f3 = legacy_prefixes.contains(&0xF3);

    let opcode = *bytes
        .get(i)
        .ok_or(MemMovDecodeError::Truncated { field: "opcode" })?;
    i += 1;

    // Two-byte opcodes go through the 0x0F escape (SDM Vol 2A 2.1.2).
    let (mnemonic, access_bits) = if opcode == 0x0F {
        let second = *bytes.get(i).ok_or(MemMovDecodeError::Truncated {
            field: "0F escape opcode",
        })?;
        i += 1;
        match (second, has_f3, has_f2, has_66) {
            // Scalar FP: the mandatory prefix picks single vs double, and with
            // it the ACCESS WIDTH — 4 bytes for MOVSS, 8 for MOVSD.
            (0x10, true, false, false) => (MemMovMnemonic::LoadScalarFp, 32),
            (0x10, false, true, false) => (MemMovMnemonic::LoadScalarFp, 64),
            (0x11, true, false, false) => (MemMovMnemonic::StoreScalarFp, 32),
            (0x11, false, true, false) => (MemMovMnemonic::StoreScalarFp, 64),
            // Packed 128-bit: MOVDQA (66) and MOVDQU (F3) differ in alignment
            // requirement, not in width or address.
            (0x6F, false, false, true) | (0x6F, true, false, false) => {
                (MemMovMnemonic::LoadPacked, 128)
            }
            (0x7F, false, false, true) | (0x7F, true, false, false) => {
                (MemMovMnemonic::StorePacked, 128)
            }
            // IMUL r, r/m.
            (0xAF, false, false, _) => (
                MemMovMnemonic::AluRegMem,
                if rex_w {
                    64
                } else if has_66 {
                    16
                } else {
                    32
                },
            ),
            // MOVZX / MOVSX r, m8 (`B6`/`BE`) and r, m16 (`B7`/`BF`): the opcode
            // byte fixes the ACCESS width. A `0x66` makes the destination 16
            // bits (a merge into the low word, not a zero extension) and the
            // backend never emits it, so it is refused by name; an F2/F3 has
            // no meaning here and is refused too.
            (0xB6 | 0xB7 | 0xBE | 0xBF, false, false, false) => (
                if second == 0xB6 || second == 0xB7 {
                    MemMovMnemonic::LoadGprZeroExtend
                } else {
                    MemMovMnemonic::LoadGprSignExtend
                },
                if second == 0xB6 || second == 0xBE {
                    8
                } else {
                    16
                },
            ),
            (0xB6 | 0xB7 | 0xBE | 0xBF, f3, f2, _) => {
                return Err(MemMovDecodeError::UnexpectedPrefix(if f3 {
                    0xF3
                } else if f2 {
                    0xF2
                } else {
                    0x66
                }));
            }
            // CMPXCHG r/m8, r8 — byte-sized whatever the prefixes say, so a
            // `0x66` is refused rather than ignored (SDM Vol 2A CMPXCHG).
            (0xB0, false, false, false) => (MemMovMnemonic::CompareExchange, 8),
            // CMPXCHG r/m16/32/64, r: REX.W wins, then 0x66, else 32.
            (0xB1, false, false, _) => (
                MemMovMnemonic::CompareExchange,
                if rex_w {
                    64
                } else if has_66 {
                    16
                } else {
                    32
                },
            ),
            // CMPXCHG8B m64 / CMPXCHG16B m128 (`0F C7 /1`): REX.W alone selects
            // the 16-byte form (SDM Vol 2A CMPXCHG8B/CMPXCHG16B); no 66/F2/F3.
            (0xC7, false, false, false) => (
                MemMovMnemonic::CompareExchangeBytes,
                if rex_w { 128 } else { 64 },
            ),
            (other, _, _, _) => return Err(MemMovDecodeError::UnknownOpcode(other)),
        }
    } else {
        // One-byte opcodes. A mandatory SSE prefix has no meaning here, so a
        // stray F2/F3 is refused rather than ignored.
        if has_f2 || has_f3 {
            return Err(MemMovDecodeError::UnexpectedPrefix(if has_f2 {
                0xF2
            } else {
                0xF3
            }));
        }
        let m = match opcode {
            0x8B => MemMovMnemonic::LoadGpr,
            0x89 => MemMovMnemonic::StoreGpr,
            0x8A => MemMovMnemonic::LoadGpr8,
            0x88 => MemMovMnemonic::StoreGpr8,
            // ADD/SUB/CMP r, r/m — memory is the SOURCE.
            0x03 | 0x2B | 0x3B => MemMovMnemonic::AluRegMem,
            // ADD/XOR r/m, r — memory is the DESTINATION.
            0x01 | 0x31 => MemMovMnemonic::AluMemReg,
            // LEA — computes the address, accesses nothing.
            0x8D => MemMovMnemonic::ComputeAddress,
            other => return Err(MemMovDecodeError::UnknownOpcode(other)),
        };
        // Access width, SDM Vol 2A 2.2.1.2: REX.W wins, then 0x66, else 32;
        // the 88/8A pair is byte-sized whatever the prefixes say.
        let w = match m {
            MemMovMnemonic::LoadGpr8 | MemMovMnemonic::StoreGpr8 => 8,
            _ if rex_w => 64,
            _ if has_66 => 16,
            _ => 32,
        };
        (m, w)
    };

    // LOCK belongs to the compare-exchange productions only, and they are
    // accepted only WITH it.
    match (lock, mnemonic.is_compare_exchange()) {
        (true, false) => return Err(MemMovDecodeError::UnexpectedPrefix(0xF0)),
        (false, true) => return Err(MemMovDecodeError::MissingLock),
        _ => {}
    }

    let modrm = *bytes.get(i).ok_or(MemMovDecodeError::Truncated {
        field: "ModR/M byte",
    })?;
    i += 1;
    let mod_field = modrm >> 6;
    let reg_field = (modrm >> 3) & 0b111;
    let rm_field = modrm & 0b111;
    if mnemonic == MemMovMnemonic::CompareExchangeBytes && reg_field != 1 {
        return Err(MemMovDecodeError::OpcodeExtension {
            opcode: 0xC7,
            extension: reg_field,
        });
    }
    let reg_root = reg_field | (u8::from(rex_r) << 3);
    // A byte register named without any REX byte is AH/CH/DH/BH for 4..7: the
    // 88/8A MOVs and the `0F B0` byte CMPXCHG alike.
    let byte_register_operand = matches!(
        mnemonic,
        MemMovMnemonic::LoadGpr8 | MemMovMnemonic::StoreGpr8
    ) || (mnemonic == MemMovMnemonic::CompareExchange
        && access_bits == 8);
    let reg_is_legacy_high_byte =
        byte_register_operand && rex.is_none() && (4..=7).contains(&reg_field);

    let read_disp8 = |i: &mut usize| -> Result<DispField, MemMovDecodeError> {
        let b = *bytes
            .get(*i)
            .ok_or(MemMovDecodeError::Truncated { field: "disp8" })?;
        *i += 1;
        Ok(DispField {
            encoded_bits: 8,
            bytes: vec![b],
            value: i64::from(b as i8),
        })
    };
    let read_disp32 = |i: &mut usize| -> Result<DispField, MemMovDecodeError> {
        if *i + 4 > bytes.len() {
            return Err(MemMovDecodeError::Truncated { field: "disp32" });
        }
        let field = [bytes[*i], bytes[*i + 1], bytes[*i + 2], bytes[*i + 3]];
        let raw = i32::from_le_bytes(field);
        *i += 4;
        Ok(DispField {
            encoded_bits: 32,
            bytes: field.to_vec(),
            value: i64::from(raw),
        })
    };

    let mut sib = None;
    let address = if mod_field == 0b11 {
        return Err(MemMovDecodeError::RegisterDirect);
    } else if rm_field == 0b100 {
        // SIB byte present.
        let sib_byte = *bytes
            .get(i)
            .ok_or(MemMovDecodeError::Truncated { field: "SIB byte" })?;
        i += 1;
        sib = Some(sib_byte);
        let shift = sib_byte >> 6;
        let index_field = (sib_byte >> 3) & 0b111;
        let base_field = sib_byte & 0b111;

        // SDM Vol 2A Table 2-3: index = 100b with REX.X clear means NO index.
        let index_root = if index_field == 0b100 && !rex_x {
            None
        } else {
            Some(index_field | (u8::from(rex_x) << 3))
        };
        // base = 101b with mod = 00 means no base, disp32 follows.
        let (base_root, disp) = if base_field == 0b101 && mod_field == 0b00 {
            (None, read_disp32(&mut i)?)
        } else {
            let root = base_field | (u8::from(rex_b) << 3);
            let disp = match mod_field {
                0b00 => DispField::absent(),
                0b01 => read_disp8(&mut i)?,
                _ => read_disp32(&mut i)?,
            };
            (Some(root), disp)
        };
        DecodedAddress::Sib {
            base_root,
            index_root,
            shift,
            disp,
        }
    } else if rm_field == 0b101 && mod_field == 0b00 {
        DecodedAddress::RipRelative {
            disp: read_disp32(&mut i)?,
        }
    } else {
        let base_root = rm_field | (u8::from(rex_b) << 3);
        let disp = match mod_field {
            0b00 => DispField::absent(),
            0b01 => read_disp8(&mut i)?,
            _ => read_disp32(&mut i)?,
        };
        DecodedAddress::BaseDisp { base_root, disp }
    };

    if i != bytes.len() {
        return Err(MemMovDecodeError::TrailingBytes {
            consumed: i,
            total: bytes.len(),
        });
    }

    Ok(DecodedMemoryMov {
        legacy_prefixes,
        lock,
        rex,
        mnemonic,
        modrm,
        sib,
        reg_root,
        reg_is_legacy_high_byte,
        address,
        access_bits,
        len: i,
    })
}

// ---------------------------------------------------------------------------
// The intent side
// ---------------------------------------------------------------------------

/// What the addressing operand SAYS the access is, independent of any encoding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemAccessIntent {
    /// 64-bit root number of the register operand.
    pub reg_root: u8,
    /// Which register FILE the operand names. `xmm3` and `rbx` are both
    /// ModR/M.reg = 011, so without this the register facet cannot tell a
    /// scalar-FP or packed form from an integer one.
    pub reg_file: RegFile,
    /// 64-bit root number of the base register.
    pub base_root: u8,
    /// 64-bit root of the index register, for SIB forms.
    pub index_root: Option<u8>,
    /// Scale FACTOR (1/2/4/8), not a shift.
    pub scale: u32,
    /// Displacement.
    pub disp: i64,
    /// Width in bits of the access.
    pub access_bits: u32,
    /// Whether memory is the destination.
    pub is_store: bool,
    /// Whether the access is the ZERO-EXTENDING load (`movzx r32, m8/m16`),
    /// which writes the whole destination with the loaded bytes zero-extended,
    /// rather than a MOV that merges a narrow value into the register's old
    /// bits. False for every store, every MOV load, and every non-GPR form.
    pub zero_extending_load: bool,
}

// ---------------------------------------------------------------------------
// Denotations
// ---------------------------------------------------------------------------

/// Stable SMT leaf for a 64-bit register root. Keying the leaf by the ROOT
/// NUMBER is what gives the obligation its teeth: if the encoder wrote a
/// different base or index register than the operand named, the decoded side
/// binds a DIFFERENT leaf and the two denotations separate.
#[must_use]
pub fn reg_leaf(root: u8) -> SmtExpr {
    SmtExpr::var(format!("addr_r{root}"), ADDR_BITS)
}

/// The SOURCE denotation: `base + index*scale + disp`, read off the INTENT.
///
/// Composed the way a trust_ir address chain composes — a MULTIPLY by the scale
/// factor — so that it is structurally distinct from the machine reading below.
#[must_use]
pub fn intent_address_denotation(intent: &MemAccessIntent) -> SmtExpr {
    let base = reg_leaf(intent.base_root);
    let scaled = intent
        .index_root
        .map(|index| reg_leaf(index).bvmul(SmtExpr::bv_const(u64::from(intent.scale), ADDR_BITS)));
    let sum = match scaled {
        Some(scaled) => base.bvadd(scaled),
        None => base,
    };
    sum.bvadd(SmtExpr::bv_const(intent.disp as u64, ADDR_BITS))
}

/// The MACHINE denotation: `base + (index << shift) + disp`, read off the
/// DECODED bytes.
///
/// A SHIFT, because that is literally what the SIB byte stores (SDM Vol 2A
/// Table 2-3). The association is also deliberately the other way round from
/// the intent side. Both choices keep this expression structurally DISTINCT
/// from [`intent_address_denotation`], so a passing comparison is a real
/// agreement between two different readings rather than a tree compared with
/// itself.
///
/// Returns `None` for a form that denotes no static address (RIP-relative,
/// register-direct), which fails closed rather than being scored.
#[must_use]
pub fn decoded_address_denotation(address: &DecodedAddress) -> Option<SmtExpr> {
    match address {
        DecodedAddress::RegisterDirect { .. } | DecodedAddress::RipRelative { .. } => None,
        DecodedAddress::BaseDisp { base_root, disp } => Some(match disp.denotation() {
            Some(d) => reg_leaf(*base_root).bvadd(d),
            // mod=00: no displacement field, so the address IS the base.
            None => reg_leaf(*base_root),
        }),
        DecodedAddress::Sib {
            base_root,
            index_root,
            shift,
            disp,
        } => {
            let scaled = index_root.map(|index| {
                reg_leaf(index).bvshl(SmtExpr::bv_const(u64::from(*shift), ADDR_BITS))
            });
            // An absent displacement contributes NO term, exactly as it
            // contributes no bytes.
            let tail = match (scaled, disp.denotation()) {
                (Some(scaled), Some(d)) => Some(scaled.bvadd(d)),
                (Some(scaled), None) => Some(scaled),
                (None, Some(d)) => Some(d),
                (None, None) => None,
            };
            Some(match (base_root, tail) {
                (Some(base), Some(tail)) => reg_leaf(*base).bvadd(tail),
                (Some(base), None) => reg_leaf(*base),
                (None, Some(tail)) => tail,
                // No base, no index, no displacement encodes nothing.
                (None, None) => return None,
            })
        }
    }
}

// ---------------------------------------------------------------------------
// Witness rows
// ---------------------------------------------------------------------------

/// How many concrete register environments every address comparison runs over.
pub const WITNESS_ROWS: usize = 24;

/// A deterministic, well-spread value for register `root` in `row`.
///
/// Spread matters: registers must not share values, or a base/index SWAP would
/// evaluate equal and the control would not refute. The mix below gives every
/// root a distinct, row-dependent value including high-bit and small cases.
#[must_use]
pub fn witness_reg_value(row: usize, root: u8) -> u64 {
    let r = row as u64;
    let k = u64::from(root);
    match row % 4 {
        0 => 0x1000u64
            .wrapping_mul(k + 1)
            .wrapping_add(r.wrapping_mul(0x21))
            .wrapping_add(1),
        1 => (0x8000_0000_0000_0000u64)
            .wrapping_add(k.wrapping_mul(0x37))
            .wrapping_add(r),
        2 => k.wrapping_mul(0x0101_0101_0101_0101).wrapping_add(r | 1),
        _ => !0u64 ^ k.wrapping_mul(0x5DEE_CE66).wrapping_add(r),
    }
}

fn witness_env(row: usize) -> &'static EvalEnv {
    static ENVS: std::sync::OnceLock<Vec<EvalEnv>> = std::sync::OnceLock::new();
    &ENVS.get_or_init(|| {
        (0..WITNESS_ROWS)
            .map(|row| {
                let mut env = EvalEnv::default();
                for root in 0u8..16 {
                    env.insert(format!("addr_r{root}"), witness_reg_value(row, root));
                }
                env
            })
            .collect()
    })[row]
}

// ---------------------------------------------------------------------------
// The comparison
// ---------------------------------------------------------------------------

/// Why an address obligation was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AddressRefutation {
    /// The two sides are the SAME tree. The whole point of this module is that
    /// this must never happen; it is the defect it was written to replace.
    Degenerate,
    /// The decode itself rejected the bytes.
    Undecodable(MemMovDecodeError),
    /// The decoded form denotes no static address.
    NoStaticAddress,
    /// A side could not be evaluated in a witness environment.
    Unevaluable { row: usize, detail: String },
    /// The addresses disagree in some row.
    Address {
        row: usize,
        source: u64,
        machine: u64,
    },
    /// The decoded register operand is not the intended one.
    RegisterOperand { expected: u8, decoded: u8 },
    /// The decoded access width is not the intended one.
    AccessWidth { expected: u32, decoded: u32 },
    /// The bytes name a LEGACY HIGH-BYTE register (AH/CH/DH/BH). The machine
    /// IR has no such operand, so an intent can never mean one: the encoding
    /// dropped a REX byte that was load-bearing.
    LegacyHighByteRegister { reg_field: u8 },
    /// The bytes name a register in a different FILE than the intent did — an
    /// XMM register where a GPR was meant, or the reverse.
    RegisterFile { expected: RegFile, decoded: RegFile },
    /// The decoded direction (load vs store) is not the intended one.
    Direction { expected: bool, decoded: bool },
    /// The decoded production is (or is not) the zero-extending load the
    /// intent names: a `movzx r32, m8` encoded as `mov r8, m8` merges into the
    /// register's old bits, and the reverse discards them.
    Extension { expected: bool, decoded: bool },
    /// The DESTINATION the decoded production writes is not the zero-extended
    /// access value the intent names, in witness row `row`.
    DestinationWrite {
        row: usize,
        intended: u64,
        encoded: u64,
    },
    /// The bytes are not a GPR load whose destination write the SDM fixes.
    NoDestinationWrite,
}

impl std::fmt::Display for AddressRefutation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AddressRefutation::Degenerate => {
                write!(f, "the source and machine addresses are the SAME tree")
            }
            AddressRefutation::Undecodable(e) => write!(f, "undecodable: {e}"),
            AddressRefutation::NoStaticAddress => write!(f, "no static effective address"),
            AddressRefutation::Unevaluable { row, detail } => {
                write!(f, "row {row}: {detail}")
            }
            AddressRefutation::Address {
                row,
                source,
                machine,
            } => write!(
                f,
                "row {row}: intended address {source:#018x} != encoded address {machine:#018x}"
            ),
            AddressRefutation::RegisterOperand { expected, decoded } => write!(
                f,
                "register operand: intended root {expected}, encoded root {decoded}"
            ),
            AddressRefutation::AccessWidth { expected, decoded } => {
                write!(f, "access width: intended {expected}, encoded {decoded}")
            }
            AddressRefutation::LegacyHighByteRegister { reg_field } => write!(
                f,
                "ModR/M.reg {reg_field} with no REX names a legacy high-byte register \
                 (AH/CH/DH/BH), which no machine-IR operand denotes"
            ),
            AddressRefutation::RegisterFile { expected, decoded } => write!(
                f,
                "register file: intended {expected:?}, encoded {decoded:?}"
            ),
            AddressRefutation::Direction { expected, decoded } => write!(
                f,
                "direction: intended is_store={expected}, encoded is_store={decoded}"
            ),
            AddressRefutation::Extension { expected, decoded } => write!(
                f,
                "extension: intended zero_extending_load={expected}, encoded \
                 zero_extending_load={decoded}"
            ),
            AddressRefutation::DestinationWrite {
                row,
                intended,
                encoded,
            } => write!(
                f,
                "row {row}: intended destination {intended:#018x} != encoded destination \
                 {encoded:#018x}"
            ),
            AddressRefutation::NoDestinationWrite => {
                write!(
                    f,
                    "the bytes are not a GPR load with an SDM destination write"
                )
            }
        }
    }
}

/// What a successful address comparison established.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AddressOutcome {
    /// Witness rows compared.
    pub rows: usize,
    /// Rows whose address had the high bit set.
    pub high_rows: usize,
}

/// Compare the INTENDED address against the address ENCODED in `bytes`.
///
/// Refuses a structurally identical pair up front — the defect this module
/// exists to replace — then requires agreement in every witness row, and
/// requires the witness set to exercise both high-bit and low addresses so a
/// passing comparison is not an artifact of a narrow environment.
pub fn address_encoding_holds(
    bytes: &[u8],
    intent: &MemAccessIntent,
) -> Result<AddressOutcome, AddressRefutation> {
    let decoded = sdm_decode_memory_mov(bytes).map_err(AddressRefutation::Undecodable)?;

    if decoded.mnemonic.reg_file() != intent.reg_file {
        return Err(AddressRefutation::RegisterFile {
            expected: intent.reg_file,
            decoded: decoded.mnemonic.reg_file(),
        });
    }
    if decoded.reg_is_legacy_high_byte {
        return Err(AddressRefutation::LegacyHighByteRegister {
            reg_field: decoded.reg_root,
        });
    }
    if decoded.reg_root != intent.reg_root {
        return Err(AddressRefutation::RegisterOperand {
            expected: intent.reg_root,
            decoded: decoded.reg_root,
        });
    }
    if decoded.access_bits != intent.access_bits {
        return Err(AddressRefutation::AccessWidth {
            expected: intent.access_bits,
            decoded: decoded.access_bits,
        });
    }
    if decoded.mnemonic.is_store() != intent.is_store {
        return Err(AddressRefutation::Direction {
            expected: intent.is_store,
            decoded: decoded.mnemonic.is_store(),
        });
    }
    if decoded.mnemonic.zero_extends() != intent.zero_extending_load {
        return Err(AddressRefutation::Extension {
            expected: intent.zero_extending_load,
            decoded: decoded.mnemonic.zero_extends(),
        });
    }

    let source = intent_address_denotation(intent);
    let machine =
        decoded_address_denotation(&decoded.address).ok_or(AddressRefutation::NoStaticAddress)?;

    if source == machine {
        return Err(AddressRefutation::Degenerate);
    }

    let mut high_rows = 0usize;
    for row in 0..WITNESS_ROWS {
        let env = witness_env(row);
        let s = source
            .try_eval(env)
            .map_err(|e| AddressRefutation::Unevaluable {
                row,
                detail: format!("source side: {e}"),
            })?
            .as_u64();
        let m = machine
            .try_eval(env)
            .map_err(|e| AddressRefutation::Unevaluable {
                row,
                detail: format!("machine side: {e}"),
            })?
            .as_u64();
        if s & 0x8000_0000_0000_0000 != 0 {
            high_rows += 1;
        }
        if s != m {
            return Err(AddressRefutation::Address {
                row,
                source: s,
                machine: m,
            });
        }
    }

    Ok(AddressOutcome {
        rows: WITNESS_ROWS,
        high_rows,
    })
}

/// Compare two address denotations directly: the degeneracy guard and the
/// witness sweep, without a decode.
///
/// Exposed so the gate can exercise the ANTI-VACUITY guard in both directions —
/// that a source-equals-machine pairing (the shape
/// `x86_reconstruct_effective_address` produced for every memory row) is
/// REFUSED, and that a genuinely distinct pairing is not refused for that
/// reason. Without deciding it both ways the guard could be stuck returning
/// `Degenerate`, and the lane would look strict while proving nothing.
pub fn compare_addresses_for_test(
    source: &SmtExpr,
    machine: &SmtExpr,
) -> Result<AddressOutcome, AddressRefutation> {
    if source == machine {
        return Err(AddressRefutation::Degenerate);
    }
    let mut high_rows = 0usize;
    for row in 0..WITNESS_ROWS {
        let env = witness_env(row);
        let s = source
            .try_eval(env)
            .map_err(|e| AddressRefutation::Unevaluable {
                row,
                detail: format!("source side: {e}"),
            })?
            .as_u64();
        let m = machine
            .try_eval(env)
            .map_err(|e| AddressRefutation::Unevaluable {
                row,
                detail: format!("machine side: {e}"),
            })?
            .as_u64();
        if s & 0x8000_0000_0000_0000 != 0 {
            high_rows += 1;
        }
        if s != m {
            return Err(AddressRefutation::Address {
                row,
                source: s,
                machine: m,
            });
        }
    }
    Ok(AddressOutcome {
        rows: WITNESS_ROWS,
        high_rows,
    })
}

// ===========================================================================
// The DESTINATION-WRITE facet of a GPR load
// ===========================================================================
//
// The address lane above says WHERE an access reads. For the zero-extending
// loads it must also say WHAT the destination register holds afterwards,
// because that is the whole difference between `movzx r32, m8` (`0F B6`) and
// `mov r8, m8` (`8A`): both read the same byte at the same address, and only
// the first defines bits 8..63 (as zero). A backend that emitted `8A` for a
// `MovzxRM8` would pass every address, register, width and direction check and
// leave stale register bits under a value its consumers read as zero-extended.
//
// SOURCE is the intent: the access value, unsigned, at 64 bits, composed as a
// CONCATENATION of a zero constant above the loaded bits.
//
// MACHINE is the SDM's destination rule for the DECODED production (Vol 1
// 3.4.1.1; Vol 2B MOV/MOVZX/MOVSX): an 8/16-bit MOV keeps the register's old
// bits above its result, a 32-bit result is zero-extended into the 64-bit
// register, a 64-bit one is the whole register, MOVZX zero-extends and MOVSX
// sign-extends to its operand size. Composed with ZERO_EXT / SIGN_EXT /
// EXTRACT+CONCAT over a leaf for the register's OLD value, so it is
// structurally distinct from the source side, and only a production that
// discards the old bits AND zero-fills agrees with the intent in every row.

/// What a GPR load leaves in its 64-bit destination register, per the SDM.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DestinationWrite {
    /// Bits `0..bits` are the access value; bits `bits..64` keep the
    /// register's old contents (an 8- or 16-bit MOV result).
    MergeLow { bits: u32 },
    /// The whole register: the access value zero-extended from `from_bits`
    /// (a 32-bit MOV result, a 64-bit MOV with `from_bits == 64`, or MOVZX).
    ZeroExtend { from_bits: u32 },
    /// The access value sign-extended from `from_bits` to the `to_bits`-bit
    /// operand size, then (for a 32-bit operand) zero-extended to 64 bits.
    SignExtend { from_bits: u32, to_bits: u32 },
}

/// The destination rule of a decoded GPR LOAD, or `None` for anything else (a
/// store, LEA, an ALU or SSE form, a compare-exchange).
#[must_use]
pub fn gpr_load_destination_write(decoded: &DecodedMemoryMov) -> Option<DestinationWrite> {
    let rex_w = decoded.rex.is_some_and(|rex| rex & 0b1000 != 0);
    match decoded.mnemonic {
        MemMovMnemonic::LoadGpr8 => Some(DestinationWrite::MergeLow { bits: 8 }),
        MemMovMnemonic::LoadGpr => Some(match decoded.access_bits {
            16 => DestinationWrite::MergeLow { bits: 16 },
            bits => DestinationWrite::ZeroExtend { from_bits: bits },
        }),
        // MOVZX with or without REX.W: a 32-bit destination zero-extends its
        // result into bits 32..63 and a 64-bit one is written whole, so the
        // register holds the same value either way (the decoder refuses the
        // 0x66 form, the one that would merge).
        MemMovMnemonic::LoadGprZeroExtend => Some(DestinationWrite::ZeroExtend {
            from_bits: decoded.access_bits,
        }),
        MemMovMnemonic::LoadGprSignExtend => Some(DestinationWrite::SignExtend {
            from_bits: decoded.access_bits,
            to_bits: if rex_w { 64 } else { 32 },
        }),
        _ => None,
    }
}

/// The 64-bit register leaf for a load destination's OLD value.
#[must_use]
pub fn destination_old_leaf() -> SmtExpr {
    SmtExpr::var("dst_old", ADDR_BITS)
}

/// The eight bytes at the effective address, little-endian, as one leaf.
#[must_use]
pub fn memory_qword_leaf() -> SmtExpr {
    SmtExpr::var("mem_qword", ADDR_BITS)
}

/// The value an access of `bits` bits reads: the low `bits` of the bytes at
/// the effective address (x86 is little-endian). A production that reads a
/// different width reads different bytes of the SAME leaf, so a byte load
/// encoded as a word load refutes whenever the next byte is nonzero.
#[must_use]
pub fn access_value_leaf(bits: u32) -> SmtExpr {
    if bits >= ADDR_BITS {
        memory_qword_leaf()
    } else {
        memory_qword_leaf().extract(bits - 1, 0)
    }
}

/// The MACHINE denotation of a load's destination after it executes.
#[must_use]
pub fn machine_destination_denotation(write: DestinationWrite) -> SmtExpr {
    match write {
        DestinationWrite::MergeLow { bits } => destination_old_leaf()
            .extract(ADDR_BITS - 1, bits)
            .concat(access_value_leaf(bits)),
        DestinationWrite::ZeroExtend { from_bits } if from_bits >= ADDR_BITS => {
            access_value_leaf(ADDR_BITS)
        }
        DestinationWrite::ZeroExtend { from_bits } => {
            access_value_leaf(from_bits).zero_ext(ADDR_BITS - from_bits)
        }
        DestinationWrite::SignExtend { from_bits, to_bits } => {
            let extended = access_value_leaf(from_bits).sign_ext(to_bits - from_bits);
            if to_bits < ADDR_BITS {
                extended.zero_ext(ADDR_BITS - to_bits)
            } else {
                extended
            }
        }
    }
}

/// The SOURCE denotation of a zero-extending load's destination: the access
/// value, unsigned, at 64 bits — `0 ++ value`, a concatenation, so that it is
/// never the same tree as the machine side's `zero_ext`.
#[must_use]
pub fn intent_destination_denotation(access_bits: u32) -> SmtExpr {
    SmtExpr::bv_const(0, ADDR_BITS - access_bits).concat(access_value_leaf(access_bits))
}

/// The OLD destination values every destination comparison runs over: zero,
/// all-ones and two patterns with every byte nonzero, so a production that
/// keeps any old bit is caught.
pub const DESTINATION_OLD_VALUES: [u64; 4] =
    [0, u64::MAX, 0xA5A5_A5A5_A5A5_A5A5, 0x0123_4567_89AB_CDEF];

/// The memory contents (the eight bytes at the effective address) every
/// destination comparison runs over: zero, small values, both sides of the
/// byte and word sign bits, all-ones, and patterns whose bytes above the
/// access are nonzero, so a sign extension, a merge and a wider or narrower
/// access are each caught.
pub const DESTINATION_MEMORY_VALUES: [u64; 12] = [
    0,
    1,
    0x7F,
    0x80,
    0xFF,
    0x7FFF,
    0x8000,
    0xFFFF,
    u64::MAX,
    0xA5A5_A5A5_A5A5_A5A5,
    0x0123_4567_89AB_CDEF,
    0x5A5A_5A5A_5A5A_5A80,
];

/// What a successful destination comparison established.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DestinationOutcome {
    /// Witness rows compared.
    pub rows: usize,
    /// Rows whose old destination had bits set above the access width.
    pub dirty_rows: usize,
    /// Rows whose access value had its top bit set.
    pub signed_rows: usize,
}

/// Compare an intended destination against a machine one over the witness
/// family, refusing a structurally identical pair up front.
pub fn compare_destinations(
    source: &SmtExpr,
    machine: &SmtExpr,
    access_bits: u32,
) -> Result<DestinationOutcome, AddressRefutation> {
    if source == machine {
        return Err(AddressRefutation::Degenerate);
    }
    let mut rows = 0usize;
    let mut dirty_rows = 0usize;
    let mut signed_rows = 0usize;
    for old in DESTINATION_OLD_VALUES {
        for value in DESTINATION_MEMORY_VALUES {
            let mut env = EvalEnv::default();
            env.insert("dst_old".to_string(), old);
            env.insert("mem_qword".to_string(), value);
            let eval = |side: &SmtExpr, which: &str| {
                side.try_eval(&env).map(|r| r.as_u64()).map_err(|e| {
                    AddressRefutation::Unevaluable {
                        row: rows,
                        detail: format!("{which} side: {e}"),
                    }
                })
            };
            let intended = eval(source, "source")?;
            let encoded = eval(machine, "machine")?;
            if access_bits < ADDR_BITS && old >> access_bits != 0 {
                dirty_rows += 1;
            }
            if (value >> (access_bits - 1)) & 1 == 1 {
                signed_rows += 1;
            }
            if intended != encoded {
                return Err(AddressRefutation::DestinationWrite {
                    row: rows,
                    intended,
                    encoded,
                });
            }
            rows += 1;
        }
    }
    Ok(DestinationOutcome {
        rows,
        dirty_rows,
        signed_rows,
    })
}

/// The DESTINATION obligation of a zero-extending load: the register the
/// decoded bytes leave behind is the access value zero-extended to 64 bits, in
/// every witness row, whatever the register held before.
///
/// Refuses an intent that is not a zero-extending GPR load (there is no
/// destination claim to check), bytes that are not a GPR load, and a witness
/// family that never exercised a dirty old register or a set top bit.
pub fn destination_write_holds(
    bytes: &[u8],
    intent: &MemAccessIntent,
) -> Result<DestinationOutcome, AddressRefutation> {
    let decoded = sdm_decode_memory_mov(bytes).map_err(AddressRefutation::Undecodable)?;
    if !intent.zero_extending_load || intent.is_store || intent.reg_file != RegFile::Gpr {
        return Err(AddressRefutation::NoDestinationWrite);
    }
    let write =
        gpr_load_destination_write(&decoded).ok_or(AddressRefutation::NoDestinationWrite)?;
    if decoded.access_bits != intent.access_bits {
        return Err(AddressRefutation::AccessWidth {
            expected: intent.access_bits,
            decoded: decoded.access_bits,
        });
    }
    let source = intent_destination_denotation(intent.access_bits);
    let machine = machine_destination_denotation(write);
    let outcome = compare_destinations(&source, &machine, intent.access_bits)?;
    if outcome.dirty_rows == 0 || outcome.signed_rows == 0 {
        return Err(AddressRefutation::Unevaluable {
            row: outcome.rows,
            detail: "the destination witnesses never set an old bit above the access or the \
                     access's top bit, so a merge or a sign extension could not refute"
                .to_string(),
        });
    }
    Ok(outcome)
}

/// The WRONG destination models every zero-extending entry must refute,
/// each run through [`compare_destinations`] against the entry's own intent.
/// A model that holds would mean the comparison cannot tell that production
/// from the one the encoder must emit.
#[must_use]
pub fn destination_model_controls(access_bits: u32) -> Vec<(&'static str, DestinationWrite)> {
    let other_width = if access_bits == 8 { 16 } else { 8 };
    vec![
        (
            "merging MOV (old bits kept above the access)",
            DestinationWrite::MergeLow { bits: access_bits },
        ),
        (
            "sign extension to 64 bits",
            DestinationWrite::SignExtend {
                from_bits: access_bits,
                to_bits: 64,
            },
        ),
        (
            "sign extension to 32 bits, then zero-extended",
            DestinationWrite::SignExtend {
                from_bits: access_bits,
                to_bits: 32,
            },
        ),
        (
            "zero extension from the other access width",
            DestinationWrite::ZeroExtend {
                from_bits: other_width,
            },
        ),
    ]
}

// ===========================================================================
// The captured corpus and the credit hook
// ===========================================================================

/// One CAPTURED memory-MOV encoding: the bytes the real encoder produced, and
/// the intent it was asked to encode.
///
/// The bytes are a capture because `trust-cg-verify` cannot call
/// `trust-cg-codegen` — that crate depends on this one, so it is a
/// DEV-dependency and only in tests. A capture can rot, so
/// `tests/support/x86_addressing_live_encode.rs` re-derives every entry from
/// the LIVE encoder and requires byte identity, and the targets that PIN the
/// published ratio repeat that re-derivation. A pinned ratio must never stand
/// on bytes the backend no longer emits.
#[derive(Debug, Clone, Copy)]
pub struct CapturedMemMov {
    /// Human-readable spelling, for diagnostics.
    pub label: &'static str,
    /// 64-bit root of the register operand.
    pub reg_root: u8,
    /// Which register file the operand names.
    pub reg_file: RegFile,
    /// 64-bit root of the base register.
    pub base_root: u8,
    /// 64-bit root of the index register, for SIB forms.
    pub index_root: Option<u8>,
    /// Scale FACTOR (1/2/4/8).
    pub scale: u32,
    /// Displacement.
    pub disp: i64,
    /// Access width in bits.
    pub access_bits: u32,
    /// Whether memory is the destination.
    pub is_store: bool,
    /// Whether this is the zero-extending load (`movzx r32, m8/m16`).
    pub zero_extending_load: bool,
    /// The bytes the live encoder emitted.
    pub bytes: &'static [u8],
}

impl CapturedMemMov {
    /// The intent this entry was encoded from.
    #[must_use]
    pub fn intent(&self) -> MemAccessIntent {
        MemAccessIntent {
            reg_root: self.reg_root,
            reg_file: self.reg_file,
            base_root: self.base_root,
            index_root: self.index_root,
            scale: self.scale,
            disp: self.disp,
            access_bits: self.access_bits,
            is_store: self.is_store,
            zero_extending_load: self.zero_extending_load,
        }
    }
}

/// Every integer memory-MOV encoding this lane is credited over.
pub const EMITTED_X86_MEM_MOV: &[CapturedMemMov] = &[
    CapturedMemMov {
        label: "MovRM rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x8b, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "MovRM r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4d, 0x8b, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "MovRM rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x8b, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "MovRM rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x8b, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovRM r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4d, 0x8b, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovRM rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x8b, 0x03],
    },
    CapturedMemMov {
        label: "MovRM32 rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8b, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "MovRM32 r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x45, 0x8b, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "MovRM32 rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8b, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "MovRM32 rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8b, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovRM32 r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x45, 0x8b, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovRM32 rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8b, 0x03],
    },
    CapturedMemMov {
        label: "MovRM16 rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 16,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x8b, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "MovRM16 r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 16,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x45, 0x8b, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "MovRM16 rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 16,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x8b, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "MovRM16 rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 16,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x8b, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovRM16 r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 16,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x45, 0x8b, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovRM16 rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 16,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x8b, 0x03],
    },
    CapturedMemMov {
        label: "MovRM8 rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 8,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8a, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "MovRM8 r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 8,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x45, 0x8a, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "MovRM8 rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 8,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8a, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "MovRM8 rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 8,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8a, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovRM8 r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 8,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x45, 0x8a, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovRM8 rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 8,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8a, 0x03],
    },
    CapturedMemMov {
        label: "MovMR rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x89, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "MovMR r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x4d, 0x89, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "MovMR rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x89, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "MovMR rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x89, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovMR r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x4d, 0x89, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovMR rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x89, 0x03],
    },
    CapturedMemMov {
        label: "MovMR32 rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x89, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "MovMR32 r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x45, 0x89, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "MovMR32 rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x89, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "MovMR32 rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x89, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovMR32 r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x45, 0x89, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovMR32 rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x89, 0x03],
    },
    CapturedMemMov {
        label: "MovMR16 rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 16,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x89, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "MovMR16 r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 16,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x45, 0x89, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "MovMR16 rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 16,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x89, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "MovMR16 rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 16,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x89, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovMR16 r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 16,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x45, 0x89, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovMR16 rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 16,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x89, 0x03],
    },
    CapturedMemMov {
        label: "MovMR8 rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x88, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "MovMR8 r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x45, 0x88, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "MovMR8 rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x88, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "MovMR8 rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x88, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovMR8 r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x45, 0x88, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovMR8 rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x88, 0x03],
    },
    CapturedMemMov {
        label: "MovRMSib rax,[rbx+rcx*8+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 8,
        disp: 16,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x8b, 0x44, 0xcb, 0x10],
    },
    CapturedMemMov {
        label: "MovRMSib r12,[r13+r14*4-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: Some(14),
        scale: 4,
        disp: -8,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4f, 0x8b, 0x64, 0xb5, 0xf8],
    },
    CapturedMemMov {
        label: "MovRMSib rdx,[rbp+rsi*1+0]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: Some(6),
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x8b, 0x54, 0x35, 0x00],
    },
    CapturedMemMov {
        label: "MovRMSib rdi,[rsp+rbx*2+4096]",
        reg_root: 7,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: Some(3),
        scale: 2,
        disp: 4096,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x8b, 0xbc, 0x5c, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovRMSib r8,[r9+r10*8-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: Some(10),
        scale: 8,
        disp: -129,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4f, 0x8b, 0x84, 0xd1, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovRMSib rcx,[r12+r15*4+127]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 12,
        index_root: Some(15),
        scale: 4,
        disp: 127,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4b, 0x8b, 0x4c, 0xbc, 0x7f],
    },
    CapturedMemMov {
        label: "MovRMSib rax,[rbx+rcx*4+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 4,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x8b, 0x04, 0x8b],
    },
    CapturedMemMov {
        label: "MovRMSib rax,[rbx+r12*4+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(12),
        scale: 4,
        disp: 16,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4a, 0x8b, 0x44, 0xa3, 0x10],
    },
    CapturedMemMov {
        label: "MovRM32Sib rax,[rbx+rcx*8+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 8,
        disp: 16,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8b, 0x44, 0xcb, 0x10],
    },
    CapturedMemMov {
        label: "MovRM32Sib r12,[r13+r14*4-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: Some(14),
        scale: 4,
        disp: -8,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x47, 0x8b, 0x64, 0xb5, 0xf8],
    },
    CapturedMemMov {
        label: "MovRM32Sib rdx,[rbp+rsi*1+0]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: Some(6),
        scale: 1,
        disp: 0,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8b, 0x54, 0x35, 0x00],
    },
    CapturedMemMov {
        label: "MovRM32Sib rdi,[rsp+rbx*2+4096]",
        reg_root: 7,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: Some(3),
        scale: 2,
        disp: 4096,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8b, 0xbc, 0x5c, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovRM32Sib r8,[r9+r10*8-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: Some(10),
        scale: 8,
        disp: -129,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x47, 0x8b, 0x84, 0xd1, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovRM32Sib rcx,[r12+r15*4+127]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 12,
        index_root: Some(15),
        scale: 4,
        disp: 127,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x43, 0x8b, 0x4c, 0xbc, 0x7f],
    },
    CapturedMemMov {
        label: "MovRM32Sib rax,[rbx+rcx*4+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 4,
        disp: 0,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8b, 0x04, 0x8b],
    },
    CapturedMemMov {
        label: "MovRM32Sib rax,[rbx+r12*4+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(12),
        scale: 4,
        disp: 16,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x42, 0x8b, 0x44, 0xa3, 0x10],
    },
    CapturedMemMov {
        label: "MovRM8Sib rax,[rbx+rcx*8+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 8,
        disp: 16,
        access_bits: 8,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8a, 0x44, 0xcb, 0x10],
    },
    CapturedMemMov {
        label: "MovRM8Sib r12,[r13+r14*4-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: Some(14),
        scale: 4,
        disp: -8,
        access_bits: 8,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x47, 0x8a, 0x64, 0xb5, 0xf8],
    },
    CapturedMemMov {
        label: "MovRM8Sib rdx,[rbp+rsi*1+0]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: Some(6),
        scale: 1,
        disp: 0,
        access_bits: 8,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8a, 0x54, 0x35, 0x00],
    },
    CapturedMemMov {
        label: "MovRM8Sib rdi,[rsp+rbx*2+4096]",
        reg_root: 7,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: Some(3),
        scale: 2,
        disp: 4096,
        access_bits: 8,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x40, 0x8a, 0xbc, 0x5c, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovRM8Sib r8,[r9+r10*8-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: Some(10),
        scale: 8,
        disp: -129,
        access_bits: 8,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x47, 0x8a, 0x84, 0xd1, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovRM8Sib rcx,[r12+r15*4+127]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 12,
        index_root: Some(15),
        scale: 4,
        disp: 127,
        access_bits: 8,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x43, 0x8a, 0x4c, 0xbc, 0x7f],
    },
    CapturedMemMov {
        label: "MovRM8Sib rax,[rbx+rcx*4+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 4,
        disp: 0,
        access_bits: 8,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8a, 0x04, 0x8b],
    },
    CapturedMemMov {
        label: "MovRM8Sib rax,[rbx+r12*4+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(12),
        scale: 4,
        disp: 16,
        access_bits: 8,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x42, 0x8a, 0x44, 0xa3, 0x10],
    },
    CapturedMemMov {
        label: "MovMRSib rax,[rbx+rcx*8+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 8,
        disp: 16,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x89, 0x44, 0xcb, 0x10],
    },
    CapturedMemMov {
        label: "MovMRSib r12,[r13+r14*4-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: Some(14),
        scale: 4,
        disp: -8,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x4f, 0x89, 0x64, 0xb5, 0xf8],
    },
    CapturedMemMov {
        label: "MovMRSib rdx,[rbp+rsi*1+0]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: Some(6),
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x89, 0x54, 0x35, 0x00],
    },
    CapturedMemMov {
        label: "MovMRSib rdi,[rsp+rbx*2+4096]",
        reg_root: 7,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: Some(3),
        scale: 2,
        disp: 4096,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x89, 0xbc, 0x5c, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovMRSib r8,[r9+r10*8-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: Some(10),
        scale: 8,
        disp: -129,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x4f, 0x89, 0x84, 0xd1, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovMRSib rcx,[r12+r15*4+127]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 12,
        index_root: Some(15),
        scale: 4,
        disp: 127,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x4b, 0x89, 0x4c, 0xbc, 0x7f],
    },
    CapturedMemMov {
        label: "MovMRSib rax,[rbx+rcx*4+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 4,
        disp: 0,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x89, 0x04, 0x8b],
    },
    CapturedMemMov {
        label: "MovMRSib rax,[rbx+r12*4+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(12),
        scale: 4,
        disp: 16,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x4a, 0x89, 0x44, 0xa3, 0x10],
    },
    CapturedMemMov {
        label: "MovMR32Sib rax,[rbx+rcx*8+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 8,
        disp: 16,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x89, 0x44, 0xcb, 0x10],
    },
    CapturedMemMov {
        label: "MovMR32Sib r12,[r13+r14*4-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: Some(14),
        scale: 4,
        disp: -8,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x47, 0x89, 0x64, 0xb5, 0xf8],
    },
    CapturedMemMov {
        label: "MovMR32Sib rdx,[rbp+rsi*1+0]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: Some(6),
        scale: 1,
        disp: 0,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x89, 0x54, 0x35, 0x00],
    },
    CapturedMemMov {
        label: "MovMR32Sib rdi,[rsp+rbx*2+4096]",
        reg_root: 7,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: Some(3),
        scale: 2,
        disp: 4096,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x89, 0xbc, 0x5c, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovMR32Sib r8,[r9+r10*8-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: Some(10),
        scale: 8,
        disp: -129,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x47, 0x89, 0x84, 0xd1, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovMR32Sib rcx,[r12+r15*4+127]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 12,
        index_root: Some(15),
        scale: 4,
        disp: 127,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x43, 0x89, 0x4c, 0xbc, 0x7f],
    },
    CapturedMemMov {
        label: "MovMR32Sib rax,[rbx+rcx*4+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 4,
        disp: 0,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x89, 0x04, 0x8b],
    },
    CapturedMemMov {
        label: "MovMR32Sib rax,[rbx+r12*4+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(12),
        scale: 4,
        disp: 16,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x42, 0x89, 0x44, 0xa3, 0x10],
    },
    CapturedMemMov {
        label: "MovMR8Sib rax,[rbx+rcx*8+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 8,
        disp: 16,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x88, 0x44, 0xcb, 0x10],
    },
    CapturedMemMov {
        label: "MovMR8Sib r12,[r13+r14*4-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: Some(14),
        scale: 4,
        disp: -8,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x47, 0x88, 0x64, 0xb5, 0xf8],
    },
    CapturedMemMov {
        label: "MovMR8Sib rdx,[rbp+rsi*1+0]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: Some(6),
        scale: 1,
        disp: 0,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x88, 0x54, 0x35, 0x00],
    },
    CapturedMemMov {
        label: "MovMR8Sib rdi,[rsp+rbx*2+4096]",
        reg_root: 7,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: Some(3),
        scale: 2,
        disp: 4096,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x40, 0x88, 0xbc, 0x5c, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovMR8Sib r8,[r9+r10*8-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: Some(10),
        scale: 8,
        disp: -129,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x47, 0x88, 0x84, 0xd1, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovMR8Sib rcx,[r12+r15*4+127]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 12,
        index_root: Some(15),
        scale: 4,
        disp: 127,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x43, 0x88, 0x4c, 0xbc, 0x7f],
    },
    CapturedMemMov {
        label: "MovMR8Sib rax,[rbx+rcx*4+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 4,
        disp: 0,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x88, 0x04, 0x8b],
    },
    CapturedMemMov {
        label: "MovMR8Sib rax,[rbx+r12*4+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(12),
        scale: 4,
        disp: 16,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x42, 0x88, 0x44, 0xa3, 0x10],
    },
    CapturedMemMov {
        label: "MovssRM xmm0,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x10, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "MovssRM xmm9,[r13-8]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x45, 0x0f, 0x10, 0x4d, 0xf8],
    },
    CapturedMemMov {
        label: "MovssRM xmm3,[rbp+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x10, 0x5d, 0x00],
    },
    CapturedMemMov {
        label: "MovssRM xmm15,[rsp+4096]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x44, 0x0f, 0x10, 0xbc, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovssRM xmm0,[r9-129]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x41, 0x0f, 0x10, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovssRM xmm9,[rbx+0]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x44, 0x0f, 0x10, 0x0b],
    },
    CapturedMemMov {
        label: "MovsdRM xmm0,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf2, 0x0f, 0x10, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "MovsdRM xmm9,[r13-8]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf2, 0x45, 0x0f, 0x10, 0x4d, 0xf8],
    },
    CapturedMemMov {
        label: "MovsdRM xmm3,[rbp+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf2, 0x0f, 0x10, 0x5d, 0x00],
    },
    CapturedMemMov {
        label: "MovsdRM xmm15,[rsp+4096]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf2, 0x44, 0x0f, 0x10, 0xbc, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovsdRM xmm0,[r9-129]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf2, 0x41, 0x0f, 0x10, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovsdRM xmm9,[rbx+0]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf2, 0x44, 0x0f, 0x10, 0x0b],
    },
    CapturedMemMov {
        label: "MovssMR xmm0,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x11, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "MovssMR xmm9,[r13-8]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x45, 0x0f, 0x11, 0x4d, 0xf8],
    },
    CapturedMemMov {
        label: "MovssMR xmm3,[rbp+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x11, 0x5d, 0x00],
    },
    CapturedMemMov {
        label: "MovssMR xmm15,[rsp+4096]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x44, 0x0f, 0x11, 0xbc, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovssMR xmm0,[r9-129]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x41, 0x0f, 0x11, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovssMR xmm9,[rbx+0]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x44, 0x0f, 0x11, 0x0b],
    },
    CapturedMemMov {
        label: "MovsdMR xmm0,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf2, 0x0f, 0x11, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "MovsdMR xmm9,[r13-8]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf2, 0x45, 0x0f, 0x11, 0x4d, 0xf8],
    },
    CapturedMemMov {
        label: "MovsdMR xmm3,[rbp+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf2, 0x0f, 0x11, 0x5d, 0x00],
    },
    CapturedMemMov {
        label: "MovsdMR xmm15,[rsp+4096]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf2, 0x44, 0x0f, 0x11, 0xbc, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovsdMR xmm0,[r9-129]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf2, 0x41, 0x0f, 0x11, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovsdMR xmm9,[rbx+0]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf2, 0x44, 0x0f, 0x11, 0x0b],
    },
    CapturedMemMov {
        label: "MovssRMSib xmm0,[rbx+rcx*8+16]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: Some(1),
        scale: 8,
        disp: 16,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x10, 0x44, 0xcb, 0x10],
    },
    CapturedMemMov {
        label: "MovssRMSib xmm9,[r13+r14*4-8]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 13,
        index_root: Some(14),
        scale: 4,
        disp: -8,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x47, 0x0f, 0x10, 0x4c, 0xb5, 0xf8],
    },
    CapturedMemMov {
        label: "MovssRMSib xmm3,[rbp+rsi*1+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 5,
        index_root: Some(6),
        scale: 1,
        disp: 0,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x10, 0x5c, 0x35, 0x00],
    },
    CapturedMemMov {
        label: "MovssRMSib xmm15,[rsp+rbx*2+4096]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 4,
        index_root: Some(3),
        scale: 2,
        disp: 4096,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x44, 0x0f, 0x10, 0xbc, 0x5c, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovssRMSib xmm0,[r9+r10*8-129]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 9,
        index_root: Some(10),
        scale: 8,
        disp: -129,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x43, 0x0f, 0x10, 0x84, 0xd1, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovssRMSib xmm9,[r12+r15*4+127]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 12,
        index_root: Some(15),
        scale: 4,
        disp: 127,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x47, 0x0f, 0x10, 0x4c, 0xbc, 0x7f],
    },
    CapturedMemMov {
        label: "MovssRMSib xmm3,[rbx+rcx*4+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: Some(1),
        scale: 4,
        disp: 0,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x10, 0x1c, 0x8b],
    },
    CapturedMemMov {
        label: "MovssRMSib xmm15,[rbx+r12*4+16]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: Some(12),
        scale: 4,
        disp: 16,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x46, 0x0f, 0x10, 0x7c, 0xa3, 0x10],
    },
    CapturedMemMov {
        label: "MovsdRMSib xmm0,[rbx+rcx*8+16]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: Some(1),
        scale: 8,
        disp: 16,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf2, 0x0f, 0x10, 0x44, 0xcb, 0x10],
    },
    CapturedMemMov {
        label: "MovsdRMSib xmm9,[r13+r14*4-8]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 13,
        index_root: Some(14),
        scale: 4,
        disp: -8,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf2, 0x47, 0x0f, 0x10, 0x4c, 0xb5, 0xf8],
    },
    CapturedMemMov {
        label: "MovsdRMSib xmm3,[rbp+rsi*1+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 5,
        index_root: Some(6),
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf2, 0x0f, 0x10, 0x5c, 0x35, 0x00],
    },
    CapturedMemMov {
        label: "MovsdRMSib xmm15,[rsp+rbx*2+4096]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 4,
        index_root: Some(3),
        scale: 2,
        disp: 4096,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf2, 0x44, 0x0f, 0x10, 0xbc, 0x5c, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovsdRMSib xmm0,[r9+r10*8-129]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 9,
        index_root: Some(10),
        scale: 8,
        disp: -129,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf2, 0x43, 0x0f, 0x10, 0x84, 0xd1, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovsdRMSib xmm9,[r12+r15*4+127]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 12,
        index_root: Some(15),
        scale: 4,
        disp: 127,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf2, 0x47, 0x0f, 0x10, 0x4c, 0xbc, 0x7f],
    },
    CapturedMemMov {
        label: "MovsdRMSib xmm3,[rbx+rcx*4+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: Some(1),
        scale: 4,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf2, 0x0f, 0x10, 0x1c, 0x8b],
    },
    CapturedMemMov {
        label: "MovsdRMSib xmm15,[rbx+r12*4+16]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: Some(12),
        scale: 4,
        disp: 16,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf2, 0x46, 0x0f, 0x10, 0x7c, 0xa3, 0x10],
    },
    CapturedMemMov {
        label: "MovdqaRM xmm0,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x0f, 0x6f, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "MovdqaRM xmm9,[r13-8]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x45, 0x0f, 0x6f, 0x4d, 0xf8],
    },
    CapturedMemMov {
        label: "MovdqaRM xmm3,[rbp+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x0f, 0x6f, 0x5d, 0x00],
    },
    CapturedMemMov {
        label: "MovdqaRM xmm15,[rsp+4096]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x44, 0x0f, 0x6f, 0xbc, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovdqaRM xmm0,[r9-129]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x41, 0x0f, 0x6f, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovdqaRM xmm9,[rbx+0]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x44, 0x0f, 0x6f, 0x0b],
    },
    CapturedMemMov {
        label: "MovdquRM xmm0,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x6f, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "MovdquRM xmm9,[r13-8]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x45, 0x0f, 0x6f, 0x4d, 0xf8],
    },
    CapturedMemMov {
        label: "MovdquRM xmm3,[rbp+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x6f, 0x5d, 0x00],
    },
    CapturedMemMov {
        label: "MovdquRM xmm15,[rsp+4096]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x44, 0x0f, 0x6f, 0xbc, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovdquRM xmm0,[r9-129]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x41, 0x0f, 0x6f, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovdquRM xmm9,[rbx+0]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x44, 0x0f, 0x6f, 0x0b],
    },
    CapturedMemMov {
        label: "MovdqaMR xmm0,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x0f, 0x7f, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "MovdqaMR xmm9,[r13-8]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x45, 0x0f, 0x7f, 0x4d, 0xf8],
    },
    CapturedMemMov {
        label: "MovdqaMR xmm3,[rbp+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x0f, 0x7f, 0x5d, 0x00],
    },
    CapturedMemMov {
        label: "MovdqaMR xmm15,[rsp+4096]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x44, 0x0f, 0x7f, 0xbc, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovdqaMR xmm0,[r9-129]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x41, 0x0f, 0x7f, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovdqaMR xmm9,[rbx+0]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x44, 0x0f, 0x7f, 0x0b],
    },
    CapturedMemMov {
        label: "MovdquMR xmm0,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x7f, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "MovdquMR xmm9,[r13-8]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x45, 0x0f, 0x7f, 0x4d, 0xf8],
    },
    CapturedMemMov {
        label: "MovdquMR xmm3,[rbp+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x7f, 0x5d, 0x00],
    },
    CapturedMemMov {
        label: "MovdquMR xmm15,[rsp+4096]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x44, 0x0f, 0x7f, 0xbc, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovdquMR xmm0,[r9-129]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x41, 0x0f, 0x7f, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovdquMR xmm9,[rbx+0]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x44, 0x0f, 0x7f, 0x0b],
    },
    CapturedMemMov {
        label: "MovdquRMSib xmm0,[rbx+rcx*8+16]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: Some(1),
        scale: 8,
        disp: 16,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x6f, 0x44, 0xcb, 0x10],
    },
    CapturedMemMov {
        label: "MovdquRMSib xmm9,[r13+r14*4-8]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 13,
        index_root: Some(14),
        scale: 4,
        disp: -8,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x47, 0x0f, 0x6f, 0x4c, 0xb5, 0xf8],
    },
    CapturedMemMov {
        label: "MovdquRMSib xmm3,[rbp+rsi*1+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 5,
        index_root: Some(6),
        scale: 1,
        disp: 0,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x6f, 0x5c, 0x35, 0x00],
    },
    CapturedMemMov {
        label: "MovdquRMSib xmm15,[rsp+rbx*2+4096]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 4,
        index_root: Some(3),
        scale: 2,
        disp: 4096,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x44, 0x0f, 0x6f, 0xbc, 0x5c, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovdquRMSib xmm0,[r9+r10*8-129]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 9,
        index_root: Some(10),
        scale: 8,
        disp: -129,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x43, 0x0f, 0x6f, 0x84, 0xd1, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovdquRMSib xmm9,[r12+r15*4+127]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 12,
        index_root: Some(15),
        scale: 4,
        disp: 127,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x47, 0x0f, 0x6f, 0x4c, 0xbc, 0x7f],
    },
    CapturedMemMov {
        label: "MovdquRMSib xmm3,[rbx+rcx*4+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: Some(1),
        scale: 4,
        disp: 0,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x6f, 0x1c, 0x8b],
    },
    CapturedMemMov {
        label: "MovdquRMSib xmm15,[rbx+r12*4+16]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: Some(12),
        scale: 4,
        disp: 16,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x46, 0x0f, 0x6f, 0x7c, 0xa3, 0x10],
    },
    CapturedMemMov {
        label: "MovdquMRSib xmm0,[rbx+rcx*8+16]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: Some(1),
        scale: 8,
        disp: 16,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x7f, 0x44, 0xcb, 0x10],
    },
    CapturedMemMov {
        label: "MovdquMRSib xmm9,[r13+r14*4-8]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 13,
        index_root: Some(14),
        scale: 4,
        disp: -8,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x47, 0x0f, 0x7f, 0x4c, 0xb5, 0xf8],
    },
    CapturedMemMov {
        label: "MovdquMRSib xmm3,[rbp+rsi*1+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 5,
        index_root: Some(6),
        scale: 1,
        disp: 0,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x7f, 0x5c, 0x35, 0x00],
    },
    CapturedMemMov {
        label: "MovdquMRSib xmm15,[rsp+rbx*2+4096]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 4,
        index_root: Some(3),
        scale: 2,
        disp: 4096,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x44, 0x0f, 0x7f, 0xbc, 0x5c, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovdquMRSib xmm0,[r9+r10*8-129]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 9,
        index_root: Some(10),
        scale: 8,
        disp: -129,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x43, 0x0f, 0x7f, 0x84, 0xd1, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovdquMRSib xmm9,[r12+r15*4+127]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 12,
        index_root: Some(15),
        scale: 4,
        disp: 127,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x47, 0x0f, 0x7f, 0x4c, 0xbc, 0x7f],
    },
    CapturedMemMov {
        label: "MovdquMRSib xmm3,[rbx+rcx*4+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: Some(1),
        scale: 4,
        disp: 0,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x7f, 0x1c, 0x8b],
    },
    CapturedMemMov {
        label: "MovdquMRSib xmm15,[rbx+r12*4+16]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: Some(12),
        scale: 4,
        disp: 16,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x46, 0x0f, 0x7f, 0x7c, 0xa3, 0x10],
    },
    CapturedMemMov {
        label: "AddRM rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x03, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "AddRM r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4d, 0x03, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "AddRM rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x03, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "AddRM rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x03, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "AddRM r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4d, 0x03, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "AddRM rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x03, 0x03],
    },
    CapturedMemMov {
        label: "SubRM rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x2b, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "SubRM r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4d, 0x2b, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "SubRM rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x2b, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "SubRM rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x2b, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "SubRM r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4d, 0x2b, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "SubRM rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x2b, 0x03],
    },
    CapturedMemMov {
        label: "CmpRM rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x3b, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "CmpRM r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4d, 0x3b, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "CmpRM rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x3b, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "CmpRM rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x3b, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "CmpRM r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4d, 0x3b, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "CmpRM rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x3b, 0x03],
    },
    CapturedMemMov {
        label: "ImulRM rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x0f, 0xaf, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "ImulRM r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4d, 0x0f, 0xaf, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "ImulRM rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x0f, 0xaf, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "ImulRM rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x0f, 0xaf, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "ImulRM r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4d, 0x0f, 0xaf, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "ImulRM rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x0f, 0xaf, 0x03],
    },
    CapturedMemMov {
        label: "XorMR rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x31, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "XorMR r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x4d, 0x31, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "XorMR rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x31, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "XorMR rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x31, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "XorMR r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x4d, 0x31, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "XorMR rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x31, 0x03],
    },
    CapturedMemMov {
        label: "AddMR rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x01, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "AddMR r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x4d, 0x01, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "AddMR rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x01, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "AddMR rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x01, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "AddMR r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x4d, 0x01, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "AddMR rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x01, 0x03],
    },
    CapturedMemMov {
        label: "ImulRMSib rax,[rbx+rcx*8+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 8,
        disp: 16,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x0f, 0xaf, 0x44, 0xcb, 0x10],
    },
    CapturedMemMov {
        label: "ImulRMSib r12,[r13+r14*4-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: Some(14),
        scale: 4,
        disp: -8,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4f, 0x0f, 0xaf, 0x64, 0xb5, 0xf8],
    },
    CapturedMemMov {
        label: "ImulRMSib rdx,[rbp+rsi*1+0]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: Some(6),
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x0f, 0xaf, 0x54, 0x35, 0x00],
    },
    CapturedMemMov {
        label: "ImulRMSib rdi,[rsp+rbx*2+4096]",
        reg_root: 7,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: Some(3),
        scale: 2,
        disp: 4096,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x0f, 0xaf, 0xbc, 0x5c, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "ImulRMSib r8,[r9+r10*8-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: Some(10),
        scale: 8,
        disp: -129,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4f, 0x0f, 0xaf, 0x84, 0xd1, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "ImulRMSib rcx,[r12+r15*4+127]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 12,
        index_root: Some(15),
        scale: 4,
        disp: 127,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4b, 0x0f, 0xaf, 0x4c, 0xbc, 0x7f],
    },
    CapturedMemMov {
        label: "ImulRMSib rax,[rbx+rcx*4+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 4,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x0f, 0xaf, 0x04, 0x8b],
    },
    CapturedMemMov {
        label: "ImulRMSib rax,[rbx+r12*4+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(12),
        scale: 4,
        disp: 16,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4a, 0x0f, 0xaf, 0x44, 0xa3, 0x10],
    },
    CapturedMemMov {
        label: "XorMRSib rax,[rbx+rcx*8+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 8,
        disp: 16,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x31, 0x44, 0xcb, 0x10],
    },
    CapturedMemMov {
        label: "XorMRSib r12,[r13+r14*4-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: Some(14),
        scale: 4,
        disp: -8,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x4f, 0x31, 0x64, 0xb5, 0xf8],
    },
    CapturedMemMov {
        label: "XorMRSib rdx,[rbp+rsi*1+0]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: Some(6),
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x31, 0x54, 0x35, 0x00],
    },
    CapturedMemMov {
        label: "XorMRSib rdi,[rsp+rbx*2+4096]",
        reg_root: 7,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: Some(3),
        scale: 2,
        disp: 4096,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x31, 0xbc, 0x5c, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "XorMRSib r8,[r9+r10*8-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: Some(10),
        scale: 8,
        disp: -129,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x4f, 0x31, 0x84, 0xd1, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "XorMRSib rcx,[r12+r15*4+127]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 12,
        index_root: Some(15),
        scale: 4,
        disp: 127,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x4b, 0x31, 0x4c, 0xbc, 0x7f],
    },
    CapturedMemMov {
        label: "XorMRSib rax,[rbx+rcx*4+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 4,
        disp: 0,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x31, 0x04, 0x8b],
    },
    CapturedMemMov {
        label: "XorMRSib rax,[rbx+r12*4+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(12),
        scale: 4,
        disp: 16,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x4a, 0x31, 0x44, 0xa3, 0x10],
    },
    CapturedMemMov {
        label: "AddMRSib rax,[rbx+rcx*8+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 8,
        disp: 16,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x01, 0x44, 0xcb, 0x10],
    },
    CapturedMemMov {
        label: "AddMRSib r12,[r13+r14*4-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: Some(14),
        scale: 4,
        disp: -8,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x4f, 0x01, 0x64, 0xb5, 0xf8],
    },
    CapturedMemMov {
        label: "AddMRSib rdx,[rbp+rsi*1+0]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: Some(6),
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x01, 0x54, 0x35, 0x00],
    },
    CapturedMemMov {
        label: "AddMRSib rdi,[rsp+rbx*2+4096]",
        reg_root: 7,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: Some(3),
        scale: 2,
        disp: 4096,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x01, 0xbc, 0x5c, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "AddMRSib r8,[r9+r10*8-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: Some(10),
        scale: 8,
        disp: -129,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x4f, 0x01, 0x84, 0xd1, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "AddMRSib rcx,[r12+r15*4+127]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 12,
        index_root: Some(15),
        scale: 4,
        disp: 127,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x4b, 0x01, 0x4c, 0xbc, 0x7f],
    },
    CapturedMemMov {
        label: "AddMRSib rax,[rbx+rcx*4+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 4,
        disp: 0,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x01, 0x04, 0x8b],
    },
    CapturedMemMov {
        label: "AddMRSib rax,[rbx+r12*4+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(12),
        scale: 4,
        disp: 16,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x4a, 0x01, 0x44, 0xa3, 0x10],
    },
    CapturedMemMov {
        label: "Lea rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x8d, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "Lea r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4d, 0x8d, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "Lea rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x8d, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "Lea rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x8d, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "Lea r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4d, 0x8d, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "Lea rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x8d, 0x03],
    },
    CapturedMemMov {
        label: "LeaSib rax,[rbx+rcx*8+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 8,
        disp: 16,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x8d, 0x44, 0xcb, 0x10],
    },
    CapturedMemMov {
        label: "LeaSib r12,[r13+r14*4-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: Some(14),
        scale: 4,
        disp: -8,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4f, 0x8d, 0x64, 0xb5, 0xf8],
    },
    CapturedMemMov {
        label: "LeaSib rdx,[rbp+rsi*1+0]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: Some(6),
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x8d, 0x54, 0x35, 0x00],
    },
    CapturedMemMov {
        label: "LeaSib rdi,[rsp+rbx*2+4096]",
        reg_root: 7,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: Some(3),
        scale: 2,
        disp: 4096,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x8d, 0xbc, 0x5c, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "LeaSib r8,[r9+r10*8-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: Some(10),
        scale: 8,
        disp: -129,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4f, 0x8d, 0x84, 0xd1, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "LeaSib rcx,[r12+r15*4+127]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 12,
        index_root: Some(15),
        scale: 4,
        disp: 127,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4b, 0x8d, 0x4c, 0xbc, 0x7f],
    },
    CapturedMemMov {
        label: "LeaSib rax,[rbx+rcx*4+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 4,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x8d, 0x04, 0x8b],
    },
    CapturedMemMov {
        label: "LeaSib rax,[rbx+r12*4+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(12),
        scale: 4,
        disp: 16,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4a, 0x8d, 0x44, 0xa3, 0x10],
    },
    CapturedMemMov {
        label: "VolatileMovRM8 rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 8,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8a, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "VolatileMovRM8 r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 8,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x45, 0x8a, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "VolatileMovRM8 rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 8,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8a, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovRM8 rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 8,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8a, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovRM8 r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 8,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x45, 0x8a, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "VolatileMovRM8 rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 8,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8a, 0x03],
    },
    CapturedMemMov {
        label: "VolatileMovRM16 rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 16,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x8b, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "VolatileMovRM16 r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 16,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x45, 0x8b, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "VolatileMovRM16 rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 16,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x8b, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovRM16 rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 16,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x8b, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovRM16 r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 16,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x45, 0x8b, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "VolatileMovRM16 rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 16,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x8b, 0x03],
    },
    CapturedMemMov {
        label: "VolatileMovRM32 rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8b, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "VolatileMovRM32 r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x45, 0x8b, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "VolatileMovRM32 rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8b, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovRM32 rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8b, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovRM32 r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x45, 0x8b, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "VolatileMovRM32 rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x8b, 0x03],
    },
    CapturedMemMov {
        label: "VolatileMovRM rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x8b, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "VolatileMovRM r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4d, 0x8b, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "VolatileMovRM rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x8b, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovRM rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x8b, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovRM r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x4d, 0x8b, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "VolatileMovRM rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x48, 0x8b, 0x03],
    },
    CapturedMemMov {
        label: "VolatileMovMR8 rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x88, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "VolatileMovMR8 r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x45, 0x88, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "VolatileMovMR8 rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x88, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovMR8 rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x88, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovMR8 r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x45, 0x88, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "VolatileMovMR8 rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x88, 0x03],
    },
    CapturedMemMov {
        label: "VolatileMovMR16 rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 16,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x89, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "VolatileMovMR16 r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 16,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x45, 0x89, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "VolatileMovMR16 rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 16,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x89, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovMR16 rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 16,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x89, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovMR16 r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 16,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x45, 0x89, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "VolatileMovMR16 rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 16,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x89, 0x03],
    },
    CapturedMemMov {
        label: "VolatileMovMR32 rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x89, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "VolatileMovMR32 r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x45, 0x89, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "VolatileMovMR32 rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x89, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovMR32 rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x89, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovMR32 r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x45, 0x89, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "VolatileMovMR32 rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x89, 0x03],
    },
    CapturedMemMov {
        label: "VolatileMovMR rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x89, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "VolatileMovMR r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x4d, 0x89, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "VolatileMovMR rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x89, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovMR rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x89, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovMR r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x4d, 0x89, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "VolatileMovMR rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x48, 0x89, 0x03],
    },
    CapturedMemMov {
        label: "VolatileMovssRM xmm0,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x10, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "VolatileMovssRM xmm9,[r13-8]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x45, 0x0f, 0x10, 0x4d, 0xf8],
    },
    CapturedMemMov {
        label: "VolatileMovssRM xmm3,[rbp+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x10, 0x5d, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovssRM xmm15,[rsp+4096]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x44, 0x0f, 0x10, 0xbc, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovssRM xmm0,[r9-129]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x41, 0x0f, 0x10, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "VolatileMovssRM xmm9,[rbx+0]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 32,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x44, 0x0f, 0x10, 0x0b],
    },
    CapturedMemMov {
        label: "VolatileMovsdRM xmm0,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf2, 0x0f, 0x10, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "VolatileMovsdRM xmm9,[r13-8]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf2, 0x45, 0x0f, 0x10, 0x4d, 0xf8],
    },
    CapturedMemMov {
        label: "VolatileMovsdRM xmm3,[rbp+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf2, 0x0f, 0x10, 0x5d, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovsdRM xmm15,[rsp+4096]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf2, 0x44, 0x0f, 0x10, 0xbc, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovsdRM xmm0,[r9-129]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf2, 0x41, 0x0f, 0x10, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "VolatileMovsdRM xmm9,[rbx+0]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf2, 0x44, 0x0f, 0x10, 0x0b],
    },
    CapturedMemMov {
        label: "VolatileMovssMR xmm0,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x11, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "VolatileMovssMR xmm9,[r13-8]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x45, 0x0f, 0x11, 0x4d, 0xf8],
    },
    CapturedMemMov {
        label: "VolatileMovssMR xmm3,[rbp+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x11, 0x5d, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovssMR xmm15,[rsp+4096]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x44, 0x0f, 0x11, 0xbc, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovssMR xmm0,[r9-129]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x41, 0x0f, 0x11, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "VolatileMovssMR xmm9,[rbx+0]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 32,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x44, 0x0f, 0x11, 0x0b],
    },
    CapturedMemMov {
        label: "VolatileMovsdMR xmm0,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf2, 0x0f, 0x11, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "VolatileMovsdMR xmm9,[r13-8]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf2, 0x45, 0x0f, 0x11, 0x4d, 0xf8],
    },
    CapturedMemMov {
        label: "VolatileMovsdMR xmm3,[rbp+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf2, 0x0f, 0x11, 0x5d, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovsdMR xmm15,[rsp+4096]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf2, 0x44, 0x0f, 0x11, 0xbc, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovsdMR xmm0,[r9-129]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf2, 0x41, 0x0f, 0x11, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "VolatileMovsdMR xmm9,[rbx+0]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 64,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf2, 0x44, 0x0f, 0x11, 0x0b],
    },
    CapturedMemMov {
        label: "VolatileMovdquRM xmm0,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x6f, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "VolatileMovdquRM xmm9,[r13-8]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x45, 0x0f, 0x6f, 0x4d, 0xf8],
    },
    CapturedMemMov {
        label: "VolatileMovdquRM xmm3,[rbp+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x6f, 0x5d, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovdquRM xmm15,[rsp+4096]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x44, 0x0f, 0x6f, 0xbc, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovdquRM xmm0,[r9-129]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x41, 0x0f, 0x6f, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "VolatileMovdquRM xmm9,[rbx+0]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0xf3, 0x44, 0x0f, 0x6f, 0x0b],
    },
    CapturedMemMov {
        label: "VolatileMovdqaRM xmm0,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x0f, 0x6f, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "VolatileMovdqaRM xmm9,[r13-8]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x45, 0x0f, 0x6f, 0x4d, 0xf8],
    },
    CapturedMemMov {
        label: "VolatileMovdqaRM xmm3,[rbp+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x0f, 0x6f, 0x5d, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovdqaRM xmm15,[rsp+4096]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x44, 0x0f, 0x6f, 0xbc, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovdqaRM xmm0,[r9-129]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x41, 0x0f, 0x6f, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "VolatileMovdqaRM xmm9,[rbx+0]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 128,
        is_store: false,
        zero_extending_load: false,
        bytes: &[0x66, 0x44, 0x0f, 0x6f, 0x0b],
    },
    CapturedMemMov {
        label: "VolatileMovdquMR xmm0,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x7f, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "VolatileMovdquMR xmm9,[r13-8]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x45, 0x0f, 0x7f, 0x4d, 0xf8],
    },
    CapturedMemMov {
        label: "VolatileMovdquMR xmm3,[rbp+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x0f, 0x7f, 0x5d, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovdquMR xmm15,[rsp+4096]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x44, 0x0f, 0x7f, 0xbc, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovdquMR xmm0,[r9-129]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x41, 0x0f, 0x7f, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "VolatileMovdquMR xmm9,[rbx+0]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf3, 0x44, 0x0f, 0x7f, 0x0b],
    },
    CapturedMemMov {
        label: "VolatileMovdqaMR xmm0,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x0f, 0x7f, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "VolatileMovdqaMR xmm9,[r13-8]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x45, 0x0f, 0x7f, 0x4d, 0xf8],
    },
    CapturedMemMov {
        label: "VolatileMovdqaMR xmm3,[rbp+0]",
        reg_root: 3,
        reg_file: RegFile::Xmm,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x0f, 0x7f, 0x5d, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovdqaMR xmm15,[rsp+4096]",
        reg_root: 15,
        reg_file: RegFile::Xmm,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x44, 0x0f, 0x7f, 0xbc, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovdqaMR xmm0,[r9-129]",
        reg_root: 0,
        reg_file: RegFile::Xmm,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x41, 0x0f, 0x7f, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "VolatileMovdqaMR xmm9,[rbx+0]",
        reg_root: 9,
        reg_file: RegFile::Xmm,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0x66, 0x44, 0x0f, 0x7f, 0x0b],
    },
    // The ZERO-EXTENDING loads (`[REX] 0F B6 /r` = movzx r32, m8 and
    // `[REX] 0F B7 /r` = movzx r32, m16), in the live corpus's order: the
    // plain `[base + disp]` forms, the byte SIB form, then the volatile twins
    // (byte-identical). The register operand is a 32-bit destination, so no
    // REX is forced for RSI/RDI (unlike `mov sil/dil, m8`).
    CapturedMemMov {
        label: "MovzxRM8 rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 8,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x0f, 0xb6, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "MovzxRM8 r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 8,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x45, 0x0f, 0xb6, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "MovzxRM8 rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 8,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x0f, 0xb6, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "MovzxRM8 rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 8,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x0f, 0xb6, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovzxRM8 r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 8,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x45, 0x0f, 0xb6, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovzxRM8 rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 8,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x0f, 0xb6, 0x03],
    },
    CapturedMemMov {
        label: "MovzxRM16 rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 16,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x0f, 0xb7, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "MovzxRM16 r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 16,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x45, 0x0f, 0xb7, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "MovzxRM16 rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 16,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x0f, 0xb7, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "MovzxRM16 rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 16,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x0f, 0xb7, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovzxRM16 r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 16,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x45, 0x0f, 0xb7, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovzxRM16 rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 16,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x0f, 0xb7, 0x03],
    },
    CapturedMemMov {
        label: "MovzxRM8Sib rax,[rbx+rcx*8+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 8,
        disp: 16,
        access_bits: 8,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x0f, 0xb6, 0x44, 0xcb, 0x10],
    },
    CapturedMemMov {
        label: "MovzxRM8Sib r12,[r13+r14*4-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: Some(14),
        scale: 4,
        disp: -8,
        access_bits: 8,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x47, 0x0f, 0xb6, 0x64, 0xb5, 0xf8],
    },
    CapturedMemMov {
        label: "MovzxRM8Sib rdx,[rbp+rsi*1+0]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: Some(6),
        scale: 1,
        disp: 0,
        access_bits: 8,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x0f, 0xb6, 0x54, 0x35, 0x00],
    },
    CapturedMemMov {
        label: "MovzxRM8Sib rdi,[rsp+rbx*2+4096]",
        reg_root: 7,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: Some(3),
        scale: 2,
        disp: 4096,
        access_bits: 8,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x0f, 0xb6, 0xbc, 0x5c, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "MovzxRM8Sib r8,[r9+r10*8-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: Some(10),
        scale: 8,
        disp: -129,
        access_bits: 8,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x47, 0x0f, 0xb6, 0x84, 0xd1, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "MovzxRM8Sib rcx,[r12+r15*4+127]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 12,
        index_root: Some(15),
        scale: 4,
        disp: 127,
        access_bits: 8,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x43, 0x0f, 0xb6, 0x4c, 0xbc, 0x7f],
    },
    CapturedMemMov {
        label: "MovzxRM8Sib rax,[rbx+rcx*4+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 4,
        disp: 0,
        access_bits: 8,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x0f, 0xb6, 0x04, 0x8b],
    },
    CapturedMemMov {
        label: "MovzxRM8Sib rax,[rbx+r12*4+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: Some(12),
        scale: 4,
        disp: 16,
        access_bits: 8,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x42, 0x0f, 0xb6, 0x44, 0xa3, 0x10],
    },
    CapturedMemMov {
        label: "VolatileMovzxRM8 rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 8,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x0f, 0xb6, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "VolatileMovzxRM8 r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 8,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x45, 0x0f, 0xb6, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "VolatileMovzxRM8 rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 8,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x0f, 0xb6, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovzxRM8 rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 8,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x0f, 0xb6, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovzxRM8 r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 8,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x45, 0x0f, 0xb6, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "VolatileMovzxRM8 rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 8,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x0f, 0xb6, 0x03],
    },
    CapturedMemMov {
        label: "VolatileMovzxRM16 rax,[rbx+16]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 16,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x0f, 0xb7, 0x43, 0x10],
    },
    CapturedMemMov {
        label: "VolatileMovzxRM16 r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 16,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x45, 0x0f, 0xb7, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "VolatileMovzxRM16 rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 16,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x0f, 0xb7, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovzxRM16 rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 16,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x0f, 0xb7, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "VolatileMovzxRM16 r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 16,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x45, 0x0f, 0xb7, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "VolatileMovzxRM16 rax,[rbx+0]",
        reg_root: 0,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 16,
        is_store: false,
        zero_extending_load: true,
        bytes: &[0x0f, 0xb7, 0x03],
    },
    // The COMPARE-EXCHANGE forms, in the live corpus's order (their own shape
    // tables: the encoder refuses an AL/AX-overlapping source or base for the
    // narrow forms, and a RAX/RBX/RCX/RDX base for the pseudo). `LOCK CMPXCHG
    // r/m8, r8` and `LOCK CMPXCHG r/m16, r16`: memory is the destination, the
    // register the replacement (its low byte / word); `sil`/`dil` need the
    // forced REX that keeps them from reading as DH/BH.
    CapturedMemMov {
        label: "Cmpxchg8 r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf0, 0x45, 0x0f, 0xb0, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "Cmpxchg8 rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf0, 0x0f, 0xb0, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "Cmpxchg8 rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf0, 0x0f, 0xb0, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "Cmpxchg8 r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf0, 0x45, 0x0f, 0xb0, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "Cmpxchg8 rsi,[rbx+0]",
        reg_root: 6,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf0, 0x40, 0x0f, 0xb0, 0x33],
    },
    CapturedMemMov {
        label: "Cmpxchg8 rdi,[rbx+16]",
        reg_root: 7,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 8,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf0, 0x40, 0x0f, 0xb0, 0x7b, 0x10],
    },
    CapturedMemMov {
        label: "Cmpxchg16 r12,[r13-8]",
        reg_root: 12,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 16,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf0, 0x66, 0x45, 0x0f, 0xb1, 0x65, 0xf8],
    },
    CapturedMemMov {
        label: "Cmpxchg16 rcx,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 16,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf0, 0x66, 0x0f, 0xb1, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "Cmpxchg16 rdx,[rsp+4096]",
        reg_root: 2,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 16,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf0, 0x66, 0x0f, 0xb1, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "Cmpxchg16 r8,[r9-129]",
        reg_root: 8,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 16,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf0, 0x66, 0x45, 0x0f, 0xb1, 0x81, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "Cmpxchg16 rsi,[rbx+0]",
        reg_root: 6,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 16,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf0, 0x66, 0x0f, 0xb1, 0x33],
    },
    CapturedMemMov {
        label: "Cmpxchg16 rdi,[rbx+16]",
        reg_root: 7,
        reg_file: RegFile::Gpr,
        base_root: 3,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 16,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf0, 0x66, 0x0f, 0xb1, 0x7b, 0x10],
    },
    // The 128-bit atomic-load pseudo's ADDRESS-bearing instruction, its
    // trailing `LOCK CMPXCHG16B m128` (the four zeroing XORs ahead of it are
    // stripped by the live re-derivation, which checks they are exactly those
    // four). No register operand: `reg_root` is the `/1` opcode extension.
    CapturedMemMov {
        label: "AtomicLoadCmpxchg16b /1,[r13-8]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 13,
        index_root: None,
        scale: 1,
        disp: -8,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf0, 0x49, 0x0f, 0xc7, 0x4d, 0xf8],
    },
    CapturedMemMov {
        label: "AtomicLoadCmpxchg16b /1,[rbp+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 5,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf0, 0x48, 0x0f, 0xc7, 0x4d, 0x00],
    },
    CapturedMemMov {
        label: "AtomicLoadCmpxchg16b /1,[rsp+4096]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 4,
        index_root: None,
        scale: 1,
        disp: 4096,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf0, 0x48, 0x0f, 0xc7, 0x8c, 0x24, 0x00, 0x10, 0x00, 0x00],
    },
    CapturedMemMov {
        label: "AtomicLoadCmpxchg16b /1,[r9-129]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 9,
        index_root: None,
        scale: 1,
        disp: -129,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf0, 0x49, 0x0f, 0xc7, 0x89, 0x7f, 0xff, 0xff, 0xff],
    },
    CapturedMemMov {
        label: "AtomicLoadCmpxchg16b /1,[rsi+0]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 6,
        index_root: None,
        scale: 1,
        disp: 0,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf0, 0x48, 0x0f, 0xc7, 0x0e],
    },
    CapturedMemMov {
        label: "AtomicLoadCmpxchg16b /1,[rdi+16]",
        reg_root: 1,
        reg_file: RegFile::Gpr,
        base_root: 7,
        index_root: None,
        scale: 1,
        disp: 16,
        access_bits: 128,
        is_store: true,
        zero_extending_load: false,
        bytes: &[0xf0, 0x48, 0x0f, 0xc7, 0x4f, 0x10],
    },
];

/// What a discharged memory-MOV address credit establishes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemMovAddressCredit {
    /// Captured encodings checked.
    pub entries: usize,
    /// Distinct addressing MODES reached (mod=00, disp8, disp32).
    pub modes: usize,
    /// Distinct access widths reached.
    pub widths: usize,
    /// Byte corruptions refuted.
    pub byte_controls_refuted: usize,
    /// Intent perturbations refuted.
    pub intent_controls_refuted: usize,
    /// Zero-extending load encodings whose DESTINATION was checked.
    pub zero_extending_entries: usize,
    /// Destination witness rows compared across those entries.
    pub destination_rows: usize,
    /// Wrong destination models (merge, sign extension, other width) refuted.
    pub destination_model_controls_refuted: usize,
}

/// THE CREDIT HOOK.
///
/// Returns `Ok` only when the whole lane holds: every captured encoding
/// discharges, the corpus reaches every addressing mode and access width the
/// family encodes, and every control REFUTES. The controls are part of the
/// credit, not a separate test — a battery that lives outside the hook cannot
/// withhold the credit when it stops refuting, which is the exact failure mode
/// this tree has hit three times before.
pub fn mem_mov_address_credit() -> Result<MemMovAddressCredit, String> {
    if EMITTED_X86_MEM_MOV.is_empty() {
        return Err(
            "ADDR-x86: the captured corpus is EMPTY; an empty set is not a \
                    discharged set"
                .to_string(),
        );
    }

    let mut modes = std::collections::BTreeSet::new();
    let mut widths = std::collections::BTreeSet::new();
    let mut byte_controls_refuted = 0usize;
    let mut intent_controls_refuted = 0usize;
    let mut zero_extending_entries = 0usize;
    let mut destination_rows = 0usize;
    let mut destination_model_controls_refuted = 0usize;
    // (access width, SIB form) pairs the zero-extending entries reach.
    let mut zero_extending_forms = std::collections::BTreeSet::new();

    for entry in EMITTED_X86_MEM_MOV {
        let intent = entry.intent();
        address_encoding_holds(entry.bytes, &intent)
            .map_err(|e| format!("ADDR-x86: {} does not hold: {e}", entry.label))?;

        // The DESTINATION facet of a zero-extending load: the decoded bytes
        // leave the access value zero-extended in the whole register, and every
        // wrong destination model refutes through the same comparison.
        if intent.zero_extending_load {
            let outcome = destination_write_holds(entry.bytes, &intent)
                .map_err(|e| format!("ADDR-x86: {} destination does not hold: {e}", entry.label))?;
            zero_extending_entries += 1;
            destination_rows += outcome.rows;
            zero_extending_forms.insert((intent.access_bits, intent.index_root.is_some()));
            let source = intent_destination_denotation(intent.access_bits);
            for (label, model) in destination_model_controls(intent.access_bits) {
                let machine = machine_destination_denotation(model);
                match compare_destinations(&source, &machine, intent.access_bits) {
                    Err(AddressRefutation::DestinationWrite { .. }) => {
                        destination_model_controls_refuted += 1;
                    }
                    other => {
                        return Err(format!(
                            "ADDR-x86: {} :: destination model control `{label}` did not \
                             refute as a destination error ({other:?})",
                            entry.label
                        ));
                    }
                }
            }
        }

        let decoded = sdm_decode_memory_mov(entry.bytes)
            .map_err(|e| format!("ADDR-x86: {} does not decode: {e}", entry.label))?;
        widths.insert(decoded.access_bits);
        match &decoded.address {
            DecodedAddress::BaseDisp { disp, .. } => {
                modes.insert(disp.encoded_bits);
            }
            DecodedAddress::Sib { disp, .. } => {
                modes.insert(disp.encoded_bits);
            }
            _ => {}
        }

        // INTENT controls: each must refute.
        for (label, perturbed) in intent_controls(&intent) {
            if address_encoding_holds(entry.bytes, &perturbed).is_ok() {
                return Err(format!(
                    "ADDR-x86: {} :: intent control `{label}` SURVIVED — an address error that \
                     cannot be refuted is not evidence",
                    entry.label
                ));
            }
            intent_controls_refuted += 1;
        }

        // BYTE controls: each must refute, or be architecturally inert.
        for (label, mutated, inert) in byte_controls(entry.bytes) {
            match address_encoding_holds(&mutated, &intent) {
                Err(_) => byte_controls_refuted += 1,
                Ok(_) if inert => {}
                Ok(_) => {
                    return Err(format!(
                        "ADDR-x86: {} :: byte control `{label}` SURVIVED and is not \
                         architecturally inert (bytes {mutated:02x?})",
                        entry.label
                    ));
                }
            }
        }
    }

    if !modes.contains(&0) {
        return Err(
            "ADDR-x86: no captured encoding uses mod=00 (no displacement field), so \
                    that addressing mode is unproven"
                .to_string(),
        );
    }
    if !modes.contains(&8) || !modes.contains(&32) {
        return Err(format!(
            "ADDR-x86: the corpus does not reach both displacement widths: {modes:?}"
        ));
    }
    // Every access width the family encodes: 8/16/32/64 for the integer forms,
    // 32/64 again for the scalar-FP ones, and 128 for the packed ones.
    let required_widths: std::collections::BTreeSet<u32> = [8, 16, 32, 64, 128].into();
    if widths != required_widths {
        return Err(format!(
            "ADDR-x86: the corpus reaches {widths:?}, not every access width the family \
             encodes ({required_widths:?})"
        ));
    }
    // The zero-extending loads must reach both access widths and both
    // addressing forms the backend encodes (the byte SIB form; there is no
    // word SIB form), or the destination facet is untested where it is used.
    let required_zero_extending_forms: std::collections::BTreeSet<(u32, bool)> =
        [(8, false), (16, false), (8, true)].into();
    if zero_extending_forms != required_zero_extending_forms {
        return Err(format!(
            "ADDR-x86: the zero-extending loads reach {zero_extending_forms:?}, not every \
             (width, SIB) form the backend encodes ({required_zero_extending_forms:?})"
        ));
    }
    // Both register FILES must be reached, or the file facet is untested.
    let files: std::collections::BTreeSet<&'static str> = EMITTED_X86_MEM_MOV
        .iter()
        .map(|e| match e.reg_file {
            RegFile::Gpr => "gpr",
            RegFile::Xmm => "xmm",
        })
        .collect();
    if files.len() != 2 {
        return Err(format!(
            "ADDR-x86: the corpus reaches only the {files:?} register file, so a decode naming \
             the other file could not be refuted"
        ));
    }

    Ok(MemMovAddressCredit {
        entries: EMITTED_X86_MEM_MOV.len(),
        modes: modes.len(),
        widths: widths.len(),
        byte_controls_refuted,
        intent_controls_refuted,
        zero_extending_entries,
        destination_rows,
        destination_model_controls_refuted,
    })
}

/// The intent perturbations every captured entry must refute.
fn intent_controls(intent: &MemAccessIntent) -> Vec<(&'static str, MemAccessIntent)> {
    let mut out = vec![
        (
            "wrong base register",
            MemAccessIntent {
                base_root: intent.base_root ^ 1,
                ..intent.clone()
            },
        ),
        (
            "displacement off by 16",
            MemAccessIntent {
                disp: intent.disp.wrapping_add(16),
                ..intent.clone()
            },
        ),
        (
            "wrong register operand",
            MemAccessIntent {
                reg_root: intent.reg_root ^ 1,
                ..intent.clone()
            },
        ),
        (
            "wrong access width",
            MemAccessIntent {
                access_bits: if intent.access_bits == 64 { 32 } else { 64 },
                ..intent.clone()
            },
        ),
        (
            "wrong direction",
            MemAccessIntent {
                is_store: !intent.is_store,
                ..intent.clone()
            },
        ),
    ];
    // A GPR load must refute when the intent names the OTHER destination rule:
    // a zero-extending intent against merging bytes and the reverse.
    if !intent.is_store && intent.reg_file == RegFile::Gpr {
        out.push((
            "zero extension flipped",
            MemAccessIntent {
                zero_extending_load: !intent.zero_extending_load,
                ..intent.clone()
            },
        ));
    }
    if let Some(index) = intent.index_root {
        out.push((
            "wrong index register",
            MemAccessIntent {
                index_root: Some(index ^ 1),
                ..intent.clone()
            },
        ));
        out.push((
            "wrong scale factor",
            MemAccessIntent {
                scale: if intent.scale == 8 { 4 } else { 8 },
                ..intent.clone()
            },
        ));
        // A base/index SWAP is only an error when the scale is not 1: at scale
        // 1 the swap denotes the SAME address, so demanding a refutation there
        // would demand that a correct address be called wrong.
        if intent.scale != 1 {
            out.push((
                "base/index swapped",
                MemAccessIntent {
                    base_root: index,
                    index_root: Some(intent.base_root),
                    ..intent.clone()
                },
            ));
        }
    }
    out
}

/// The byte corruptions every captured entry must refute, each flagged with
/// whether it is ARCHITECTURALLY INERT for this encoding.
///
/// Only two corruptions can be inert, and both are SDM facts rather than
/// conveniences: REX.X extends only the SIB index field, so on a form with no
/// SIB byte it extends nothing (Vol 2A Table 2-4); and the SIB scale field is
/// ignored when the index field encodes NO index (Table 2-3).
fn byte_controls(bytes: &[u8]) -> Vec<(&'static str, Vec<u8>, bool)> {
    let mut i = 0usize;
    // Mandatory and operand-size prefixes come FIRST (with the compare-
    // exchange forms' LOCK among them), then REX, then the opcode — which may
    // be a two-byte 0x0F escape. Skipping only 0x66 here made a control
    // mistake the REX byte for ModR/M on every SSE and packed form, so `B6
    // ModR/M.reg rewritten` actually toggled REX.W — inert on a form whose
    // width comes from the mandatory prefix — and survived.
    let mut lock_at = None;
    while i < bytes.len() && matches!(bytes[i], 0x66 | 0xF2 | 0xF3 | 0xF0) {
        if bytes[i] == 0xF0 {
            lock_at = Some(i);
        }
        i += 1;
    }
    let rex = if i < bytes.len() && bytes[i] & 0xF0 == 0x40 {
        let r = i;
        i += 1;
        Some(r)
    } else {
        None
    };
    let opcode = i;
    let modrm = if bytes.get(i) == Some(&0x0F) {
        i + 2
    } else {
        i + 1
    };
    if modrm >= bytes.len() {
        return Vec::new();
    }
    let rm = bytes[modrm] & 0b111;
    let sib = if rm == 0b100 && modrm + 1 < bytes.len() {
        Some(modrm + 1)
    } else {
        None
    };
    let no_index = sib.is_some_and(|s| {
        let index_field = (bytes[s] >> 3) & 0b111;
        let rex_x = rex.is_some_and(|r| bytes[r] & 0b0010 != 0);
        index_field == 0b100 && !rex_x
    });

    let mut out: Vec<(&'static str, Vec<u8>, bool)> = Vec::new();
    let flip = |label: &'static str,
                at: usize,
                xor: u8,
                inert: bool,
                out: &mut Vec<(&'static str, Vec<u8>, bool)>| {
        let mut b = bytes.to_vec();
        b[at] ^= xor;
        out.push((label, b, inert));
    };
    if let Some(r) = rex {
        flip("REX.B toggled", r, 0b0001, false, &mut out);
        flip("REX.X toggled", r, 0b0010, sib.is_none(), &mut out);
        flip("REX.R toggled", r, 0b0100, false, &mut out);
        if bytes[r] & 0b1000 != 0 {
            flip("REX.W cleared", r, 0b1000, false, &mut out);
        }
    }
    let direction_byte = if bytes.get(opcode) == Some(&0x0F) {
        opcode + 1
    } else {
        opcode
    };
    flip(
        "opcode direction bit",
        direction_byte,
        0b0000_0010,
        false,
        &mut out,
    );
    flip("ModR/M.reg rewritten", modrm, 0b0000_1000, false, &mut out);
    // The MOVZX opcode byte carries two facets of its own: bit 0 is the
    // ACCESS width (`B6` byte / `B7` word) and bit 3 the EXTENSION (`B6`/`B7`
    // zero, `BE`/`BF` sign). Neither is inert.
    if bytes.get(opcode) == Some(&0x0F) && matches!(bytes.get(opcode + 1), Some(0xB6 | 0xB7)) {
        flip(
            "MOVZX access width flipped",
            opcode + 1,
            0b0000_0001,
            false,
            &mut out,
        );
        flip(
            "MOVZX turned into MOVSX",
            opcode + 1,
            0b0000_1000,
            false,
            &mut out,
        );
    }
    if let Some(s) = sib {
        flip(
            "SIB scale field rotated",
            s,
            0b0100_0000,
            no_index,
            &mut out,
        );
        flip("SIB index field rewritten", s, 0b0000_1000, false, &mut out);
        flip("SIB base field rewritten", s, 0b0000_0001, false, &mut out);
    }
    if let Some(at) = lock_at {
        let mut unlocked = bytes.to_vec();
        unlocked.remove(at);
        out.push(("LOCK prefix dropped", unlocked, false));
    }
    let mut truncated = bytes.to_vec();
    truncated.pop();
    out.push(("last byte dropped", truncated, false));
    let mut appended = bytes.to_vec();
    appended.push(0x90);
    out.push(("byte appended", appended, false));
    out
}

#[cfg(test)]
mod sdm_hand_vectors {
    use super::*;

    /// HAND-WRITTEN decode vectors, transcribed from Intel SDM Vol 2A Tables
    /// 2-1/2-2/2-3 — never produced by the encoder.
    ///
    /// The whole claim of this module is that the machine side is read from the
    /// bytes INDEPENDENTLY of the encoder. That independence is worth nothing
    /// if the only thing the decoder is ever checked against is the encoder's
    /// own output: a bug mirrored in both (say, the decoder masking the SIB
    /// scale field to one bit while the encoder emits one bit) would agree on
    /// every corpus row and be invisible. These vectors are the fixed point
    /// that a mirrored bug cannot move.
    fn decode(bytes: &[u8]) -> DecodedMemoryMov {
        sdm_decode_memory_mov(bytes).unwrap_or_else(|e| panic!("{bytes:02x?} must decode: {e}"))
    }

    #[test]
    fn mod00_no_sib_has_no_displacement_field() {
        // REX.W 8B /r, mod=00 rm=011 -> [rbx], NO displacement bytes.
        let d = decode(&[0x48, 0x8B, 0x03]);
        assert_eq!(d.mnemonic, MemMovMnemonic::LoadGpr);
        assert_eq!(d.access_bits, 64);
        assert_eq!(d.reg_root, 0);
        assert_eq!(
            d.address,
            DecodedAddress::BaseDisp {
                base_root: 3,
                disp: DispField::absent(),
            }
        );
        assert_eq!(d.len, 3);
        // And the absent field contributes NO term, so `[rbx]` is just rbx.
        assert_eq!(
            decoded_address_denotation(&d.address).expect("static address"),
            reg_leaf(3)
        );
    }

    #[test]
    fn mod01_disp8_is_sign_extended() {
        // 4D = REX.W|REX.R|REX.B; modrm 65 = mod=01 reg=100 rm=101; disp8 F8.
        let d = decode(&[0x4D, 0x8B, 0x65, 0xF8]);
        assert_eq!(d.reg_root, 12, "reg 100 + REX.R<<3 = r12");
        match &d.address {
            DecodedAddress::BaseDisp { base_root, disp } => {
                assert_eq!(*base_root, 13, "rm 101 + REX.B<<3 = r13");
                assert_eq!(disp.encoded_bits, 8);
                assert_eq!(disp.value, -8, "0xF8 sign-extends to -8");
            }
            other => panic!("expected BaseDisp, got {other:?}"),
        }
    }

    #[test]
    fn sib_scale_field_is_a_shift_not_a_factor() {
        // modrm 44 = mod=01 reg=000 rm=100 (SIB); sib CB = 11 001 011.
        let d = decode(&[0x48, 0x8B, 0x44, 0xCB, 0x10]);
        match &d.address {
            DecodedAddress::Sib {
                base_root,
                index_root,
                shift,
                disp,
            } => {
                assert_eq!(*base_root, Some(3), "SIB base 011 = rbx");
                assert_eq!(*index_root, Some(1), "SIB index 001 = rcx");
                assert_eq!(*shift, 3, "scale field 11b is a SHIFT of 3, i.e. factor 8");
                assert_eq!(SDM_SIB_SCALE_FACTOR[*shift as usize], 8);
                assert_eq!(disp.value, 16);
            }
            other => panic!("expected Sib, got {other:?}"),
        }
    }

    #[test]
    fn rex_x_turns_the_no_index_sentinel_into_r12() {
        // 4A = REX.W|REX.X; sib A3 = 10 100 011 -> index field 100 WITH REX.X.
        let d = decode(&[0x4A, 0x8B, 0x44, 0xA3, 0x10]);
        match &d.address {
            DecodedAddress::Sib {
                index_root, shift, ..
            } => {
                assert_eq!(
                    *index_root,
                    Some(12),
                    "index 100 with REX.X SET is r12, NOT the no-index sentinel"
                );
                assert_eq!(*shift, 2);
            }
            other => panic!("expected Sib, got {other:?}"),
        }
        // And with REX.X clear the SAME index field means NO index — a
        // different address, which is the defect a dropped REX.X causes.
        let dropped = decode(&[0x48, 0x8B, 0x44, 0xA3, 0x10]);
        match &dropped.address {
            DecodedAddress::Sib { index_root, .. } => {
                assert_eq!(*index_root, None, "index 100 without REX.X is NO index")
            }
            other => panic!("expected Sib, got {other:?}"),
        }
        assert_ne!(
            decoded_address_denotation(&d.address),
            decoded_address_denotation(&dropped.address),
            "dropping REX.X must change the ADDRESS, not just the bytes"
        );
    }

    #[test]
    fn sib_base_101_with_mod00_means_no_base_and_a_disp32() {
        // sib 25 = 00 100 101: shift 0, index 100 (none), base 101 + mod 00.
        let d = decode(&[0x48, 0x8B, 0x04, 0x25, 0x00, 0x10, 0x00, 0x00]);
        match &d.address {
            DecodedAddress::Sib {
                base_root,
                index_root,
                disp,
                ..
            } => {
                assert_eq!(*base_root, None, "base 101 with mod=00 encodes NO base");
                assert_eq!(*index_root, None, "index 100 without REX.X is no index");
                assert_eq!(disp.encoded_bits, 32);
                assert_eq!(disp.value, 0x1000);
            }
            other => panic!("expected Sib, got {other:?}"),
        }
    }

    #[test]
    fn mod00_rm101_is_rip_relative_and_denotes_no_static_address() {
        let d = decode(&[0x48, 0x8B, 0x05, 0x10, 0x00, 0x00, 0x00]);
        assert!(matches!(d.address, DecodedAddress::RipRelative { .. }));
        assert!(
            decoded_address_denotation(&d.address).is_none(),
            "a RIP-relative address is not a static function of the registers, so it must \
             fail closed rather than be scored"
        );
    }

    #[test]
    fn a_byte_form_without_rex_names_the_legacy_high_byte_registers() {
        // 8A, modrm 7C = mod=01 reg=111 rm=100 -> SIB; reg field 7, NO REX.
        let d = decode(&[0x8A, 0x7C, 0x5C, 0x10]);
        assert_eq!(d.access_bits, 8);
        assert!(
            d.reg_is_legacy_high_byte,
            "ModR/M.reg 111 with no REX on 8A names BH, not DIL"
        );
        // With a REX present — even an all-zero one — the same field is DIL.
        let with_rex = decode(&[0x40, 0x8A, 0x7C, 0x5C, 0x10]);
        assert!(!with_rex.reg_is_legacy_high_byte);
        assert_eq!(with_rex.reg_root, 7);
    }

    #[test]
    fn the_operand_size_prefix_and_rex_w_select_the_access_width() {
        assert_eq!(decode(&[0x8B, 0x43, 0x10]).access_bits, 32, "no prefix");
        assert_eq!(decode(&[0x66, 0x8B, 0x43, 0x10]).access_bits, 16, "0x66");
        assert_eq!(decode(&[0x48, 0x8B, 0x43, 0x10]).access_bits, 64, "REX.W");
        assert_eq!(
            decode(&[0x66, 0x48, 0x8B, 0x43, 0x10]).access_bits,
            64,
            "REX.W WINS over 0x66 (SDM Vol 2A 2.2.1.2)"
        );
        assert_eq!(
            decode(&[0x8A, 0x43, 0x10]).access_bits,
            8,
            "8A is byte-sized"
        );
        assert_eq!(
            decode(&[0x66, 0x8A, 0x43, 0x10]).access_bits,
            8,
            "0x66 does not widen a byte form"
        );
    }

    #[test]
    fn the_direction_comes_from_the_opcode() {
        assert!(!decode(&[0x48, 0x8B, 0x03]).mnemonic.is_store(), "8B loads");
        assert!(decode(&[0x48, 0x89, 0x03]).mnemonic.is_store(), "89 stores");
        assert!(!decode(&[0x8A, 0x03]).mnemonic.is_store(), "8A loads");
        assert!(decode(&[0x88, 0x03]).mnemonic.is_store(), "88 stores");
    }

    /// The LOCK compare-exchange productions, from the host assembler's bytes
    /// (`clang -c`, read back with objdump) — never from the encoder.
    #[test]
    fn lock_compare_exchange_forms_decode_with_their_widths() {
        // lock cmpxchg16b (%rdi) = F0 48 0F C7 0F: REX.W selects 16 bytes, the
        // reg field is the /1 extension, [rdi] with no displacement.
        let d = decode(&[0xF0, 0x48, 0x0F, 0xC7, 0x0F]);
        assert_eq!(d.mnemonic, MemMovMnemonic::CompareExchangeBytes);
        assert!(d.lock);
        assert_eq!(d.access_bits, 128);
        assert_eq!(d.reg_root, 1, "the /1 opcode extension");
        assert!(d.mnemonic.is_store());
        assert_eq!(
            d.address,
            DecodedAddress::BaseDisp {
                base_root: 7,
                disp: DispField::absent(),
            }
        );
        // Without REX.W the same bytes are CMPXCHG8B: an 8-byte access.
        assert_eq!(decode(&[0xF0, 0x0F, 0xC7, 0x0F]).access_bits, 64);
        // lock cmpxchg16b -24(%r13) = F0 49 0F C7 4D E8.
        match decode(&[0xF0, 0x49, 0x0F, 0xC7, 0x4D, 0xE8]).address {
            DecodedAddress::BaseDisp { base_root, disp } => {
                assert_eq!(base_root, 13);
                assert_eq!(disp.value, -24);
            }
            other => panic!("expected BaseDisp, got {other:?}"),
        }
        // lock cmpxchgw %si, 16(%rbx) = 66 F0 0F B1 73 10 (the assembler puts
        // 66 first; the encoder puts F0 first — both orders decode).
        let w = decode(&[0x66, 0xF0, 0x0F, 0xB1, 0x73, 0x10]);
        assert_eq!(w.mnemonic, MemMovMnemonic::CompareExchange);
        assert_eq!((w.access_bits, w.reg_root), (16, 6));
        assert_eq!(
            decode(&[0xF0, 0x66, 0x0F, 0xB1, 0x73, 0x10]).access_bits,
            16
        );
        // lock cmpxchgb %r9b, -8(%r13) = F0 45 0F B0 4D F8.
        let b = decode(&[0xF0, 0x45, 0x0F, 0xB0, 0x4D, 0xF8]);
        assert_eq!((b.access_bits, b.reg_root), (8, 9));
        // lock cmpxchgb %cl, (%rbp) = F0 0F B0 4D 00.
        assert_eq!(decode(&[0xF0, 0x0F, 0xB0, 0x4D, 0x00]).reg_root, 1);
        // ModR/M.reg 111 on a byte CMPXCHG with no REX names BH, not DIL.
        assert!(decode(&[0xF0, 0x0F, 0xB0, 0x7B, 0x10]).reg_is_legacy_high_byte);
    }

    #[test]
    fn lock_is_required_by_compare_exchange_and_refused_elsewhere() {
        use MemMovDecodeError as E;
        assert_eq!(
            sdm_decode_memory_mov(&[0x48, 0x0F, 0xC7, 0x0F]),
            Err(E::MissingLock),
            "an unlocked CMPXCHG16B is not an encoding the backend emits"
        );
        assert_eq!(
            sdm_decode_memory_mov(&[0x66, 0x0F, 0xB1, 0x73, 0x10]),
            Err(E::MissingLock)
        );
        assert_eq!(
            sdm_decode_memory_mov(&[0xF0, 0x48, 0x8B, 0x03]),
            Err(E::UnexpectedPrefix(0xF0)),
            "LOCK on a MOV is refused by name"
        );
        assert_eq!(
            sdm_decode_memory_mov(&[0xF0, 0xF0, 0x48, 0x0F, 0xC7, 0x0F]),
            Err(E::UnexpectedPrefix(0xF0))
        );
        assert_eq!(
            sdm_decode_memory_mov(&[0x48, 0xF0, 0x0F, 0xC7, 0x0F]),
            Err(E::PrefixAfterRex(0xF0))
        );
        // 0F C7 /6 is RDRAND's extension, not CMPXCHG16B; mod=11 is #UD.
        assert_eq!(
            sdm_decode_memory_mov(&[0xF0, 0x48, 0x0F, 0xC7, 0x37]),
            Err(E::OpcodeExtension {
                opcode: 0xC7,
                extension: 6
            })
        );
        assert_eq!(
            sdm_decode_memory_mov(&[0xF0, 0x48, 0x0F, 0xC7, 0xCF]),
            Err(E::RegisterDirect)
        );
        // A 0x66 on the byte form is refused rather than ignored.
        assert_eq!(
            sdm_decode_memory_mov(&[0x66, 0xF0, 0x0F, 0xB0, 0x4D, 0x00]),
            Err(E::UnknownOpcode(0xB0))
        );
    }

    /// MOVZX/MOVSX with a memory operand, from the host assembler's bytes
    /// (`clang -c`, read back with objdump) — never from the encoder: the
    /// opcode byte fixes the ACCESS width and the EXTENSION, the register
    /// operand is a 32/64-bit destination (no AH..BH spelling without a REX),
    /// and the 0x66 form, which writes only 16 bits, is refused.
    #[test]
    fn movzx_and_movsx_memory_forms_decode_with_width_extension_and_destination() {
        // movzbl (%rbx), %eax = 0F B6 03
        let d = decode(&[0x0F, 0xB6, 0x03]);
        assert_eq!(d.mnemonic, MemMovMnemonic::LoadGprZeroExtend);
        assert_eq!((d.access_bits, d.reg_root), (8, 0));
        assert!(!d.mnemonic.is_store() && d.mnemonic.zero_extends());
        assert_eq!(d.mnemonic.reg_file(), RegFile::Gpr);
        assert_eq!(
            gpr_load_destination_write(&d),
            Some(DestinationWrite::ZeroExtend { from_bits: 8 })
        );
        // movzbl (%rbx), %esi = 0F B6 33: ModR/M.reg 110 with no REX is ESI,
        // a 32-bit destination, never DH.
        let esi = decode(&[0x0F, 0xB6, 0x33]);
        assert_eq!(esi.reg_root, 6);
        assert!(!esi.reg_is_legacy_high_byte);
        // movzwl 16(%rbx), %esi = 0F B7 73 10
        let w = decode(&[0x0F, 0xB7, 0x73, 0x10]);
        assert_eq!(
            (w.mnemonic, w.access_bits, w.reg_root),
            (MemMovMnemonic::LoadGprZeroExtend, 16, 6)
        );
        // movzwl 4096(%rsp), %edx = 0F B7 94 24 00 10 00 00
        let sp = decode(&[0x0F, 0xB7, 0x94, 0x24, 0x00, 0x10, 0x00, 0x00]);
        assert!(matches!(
            sp.address,
            DecodedAddress::Sib {
                base_root: Some(4),
                index_root: None,
                ..
            }
        ));
        // movzbq -8(%r13), %r12 = 4D 0F B6 65 F8: REX.W leaves the same value.
        let q = decode(&[0x4D, 0x0F, 0xB6, 0x65, 0xF8]);
        assert_eq!((q.access_bits, q.reg_root), (8, 12));
        assert_eq!(
            gpr_load_destination_write(&q),
            Some(DestinationWrite::ZeroExtend { from_bits: 8 })
        );
        // movzbl 16(%rbx,%rcx,8), %eax and movzbl -8(%r13,%r14,4), %r12d.
        let sib = decode(&[0x0F, 0xB6, 0x44, 0xCB, 0x10]);
        assert!(matches!(
            sib.address,
            DecodedAddress::Sib {
                base_root: Some(3),
                index_root: Some(1),
                shift: 3,
                ..
            }
        ));
        let sib_rex = decode(&[0x47, 0x0F, 0xB6, 0x64, 0xB5, 0xF8]);
        assert_eq!(sib_rex.reg_root, 12);
        assert!(matches!(
            sib_rex.address,
            DecodedAddress::Sib {
                base_root: Some(13),
                index_root: Some(14),
                shift: 2,
                ..
            }
        ));
        // movsbl (%rbx), %eax = 0F BE 03; movswq (%rbx), %rax = 48 0F BF 03.
        let sb = decode(&[0x0F, 0xBE, 0x03]);
        assert_eq!(
            (sb.mnemonic, sb.access_bits),
            (MemMovMnemonic::LoadGprSignExtend, 8)
        );
        assert!(!sb.mnemonic.zero_extends());
        assert_eq!(
            gpr_load_destination_write(&sb),
            Some(DestinationWrite::SignExtend {
                from_bits: 8,
                to_bits: 32
            })
        );
        assert_eq!(
            gpr_load_destination_write(&decode(&[0x48, 0x0F, 0xBF, 0x03])),
            Some(DestinationWrite::SignExtend {
                from_bits: 16,
                to_bits: 64
            })
        );
        // movzbw (%rbx), %ax = 66 0F B6 03 writes only AX: refused.
        assert_eq!(
            sdm_decode_memory_mov(&[0x66, 0x0F, 0xB6, 0x03]),
            Err(MemMovDecodeError::UnexpectedPrefix(0x66))
        );
        // The MOV loads' destination rules: movb (%rbx),%al = 8A 03 and
        // movw (%rbx),%ax = 66 8B 03 MERGE; movl (%rbx),%eax = 8B 03
        // zero-extends from 32.
        assert_eq!(
            gpr_load_destination_write(&decode(&[0x8A, 0x03])),
            Some(DestinationWrite::MergeLow { bits: 8 })
        );
        assert_eq!(
            gpr_load_destination_write(&decode(&[0x66, 0x8B, 0x03])),
            Some(DestinationWrite::MergeLow { bits: 16 })
        );
        assert_eq!(
            gpr_load_destination_write(&decode(&[0x8B, 0x03])),
            Some(DestinationWrite::ZeroExtend { from_bits: 32 })
        );
        // A store has no destination register.
        assert_eq!(gpr_load_destination_write(&decode(&[0x88, 0x03])), None);
    }

    /// The destination comparison decides the zero-extension, both ways: the
    /// MOVZX bytes hold against a zero-extending intent over every witness,
    /// and the merging byte MOV at the SAME address refutes there, as a
    /// destination error, on a row whose old register bits are set.
    #[test]
    fn the_destination_facet_tells_movzx_from_a_merging_mov() {
        let intent = MemAccessIntent {
            reg_root: 0,
            reg_file: RegFile::Gpr,
            base_root: 3,
            index_root: None,
            scale: 1,
            disp: 0,
            access_bits: 8,
            is_store: false,
            zero_extending_load: true,
        };
        let held = destination_write_holds(&[0x0F, 0xB6, 0x03], &intent)
            .expect("movzbl (%rbx), %eax zero-extends the byte");
        assert!(held.dirty_rows > 0 && held.signed_rows > 0);
        assert!(matches!(
            destination_write_holds(&[0x8A, 0x03], &intent),
            Err(AddressRefutation::DestinationWrite { .. })
        ));
        // The same merge is refused by the address lane's EXTENSION facet.
        assert!(matches!(
            address_encoding_holds(&[0x8A, 0x03], &intent),
            Err(AddressRefutation::Extension {
                expected: true,
                decoded: false
            })
        ));
        // MOVSX at the same address refutes on a byte with its top bit set.
        assert!(matches!(
            destination_write_holds(&[0x48, 0x0F, 0xBE, 0x03], &intent),
            Err(AddressRefutation::DestinationWrite { .. })
        ));
        // A word load (B7) reads the next byte too.
        assert!(matches!(
            destination_write_holds(&[0x0F, 0xB7, 0x03], &intent),
            Err(AddressRefutation::AccessWidth {
                expected: 8,
                decoded: 16
            })
        ));
        // And the anti-vacuity guard refuses a machine side spelled like the
        // source side.
        let source = intent_destination_denotation(8);
        assert_eq!(
            compare_destinations(&source, &source, 8),
            Err(AddressRefutation::Degenerate)
        );
    }

    #[test]
    fn malformed_and_non_canonical_byte_strings_are_refused_by_name() {
        use MemMovDecodeError as E;
        assert_eq!(sdm_decode_memory_mov(&[]), Err(E::Empty));
        assert_eq!(
            sdm_decode_memory_mov(&[0x48, 0x90, 0x03]),
            Err(E::UnknownOpcode(0x90))
        );
        assert_eq!(
            sdm_decode_memory_mov(&[0x48, 0x48, 0x8B, 0x03]),
            Err(E::DoubledRex)
        );
        assert_eq!(
            sdm_decode_memory_mov(&[0x48, 0x66, 0x8B, 0x03]),
            Err(E::PrefixAfterRex(0x66))
        );
        assert_eq!(
            sdm_decode_memory_mov(&[0xF3, 0x8B, 0x03]),
            Err(E::UnexpectedPrefix(0xF3))
        );
        assert_eq!(
            sdm_decode_memory_mov(&[0x48, 0x8B, 0xC3]),
            Err(E::RegisterDirect),
            "mod=11 has no effective address"
        );
        assert_eq!(
            sdm_decode_memory_mov(&[0x48, 0x8B, 0x43]),
            Err(E::Truncated { field: "disp8" })
        );
        assert_eq!(
            sdm_decode_memory_mov(&[0x48, 0x8B, 0x44]),
            Err(E::Truncated { field: "SIB byte" })
        );
        assert!(matches!(
            sdm_decode_memory_mov(&[0x48, 0x8B, 0x03, 0x90]),
            Err(E::TrailingBytes { .. })
        ));
    }
}
