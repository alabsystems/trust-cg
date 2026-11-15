// trust-cg-verify/x86_encoding_proofs.rs - the x86-64 MOV-immediate byte family
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: Intel 64 and IA-32 Architectures Software Developer's Manual —
//   Vol 2A §2.1     (instruction format: legacy prefixes, opcode, ModR/M,
//                    immediate; §2.1.1 the four legacy prefix groups),
//   Vol 2A §2.2.1   (REX prefixes: `0100WRXB`; a REX "must immediately precede
//                    the opcode byte"; REX.W takes precedence over 66H; with
//                    any REX present the byte registers 4..7 are SPL/BPL/SIL/DIL
//                    and AH/CH/DH/BH are not addressable),
//   Vol 2A §3.1.1.1 (the `+rb` / `+rw` / `+rd` / `+ro` opcode-embedded register
//                    and Table 3-1's register numbering),
//   Vol 2B "MOV—Move": `B0+rb ib`, `B8+rw iw`, `B8+rd id`, `REX.W B8+rd io`,
//                    `C6 /0 ib`, `C7 /0 iw`, `C7 /0 id`, and `REX.W C7 /0 id`
//                    ("move imm32 SIGN EXTENDED to 64-bits to r/m64"),
//   Vol 1 §3.4.1.1  (general-purpose registers in 64-bit mode: 64-bit operands
//                    generate a 64-bit result; 32-bit operands generate a 32-bit
//                    result ZERO-EXTENDED to 64 bits; 8-bit and 16-bit operands
//                    leave the upper 56 / 48 bits of the destination UNMODIFIED).
//
// WHAT THIS FAMILY IS. Every other x86-64 coverage credit is about what an
// instruction COMPUTES from its operands. `MOV r, imm` computes nothing: its
// whole meaning is "this register now holds this constant", so the only thing
// standing between "the backend meant RAX := -1" and "the bytes say RAX := -1"
// is the encoder — its register numbering, its REX bits, its choice among the
// four physical forms, its immediate width and byte order, and the ISA's
// zero- versus sign-extension rules. The retracted ledger entry modelled the
// row as `const == const`, a self-equality that refutes nothing. This module
// replaces it with an obligation over the REAL EMITTED BYTES:
//
//   * MACHINE side: [`sdm_decode_mov_imm`] takes ONLY bytes — no hint from the
//     intent — and walks the SDM instruction format (legacy prefixes, REX,
//     one-byte opcode map, ModR/M for the group-11 forms, operand-size
//     attribute, immediate). [`DecodedMovImm::reg_write`] then applies the
//     Vol 1 §3.4.1.1 register-write rules to get the write the hardware
//     performs.
//   * SOURCE side: [`intent_reg_write`] takes ONLY the machine-IR intent — the
//     destination register's NAME and the i64 immediate — and states the write
//     the machine IR means. It never sees a byte, a REX bit or a register
//     number from the encoder.
//   * COMPARISON: both sides are a [`RegWrite`] — a total function on the
//     64-bit root register, `old -> (old & !mask) | value`. Two `RegWrite`s
//     denote the same function iff their `(root, mask, value)` triples are
//     equal (the lemma on [`RegWrite`]), so comparing triples is an EXACT
//     decision of "for every prior register value", not a sample.
//
// HOW THE MACHINE SIDE STAYS INDEPENDENT. This crate cannot depend on
// `trust-cg-codegen` (that crate depends on THIS one), so nothing here can call
// the encoder, and nothing here does:
//
//   * the register tables below are transcribed from the SDM, not imported from
//     `trust-cg-ir`; the intent enters them by NAME and the decode enters them
//     by NUMBER, and the only thing connecting the two ends is the encoder's
//     own `hw_enc` table — which is exactly the thing under test;
//   * the decoder models forms the encoder NEVER emits (`C6 /0`, `C7 /0`,
//     AH/CH/DH/BH, `REX.W C7 /0` sign-extension), so it cannot have been
//     obtained by inverting `encode.rs`'s four-way ladder, and the sign-versus-
//     zero-extension negative control refutes on VALUE rather than on
//     "unknown opcode";
//   * the coverage-gate credit hook cannot run the encoder either, so it runs
//     over [`EMITTED_X86_MOV_IMMEDIATES`] — bytes CAPTURED from the real
//     encoder. `tests/x86_encoding_gate.rs` holds `trust-cg-codegen` as a
//     DEV-dependency, re-encodes every entry through the live encoder and fails
//     on any divergence, so the capture cannot rot under a green row.
//
// THE GATE CREDIT IS CORPUS-BASED; THE PER-COMPILE CHECK IS SEPARATE. The
// coverage-gate row is credited over the captured corpus. That corpus is tied to
// the live encoder by `tests/x86_encoding_gate.rs`, which is a target of the
// local meta-gate (`scripts/soundness_check.sh` TRUST_CG_GATES). The
// ratio-pinning target `coverage_gate_tests` also re-derives the corpus from the
// live encoder, so the pinned ratio cannot stay green on a stale capture.
// Separately, `trust-cg-codegen`'s ENC-3 decode-check (`x86_64::decode_check`)
// calls [`mov_imm_check_for_preg`] on every `MovRI` the x86 pipeline records for
// it. In ENC-3's default `enforce` mode a refutation FAILS THE COMPILE.
// `TCG_DECODE_CHECK=off|warn` and `TCG_NO_DECODE_CHECK=1` remove that
// per-compile check, and nothing here claims it ran under those settings.
// [`mov_imm_check`] allocates nothing on the holding path, so running it on
// every instruction is cheap.
//
// THE TEETH ARE PART OF THE CREDIT. [`mov_imm_discharges_valid`] does not
// return `Ok` unless every mutant in [`mov_imm_mutants`] — wrong register,
// flipped REX.B, sign-for-zero extension in both directions, truncated imm64,
// wrong-width form, wrong opcode, every single-byte immediate corruption,
// dropped forced REX, redundant prefixes, bad framing, and every source-side
// re-claim — is REFUTED, and refuted for its STATED reason class. A control
// that survives, or that refutes for the wrong reason, withholds the credit.
//
// WHAT THIS FAMILY DOES NOT ESTABLISH, said plainly (the same list is carried
// as data in [`X86_MOV_IMM_DEFERRALS`] and pinned by the gate test):
//
//   * NOT that the lowering or any pass chose the RIGHT constant or the right
//     register. A wrong constant encodes and decodes perfectly.
//   * NOT that an out-of-width immediate was intended. For a `w < 64`
//     destination the source semantics is `imm mod 2^w` — the optimizer's own
//     model (`x86_const_fold::normalize_const_for_vreg`). Such intents are
//     reported as `truncating` and counted, never refuted.
//   * NOT that the chosen FORM is the shortest. `MOV RAX,-1` is emitted as the
//     10-byte `REX.W B8 io` although the 7-byte `REX.W C7 /0 id` exists. What
//     IS pinned is the absence of redundant prefixes / REX bits and exact
//     framing.
//   * NOTHING about instruction placement, reachability or dataflow.
//   * NOTHING about the hand-assembled raw-byte `movabs` in the JIT
//     profile-counter trampolines: those are not `X86Opcode::MovRI` and their
//     imm64 is patched at run time.
//   * NOT that the ISA rules are right. They are TRANSCRIBED from the SDM and
//     are this family's trust base. No silicon differential is part of it.
//   * NOT a compared RFLAGS / frame facet. [`RegWrite`] describes only the
//     destination root register. "MOV r,imm writes no flag, no other register
//     and no memory" holds for the four accepted productions only because the
//     SDM says so ("Flags Affected: None"), and that is TRUST BASE. What the
//     obligation does enforce is CLOSURE: any byte sequence that is not one of
//     those four productions is refused. That includes the flag-clobbering
//     `XOR r,r` zeroing idiom, which control M6b shows refuting.
//   * NOT a for-all theorem over every i64 on every register.
//   * NOT a general x86 decoder.
//   * NOTHING about any other x86-64 RED row.

//! The x86-64 `MOV r, imm` encoding obligation: an independent SDM-derived
//! decoder for the MOV-immediate family, the 64-bit register-write denotation
//! of both the decoded bytes and the machine-IR intent, the typed refutations
//! between them, a captured corpus of real emitted encodings, and the
//! coverage-gate credit hook that demands the negative controls refute.

use std::fmt;

use trust_cg_ir::X86PReg;
use trust_cg_ir::x86_64_regs::x86_preg_name;

// ===========================================================================
// (1) Register tables, transcribed from the SDM
// ===========================================================================

/// 64-bit general-purpose registers in SDM register-number order
/// (Vol 2A Table 3-1 with REX.B/REX.R supplying bit 3).
pub const SDM_R64: [&str; 16] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
    "r14", "r15",
];

/// 32-bit general-purpose registers in SDM register-number order.
pub const SDM_R32: [&str; 16] = [
    "eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi", "r8d", "r9d", "r10d", "r11d", "r12d",
    "r13d", "r14d", "r15d",
];

/// 16-bit general-purpose registers in SDM register-number order.
pub const SDM_R16: [&str; 16] = [
    "ax", "cx", "dx", "bx", "sp", "bp", "si", "di", "r8w", "r9w", "r10w", "r11w", "r12w", "r13w",
    "r14w", "r15w",
];

/// Byte registers addressable WITH a REX prefix present (SDM Vol 2A §2.2.1.2 /
/// §3.1.1.1): numbers 4..=7 are SPL/BPL/SIL/DIL.
pub const SDM_R8_REX: [&str; 16] = [
    "al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil", "r8b", "r9b", "r10b", "r11b", "r12b",
    "r13b", "r14b", "r15b",
];

/// Byte registers addressable WITHOUT a REX prefix: numbers 4..=7 are the
/// legacy high-byte registers AH/CH/DH/BH, which alias bits 15:8 of
/// RAX/RCX/RDX/RBX.
pub const SDM_R8_LEGACY: [&str; 8] = ["al", "cl", "dl", "bl", "ah", "ch", "dh", "bh"];

/// One general-purpose register as the SDM describes it: which 64-bit ROOT
/// register it aliases, how many bits wide it is, and whether it is one of the
/// four legacy HIGH-BYTE registers (bits 15:8 of the root rather than 7:0).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SdmReg {
    /// SDM number of the 64-bit root register, `0..=15` (`0` = RAX … `15` = R15).
    pub root: u8,
    /// Register width in bits: 8, 16, 32 or 64.
    pub bits: u8,
    /// True only for AH/CH/DH/BH.
    pub high_byte: bool,
}

/// Look a register up by its assembly NAME in the SDM tables above.
///
/// Returns `None` for anything that is not a general-purpose register (XMM,
/// RFLAGS, RIP, a misspelling): the source side fails closed on those.
pub fn sdm_reg(name: &str) -> Option<SdmReg> {
    let find = |table: &[&str]| table.iter().position(|&n| n == name);
    if let Some(i) = find(&SDM_R64) {
        return Some(SdmReg {
            root: i as u8,
            bits: 64,
            high_byte: false,
        });
    }
    if let Some(i) = find(&SDM_R32) {
        return Some(SdmReg {
            root: i as u8,
            bits: 32,
            high_byte: false,
        });
    }
    if let Some(i) = find(&SDM_R16) {
        return Some(SdmReg {
            root: i as u8,
            bits: 16,
            high_byte: false,
        });
    }
    if let Some(i) = find(&SDM_R8_REX) {
        return Some(SdmReg {
            root: i as u8,
            bits: 8,
            high_byte: false,
        });
    }
    // AH/CH/DH/BH: legacy numbers 4..=7 alias bits 15:8 of roots 0..=3.
    if let Some(i) = find(&SDM_R8_LEGACY[4..]) {
        return Some(SdmReg {
            root: i as u8,
            bits: 8,
            high_byte: true,
        });
    }
    None
}

/// The assembly name of the `bits`-wide low alias of root register `root`
/// (never a high-byte register). `None` if `root > 15` or `bits` is not a GPR
/// width.
pub fn sdm_name(root: u8, bits: u8) -> Option<&'static str> {
    let i = usize::from(root);
    match bits {
        64 => SDM_R64.get(i).copied(),
        32 => SDM_R32.get(i).copied(),
        16 => SDM_R16.get(i).copied(),
        8 => SDM_R8_REX.get(i).copied(),
        _ => None,
    }
}

// ===========================================================================
// (2) The decoder — a walk of the SDM instruction format, bytes only
// ===========================================================================

/// SDM Vol 2A §2.1.1 legacy prefix groups. Only the operand-size override is
/// MODELLED; every other legacy prefix is recognised so that it can be refused
/// by name rather than misread as an opcode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LegacyPrefix {
    /// Group 1: F0 LOCK, F2 REPNE, F3 REP.
    LockOrRepeat,
    /// Group 2: 2E/36/3E/26/64/65 segment overrides (and branch hints).
    Segment,
    /// Group 3: 66 operand-size override.
    OperandSize,
    /// Group 4: 67 address-size override.
    AddressSize,
}

/// The legacy prefix byte table (SDM Vol 2A §2.1.1).
const LEGACY_PREFIXES: &[(u8, LegacyPrefix)] = &[
    (0xF0, LegacyPrefix::LockOrRepeat),
    (0xF2, LegacyPrefix::LockOrRepeat),
    (0xF3, LegacyPrefix::LockOrRepeat),
    (0x2E, LegacyPrefix::Segment),
    (0x36, LegacyPrefix::Segment),
    (0x3E, LegacyPrefix::Segment),
    (0x26, LegacyPrefix::Segment),
    (0x64, LegacyPrefix::Segment),
    (0x65, LegacyPrefix::Segment),
    (0x66, LegacyPrefix::OperandSize),
    (0x67, LegacyPrefix::AddressSize),
];

fn legacy_prefix(byte: u8) -> Option<LegacyPrefix> {
    LEGACY_PREFIXES
        .iter()
        .find(|&&(b, _)| b == byte)
        .map(|&(_, p)| p)
}

/// In 64-bit mode the bytes `40..=4F` are REX prefixes, not opcodes
/// (SDM Vol 2A §2.2.1).
fn is_rex(byte: u8) -> bool {
    (0x40..=0x4F).contains(&byte)
}

/// Which SDM `MOV` immediate production the bytes matched.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MovImmForm {
    /// `B0+rb ib` — MOV r8, imm8.
    B0PlusRb,
    /// `B8+rw iw` / `B8+rd id` / `REX.W B8+rd io` — MOV r16/r32/r64, imm.
    B8PlusRd,
    /// `C6 /0 ib` with ModR/M.mod = 11 — MOV r/m8, imm8 (register destination).
    C6Slash0,
    /// `C7 /0 iw` / `C7 /0 id` / `REX.W C7 /0 id` with ModR/M.mod = 11.
    C7Slash0,
}

/// One row of the one-byte opcode map restricted to the MOV-immediate family.
struct OpcodeMapRow {
    lo: u8,
    hi: u8,
    form: MovImmForm,
    /// The production is a byte-operand one (`ib` on an 8-bit destination).
    byte_operand: bool,
    /// The register comes from a ModR/M byte rather than the opcode's low 3 bits.
    modrm: bool,
}

/// SDM Vol 2B "MOV": the four immediate-to-register productions.
const MOV_IMM_OPCODE_MAP: &[OpcodeMapRow] = &[
    OpcodeMapRow {
        lo: 0xB0,
        hi: 0xB7,
        form: MovImmForm::B0PlusRb,
        byte_operand: true,
        modrm: false,
    },
    OpcodeMapRow {
        lo: 0xB8,
        hi: 0xBF,
        form: MovImmForm::B8PlusRd,
        byte_operand: false,
        modrm: false,
    },
    OpcodeMapRow {
        lo: 0xC6,
        hi: 0xC6,
        form: MovImmForm::C6Slash0,
        byte_operand: true,
        modrm: true,
    },
    OpcodeMapRow {
        lo: 0xC7,
        hi: 0xC7,
        form: MovImmForm::C7Slash0,
        byte_operand: false,
        modrm: true,
    },
];

/// How the immediate bytes become the operand-size value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ImmExtension {
    /// The immediate is exactly as wide as the operand (`ib`/`iw`/`id`/`io`).
    Exact,
    /// `REX.W C7 /0 id`: a 32-bit immediate SIGN-EXTENDED to the 64-bit operand.
    SignExtend32To64,
}

/// Why the bytes are not one well-formed MOV-immediate-to-register
/// instruction. Every variant is a REFUTATION, never a "could not tell".
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MovImmDecodeError {
    /// A legacy prefix other than 66h. LOCK/REP/segment/address-size prefixes
    /// have no modelled meaning on MOV r,imm; refuse rather than ignore.
    UnmodelledPrefix(u8),
    /// A REX byte followed by a legacy prefix or a second REX. Hardware would
    /// IGNORE such a REX (it must immediately precede the opcode); refusing is
    /// the fail-closed reading.
    RexNotAdjacentToOpcode {
        /// The REX byte that was not adjacent to the opcode.
        rex: u8,
        /// The prefix byte found where the opcode had to be.
        next: u8,
    },
    /// The opcode byte is not in the MOV-immediate rows of the opcode map.
    NotMovImmediate {
        /// The opcode byte found.
        opcode: u8,
    },
    /// `C6`/`C7` with ModR/M.mod != 11: a STORE to memory, not a register write.
    MemoryFormIsAStore {
        /// The ModR/M byte found.
        modrm: u8,
    },
    /// `C6`/`C7` with ModR/M.reg != 0. Group 11 defines only `/0` as MOV
    /// (`C6 F8` is XABORT and `C7 F8` is XBEGIN).
    UndefinedGroup11Extension {
        /// The ModR/M.reg field found.
        reg: u8,
    },
    /// The byte stream ended before the instruction did.
    Truncated {
        /// Total bytes the instruction needs, as far as the decode got.
        needed: usize,
        /// Bytes available.
        available: usize,
    },
}

impl fmt::Display for MovImmDecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnmodelledPrefix(b) => write!(
                f,
                "legacy prefix 0x{b:02x} has no modelled meaning on MOV r,imm (only 66h is modelled)"
            ),
            Self::RexNotAdjacentToOpcode { rex, next } => write!(
                f,
                "REX 0x{rex:02x} is followed by prefix byte 0x{next:02x}, not by the opcode — \
                 hardware ignores such a REX"
            ),
            Self::NotMovImmediate { opcode } => write!(
                f,
                "opcode 0x{opcode:02x} is not a MOV-immediate production (B0+rb, B8+rd, C6 /0, C7 /0)"
            ),
            Self::MemoryFormIsAStore { modrm } => write!(
                f,
                "ModR/M 0x{modrm:02x} has mod != 11: a memory destination is a STORE, not a \
                 register write"
            ),
            Self::UndefinedGroup11Extension { reg } => write!(
                f,
                "group-11 opcode extension /{reg} is not MOV (only /0 is; C7 /7 is XBEGIN)"
            ),
            Self::Truncated { needed, available } => write!(
                f,
                "instruction needs at least {needed} byte(s), only {available} available"
            ),
        }
    }
}

/// One decoded MOV-immediate-to-register instruction, as the SDM reads it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DecodedMovImm {
    /// Which SDM production matched.
    pub form: MovImmForm,
    /// The operand-size attribute: 8, 16, 32 or 64.
    pub operand_bits: u8,
    /// The destination register NUMBER: `low3 | REX.B << 3`, `0..=15`.
    pub reg_number: u8,
    /// True iff the destination is AH/CH/DH/BH (8-bit form, NO REX, number 4..=7).
    pub high_byte: bool,
    /// The immediate bytes, in stream order; only `imm[..imm_len]` is meaningful.
    pub imm: [u8; 8],
    /// How many immediate bytes the production carries.
    pub imm_len: usize,
    /// How the immediate becomes the operand-size value.
    pub extension: ImmExtension,
    /// Total bytes the instruction occupies.
    pub len_consumed: usize,
    /// How many 66h operand-size prefixes preceded the opcode.
    pub n_66: u8,
    /// The REX byte, if one was present.
    pub rex: Option<u8>,
    /// Offset of the opcode byte.
    pub opcode_at: usize,
    /// Offset of the first immediate byte.
    pub imm_at: usize,
}

/// SDM Vol 2A §2.2.1.2: the operand-size attribute in 64-bit mode for a
/// non-byte production. REX.W = 1 selects 64 and "takes precedence over" 66h;
/// otherwise 66h selects 16; otherwise the default is 32.
fn operand_size_attribute(byte_operand: bool, rex_w: bool, has_66: bool) -> u8 {
    if byte_operand {
        8
    } else if rex_w {
        64
    } else if has_66 {
        16
    } else {
        32
    }
}

/// SDM Vol 2B "MOV": the immediate each production carries at each operand
/// size. `B8+rd` at 64 is the only true imm64 in the ISA; `C7 /0` at 64 carries
/// an imm32 that is sign-extended.
fn immediate_shape(form: MovImmForm, operand_bits: u8) -> (usize, ImmExtension) {
    match (form, operand_bits) {
        (MovImmForm::C7Slash0, 64) => (4, ImmExtension::SignExtend32To64),
        (_, bits) => (usize::from(bits / 8), ImmExtension::Exact),
    }
}

/// Decode exactly one MOV-immediate-to-register instruction from the FRONT of
/// `bytes`, from the bytes alone.
///
/// This is a walk of the SDM instruction format — legacy prefixes, then an
/// optional REX that must be adjacent to the opcode, then a one-byte opcode-map
/// lookup, then ModR/M for the group-11 productions, then the operand-size
/// attribute, then the immediate — and NOT an inversion of the encoder's
/// `if gpr8 / else` ladder. It models productions the encoder never emits.
///
/// It fails closed on everything that is not this family. It does NOT require
/// the instruction to fill `bytes`: [`DecodedMovImm::len_consumed`] says how
/// far it read, and [`mov_imm_check`] turns a shortfall into `TrailingBytes`.
pub fn sdm_decode_mov_imm(bytes: &[u8]) -> Result<DecodedMovImm, MovImmDecodeError> {
    let mut at = 0usize;

    // (1) Legacy prefixes, any number, any order (SDM Vol 2A §2.1.1).
    let mut n_66 = 0u8;
    while let Some(&b) = bytes.get(at) {
        match legacy_prefix(b) {
            Some(LegacyPrefix::OperandSize) => {
                n_66 = n_66.saturating_add(1);
                at += 1;
            }
            Some(_) => return Err(MovImmDecodeError::UnmodelledPrefix(b)),
            None => break,
        }
    }

    // (2) At most one REX, and it must immediately precede the opcode.
    let mut rex = None;
    if let Some(&b) = bytes.get(at)
        && is_rex(b)
    {
        rex = Some(b);
        at += 1;
        if let Some(&next) = bytes.get(at)
            && (legacy_prefix(next).is_some() || is_rex(next))
        {
            return Err(MovImmDecodeError::RexNotAdjacentToOpcode { rex: b, next });
        }
    }
    let rex_w = rex.is_some_and(|r| r & 0x08 != 0);
    let rex_b = rex.is_some_and(|r| r & 0x01 != 0);

    // (3) One-byte opcode map.
    let opcode_at = at;
    let Some(&opcode) = bytes.get(at) else {
        return Err(MovImmDecodeError::Truncated {
            needed: at + 1,
            available: bytes.len(),
        });
    };
    at += 1;
    let Some(row) = MOV_IMM_OPCODE_MAP
        .iter()
        .find(|row| row.lo <= opcode && opcode <= row.hi)
    else {
        return Err(MovImmDecodeError::NotMovImmediate { opcode });
    };
    let low3 = if row.modrm {
        let Some(&modrm) = bytes.get(at) else {
            return Err(MovImmDecodeError::Truncated {
                needed: at + 1,
                available: bytes.len(),
            });
        };
        at += 1;
        let (md, reg, rm) = (modrm >> 6, (modrm >> 3) & 0x7, modrm & 0x7);
        if reg != 0 {
            return Err(MovImmDecodeError::UndefinedGroup11Extension { reg });
        }
        if md != 0b11 {
            return Err(MovImmDecodeError::MemoryFormIsAStore { modrm });
        }
        rm
    } else {
        opcode - row.lo
    };

    // (4) Operand-size attribute, (5) immediate length.
    let operand_bits = operand_size_attribute(row.byte_operand, rex_w, n_66 > 0);
    let (imm_len, extension) = immediate_shape(row.form, operand_bits);
    let imm_at = at;
    let Some(imm_bytes) = bytes.get(at..at + imm_len) else {
        return Err(MovImmDecodeError::Truncated {
            needed: at + imm_len,
            available: bytes.len(),
        });
    };
    let mut imm = [0u8; 8];
    for (slot, &b) in imm.iter_mut().zip(imm_bytes) {
        *slot = b;
    }
    at += imm_len;

    // (6) The register. Without ANY REX, byte-register numbers 4..=7 are
    // AH/CH/DH/BH; with a REX present (even a bare 0x40) they are
    // SPL/BPL/SIL/DIL.
    let high_byte = row.byte_operand && rex.is_none() && (4..=7).contains(&low3);
    let reg_number = low3 | (u8::from(rex_b) << 3);

    Ok(DecodedMovImm {
        form: row.form,
        operand_bits,
        reg_number,
        high_byte,
        imm,
        imm_len,
        extension,
        len_consumed: at,
        n_66,
        rex,
        opcode_at,
        imm_at,
    })
}

// ===========================================================================
// (3) Denotation: a write to the 64-bit root register
// ===========================================================================

/// The effect of one MOV r,imm on its destination's 64-bit ROOT register, as a
/// total function of the register's prior value:
///
/// ```text
///   post(old) = (old & !written_mask) | value        with  value & !written_mask == 0
/// ```
///
/// # Lemma (equality of triples IS equality of functions)
///
/// Two `RegWrite`s on the same root denote the same `u64 -> u64` function iff
/// their `(written_mask, value)` pairs are equal.
///
/// *If the masks differ* at some bit `i`, say `i` is written by `a` and
/// preserved by `b`: choose `old` with bit `i` equal to the COMPLEMENT of `a`'s
/// written bit; then `a.post(old)` and `b.post(old)` differ at bit `i`.
/// *If the masks agree and the values differ* at bit `i`, then `i` is inside the
/// mask (the invariant zeroes everything outside it), so the two posts differ
/// at bit `i` for EVERY `old`. Conversely equal pairs give equal functions.
///
/// So comparing `(root, written_mask, value)` decides "for all prior register
/// values" exactly. [`RegWrite::distinguishing_old`] constructs the witness, and
/// `tests/x86_encoding_gate.rs` exercises it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RegWrite {
    /// SDM number of the 64-bit root register written, `0..=15`.
    pub root: u8,
    /// The bits of the root register the instruction WRITES.
    pub written_mask: u64,
    /// The value placed in those bits (zero outside the mask).
    pub value: u64,
}

impl RegWrite {
    /// The root register's value after the write, given its value before.
    pub fn apply(&self, old: u64) -> u64 {
        (old & !self.written_mask) | self.value
    }

    /// A prior register value on which `self` and `other` produce DIFFERENT
    /// results, or `None` iff they denote the same function (same root assumed).
    /// This is the constructive half of the lemma above.
    pub fn distinguishing_old(&self, other: &RegWrite) -> Option<u64> {
        let mask_diff = self.written_mask ^ other.written_mask;
        if mask_diff != 0 {
            // Bits written by exactly one side: make `old` the complement of
            // whatever that side writes there, so the preserving side keeps the
            // complement and the writing side overwrites it.
            let written_there = (self.value | other.value) & mask_diff;
            return Some(!written_there & mask_diff);
        }
        if self.value != other.value {
            return Some(0);
        }
        None
    }
}

impl DecodedMovImm {
    /// The immediate as an unsigned integer: the POSITIONAL sum
    /// `Σ imm[k] · 2^(8k)` — x86 immediates are little-endian (SDM Vol 1
    /// §1.3.1). Written as an explicit sum rather than `from_le_bytes` so it is
    /// not the mirror image of the encoder's `to_le_bytes`.
    pub fn raw_immediate(&self) -> u64 {
        let mut raw = 0u64;
        for (k, &byte) in self.imm[..self.imm_len].iter().enumerate() {
            raw += u64::from(byte) << (8 * k);
        }
        raw
    }

    /// The write this instruction performs, by SDM Vol 1 §3.4.1.1.
    pub fn reg_write(&self) -> RegWrite {
        let raw = self.raw_immediate();
        let root = if self.high_byte {
            self.reg_number - 4
        } else {
            self.reg_number
        };
        let (written_mask, value) = match (self.operand_bits, self.high_byte, self.extension) {
            // 64-bit operand, imm64: the result is the immediate as is.
            (64, _, ImmExtension::Exact) => (u64::MAX, raw),
            // 64-bit operand, imm32: bit 31 is replicated through bits 63:32.
            (64, _, ImmExtension::SignExtend32To64) => {
                let upper = if raw & 0x8000_0000 != 0 {
                    0xFFFF_FFFF_0000_0000
                } else {
                    0
                };
                (u64::MAX, upper | raw)
            }
            // 32-bit operand: the upper 32 bits are WRITTEN — with zero.
            (32, _, _) => (u64::MAX, raw),
            // 16-bit operand: bits 63:16 are left unmodified.
            (16, _, _) => (0xFFFF, raw),
            // AH/CH/DH/BH: bits 15:8 of the root.
            (_, true, _) => (0xFF00, raw << 8),
            // 8-bit low operand: bits 63:8 are left unmodified.
            _ => (0xFF, raw),
        };
        RegWrite {
            root,
            written_mask,
            value,
        }
    }

    /// The SDM name of the decoded destination register, for messages.
    pub fn reg_name(&self) -> &'static str {
        if self.high_byte {
            return SDM_R8_LEGACY
                .get(usize::from(self.reg_number))
                .copied()
                .unwrap_or("<bad-reg>");
        }
        sdm_name(self.reg_number, self.operand_bits).unwrap_or("<bad-reg>")
    }
}

// ===========================================================================
// (4) The source side — from the machine-IR intent alone
// ===========================================================================

/// The write the machine-IR instruction `MovRI dst, imm` MEANS, plus whether
/// the immediate had to be truncated to fit the destination.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntentWrite {
    /// The register write the intent denotes.
    pub write: RegWrite,
    /// True iff `imm` is representable NEITHER as a signed NOR as an unsigned
    /// `w`-bit value for a `w < 64` destination. Reported and counted; NOT a
    /// refutation, because the machine-IR semantics is `imm mod 2^w`.
    pub truncating: bool,
}

/// The intent named a destination that is not a general-purpose register.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnknownRegister(pub String);

/// The SOURCE side: what `MovRI <dst_name>, <imm>` means, stated without any
/// reference to bytes, REX bits or register numbers from the encoder.
///
/// This is the machine-IR semantics the rest of the repository already uses:
/// the optimizer models a 32-bit `MovRI` as `(imm as u32) as i64`
/// (`x86_const_fold::normalize_const_for_vreg`), and post-RA dataflow treats a
/// 32-bit `MovRI` as a FULL definition of the root register and an 8/16-bit one
/// as a PARTIAL write that preserves the rest (`post_ra_dataflow`). It is total:
/// the immediate is taken `mod 2^w`.
///
/// * 64-bit destination: all 64 bits written with `imm`. NO extension rule
///   appears here — which is what lets the 64-bit-intent entries that the
///   encoder aliases to the 5-byte zero-extending form cross-check the machine
///   side's zero-extension rule instead of merely sharing it.
/// * 32-bit destination: all 64 bits written; low 32 are `imm mod 2^32`, upper
///   32 are zero.
/// * 16-bit destination: bits 15:0 written.
/// * 8-bit destination: bits 7:0 written (bits 15:8 for AH/CH/DH/BH, which the
///   machine IR cannot name but the SDM tables can).
pub fn intent_reg_write(dst_name: &str, imm: i64) -> Result<IntentWrite, UnknownRegister> {
    let Some(reg) = sdm_reg(dst_name) else {
        return Err(UnknownRegister(dst_name.to_string()));
    };
    let bits = u32::from(reg.bits);
    let low = |w: u32| (imm as u64) & ((1u64 << w) - 1);
    let (written_mask, value) = match (reg.bits, reg.high_byte) {
        (64, _) => (u64::MAX, imm as u64),
        (32, _) => (u64::MAX, low(32)),
        (16, _) => (0xFFFF, low(16)),
        (_, true) => (0xFF00, low(8) << 8),
        _ => (0xFF, low(8)),
    };
    let truncating = if bits >= 64 {
        false
    } else {
        let fits_signed = imm >= -(1i64 << (bits - 1)) && imm < (1i64 << (bits - 1));
        let fits_unsigned = imm >= 0 && imm < (1i64 << bits);
        !(fits_signed || fits_unsigned)
    };
    Ok(IntentWrite {
        write: RegWrite {
            root: reg.root,
            written_mask,
            value,
        },
        truncating,
    })
}

// ===========================================================================
// (5) Canonicality — every prefix byte and REX bit present must be load-bearing
// ===========================================================================

/// Why an otherwise-decodable encoding is not CANONICAL.
///
/// This is the x86 analogue of the wasm family's canonical-LEB-length pin: the
/// ISA admits value-neutral padding (a redundant 66h, a bare REX, a REX bit the
/// production ignores), and a denotation-only check cannot see it. The rule is
/// stated WITHOUT encoder policy — *every prefix byte and every REX bit present
/// must be load-bearing* — and the FORM is deliberately not pinned: a
/// shortest-form rule would refute today's correct encoder, which emits the
/// 10-byte `REX.W B8 io` for `MOV RAX,-1` where the 7-byte `REX.W C7 /0 id`
/// exists.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NonCanonicalReason {
    /// More than one 66h prefix.
    Duplicate66,
    /// A 66h prefix that does not select the operand size: on a byte production,
    /// or overridden by REX.W.
    OperandSizePrefixNotLoadBearing,
    /// REX.R set: no MOV-immediate production has a ModR/M.reg REGISTER.
    RexRSet,
    /// REX.X set: no MOV-immediate-to-register production has a SIB index.
    RexXSet,
    /// REX.W set on a byte production, where it selects nothing.
    RexWOnByteForm,
    /// A bare `0x40` that changes nothing: it is load-bearing only on a byte
    /// production whose register number is 4..=7 (SPL/BPL/SIL/DIL vs AH..BH).
    BareRexNotLoadBearing,
}

impl fmt::Display for NonCanonicalReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Duplicate66 => "more than one 66h operand-size prefix",
            Self::OperandSizePrefixNotLoadBearing => {
                "a 66h prefix that does not select the operand size (byte production, or \
                 overridden by REX.W)"
            }
            Self::RexRSet => "REX.R is set but the production has no ModR/M.reg register",
            Self::RexXSet => "REX.X is set but the production has no SIB index",
            Self::RexWOnByteForm => "REX.W is set on a byte production",
            Self::BareRexNotLoadBearing => {
                "a bare REX 0x40 that does not change which register is addressed"
            }
        })
    }
}

/// The canonicality rule list. `Ok(())` iff every prefix byte and REX bit
/// present in `d` is load-bearing.
pub fn canonicality(d: &DecodedMovImm) -> Result<(), NonCanonicalReason> {
    if d.n_66 > 1 {
        return Err(NonCanonicalReason::Duplicate66);
    }
    if d.n_66 == 1 && d.operand_bits != 16 {
        return Err(NonCanonicalReason::OperandSizePrefixNotLoadBearing);
    }
    if let Some(rex) = d.rex {
        if rex & 0x04 != 0 {
            return Err(NonCanonicalReason::RexRSet);
        }
        if rex & 0x02 != 0 {
            return Err(NonCanonicalReason::RexXSet);
        }
        if d.operand_bits == 8 && rex & 0x08 != 0 {
            return Err(NonCanonicalReason::RexWOnByteForm);
        }
        let low3 = d.reg_number & 0x7;
        let bare_is_load_bearing = d.operand_bits == 8 && (4..=7).contains(&low3);
        if rex == 0x40 && !bare_is_load_bearing {
            return Err(NonCanonicalReason::BareRexNotLoadBearing);
        }
    }
    Ok(())
}

// ===========================================================================
// (6) The obligation, with TYPED refutations
// ===========================================================================

/// Why the emitted bytes do NOT denote the intended register write. Typed, so a
/// negative control asserts the REASON it was refuted and cannot pass by being
/// rejected for some unrelated reason.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MovImmRefutation {
    /// The independent decoder rejected the bytes.
    Decode(MovImmDecodeError),
    /// The decoder consumed fewer bytes than were emitted for this instruction.
    TrailingBytes {
        /// Bytes the decoded instruction occupies.
        consumed: usize,
        /// Bytes that were emitted.
        len: usize,
    },
    /// A prefix byte or REX bit that is not load-bearing.
    NonCanonical(NonCanonicalReason),
    /// The intent's destination is not a general-purpose register.
    UnknownIntentRegister(String),
    /// The bytes write a different ROOT register than the intent names.
    Register {
        /// SDM number of the root the intent names.
        intended_root: u8,
        /// SDM number of the root the bytes write.
        decoded_root: u8,
    },
    /// The bytes write a different SET OF BITS of the root register (wrong
    /// width, or the AH..BH slot instead of the low byte).
    WrittenBits {
        /// Bits the intent writes.
        intended_mask: u64,
        /// Bits the bytes write.
        decoded_mask: u64,
    },
    /// Same register, same bits, DIFFERENT VALUE — a wrong immediate, a wrong
    /// byte order, or sign- where zero-extension was meant (or the reverse).
    Value {
        /// The value the intent writes.
        intended: u64,
        /// The value the bytes write.
        decoded: u64,
    },
}

/// The reason CLASS of a refutation, for negative controls to assert against.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RefutationClass {
    /// [`MovImmDecodeError::Truncated`].
    DecodeTruncated,
    /// [`MovImmDecodeError::UnmodelledPrefix`].
    DecodeUnmodelledPrefix,
    /// [`MovImmDecodeError::RexNotAdjacentToOpcode`].
    DecodeRexNotAdjacent,
    /// [`MovImmDecodeError::NotMovImmediate`].
    DecodeNotMovImmediate,
    /// [`MovImmDecodeError::MemoryFormIsAStore`].
    DecodeMemoryForm,
    /// [`MovImmDecodeError::UndefinedGroup11Extension`].
    DecodeGroup11,
    /// [`MovImmRefutation::TrailingBytes`].
    TrailingBytes,
    /// [`MovImmRefutation::NonCanonical`].
    NonCanonical,
    /// [`MovImmRefutation::UnknownIntentRegister`].
    UnknownIntentRegister,
    /// [`MovImmRefutation::Register`].
    Register,
    /// [`MovImmRefutation::WrittenBits`].
    WrittenBits,
    /// [`MovImmRefutation::Value`].
    Value,
}

impl MovImmRefutation {
    /// The reason class of this refutation.
    pub fn class(&self) -> RefutationClass {
        match self {
            Self::Decode(MovImmDecodeError::Truncated { .. }) => RefutationClass::DecodeTruncated,
            Self::Decode(MovImmDecodeError::UnmodelledPrefix(_)) => {
                RefutationClass::DecodeUnmodelledPrefix
            }
            Self::Decode(MovImmDecodeError::RexNotAdjacentToOpcode { .. }) => {
                RefutationClass::DecodeRexNotAdjacent
            }
            Self::Decode(MovImmDecodeError::NotMovImmediate { .. }) => {
                RefutationClass::DecodeNotMovImmediate
            }
            Self::Decode(MovImmDecodeError::MemoryFormIsAStore { .. }) => {
                RefutationClass::DecodeMemoryForm
            }
            Self::Decode(MovImmDecodeError::UndefinedGroup11Extension { .. }) => {
                RefutationClass::DecodeGroup11
            }
            Self::TrailingBytes { .. } => RefutationClass::TrailingBytes,
            Self::NonCanonical(_) => RefutationClass::NonCanonical,
            Self::UnknownIntentRegister(_) => RefutationClass::UnknownIntentRegister,
            Self::Register { .. } => RefutationClass::Register,
            Self::WrittenBits { .. } => RefutationClass::WrittenBits,
            Self::Value { .. } => RefutationClass::Value,
        }
    }
}

impl fmt::Display for MovImmRefutation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Decode(e) => write!(f, "independent SDM decoder REJECTED the bytes: {e}"),
            Self::TrailingBytes { consumed, len } => write!(
                f,
                "decode consumed {consumed} of {len} emitted byte(s) — the rest is not part of \
                 this instruction"
            ),
            Self::NonCanonical(why) => write!(f, "non-canonical encoding: {why}"),
            Self::UnknownIntentRegister(name) => write!(
                f,
                "intent destination `{name}` is not a general-purpose register"
            ),
            Self::Register {
                intended_root,
                decoded_root,
            } => write!(
                f,
                "destination register: intent writes root {} but the bytes write root {}",
                sdm_name(*intended_root, 64).unwrap_or("<bad-reg>"),
                sdm_name(*decoded_root, 64).unwrap_or("<bad-reg>"),
            ),
            Self::WrittenBits {
                intended_mask,
                decoded_mask,
            } => write!(
                f,
                "written bits: intent writes mask {intended_mask:#018x} but the bytes write \
                 {decoded_mask:#018x} (wrong width or high-byte slot)"
            ),
            Self::Value { intended, decoded } => write!(
                f,
                "written value: intent writes {intended:#018x} but the bytes write \
                 {decoded:#018x}"
            ),
        }
    }
}

/// What a HOLDING obligation established.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MovImmHolds {
    /// The instruction the independent decoder read.
    pub decoded: DecodedMovImm,
    /// The register write both sides agree on.
    pub write: RegWrite,
    /// The intent's immediate was outside both the signed and the unsigned
    /// range of its destination width (counted, not refuted).
    pub truncating_intent: bool,
}

/// THE OBLIGATION. `bytes` — the REAL emitted encoding of ONE `MovRI` — denote,
/// under the independent SDM decode, exactly the 64-bit register write that the
/// machine-IR intent `(dst_name, imm)` means, with no byte left over and no
/// prefix byte or REX bit that is not load-bearing.
///
/// Checks run in a fixed order and each failure is a typed
/// [`MovImmRefutation`]: decode, framing, canonicality, intent register, root
/// register, written bits, written value.
pub fn mov_imm_check(
    dst_name: &str,
    imm: i64,
    bytes: &[u8],
) -> Result<MovImmHolds, MovImmRefutation> {
    let decoded = sdm_decode_mov_imm(bytes).map_err(MovImmRefutation::Decode)?;
    if decoded.len_consumed != bytes.len() {
        return Err(MovImmRefutation::TrailingBytes {
            consumed: decoded.len_consumed,
            len: bytes.len(),
        });
    }
    canonicality(&decoded).map_err(MovImmRefutation::NonCanonical)?;
    let intent = intent_reg_write(dst_name, imm)
        .map_err(|UnknownRegister(name)| MovImmRefutation::UnknownIntentRegister(name))?;
    let machine = decoded.reg_write();
    if machine.root != intent.write.root {
        return Err(MovImmRefutation::Register {
            intended_root: intent.write.root,
            decoded_root: machine.root,
        });
    }
    if machine.written_mask != intent.write.written_mask {
        return Err(MovImmRefutation::WrittenBits {
            intended_mask: intent.write.written_mask,
            decoded_mask: machine.written_mask,
        });
    }
    if machine.value != intent.write.value {
        return Err(MovImmRefutation::Value {
            intended: intent.write.value,
            decoded: machine.value,
        });
    }
    Ok(MovImmHolds {
        decoded,
        write: machine,
        truncating_intent: intent.truncating,
    })
}

/// [`mov_imm_check`] for a `trust-cg-ir` physical register. The register is
/// handed over by its assembly NAME — `trust-cg-ir`'s name table, the one its
/// `Display` prints — and never by `hw_enc`, which is the table the encoder
/// uses and therefore the one under test. A non-GPR destination refutes as
/// `UnknownIntentRegister`.
pub fn mov_imm_check_for_preg(
    dst: X86PReg,
    imm: i64,
    bytes: &[u8],
) -> Result<MovImmHolds, MovImmRefutation> {
    mov_imm_check(x86_preg_name(dst), imm, bytes)
}

/// One obligation and its verdict, named so a failure says what it was about.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MovImmObligation {
    /// What the obligation claims, in one line.
    pub name: String,
    /// `Ok` iff the bytes denote the intended write.
    pub outcome: Result<MovImmHolds, MovImmRefutation>,
}

impl MovImmObligation {
    /// True iff the obligation holds (the only outcome that is credit).
    pub fn is_holding(&self) -> bool {
        self.outcome.is_ok()
    }

    /// The refutation's reason class, if refuted.
    pub fn refutation_class(&self) -> Option<RefutationClass> {
        self.outcome.as_ref().err().map(MovImmRefutation::class)
    }
}

/// Build the named obligation for one emitted `MovRI`.
pub fn mov_imm_obligation(dst_name: &str, imm: i64, bytes: &[u8]) -> MovImmObligation {
    MovImmObligation {
        name: format!(
            "MOV {dst_name},{imm:#x} -> emitted {bytes:02x?} decodes (SDM) to the same 64-bit \
             register write"
        ),
        outcome: mov_imm_check(dst_name, imm, bytes),
    }
}

// ===========================================================================
// (7) Physical form classes — what the corpus must cover to earn the credit
// ===========================================================================

/// The physical form classes the encoder emits. Computed from the DECODED
/// instruction plus the intent's width, so a corpus cannot claim a class by
/// labelling itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum MovImmFormClass {
    /// `B0+rb ib`, no REX (AL/CL/DL/BL).
    Byte,
    /// `40 B0+rb ib` — the forced bare REX for SPL/BPL/SIL/DIL.
    ByteBareRex,
    /// `41 B0+rb ib` — R8B..R15B.
    ByteRexB,
    /// `66 B8+rw iw`.
    Word,
    /// `66 41 B8+rw iw`.
    WordRexB,
    /// `B8+rd id` for a 32-bit intent.
    Dword,
    /// `41 B8+rd id` for a 32-bit intent.
    DwordRexB,
    /// `B8+rd id` for a 64-bit intent (the zero-extending alias).
    QwordAliasedToDword,
    /// `41 B8+rd id` for a 64-bit intent.
    QwordAliasedToDwordRexB,
    /// `48 B8+rd io` — movabs.
    Movabs,
    /// `49 B8+rd io`.
    MovabsRexB,
}

/// Every class the credit hook demands at least one corpus entry of.
pub const REQUIRED_FORM_CLASSES: [MovImmFormClass; 11] = [
    MovImmFormClass::Byte,
    MovImmFormClass::ByteBareRex,
    MovImmFormClass::ByteRexB,
    MovImmFormClass::Word,
    MovImmFormClass::WordRexB,
    MovImmFormClass::Dword,
    MovImmFormClass::DwordRexB,
    MovImmFormClass::QwordAliasedToDword,
    MovImmFormClass::QwordAliasedToDwordRexB,
    MovImmFormClass::Movabs,
    MovImmFormClass::MovabsRexB,
];

/// Classify a holding `+r`-form encoding. `None` for the group-11 productions
/// (which the encoder does not emit) and for AH/CH/DH/BH.
pub fn form_class(intent_bits: u8, d: &DecodedMovImm) -> Option<MovImmFormClass> {
    use MovImmFormClass as C;
    if d.high_byte || !matches!(d.form, MovImmForm::B0PlusRb | MovImmForm::B8PlusRd) {
        return None;
    }
    let rex_b = d.rex.is_some_and(|r| r & 1 != 0);
    Some(match (d.operand_bits, intent_bits, rex_b) {
        (8, _, true) => C::ByteRexB,
        (8, _, false) if d.rex.is_some() => C::ByteBareRex,
        (8, _, false) => C::Byte,
        (16, _, false) => C::Word,
        (16, _, true) => C::WordRexB,
        (32, 64, false) => C::QwordAliasedToDword,
        (32, 64, true) => C::QwordAliasedToDwordRexB,
        (32, _, false) => C::Dword,
        (32, _, true) => C::DwordRexB,
        (_, _, false) => C::Movabs,
        (_, _, true) => C::MovabsRexB,
    })
}

// ===========================================================================
// (8) Negative controls — deliberately wrong wirings that MUST refute
// ===========================================================================

/// Which side of the obligation a negative control moved.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MutantSide {
    /// The real bytes were mutated; the intent is unchanged.
    Machine,
    /// The same real bytes; a different claim about what they mean.
    Source,
}

/// One negative control: a wrong `(intent, bytes)` pairing and the reason class
/// it must be refuted for.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MovImmMutant {
    /// The control's label; one of [`REQUIRED_MUTANT_LABELS`].
    pub label: &'static str,
    /// Which side moved.
    pub side: MutantSide,
    /// The (possibly re-claimed) destination register name.
    pub dst_name: String,
    /// The (possibly re-claimed) immediate.
    pub imm: i64,
    /// The (possibly mutated) bytes.
    pub bytes: Vec<u8>,
    /// The reason class the obligation must refute this control for.
    pub expect: RefutationClass,
}

/// M1: a different register in the opcode's low 3 bits (or ModR/M.rm).
pub const M1_WRONG_REG_LOW3: &str = "M1 wrong register (low 3 register bits)";
/// M2: REX.B toggled, inserted or stripped — the high-register bit.
pub const M2_WRONG_REG_REX_B: &str = "M2 wrong register (REX.B toggled/inserted/stripped)";
/// M3a: a negative 64-bit intent re-encoded as the ZERO-extending `B8+rd id`.
pub const M3A_ZERO_FOR_SIGN: &str =
    "M3a zero-extending B8+rd imm32 where a negative imm64 was meant";
/// M3b: a bit-31-set zero-extended value re-encoded as SIGN-extending `REX.W C7 /0`.
pub const M3B_SIGN_FOR_ZERO: &str =
    "M3b sign-extending REX.W C7 /0 imm32 where zero-extension was meant";
/// M4a: the top 4 immediate bytes of a movabs dropped.
pub const M4A_IMM64_DROPPED_HALF: &str = "M4a movabs with the top 4 immediate bytes dropped";
/// M4b: the top 4 immediate bytes of a movabs zeroed in place.
pub const M4B_IMM64_ZEROED_HALF: &str = "M4b movabs with the top 4 immediate bytes zeroed";
/// M5a: 66h inserted before an imm32 form.
pub const M5A_66_ON_DWORD: &str = "M5a 66h inserted before a B8+rd imm32 form";
/// M5b: REX.W cleared on a movabs.
pub const M5B_REX_W_CLEARED: &str = "M5b REX.W cleared on a movabs";
/// M5c: REX.W set on an imm32 form.
pub const M5C_REX_W_SET: &str = "M5c REX.W set on a B8+rd imm32 form";
/// M5d: the 66h prefix stripped from a 16-bit form.
pub const M5D_66_STRIPPED: &str = "M5d 66h stripped from a 16-bit form";
/// M6: the opcode byte replaced by a non-MOV opcode that takes the same immediate.
pub const M6_WRONG_OPCODE: &str = "M6 wrong opcode (ADD/PUSH/MOV-moffs/TEST/group-1)";
/// M6b: a zero intent emitted as the flag-clobbering `XOR r,r` zeroing idiom.
pub const M6B_FLAG_CLOBBERING_ZERO_IDIOM: &str =
    "M6b zero intent emitted as the flag-clobbering XOR r,r zeroing idiom";
/// M7a: one immediate byte corrupted in its low bit.
pub const M7A_IMM_BYTE_FLIP_LOW: &str = "M7a one immediate byte ^ 0x01";
/// M7b: one immediate byte corrupted in its high bit.
pub const M7B_IMM_BYTE_FLIP_HIGH: &str = "M7b one immediate byte ^ 0x80";
/// M7c: the immediate bytes reversed (byte order).
pub const M7C_IMM_REVERSED: &str = "M7c immediate bytes reversed (byte order)";
/// M8: the forced bare REX dropped from SPL/BPL/SIL/DIL.
pub const M8_DROPPED_FORCED_REX: &str = "M8 forced bare REX dropped (SPL..DIL becomes AH..BH)";
/// M9a: a redundant bare REX inserted.
pub const M9A_REDUNDANT_BARE_REX: &str = "M9a redundant bare REX 0x40 inserted";
/// M9b: REX.R set.
pub const M9B_REX_R: &str = "M9b REX.R set";
/// M9c: REX.X set.
pub const M9C_REX_X: &str = "M9c REX.X set";
/// M9d: REX.W set on a byte form.
pub const M9D_REX_W_ON_BYTE: &str = "M9d REX.W set on a byte form";
/// M9e: a second 66h.
pub const M9E_DOUBLE_66: &str = "M9e 66h doubled";
/// M9f: 66h together with REX.W.
pub const M9F_66_WITH_REX_W: &str = "M9f 66h together with REX.W";
/// M9g: 66h on a byte form.
pub const M9G_66_ON_BYTE: &str = "M9g 66h on a byte form";
/// M9h: an unmodelled legacy prefix.
pub const M9H_UNMODELLED_PREFIX: &str =
    "M9h unmodelled legacy prefix (every group-1, group-2 and group-4 byte)";
/// M10a: one byte appended.
pub const M10A_APPENDED_BYTE: &str = "M10a one byte appended";
/// M10b: the last byte dropped.
pub const M10B_DROPPED_LAST_BYTE: &str = "M10b last byte dropped";
/// S1: the same bytes claimed to carry `imm + 1`.
pub const S1_IMM_PLUS_ONE: &str = "S1 intent immediate + 1";
/// S2: the same bytes claimed to carry an immediate with the upper 32 bits flipped.
pub const S2_UPPER_HALF: &str = "S2 64-bit intent with the upper 32 bits flipped";
/// S3: the same bytes claimed to write a sibling register.
pub const S3_SIBLING_REG: &str = "S3 intent register sibling";
/// S4: the same bytes claimed at a different width whose denotation differs.
pub const S4_WIDTH_RECLAIM: &str = "S4 intent width re-claimed where the denotation differs";

/// Every control label. The credit hook demands each fires at least once over
/// the corpus, so a facet cannot go quietly unexercised.
pub const REQUIRED_MUTANT_LABELS: &[&str] = &[
    M1_WRONG_REG_LOW3,
    M2_WRONG_REG_REX_B,
    M3A_ZERO_FOR_SIGN,
    M3B_SIGN_FOR_ZERO,
    M4A_IMM64_DROPPED_HALF,
    M4B_IMM64_ZEROED_HALF,
    M5A_66_ON_DWORD,
    M5B_REX_W_CLEARED,
    M5C_REX_W_SET,
    M5D_66_STRIPPED,
    M6_WRONG_OPCODE,
    M6B_FLAG_CLOBBERING_ZERO_IDIOM,
    M7A_IMM_BYTE_FLIP_LOW,
    M7B_IMM_BYTE_FLIP_HIGH,
    M7C_IMM_REVERSED,
    M8_DROPPED_FORCED_REX,
    M9A_REDUNDANT_BARE_REX,
    M9B_REX_R,
    M9C_REX_X,
    M9D_REX_W_ON_BYTE,
    M9E_DOUBLE_66,
    M9F_66_WITH_REX_W,
    M9G_66_ON_BYTE,
    M9H_UNMODELLED_PREFIX,
    M10A_APPENDED_BYTE,
    M10B_DROPPED_LAST_BYTE,
    S1_IMM_PLUS_ONE,
    S2_UPPER_HALF,
    S3_SIBLING_REG,
    S4_WIDTH_RECLAIM,
];

/// Reassemble an instruction from its SDM parts: `[66h]* [REX] opcode.. imm..`.
fn assemble(n_66: usize, rex: Option<u8>, opcode: &[u8], imm: &[u8]) -> Vec<u8> {
    let mut out = vec![0x66u8; n_66];
    out.extend(rex);
    out.extend_from_slice(opcode);
    out.extend_from_slice(imm);
    out
}

/// The negative-control battery for ONE holding `(intent, bytes)` pair.
///
/// Each control is a small SDM-format mutation of the REAL bytes (machine side
/// moved) or a different claim about the same real bytes (source side moved),
/// paired with the reason class the obligation MUST refute it for. The expected
/// classes are stated from the SDM, not computed by running the obligation.
///
/// Returns an empty battery if `(dst_name, imm, bytes)` does not itself hold —
/// a control is only meaningful relative to a holding original.
pub fn mov_imm_mutants(dst_name: &str, imm: i64, bytes: &[u8]) -> Vec<MovImmMutant> {
    let Ok(holds) = mov_imm_check(dst_name, imm, bytes) else {
        return Vec::new();
    };
    let Some(intent_reg) = sdm_reg(dst_name) else {
        return Vec::new();
    };
    let d = holds.decoded;
    let opcode = &bytes[d.opcode_at..d.imm_at];
    let imm_bytes = &bytes[d.imm_at..];
    let n_66 = usize::from(d.n_66);
    let low3 = d.reg_number & 0x7;
    let rex_b = d.rex.is_some_and(|r| r & 1 != 0);
    let is_byte = d.operand_bits == 8;
    let plus_r = matches!(d.form, MovImmForm::B0PlusRb | MovImmForm::B8PlusRd);
    let is_movabs = d.form == MovImmForm::B8PlusRd && d.operand_bits == 64;
    let is_dword_plus_r = d.form == MovImmForm::B8PlusRd && d.operand_bits == 32;

    let mut out = Vec::new();
    let mut machine = |label: &'static str, mutated: Vec<u8>, expect: RefutationClass| {
        out.push(MovImmMutant {
            label,
            side: MutantSide::Machine,
            dst_name: dst_name.to_string(),
            imm,
            bytes: mutated,
            expect,
        });
    };
    let with_low3 = |n: u8| -> Vec<u8> {
        let mut o = opcode.to_vec();
        // `+r` productions carry the register in the opcode byte; the group-11
        // productions carry it in ModR/M.rm.
        let at = usize::from(!plus_r);
        if let Some(b) = o.get_mut(at) {
            *b = (*b & !0x7) | (n & 0x7);
        }
        o
    };

    // M1. A different register number in the low 3 bits. Under a bare REX the
    // replacement stays inside 4..=7 so the mutant is still CANONICAL and must
    // be refuted as a wrong REGISTER, not as redundant padding.
    let other_low3 = if d.rex == Some(0x40) {
        4 + ((low3.saturating_sub(4) + 1) % 4)
    } else {
        (low3 + 1) & 0x7
    };
    machine(
        M1_WRONG_REG_LOW3,
        assemble(n_66, d.rex, &with_low3(other_low3), imm_bytes),
        RefutationClass::Register,
    );

    // M2. The high-register bit: r8d <-> eax and friends.
    let rex_b_moved = match d.rex {
        None => Some(0x41),
        Some(0x41) => None,
        Some(r) => Some(r ^ 0x01),
    };
    machine(
        M2_WRONG_REG_REX_B,
        assemble(n_66, rex_b_moved, opcode, imm_bytes),
        RefutationClass::Register,
    );

    // M3a. THE ROW'S NAMED HAZARD. A 64-bit intent in [-2^31, 0) squeezed into
    // the 5-byte `B8+rd id`: it decodes cleanly, and the hardware ZERO-extends
    // it — 0x00000000_FFFFFFFF where 0xFFFFFFFF_FFFFFFFF was meant.
    if is_movabs && intent_reg.bits == 64 && (i64::from(i32::MIN)..0).contains(&imm) {
        machine(
            M3A_ZERO_FOR_SIGN,
            assemble(0, rex_b.then_some(0x41), opcode, &imm_bytes[..4]),
            RefutationClass::Value,
        );
    }
    // M3b. The other direction: a zero-extended value with bit 31 set moved to
    // the SIGN-extending `REX.W C7 /0 id`.
    if is_dword_plus_r && d.raw_immediate() & 0x8000_0000 != 0 {
        machine(
            M3B_SIGN_FOR_ZERO,
            assemble(
                0,
                Some(0x48 | u8::from(rex_b)),
                &[0xC7, 0xC0 | low3],
                imm_bytes,
            ),
            RefutationClass::Value,
        );
    }

    // M4. Truncated imm64.
    if is_movabs {
        machine(
            M4A_IMM64_DROPPED_HALF,
            assemble(n_66, d.rex, opcode, &imm_bytes[..4]),
            RefutationClass::DecodeTruncated,
        );
        if imm_bytes[4..].iter().any(|&b| b != 0) {
            let mut zeroed = imm_bytes.to_vec();
            zeroed[4..].fill(0);
            machine(
                M4B_IMM64_ZEROED_HALF,
                assemble(n_66, d.rex, opcode, &zeroed),
                RefutationClass::Value,
            );
        }
        machine(
            M5B_REX_W_CLEARED,
            assemble(n_66, d.rex.map(|r| r & !0x08), opcode, imm_bytes),
            RefutationClass::TrailingBytes,
        );
    }

    // M5. Wrong-width form.
    if is_dword_plus_r {
        machine(
            M5A_66_ON_DWORD,
            assemble(1, d.rex, opcode, imm_bytes),
            RefutationClass::TrailingBytes,
        );
        machine(
            M5C_REX_W_SET,
            assemble(n_66, Some(d.rex.unwrap_or(0x40) | 0x08), opcode, imm_bytes),
            RefutationClass::DecodeTruncated,
        );
    }
    if d.operand_bits == 16 {
        machine(
            M5D_66_STRIPPED,
            assemble(0, d.rex, opcode, imm_bytes),
            RefutationClass::DecodeTruncated,
        );
        machine(
            M9E_DOUBLE_66,
            assemble(2, d.rex, opcode, imm_bytes),
            RefutationClass::NonCanonical,
        );
    }

    // M6. A different opcode that takes the same immediate. Only the four MOV
    // productions decode at all. That CLOSURE is the only part of "MOV r,imm
    // does not write RFLAGS" this obligation enforces. That the four productions
    // themselves write no flags is transcribed from the SDM and named as trust
    // base in `X86_MOV_IMM_DEFERRALS`. `RegWrite` has no flags component, so
    // nothing here COMPARES a flags effect.
    let wrong_opcodes: &[u8] = match d.form {
        // ADD eAX,imm32 / PUSH imm32 / MOV eAX,moffs.
        MovImmForm::B8PlusRd => &[0x05, 0x68, 0xA1],
        // TEST AL,imm8 / ADD AL,imm8.
        MovImmForm::B0PlusRb => &[0xA8, 0x04],
        // Group 1 (ALU r/m,imm) / group 2 (shift r/m,imm8).
        MovImmForm::C6Slash0 | MovImmForm::C7Slash0 => &[0x81, 0xC1],
    };
    for &wrong in wrong_opcodes {
        let mut o = opcode.to_vec();
        o[0] = wrong;
        machine(
            M6_WRONG_OPCODE,
            assemble(n_66, d.rex, &o, imm_bytes),
            RefutationClass::DecodeNotMovImmediate,
        );
    }
    // M6b. The flags hazard made concrete. A zero intent emitted as `XOR r,r`
    // leaves the right VALUE in the register, but XOR clobbers RFLAGS, and the
    // backend relies on MovRI keeping the flags between a CMP and its
    // Jcc/SETcc/CMOVcc. `XOR r/m,r` is `31 /r` (`30 /r` for bytes). REX.R and
    // REX.B both carry the high register bit, the operand-size prefixes are
    // unchanged, and ModR/M is mod=11, reg=rm=the register. It must refute as
    // "not a MOV-immediate production": closure, not a flags model.
    if holds.write.value == 0 && plus_r {
        let xor_rex = if rex_b {
            Some(0x45 | if d.operand_bits == 64 { 0x08 } else { 0 })
        } else if d.operand_bits == 64 {
            Some(0x48)
        } else {
            d.rex
        };
        let xor_opcode = if is_byte { 0x30 } else { 0x31 };
        machine(
            M6B_FLAG_CLOBBERING_ZERO_IDIOM,
            assemble(n_66, xor_rex, &[xor_opcode, 0xC0 | (low3 << 3) | low3], &[]),
            RefutationClass::DecodeNotMovImmediate,
        );
    }

    // M7. Wrong immediate: every byte, low bit and high bit; and byte order.
    for k in 0..imm_bytes.len() {
        for (label, flip) in [
            (M7A_IMM_BYTE_FLIP_LOW, 0x01u8),
            (M7B_IMM_BYTE_FLIP_HIGH, 0x80u8),
        ] {
            let mut m = imm_bytes.to_vec();
            m[k] ^= flip;
            machine(
                label,
                assemble(n_66, d.rex, opcode, &m),
                RefutationClass::Value,
            );
        }
    }
    let reversed: Vec<u8> = imm_bytes.iter().rev().copied().collect();
    if reversed != imm_bytes {
        machine(
            M7C_IMM_REVERSED,
            assemble(n_66, d.rex, opcode, &reversed),
            RefutationClass::Value,
        );
    }

    // M8. The forced bare REX dropped: SIL becomes DH, a different ROOT.
    if d.rex == Some(0x40) {
        machine(
            M8_DROPPED_FORCED_REX,
            assemble(n_66, None, opcode, imm_bytes),
            RefutationClass::Register,
        );
    }

    // M9. Value-neutral padding — invisible to a denotation-only check.
    if !d.high_byte {
        if d.rex.is_none() {
            machine(
                M9A_REDUNDANT_BARE_REX,
                assemble(n_66, Some(0x40), opcode, imm_bytes),
                RefutationClass::NonCanonical,
            );
        }
        machine(
            M9B_REX_R,
            assemble(n_66, Some(d.rex.unwrap_or(0x40) | 0x04), opcode, imm_bytes),
            RefutationClass::NonCanonical,
        );
        machine(
            M9C_REX_X,
            assemble(n_66, Some(d.rex.unwrap_or(0x40) | 0x02), opcode, imm_bytes),
            RefutationClass::NonCanonical,
        );
        if is_byte {
            machine(
                M9D_REX_W_ON_BYTE,
                assemble(n_66, Some(d.rex.unwrap_or(0x40) | 0x08), opcode, imm_bytes),
                RefutationClass::NonCanonical,
            );
        }
    }
    if d.operand_bits == 64 {
        machine(
            M9F_66_WITH_REX_W,
            assemble(1, d.rex, opcode, imm_bytes),
            RefutationClass::NonCanonical,
        );
    }
    if is_byte {
        machine(
            M9G_66_ON_BYTE,
            assemble(1, d.rex, opcode, imm_bytes),
            RefutationClass::NonCanonical,
        );
    }
    // Every legacy prefix other than 66h, taken from SDM Vol 2A §2.1.1 group
    // by group rather than from `LEGACY_PREFIXES`. A byte missing from that
    // table would be misread as an opcode and refute for the WRONG reason.
    for prefix in [
        0xF0u8, 0xF2, 0xF3, // group 1
        0x26, 0x2E, 0x36, 0x3E, 0x64, 0x65, // group 2
        0x67, // group 4
    ] {
        let mut m = vec![prefix];
        m.extend_from_slice(bytes);
        machine(
            M9H_UNMODELLED_PREFIX,
            m,
            RefutationClass::DecodeUnmodelledPrefix,
        );
    }

    // M10. Framing.
    let mut appended = bytes.to_vec();
    appended.push(0x90);
    machine(M10A_APPENDED_BYTE, appended, RefutationClass::TrailingBytes);
    machine(
        M10B_DROPPED_LAST_BYTE,
        bytes[..bytes.len() - 1].to_vec(),
        RefutationClass::DecodeTruncated,
    );

    // ---- SOURCE side moved: the same real bytes, a different claim ----------
    let mut source = |label: &'static str, name: &str, claimed: i64, expect: RefutationClass| {
        out.push(MovImmMutant {
            label,
            side: MutantSide::Source,
            dst_name: name.to_string(),
            imm: claimed,
            bytes: bytes.to_vec(),
            expect,
        });
    };

    // S1. `imm + 1 mod 2^w` differs from `imm mod 2^w` at every width.
    source(
        S1_IMM_PLUS_ONE,
        dst_name,
        imm.wrapping_add(1),
        RefutationClass::Value,
    );

    // S2. The 64-bit source side carries NO extension rule (value = imm), so
    // flipping the claimed upper half against the zero-extending 5-byte alias
    // is the zero-extension rule checked from the other side.
    if intent_reg.bits == 64 {
        source(
            S2_UPPER_HALF,
            dst_name,
            imm ^ (0xFFFF_FFFF_0000_0000u64 as i64),
            RefutationClass::Value,
        );
    }

    // S3. A sibling register of the same width.
    if !intent_reg.high_byte {
        for sibling_root in [(intent_reg.root + 1) % 16, intent_reg.root ^ 8] {
            if let Some(name) = sdm_name(sibling_root, intent_reg.bits) {
                source(S3_SIBLING_REG, name, imm, RefutationClass::Register);
            }
        }

        // S4. A different WIDTH of the same root, wherever the denotation
        // really differs. 32- and 64-bit destinations both write all 64 bits;
        // 16- and 8-bit ones write only their own. So a re-claim across that
        // line, or between 8 and 16, is a WRITTEN-BITS refutation; a re-claim
        // between 32 and 64 is a VALUE refutation iff the immediate's upper 32
        // bits are non-zero — and otherwise it is NOT a control at all, because
        // `mov eax,42` IS `mov rax,42`. That pair must HOLD, and the gate test
        // asserts that it does: the comparison is on denotation, not spelling.
        let writes_whole_root = |bits: u8| bits >= 32;
        for claimed_bits in [8u8, 16, 32, 64] {
            if claimed_bits == intent_reg.bits {
                continue;
            }
            let Some(name) = sdm_name(intent_reg.root, claimed_bits) else {
                continue;
            };
            let expect = if writes_whole_root(claimed_bits) && writes_whole_root(intent_reg.bits) {
                if (imm as u64) >> 32 == 0 {
                    continue;
                }
                RefutationClass::Value
            } else {
                RefutationClass::WrittenBits
            };
            source(S4_WIDTH_RECLAIM, name, imm, expect);
        }
    }

    out
}

/// One hand-written vector: `(why, intent register, intent immediate, bytes)`.
pub type SdmHandVector = (&'static str, &'static str, i64, &'static [u8]);

/// Encodings typed from the SDM that the encoder NEVER emits, each of which
/// must HOLD. They show the decoder was not obtained by inverting `encode.rs`:
/// an inversion of its four-way ladder knows nothing of group 11, of AH..BH, or
/// of the sign-extending imm32.
pub const SDM_HAND_VECTORS_HOLD: &[SdmHandVector] = &[
    (
        "REX.W C7 /0 id sign-extends: the 7-byte MOV RAX,-1",
        "rax",
        -1,
        &[0x48, 0xC7, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF],
    ),
    (
        "REX.WB C7 /0 id with bit 31 clear: sign- and zero-extension agree",
        "r10",
        0x7FFF_FFFF,
        &[0x49, 0xC7, 0xC2, 0xFF, 0xFF, 0xFF, 0x7F],
    ),
    (
        "B0+rb without REX, number 4: AH (bits 15:8 of RAX)",
        "ah",
        7,
        &[0xB4, 0x07],
    ),
    // All four high-byte registers, not only the two ends. The decoder derives
    // the root as `number - 4` while the source side looks the NAME up in
    // `SDM_R8_LEGACY`, so a permutation of that table (CH/DH swapped, say)
    // refutes one of these as a wrong Register.
    ("B0+rb without REX, number 5: CH", "ch", 0x5A, &[0xB5, 0x5A]),
    ("B0+rb without REX, number 6: DH", "dh", 0x6B, &[0xB6, 0x6B]),
    ("B0+rb without REX, number 7: BH", "bh", 0x80, &[0xB7, 0x80]),
    (
        "C6 /0 ib with rm=5 and no REX: CH",
        "ch",
        0x11,
        &[0xC6, 0xC5, 0x11],
    ),
    (
        // The imm64 form of a value that FITS in 32 bits. The encoder picks a
        // shorter form for 7, so this is never emitted, yet it is canonical
        // (no redundant prefix) and must still denote `r15 := 7`. An earlier
        // version used a genuinely 64-bit immediate here, which the live encoder
        // DOES emit byte-for-byte, so it failed the "never emitted" premise.
        "REX.WB B8+7 io: movabs R15 with an imm32-sized value",
        "r15",
        7,
        &[0x49, 0xBF, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
    ),
    ("66 C7 /0 iw", "ax", 0x1234, &[0x66, 0xC7, 0xC0, 0x34, 0x12]),
    ("C6 /0 ib", "al", 7, &[0xC6, 0xC0, 0x07]),
    (
        "C7 /0 id (32-bit, zero-extends)",
        "eax",
        42,
        &[0xC7, 0xC0, 0x2A, 0x00, 0x00, 0x00],
    ),
    ("REX.B C6 /0 ib: R9B", "r9b", 7, &[0x41, 0xC6, 0xC1, 0x07]),
    (
        "bare REX C6 /0 ib: SIL, not DH",
        "sil",
        7,
        &[0x40, 0xC6, 0xC6, 0x07],
    ),
];

/// One hand-written vector that must REFUTE, and the reason class it must
/// refute for: `(why, intent register, intent immediate, bytes, class)`.
pub type SdmHandRefutation = (
    &'static str,
    &'static str,
    i64,
    &'static [u8],
    RefutationClass,
);

/// Hand-written wrong pairings that must each REFUTE for the stated reason.
pub const SDM_HAND_VECTORS_REFUTE: &[SdmHandRefutation] = &[
    (
        "THE ROW'S NAMED HAZARD: MOV RAX,-1 mis-aliased to the zero-extending 5-byte form",
        "rax",
        -1,
        &[0xB8, 0xFF, 0xFF, 0xFF, 0xFF],
        RefutationClass::Value,
    ),
    (
        "sign-extending REX.W C7 /0 where MOV RAX,0x80000000 was meant",
        "rax",
        0x8000_0000,
        &[0x48, 0xC7, 0xC0, 0x00, 0x00, 0x00, 0x80],
        RefutationClass::Value,
    ),
    (
        "AH where AL was meant: the same root register, the wrong byte slot",
        "al",
        7,
        &[0xB4, 0x07],
        RefutationClass::WrittenBits,
    ),
    (
        "dropped forced REX: DH where SIL was meant",
        "sil",
        7,
        &[0xB6, 0x07],
        RefutationClass::Register,
    ),
    (
        "dropped forced REX: CH where BPL was meant",
        "bpl",
        7,
        &[0xB5, 0x07],
        RefutationClass::Register,
    ),
    (
        "CH where DH was meant: high-byte slot of RCX, not RDX",
        "dh",
        7,
        &[0xB5, 0x07],
        RefutationClass::Register,
    ),
    (
        "DH where CH was meant: high-byte slot of RDX, not RCX",
        "ch",
        7,
        &[0xB6, 0x07],
        RefutationClass::Register,
    ),
    (
        "AH where BH was meant: high-byte slot of RAX, not RBX",
        "bh",
        7,
        &[0xB4, 0x07],
        RefutationClass::Register,
    ),
    (
        "C7 with no ModR/M byte",
        "eax",
        0,
        &[0xC7],
        RefutationClass::DecodeTruncated,
    ),
    (
        "C7 /0 with a MEMORY destination is a store, not a register write",
        "eax",
        42,
        &[0xC7, 0x00, 0x2A, 0x00, 0x00, 0x00],
        RefutationClass::DecodeMemoryForm,
    ),
    (
        "C7 /7 is XBEGIN, not MOV",
        "eax",
        0,
        &[0xC7, 0xF8, 0x00, 0x00, 0x00, 0x00],
        RefutationClass::DecodeGroup11,
    ),
    (
        "a REX that is not adjacent to the opcode",
        "ax",
        0x1234,
        &[0x48, 0x66, 0xB8, 0x34, 0x12],
        RefutationClass::DecodeRexNotAdjacent,
    ),
    (
        "two REX prefixes",
        "rax",
        0x1122_3344_5566_7788,
        &[
            0x48, 0x48, 0xB8, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11,
        ],
        RefutationClass::DecodeRexNotAdjacent,
    ),
    (
        "an intent that names a non-GPR destination",
        "xmm0",
        0,
        &[0xB8, 0x00, 0x00, 0x00, 0x00],
        RefutationClass::UnknownIntentRegister,
    ),
    (
        "an empty byte stream",
        "eax",
        0,
        &[],
        RefutationClass::DecodeTruncated,
    ),
];

/// Label of the generated group-11 opcode-extension controls.
pub const D1_GROUP11_EXTENSION: &str = "D1 C6/C7 with ModR/M.reg /1../7 is not MOV (only /0 is)";
/// Label of the generated memory-destination controls.
pub const D2_MEMORY_DESTINATION: &str =
    "D2 C6/C7 /0 with ModR/M.mod 00/01/10 is a store, not a register write";

/// One MOV-imm spelling under test: `(prefix bytes, opcode, intent register,
/// intent immediate, immediate bytes)`.
type MovImmSpelling = (&'static [u8], u8, &'static str, i64, &'static [u8]);

/// DECODER controls for productions the encoder never emits. The corpus mutants
/// above are all mutations of `+r`-form bytes, so they cannot reach the
/// ModR/M-level decisions of the group-11 productions. These controls do:
///
/// * `D1`: every opcode extension `/1`..`/7` of `C6`, `C7`, `66 C7` and
///   `REX.W C7`, with mod=11. SDM Vol 2B defines only `/0` as MOV (`C6 /7`
///   and `C7 /7` are XABORT and XBEGIN; the rest are undefined). Each must refute
///   as `DecodeGroup11`. A decoder that accepted `/1` would read `C7 C8 id` as a
///   register write and the control would SURVIVE.
/// * `D2`: `/0` with mod 00, 01 and 10, over rm 0 (plain base), 4 (SIB) and 5
///   (RIP-relative at mod 00), on each of the same four spellings. Every one of
///   these is a memory destination and must refute as `DecodeMemoryForm`. A
///   decoder that let mod 01/10 through would read the displacement as the
///   immediate.
///
/// Each vector carries a well-formed immediate after the ModR/M byte, so a
/// decoder that wrongly let the bytes through would see a complete instruction.
/// The expected class is stated from the SDM, never computed by running the
/// obligation.
pub fn sdm_decoder_controls() -> Vec<MovImmMutant> {
    // (prefix bytes, opcode, destination name for the intent, immediate bytes).
    let spellings: [MovImmSpelling; 4] = [
        (&[], 0xC6, "al", 0x2A, &[0x2A]),
        (&[], 0xC7, "eax", 0x2A, &[0x2A, 0x00, 0x00, 0x00]),
        (&[0x66], 0xC7, "ax", 0x2A, &[0x2A, 0x00]),
        (&[0x48], 0xC7, "rax", 0x2A, &[0x2A, 0x00, 0x00, 0x00]),
    ];
    let mut out = Vec::new();
    for (prefix, opcode, dst, imm, imm_bytes) in spellings {
        let control = |label: &'static str, modrm: u8, expect: RefutationClass| {
            let mut bytes = prefix.to_vec();
            bytes.push(opcode);
            bytes.push(modrm);
            bytes.extend_from_slice(imm_bytes);
            MovImmMutant {
                label,
                side: MutantSide::Machine,
                dst_name: dst.to_string(),
                imm,
                bytes,
                expect,
            }
        };
        for reg in 1u8..=7 {
            out.push(control(
                D1_GROUP11_EXTENSION,
                0xC0 | (reg << 3),
                RefutationClass::DecodeGroup11,
            ));
        }
        for md in [0b00u8, 0b01, 0b10] {
            for rm in [0u8, 4, 5] {
                out.push(control(
                    D2_MEMORY_DESTINATION,
                    (md << 6) | rm,
                    RefutationClass::DecodeMemoryForm,
                ));
            }
        }
    }
    for &(why, dst_name, imm, bytes, expect) in SDM_HAND_VECTORS_REFUTE {
        out.push(MovImmMutant {
            label: why,
            side: MutantSide::Machine,
            dst_name: dst_name.to_string(),
            imm,
            bytes: bytes.to_vec(),
            expect,
        });
    }
    out
}

// ===========================================================================
// (9) The coverage-gate credit hook
// ===========================================================================

/// What the credit hook established, for the gate row's note.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MovImmCredit {
    /// Captured real encodings that hold.
    pub entries: usize,
    /// Distinct physical form classes those encodings cover (all 11 required).
    pub forms_seen: usize,
    /// Negative controls run — every one refuted for its stated reason class.
    pub mutants_refuted: usize,
    /// Hand-written SDM vectors the encoder never emits, all holding.
    pub hand_vectors_held: usize,
    /// Corpus intents whose immediate was truncated to the destination width.
    pub truncating_intents: usize,
}

/// Run one negative control and demand its stated reason class.
///
/// `Ok` only when the control is REFUTED and its refutation class equals the
/// stated one. A control that survives is an `Err` naming it SURVIVED, and one
/// that refutes for another reason is an `Err` naming the WRONG REASON.
/// `tests/x86_encoding_gate.rs` feeds the hook both kinds and requires a
/// refusal.
pub fn control_is_refuted_as_stated(m: &MovImmMutant) -> Result<(), String> {
    match mov_imm_check(&m.dst_name, m.imm, &m.bytes) {
        Ok(_) => Err(format!(
            "negative control SURVIVED — `{}`: MOV {},{:#x} vs bytes {:02x?} was accepted",
            m.label, m.dst_name, m.imm, m.bytes
        )),
        Err(r) if r.class() != m.expect => Err(format!(
            "negative control refuted for the WRONG REASON — `{}`: MOV {},{:#x} vs bytes {:02x?} \
             must refute as {:?} but refuted as {:?} ({r})",
            m.label,
            m.dst_name,
            m.imm,
            m.bytes,
            m.expect,
            r.class()
        )),
        Err(_) => Ok(()),
    }
}

/// THE COVERAGE-GATE CREDIT HOOK for `x86_64::MovRI`.
///
/// `Ok` iff ALL of:
///
/// 1. [`EMITTED_X86_MOV_IMMEDIATES`] is non-empty and EVERY captured encoding
///    holds (an empty set is not a discharged set);
/// 2. FORM COVERAGE, computed from the DECODED forms: at least one entry of
///    each of the 11 [`REQUIRED_FORM_CLASSES`] — a narrow corpus cannot credit
///    the row;
/// 3. THE TEETH: every control [`mov_imm_mutants`] builds over every corpus
///    entry is refuted FOR ITS STATED REASON CLASS, every label in
///    [`REQUIRED_MUTANT_LABELS`] fired at least once, every
///    [`sdm_decoder_controls`] entry (the group-11 and memory-form decoder
///    controls plus [`SDM_HAND_VECTORS_REFUTE`]) refutes for its stated class,
///    and every [`SDM_HAND_VECTORS_HOLD`] entry holds. The row's own bar is "a
///    lane that cannot show refuting controls has not met the bar"; here that
///    is literally a precondition of green, and
///    `tests/x86_encoding_gate.rs::credit_hook_refuses_surviving_or_misattributed_controls`
///    shows the hook REFUSING when handed a control that survives or refutes for
///    the wrong reason.
///
/// What the hook cannot check is that the corpus is still what the live
/// encoder emits. This crate cannot run the encoder. `x86_encoding_gate` and
/// `coverage_gate_tests` re-derive the corpus from the live encoder, and both
/// run in the local meta-gate.
///
/// # What crediting the row does NOT say
///
/// Read the credited row as exactly this and nothing more: **for `MOV r,imm`,
/// the bytes the x86-64 encoder emitted denote, under an independent
/// SDM-derived decode, the same write to the 64-bit destination register that
/// the machine-IR instruction (destination register name, i64 immediate)
/// means** — for 8/16-bit writes, for every prior value of the register. The
/// ten things it does not say are carried as data in
/// [`X86_MOV_IMM_DEFERRALS`].
pub fn mov_imm_discharges_valid() -> Result<MovImmCredit, String> {
    mov_imm_credit_over(EMITTED_X86_MOV_IMMEDIATES)
}

/// [`mov_imm_discharges_valid`] over an explicit corpus. The gate hook always
/// passes [`EMITTED_X86_MOV_IMMEDIATES`]; this entry point exists so the gate
/// test can show the hook FAILS CLOSED on an empty corpus, a narrow corpus and a
/// corpus carrying one wrong encoding.
pub fn mov_imm_credit_over(corpus: &[EmittedMovImmediate]) -> Result<MovImmCredit, String> {
    mov_imm_credit_over_with(
        corpus,
        &mov_imm_mutants,
        &sdm_decoder_controls(),
        SDM_HAND_VECTORS_HOLD,
    )
}

/// The negative-control battery builder the hook runs per corpus entry.
pub type MutantBattery<'a> = &'a dyn Fn(&str, i64, &[u8]) -> Vec<MovImmMutant>;

/// The credit hook with every ingredient explicit. The gate never calls this
/// directly: [`mov_imm_credit_over`] passes the real [`mov_imm_mutants`],
/// [`sdm_decoder_controls`] and [`SDM_HAND_VECTORS_HOLD`]. It is public so the
/// gate test can hand the hook a battery with a SURVIVING control, a control
/// that refutes for the WRONG REASON, a battery missing a required label, a
/// decoder control that holds, or a hold vector that refutes. The hook must
/// refuse each one. Without that, a hook whose control check had been forced
/// to `Ok` would still discharge on today's (all-refuting) controls, and no test
/// would notice.
pub fn mov_imm_credit_over_with(
    corpus: &[EmittedMovImmediate],
    battery_for: MutantBattery<'_>,
    decoder_controls: &[MovImmMutant],
    hand_hold: &[SdmHandVector],
) -> Result<MovImmCredit, String> {
    if corpus.is_empty() {
        return Err(
            "the captured MOV-immediate corpus is empty — an empty set is not a \
                    discharged set"
                .to_string(),
        );
    }
    let mut classes = std::collections::BTreeSet::new();
    let mut labels = std::collections::BTreeSet::new();
    let mut mutants_refuted = 0usize;
    let mut truncating_intents = 0usize;
    for &(dst_name, imm, bytes) in corpus {
        let ob = mov_imm_obligation(dst_name, imm, bytes);
        let holds = match &ob.outcome {
            Ok(h) => *h,
            Err(r) => return Err(format!("captured encoding REFUTED — {}: {r}", ob.name)),
        };
        truncating_intents += usize::from(holds.truncating_intent);
        let Some(intent_reg) = sdm_reg(dst_name) else {
            return Err(format!("corpus names a non-GPR destination `{dst_name}`"));
        };
        let Some(class) = form_class(intent_reg.bits, &holds.decoded) else {
            return Err(format!(
                "{}: holds, but in a form the encoder is not known to emit ({:?}); the corpus is \
                 a capture of REAL emitted bytes and must not carry hand-made forms",
                ob.name, holds.decoded.form
            ));
        };
        classes.insert(class);
        let battery = battery_for(dst_name, imm, bytes);
        if battery.is_empty() {
            return Err(format!("{}: produced no negative controls", ob.name));
        }
        for m in &battery {
            control_is_refuted_as_stated(m)?;
            labels.insert(m.label);
            mutants_refuted += 1;
        }
    }
    for required in REQUIRED_FORM_CLASSES {
        if !classes.contains(&required) {
            return Err(format!(
                "form coverage: the corpus holds no {required:?} encoding — a narrow corpus \
                 cannot credit the row"
            ));
        }
    }
    for &required in REQUIRED_MUTANT_LABELS {
        if !labels.contains(required) {
            return Err(format!(
                "negative control `{required}` never fired over the corpus — that facet is \
                 unexercised"
            ));
        }
    }
    if decoder_controls.is_empty() {
        return Err(
            "no decoder controls were supplied — the group-11 and memory-form decisions would \
             be unexercised"
                .to_string(),
        );
    }
    for required in [D1_GROUP11_EXTENSION, D2_MEMORY_DESTINATION] {
        if !decoder_controls.iter().any(|m| m.label == required) {
            return Err(format!(
                "decoder control `{required}` is absent — that decoder decision is unexercised"
            ));
        }
    }
    for m in decoder_controls {
        control_is_refuted_as_stated(m)?;
        mutants_refuted += 1;
    }
    if hand_hold.is_empty() {
        return Err("no SDM hand vectors that must HOLD were supplied".to_string());
    }
    for &(why, dst_name, imm, bytes) in hand_hold {
        if let Err(r) = mov_imm_check(dst_name, imm, bytes) {
            return Err(format!(
                "SDM hand vector `{why}` (MOV {dst_name},{imm:#x} = {bytes:02x?}) must HOLD but \
                 was refuted: {r}"
            ));
        }
    }
    Ok(MovImmCredit {
        entries: corpus.len(),
        forms_seen: classes.len(),
        mutants_refuted,
        hand_vectors_held: hand_hold.len(),
        truncating_intents,
    })
}

// ===========================================================================
// (10) Named deferrals — what the credit does NOT claim, as data
// ===========================================================================

/// One thing the MOV-immediate credit does NOT establish.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct X86MovImmDeferral {
    /// The property a reader could reasonably assume the credit covers.
    pub name: &'static str,
    /// Who owns it instead.
    pub owner: &'static str,
    /// Why this family cannot honestly discharge it.
    pub reason: &'static str,
}

/// The named non-claims of the MOV-immediate credit. Pinned by
/// `tests/x86_encoding_gate.rs`: removing one requires landing its evidence;
/// adding one is a deliberate, reviewable admission.
pub const X86_MOV_IMM_DEFERRALS: &[X86MovImmDeferral] = &[
    X86MovImmDeferral {
        name: "that the LOWERING or any pass chose the RIGHT constant or the right register",
        owner: "the lowering / ALU reconstruction families and the pass validators (constant); \
                regalloc translation validation and post_ra_dataflow (register)",
        reason: "a wrong constant, or a wrong-but-valid register, encodes and decodes perfectly. \
                 This family's source side IS the machine-IR instruction; whether that \
                 instruction is the right one is upstream of it",
    },
    X86MovImmDeferral {
        name: "that an out-of-width immediate was intended",
        owner: "lowering",
        reason: "for a w<64 destination the source semantics is imm mod 2^w, which is the \
                 optimizer's own model (x86_const_fold::normalize_const_for_vreg). An intent \
                 whose immediate fits neither the signed nor the unsigned w-bit range is \
                 reported as `truncating` and counted, but not refuted; if the dropped bits \
                 mattered, that is a lowering bug this family cannot see",
    },
    X86MovImmDeferral {
        name: "that the chosen FORM is the shortest",
        owner: "nobody — a code-size matter, not a soundness one",
        reason: "MOV RAX,-1 is emitted as the 10-byte REX.W B8 io although the 7-byte REX.W C7 /0 \
                 id exists. The form is deliberately unpinned: a shortest-form rule would refute \
                 today's correct encoder. What IS pinned is that every prefix byte and REX bit \
                 present is load-bearing, and exact framing",
    },
    X86MovImmDeferral {
        name: "instruction PLACEMENT: right offset, reached, not overwritten, consumed by the \
               right instruction",
        owner: "layout, CFG and dataflow validation",
        reason: "the obligation speaks about the bytes of ONE instruction in isolation",
    },
    X86MovImmDeferral {
        name: "the raw-byte movabs in the JIT profile-counter trampolines",
        owner: "unowned — not in the opcode inventory",
        reason: "those sequences are hand-assembled bytes, not X86Opcode::MovRI instances, and \
                 their imm64 is patched at run time; the coverage row this family credits does \
                 not name them",
    },
    X86MovImmDeferral {
        name: "that the ISA semantics are right",
        owner: "this family's TRUST BASE (Intel SDM Vol 1 §3.4.1.1, Vol 2A §2.2.1, Vol 2B MOV)",
        reason: "\"32-bit writes zero-extend\", \"8/16-bit writes preserve the upper bits\", \
                 \"REX.W C7 /0 sign-extends\" and the register numbering are TRANSCRIBED from the \
                 SDM, as x86_64_semantics.rs is for ADD. The zero-extension rule is cross-checked \
                 rather than merely assumed — the 64-bit-intent alias entries have a source side \
                 with no extension rule in it — but an encoder alias predicate and a decoder \
                 belief that were wrong in a mutually compensating way would pass. Only silicon \
                 or an external emulator can exclude that, and no silicon differential is part \
                 of this credit",
    },
    X86MovImmDeferral {
        name: "that MOV r,imm writes no RFLAGS bit, no other register and no memory (the FRAME \
               facet)",
        owner: "this family's TRUST BASE (Intel SDM Vol 2B MOV, \"Flags Affected: None\")",
        reason: "RegWrite describes only the destination root register. No flags, other-register \
                 or memory component is COMPARED, because the decoder accepts only the four MOV \
                 immediate productions and a flags field on them would be a constant on both \
                 sides, which is X==X. What IS enforced is CLOSURE: every other byte sequence is \
                 refused, including the flag-clobbering XOR r,r zeroing idiom (control M6b), \
                 ADD/TEST/group-1 substitutes (M6), and memory destinations (D2). That the four \
                 accepted productions leave RFLAGS and the rest of the machine untouched is \
                 transcribed from the SDM, not proven here",
    },
    X86MovImmDeferral {
        name: "every i64 immediate on every register",
        owner: "this family — a coverage limit, not a structural one",
        reason: "the gate hook runs a CAPTURED corpus covering all 11 emitted form classes, the \
                 alias threshold, the sign edges and all-bytes-distinct values; the live sweep \
                 is stratified, not exhaustive. The gate CREDIT is corpus-based. Per compile, \
                 trust-cg-codegen's ENC-3 decode-check runs mov_imm_check on every MovRI the x86 \
                 pipeline records and, in its default enforce mode, fails the compile on a \
                 refutation. That checks the instructions a compile emits; it is not a for-all \
                 theorem, and TCG_DECODE_CHECK=off|warn or TCG_NO_DECODE_CHECK=1 turn it off",
    },
    X86MovImmDeferral {
        name: "a general x86 decoder",
        owner: "trust-cg-codegen's decode_check (ENC-3), a different and broader artefact",
        reason: "sdm_decode_mov_imm recognises the MOV-immediate-to-register family only and \
                 fails closed on everything else, including memory-destination C6/C7 (a store), \
                 any legacy prefix other than 66h, and a REX that is not adjacent to the opcode",
    },
    X86MovImmDeferral {
        name: "the other 28 x86-64 RED rows",
        owner: "their own families: the ten SSE lane ops, the two narrow LOCK CMPXCHG forms, the \
                sixteen volatile MOV forms",
        reason: "those are value/effect SEMANTICS questions, not immediate-decode questions; \
                 nothing in this design generalises to them and they stay RED by name",
    },
];

// ===========================================================================
// (11) The captured corpus of REAL emitted encodings
// ===========================================================================

/// One captured encoding: `(SDM destination name, intent immediate, the bytes
/// the REAL x86-64 encoder emitted)`.
pub type EmittedMovImmediate = (&'static str, i64, &'static [u8]);

/// The bytes the real x86-64 encoder
/// (`trust_cg_codegen::x86_64::X86Encoder::encode_instruction`) emitted for
/// each `MovRI` intent, captured by running it — never typed in by hand.
///
/// # Why a captured corpus exists at all
///
/// The coverage gate's credit hook runs inside this crate, and this crate
/// cannot depend on `trust-cg-codegen` (that crate depends on this one). So the
/// gate cannot run the encoder to get live bytes. It runs over these instead.
///
/// # Why the capture is not a trust-me
///
/// `tests/x86_encoding_gate.rs::corpus_is_what_the_live_encoder_emits_today`
/// re-encodes EVERY entry through the live encoder and asserts the emitted bytes
/// are byte-identical to the capture. `x86_encoding_gate` is a target of the
/// local meta-gate (`scripts/soundness_check.sh`). The target that pins the
/// x86-64 ratio, `coverage_gate_tests`, repeats the same re-derivation, so an
/// encoder change that alters these bytes turns the meta-gate RED rather than
/// leaving a green row standing on a stale capture.
///
/// Nothing in this corpus is an independent witness of the ENCODING. The
/// eleven entries `encoder_unit_test_vectors_appear_verbatim_in_the_corpus`
/// pins are the same vectors as `encode.rs`'s own MovRI unit tests, so they add
/// no independence. The independence of the credit rests entirely on
/// [`sdm_decode_mov_imm`] and its controls.
///
/// # What the value set covers
///
/// For one legacy and one REX.B register per width: zero-adjacent values, the
/// zero-extending-alias threshold (`0x7FFF_FFFF`, `0x8000_0000`,
/// `0x8000_0001`, `0xFFFF_FFFF`, `0x1_0000_0000`), the sign edges (`-1`, `-2`,
/// `i32::MIN`, `i32::MIN - 1`, `i64::MIN`, `i64::MAX`), imm64 values with all
/// eight bytes distinct (byte order), a signed spelling of a 32-bit immediate
/// (`eax, -1` — isel really emits that), and one TRUNCATING intent per narrow
/// width. Then a sweep of all 16 registers at each width — 64-bit twice, once
/// as a movabs and once aliased to the zero-extending form with bit 31 set —
/// which covers RSP/RBP/R12/R13 and the forced bare REX on SPL/BPL/SIL/DIL.
///
/// It does NOT cover every i64 on every register — see
/// [`X86_MOV_IMM_DEFERRALS`].
pub const EMITTED_X86_MOV_IMMEDIATES: &[EmittedMovImmediate] = &[
    // ---- 64-bit intents: the alias threshold, the sign edges, imm64 (legacy + REX.B register) ----
    ("rax", 0, &[0xB8, 0x00, 0x00, 0x00, 0x00]),
    ("rax", 1, &[0xB8, 0x01, 0x00, 0x00, 0x00]),
    ("rax", 0x2A, &[0xB8, 0x2A, 0x00, 0x00, 0x00]),
    ("rax", 0x7FFF_FFFF, &[0xB8, 0xFF, 0xFF, 0xFF, 0x7F]),
    ("rax", 0x8000_0000, &[0xB8, 0x00, 0x00, 0x00, 0x80]),
    ("rax", 0x8000_0001, &[0xB8, 0x01, 0x00, 0x00, 0x80]),
    ("rax", 0xFFFF_FFFF, &[0xB8, 0xFF, 0xFF, 0xFF, 0xFF]),
    (
        "rax",
        0x1_0000_0000,
        &[0x48, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00],
    ),
    (
        "rax",
        -1,
        &[0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
    ),
    (
        "rax",
        -2,
        &[0x48, 0xB8, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
    ),
    (
        "rax",
        -0x8000_0000,
        &[0x48, 0xB8, 0x00, 0x00, 0x00, 0x80, 0xFF, 0xFF, 0xFF, 0xFF],
    ),
    (
        "rax",
        -0x8000_0001,
        &[0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0x7F, 0xFF, 0xFF, 0xFF, 0xFF],
    ),
    (
        "rax",
        i64::MIN,
        &[0x48, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80],
    ),
    (
        "rax",
        0x7FFF_FFFF_FFFF_FFFF,
        &[0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F],
    ),
    (
        "rax",
        0x123_4567_89AB_CDEF,
        &[0x48, 0xB8, 0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01],
    ),
    (
        "rax",
        -0x123_4567_89AB_CDF0,
        &[0x48, 0xB8, 0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE],
    ),
    (
        "rax",
        -0x1_0000_0000,
        &[0x48, 0xB8, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF],
    ),
    ("r9", 0, &[0x41, 0xB9, 0x00, 0x00, 0x00, 0x00]),
    ("r9", 1, &[0x41, 0xB9, 0x01, 0x00, 0x00, 0x00]),
    ("r9", 0x2A, &[0x41, 0xB9, 0x2A, 0x00, 0x00, 0x00]),
    ("r9", 0x7FFF_FFFF, &[0x41, 0xB9, 0xFF, 0xFF, 0xFF, 0x7F]),
    ("r9", 0x8000_0000, &[0x41, 0xB9, 0x00, 0x00, 0x00, 0x80]),
    ("r9", 0x8000_0001, &[0x41, 0xB9, 0x01, 0x00, 0x00, 0x80]),
    ("r9", 0xFFFF_FFFF, &[0x41, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF]),
    (
        "r9",
        0x1_0000_0000,
        &[0x49, 0xB9, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00],
    ),
    (
        "r9",
        -1,
        &[0x49, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
    ),
    (
        "r9",
        -2,
        &[0x49, 0xB9, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
    ),
    (
        "r9",
        -0x8000_0000,
        &[0x49, 0xB9, 0x00, 0x00, 0x00, 0x80, 0xFF, 0xFF, 0xFF, 0xFF],
    ),
    (
        "r9",
        -0x8000_0001,
        &[0x49, 0xB9, 0xFF, 0xFF, 0xFF, 0x7F, 0xFF, 0xFF, 0xFF, 0xFF],
    ),
    (
        "r9",
        i64::MIN,
        &[0x49, 0xB9, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80],
    ),
    (
        "r9",
        0x7FFF_FFFF_FFFF_FFFF,
        &[0x49, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F],
    ),
    (
        "r9",
        0x123_4567_89AB_CDEF,
        &[0x49, 0xB9, 0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01],
    ),
    (
        "r9",
        -0x123_4567_89AB_CDF0,
        &[0x49, 0xB9, 0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE],
    ),
    (
        "r9",
        -0x1_0000_0000,
        &[0x49, 0xB9, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF],
    ),
    // ---- 32-bit intents, including a signed spelling and a truncating one ----
    ("eax", 0, &[0xB8, 0x00, 0x00, 0x00, 0x00]),
    ("eax", 1, &[0xB8, 0x01, 0x00, 0x00, 0x00]),
    ("eax", 0x2A, &[0xB8, 0x2A, 0x00, 0x00, 0x00]),
    ("eax", -1, &[0xB8, 0xFF, 0xFF, 0xFF, 0xFF]),
    ("eax", 0x7FFF_FFFF, &[0xB8, 0xFF, 0xFF, 0xFF, 0x7F]),
    ("eax", 0x8000_0000, &[0xB8, 0x00, 0x00, 0x00, 0x80]),
    ("eax", 0x8000_0001, &[0xB8, 0x01, 0x00, 0x00, 0x80]),
    ("eax", 0xFFFF_FFFF, &[0xB8, 0xFF, 0xFF, 0xFF, 0xFF]),
    ("eax", -0x8000_0000, &[0xB8, 0x00, 0x00, 0x00, 0x80]),
    ("eax", 0x1234_5678, &[0xB8, 0x78, 0x56, 0x34, 0x12]),
    ("eax", 0x1_0000_0001, &[0xB8, 0x01, 0x00, 0x00, 0x00]),
    ("r9d", 0, &[0x41, 0xB9, 0x00, 0x00, 0x00, 0x00]),
    ("r9d", 1, &[0x41, 0xB9, 0x01, 0x00, 0x00, 0x00]),
    ("r9d", 0x2A, &[0x41, 0xB9, 0x2A, 0x00, 0x00, 0x00]),
    ("r9d", -1, &[0x41, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF]),
    ("r9d", 0x7FFF_FFFF, &[0x41, 0xB9, 0xFF, 0xFF, 0xFF, 0x7F]),
    ("r9d", 0x8000_0000, &[0x41, 0xB9, 0x00, 0x00, 0x00, 0x80]),
    ("r9d", 0x8000_0001, &[0x41, 0xB9, 0x01, 0x00, 0x00, 0x80]),
    ("r9d", 0xFFFF_FFFF, &[0x41, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF]),
    ("r9d", -0x8000_0000, &[0x41, 0xB9, 0x00, 0x00, 0x00, 0x80]),
    ("r9d", 0x1234_5678, &[0x41, 0xB9, 0x78, 0x56, 0x34, 0x12]),
    ("r9d", 0x1_0000_0001, &[0x41, 0xB9, 0x01, 0x00, 0x00, 0x00]),
    // ---- 16-bit intents, including a truncating one ----
    ("ax", 0, &[0x66, 0xB8, 0x00, 0x00]),
    ("ax", 1, &[0x66, 0xB8, 0x01, 0x00]),
    ("ax", -1, &[0x66, 0xB8, 0xFF, 0xFF]),
    ("ax", 0x1234, &[0x66, 0xB8, 0x34, 0x12]),
    ("ax", 0x7FFF, &[0x66, 0xB8, 0xFF, 0x7F]),
    ("ax", 0x8000, &[0x66, 0xB8, 0x00, 0x80]),
    ("ax", 0xFFFF, &[0x66, 0xB8, 0xFF, 0xFF]),
    ("ax", 0x1_2345, &[0x66, 0xB8, 0x45, 0x23]),
    ("r14w", 0, &[0x66, 0x41, 0xBE, 0x00, 0x00]),
    ("r14w", 1, &[0x66, 0x41, 0xBE, 0x01, 0x00]),
    ("r14w", -1, &[0x66, 0x41, 0xBE, 0xFF, 0xFF]),
    ("r14w", 0x1234, &[0x66, 0x41, 0xBE, 0x34, 0x12]),
    ("r14w", 0x7FFF, &[0x66, 0x41, 0xBE, 0xFF, 0x7F]),
    ("r14w", 0x8000, &[0x66, 0x41, 0xBE, 0x00, 0x80]),
    ("r14w", 0xFFFF, &[0x66, 0x41, 0xBE, 0xFF, 0xFF]),
    ("r14w", 0x1_2345, &[0x66, 0x41, 0xBE, 0x45, 0x23]),
    // ---- 8-bit intents, including a truncating one ----
    ("al", 0, &[0xB0, 0x00]),
    ("al", 1, &[0xB0, 0x01]),
    ("al", 7, &[0xB0, 0x07]),
    ("al", -1, &[0xB0, 0xFF]),
    ("al", 0x7F, &[0xB0, 0x7F]),
    ("al", 0x80, &[0xB0, 0x80]),
    ("al", 0xFF, &[0xB0, 0xFF]),
    ("al", 0x1FF, &[0xB0, 0xFF]),
    ("r9b", 0, &[0x41, 0xB1, 0x00]),
    ("r9b", 1, &[0x41, 0xB1, 0x01]),
    ("r9b", 7, &[0x41, 0xB1, 0x07]),
    ("r9b", -1, &[0x41, 0xB1, 0xFF]),
    ("r9b", 0x7F, &[0x41, 0xB1, 0x7F]),
    ("r9b", 0x80, &[0x41, 0xB1, 0x80]),
    ("r9b", 0xFF, &[0x41, 0xB1, 0xFF]),
    ("r9b", 0x1FF, &[0x41, 0xB1, 0xFF]),
    // ---- register sweep, 64-bit movabs, all immediate bytes distinct ----
    (
        "rcx",
        0x123_4567_89AB_CDEF,
        &[0x48, 0xB9, 0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01],
    ),
    (
        "rdx",
        0x123_4567_89AB_CDEF,
        &[0x48, 0xBA, 0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01],
    ),
    (
        "rbx",
        0x123_4567_89AB_CDEF,
        &[0x48, 0xBB, 0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01],
    ),
    (
        "rsp",
        0x123_4567_89AB_CDEF,
        &[0x48, 0xBC, 0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01],
    ),
    (
        "rbp",
        0x123_4567_89AB_CDEF,
        &[0x48, 0xBD, 0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01],
    ),
    (
        "rsi",
        0x123_4567_89AB_CDEF,
        &[0x48, 0xBE, 0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01],
    ),
    (
        "rdi",
        0x123_4567_89AB_CDEF,
        &[0x48, 0xBF, 0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01],
    ),
    (
        "r8",
        0x123_4567_89AB_CDEF,
        &[0x49, 0xB8, 0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01],
    ),
    (
        "r10",
        0x123_4567_89AB_CDEF,
        &[0x49, 0xBA, 0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01],
    ),
    (
        "r11",
        0x123_4567_89AB_CDEF,
        &[0x49, 0xBB, 0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01],
    ),
    (
        "r12",
        0x123_4567_89AB_CDEF,
        &[0x49, 0xBC, 0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01],
    ),
    (
        "r13",
        0x123_4567_89AB_CDEF,
        &[0x49, 0xBD, 0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01],
    ),
    (
        "r14",
        0x123_4567_89AB_CDEF,
        &[0x49, 0xBE, 0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01],
    ),
    (
        "r15",
        0x123_4567_89AB_CDEF,
        &[0x49, 0xBF, 0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01],
    ),
    // ---- register sweep, 64-bit intent ALIASED to the zero-extending form, bit 31 set ----
    ("rax", 0x89AB_CDEF, &[0xB8, 0xEF, 0xCD, 0xAB, 0x89]),
    ("rcx", 0x89AB_CDEF, &[0xB9, 0xEF, 0xCD, 0xAB, 0x89]),
    ("rdx", 0x89AB_CDEF, &[0xBA, 0xEF, 0xCD, 0xAB, 0x89]),
    ("rbx", 0x89AB_CDEF, &[0xBB, 0xEF, 0xCD, 0xAB, 0x89]),
    ("rsp", 0x89AB_CDEF, &[0xBC, 0xEF, 0xCD, 0xAB, 0x89]),
    ("rbp", 0x89AB_CDEF, &[0xBD, 0xEF, 0xCD, 0xAB, 0x89]),
    ("rsi", 0x89AB_CDEF, &[0xBE, 0xEF, 0xCD, 0xAB, 0x89]),
    ("rdi", 0x89AB_CDEF, &[0xBF, 0xEF, 0xCD, 0xAB, 0x89]),
    ("r8", 0x89AB_CDEF, &[0x41, 0xB8, 0xEF, 0xCD, 0xAB, 0x89]),
    ("r9", 0x89AB_CDEF, &[0x41, 0xB9, 0xEF, 0xCD, 0xAB, 0x89]),
    ("r10", 0x89AB_CDEF, &[0x41, 0xBA, 0xEF, 0xCD, 0xAB, 0x89]),
    ("r11", 0x89AB_CDEF, &[0x41, 0xBB, 0xEF, 0xCD, 0xAB, 0x89]),
    ("r12", 0x89AB_CDEF, &[0x41, 0xBC, 0xEF, 0xCD, 0xAB, 0x89]),
    ("r13", 0x89AB_CDEF, &[0x41, 0xBD, 0xEF, 0xCD, 0xAB, 0x89]),
    ("r14", 0x89AB_CDEF, &[0x41, 0xBE, 0xEF, 0xCD, 0xAB, 0x89]),
    ("r15", 0x89AB_CDEF, &[0x41, 0xBF, 0xEF, 0xCD, 0xAB, 0x89]),
    // ---- register sweep, 32-bit, bit 31 set ----
    ("eax", 0x9234_5678, &[0xB8, 0x78, 0x56, 0x34, 0x92]),
    ("ecx", 0x9234_5678, &[0xB9, 0x78, 0x56, 0x34, 0x92]),
    ("edx", 0x9234_5678, &[0xBA, 0x78, 0x56, 0x34, 0x92]),
    ("ebx", 0x9234_5678, &[0xBB, 0x78, 0x56, 0x34, 0x92]),
    ("esp", 0x9234_5678, &[0xBC, 0x78, 0x56, 0x34, 0x92]),
    ("ebp", 0x9234_5678, &[0xBD, 0x78, 0x56, 0x34, 0x92]),
    ("esi", 0x9234_5678, &[0xBE, 0x78, 0x56, 0x34, 0x92]),
    ("edi", 0x9234_5678, &[0xBF, 0x78, 0x56, 0x34, 0x92]),
    ("r8d", 0x9234_5678, &[0x41, 0xB8, 0x78, 0x56, 0x34, 0x92]),
    ("r9d", 0x9234_5678, &[0x41, 0xB9, 0x78, 0x56, 0x34, 0x92]),
    ("r10d", 0x9234_5678, &[0x41, 0xBA, 0x78, 0x56, 0x34, 0x92]),
    ("r11d", 0x9234_5678, &[0x41, 0xBB, 0x78, 0x56, 0x34, 0x92]),
    ("r12d", 0x9234_5678, &[0x41, 0xBC, 0x78, 0x56, 0x34, 0x92]),
    ("r13d", 0x9234_5678, &[0x41, 0xBD, 0x78, 0x56, 0x34, 0x92]),
    ("r14d", 0x9234_5678, &[0x41, 0xBE, 0x78, 0x56, 0x34, 0x92]),
    ("r15d", 0x9234_5678, &[0x41, 0xBF, 0x78, 0x56, 0x34, 0x92]),
    // ---- register sweep, 16-bit ----
    ("ax", 0x9234, &[0x66, 0xB8, 0x34, 0x92]),
    ("cx", 0x9234, &[0x66, 0xB9, 0x34, 0x92]),
    ("dx", 0x9234, &[0x66, 0xBA, 0x34, 0x92]),
    ("bx", 0x9234, &[0x66, 0xBB, 0x34, 0x92]),
    ("sp", 0x9234, &[0x66, 0xBC, 0x34, 0x92]),
    ("bp", 0x9234, &[0x66, 0xBD, 0x34, 0x92]),
    ("si", 0x9234, &[0x66, 0xBE, 0x34, 0x92]),
    ("di", 0x9234, &[0x66, 0xBF, 0x34, 0x92]),
    ("r8w", 0x9234, &[0x66, 0x41, 0xB8, 0x34, 0x92]),
    ("r9w", 0x9234, &[0x66, 0x41, 0xB9, 0x34, 0x92]),
    ("r10w", 0x9234, &[0x66, 0x41, 0xBA, 0x34, 0x92]),
    ("r11w", 0x9234, &[0x66, 0x41, 0xBB, 0x34, 0x92]),
    ("r12w", 0x9234, &[0x66, 0x41, 0xBC, 0x34, 0x92]),
    ("r13w", 0x9234, &[0x66, 0x41, 0xBD, 0x34, 0x92]),
    ("r14w", 0x9234, &[0x66, 0x41, 0xBE, 0x34, 0x92]),
    ("r15w", 0x9234, &[0x66, 0x41, 0xBF, 0x34, 0x92]),
    // ---- register sweep, 8-bit (SPL/BPL/SIL/DIL take the forced bare REX) ----
    ("al", 0xA5, &[0xB0, 0xA5]),
    ("cl", 0xA5, &[0xB1, 0xA5]),
    ("dl", 0xA5, &[0xB2, 0xA5]),
    ("bl", 0xA5, &[0xB3, 0xA5]),
    ("spl", 0xA5, &[0x40, 0xB4, 0xA5]),
    ("bpl", 0xA5, &[0x40, 0xB5, 0xA5]),
    ("sil", 0xA5, &[0x40, 0xB6, 0xA5]),
    ("dil", 0xA5, &[0x40, 0xB7, 0xA5]),
    ("r8b", 0xA5, &[0x41, 0xB0, 0xA5]),
    ("r9b", 0xA5, &[0x41, 0xB1, 0xA5]),
    ("r10b", 0xA5, &[0x41, 0xB2, 0xA5]),
    ("r11b", 0xA5, &[0x41, 0xB3, 0xA5]),
    ("r12b", 0xA5, &[0x41, 0xB4, 0xA5]),
    ("r13b", 0xA5, &[0x41, 0xB5, 0xA5]),
    ("r14b", 0xA5, &[0x41, 0xB6, 0xA5]),
    ("r15b", 0xA5, &[0x41, 0xB7, 0xA5]),
    // ---- hand-checked anchors not already listed above ----
    ("r8", 0x2A, &[0x41, 0xB8, 0x2A, 0x00, 0x00, 0x00]),
    (
        "r8",
        0x1_0000_0000,
        &[0x49, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00],
    ),
    (
        "rax",
        0x1234_5678_9ABC_DEF0,
        &[0x48, 0xB8, 0xF0, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12],
    ),
    ("r8b", 7, &[0x41, 0xB0, 0x07]),
    ("sil", 7, &[0x40, 0xB6, 0x07]),
];
