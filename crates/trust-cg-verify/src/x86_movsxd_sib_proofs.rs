// trust-cg-verify/x86_movsxd_sib_proofs.rs - the x86-64 scaled sign-extending load
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: Intel 64 and IA-32 Architectures Software Developer's Manual —
//   Vol 2A §2.1     (instruction format: legacy prefixes, opcode, ModR/M, SIB,
//                    displacement; §2.1.1 the four legacy prefix groups),
//   Vol 2A §2.1.5   (Table 2-2 the 32/64-bit ModR/M byte, Table 2-3 the SIB
//                    byte: `scale` is the 2-bit SHIFT, the effective scale
//                    factor is `1 << scale`; ModR/M.rm = 100b selects a SIB
//                    byte; SIB.index = 100b with REX.X = 0 means NO index
//                    register; SIB.base = 101b with ModR/M.mod = 00 means NO
//                    base register and a disp32 follows; ModR/M.rm = 101b with
//                    mod = 00 is RIP-relative in 64-bit mode),
//   Vol 2A §2.2.1   (REX prefixes `0100WRXB`; a REX "must immediately precede
//                    the opcode byte"; REX.W takes precedence over 66H),
//   Vol 2B "MOVSXD—Move Doubleword to Quadword with Sign-Extension":
//                    `63 /r` MOVSXD r16,r/m16 · `63 /r` MOVSXD r32,r/m32 ·
//                    `REX.W + 63 /r` MOVSXD r64,r/m32,
//   Vol 2B "MOV—Move": `8B /r` MOV r16/r32/r64, r/m,
//   Vol 1 §3.4.1.1  (general-purpose registers in 64-bit mode: 64-bit operands
//                    give a 64-bit result; 32-bit operands give a 32-bit result
//                    ZERO-EXTENDED to 64 bits; 16-bit and 8-bit operands leave
//                    the upper 48 / 56 bits of the destination UNMODIFIED).
//
// WHAT THIS FAMILY IS. `MOVSXD r64, [base + index*scale + disp]` is the x86-64
// SCALED SIGN-EXTENDING LOAD — the counterpart of the AArch64
// `LDRSW Xt, [Xn, Xm, LSL #2]` that `aarch64_jumptable_proofs` discharges. The
// coverage row carried a fail-closed allowlist entry whose own reason text asked
// for exactly this: "Upgrade to a genuine scaled-sext-load proof (aarch64
// LdrswRO analogue) before default-ON". This module is that upgrade, built to
// the x86 phase's bar rather than the AArch64 one — the machine side is rebuilt
// from the REAL EMITTED BYTES, not from a hand-written model of the addressing
// mode:
//
//   * MACHINE side: [`sdm_decode_scaled_load`] takes ONLY bytes — no hint from
//     the intent — and walks the SDM instruction format (legacy prefixes, REX,
//     the one-byte opcode map, ModR/M, SIB, displacement). What comes out is an
//     [`AddressForm`] and a load width / extension read off the opcode and
//     REX.W. [`DecodedScaledLoad::machine_write`] turns that into the register
//     WRITE the hardware performs: which 64-bit root, which bits of it, and the
//     value, as an [`SmtExpr`] over per-register leaves NAMED from the DECODED
//     register NUMBERS.
//   * SOURCE side: [`intent_write`] takes ONLY the machine-IR intent — the
//     destination, base and index register NAMES, the table ENTRY SIZE in bytes
//     and the displacement — and states the write the machine IR means. It never
//     sees a byte, a REX bit, a SIB scale field or a register number.
//   * The two sides are STRUCTURALLY DISTINCT, and deliberately so:
//
//         SOURCE   MemLoad(base + index*entry_size + disp, 32, SIGNED, 64)
//         MACHINE  SignExtend(MemLoad(base + (index << ss) + disp, 32, unsigned, 32), 32)
//
//     a multiply against a shift (the SDM's SIB `scale` field IS a shift
//     amount), and a sign-extending load against a zero-filling load composed
//     with an explicit sign-extend. They denote the same function; neither is
//     the other's spelling. [`compare_denotations`] REFUSES a machine side that
//     is structurally identical to the source side, so this family cannot decay
//     into the `X == X` that the retracted memory "proofs" were.
//
// WHAT IS DECIDED EXACTLY AND WHAT IS DECIDED OVER WITNESSES, said plainly.
//
//   * THE EFFECTIVE ADDRESS IS EXACT. `base + index*s + disp` and
//     `base + (index << ss) + disp` agree for every 64-bit `base`/`index` IF AND
//     ONLY IF `s == 1 << ss`: sufficiency is the bitvector identity
//     `bvmul(i, 2^k) == bvshl(i, k)`, and necessity follows by taking
//     `index = 1`, where the two index terms are the constants `s` and `1 << ss`
//     themselves. [`movsxd_sib_check`] decides that constant equality, so the
//     address facet is settled for ALL addresses, not sampled. The same lemma
//     is what makes a WRONG SCALE refutable at all.
//   * THE VALUE IS DECIDED OVER A WITNESS FAMILY. The composed denotation is
//     evaluated at [`WITNESS_ROWS`] assignments of all sixteen 64-bit roots
//     ([`witness_reg_value`]) and must agree at every one. The family is checked
//     for NON-VACUITY first: it must contain a witness whose loaded doubleword
//     has bit 31 SET and one where it is CLEAR, so the sign-extension is
//     genuinely exercised in both directions rather than passing because every
//     sampled entry happened to be positive. `tests/x86_movsxd_sib_gate.rs`
//     additionally runs the full `verify_by_evaluation` sweep over a real
//     [`crate::lowering_proof::ProofObligation`] and an EXHAUSTIVE sweep over a
//     contiguous 2^16 address window.
//
// THE GATE CREDIT IS CORPUS-BASED; THERE IS NO PER-COMPILE CHECK TO CLAIM. The
// coverage-gate row is credited over [`EMITTED_X86_MOVSXD_SIB`], bytes CAPTURED
// from the real encoder, because `trust-cg-verify` cannot depend on
// `trust-cg-codegen` (that crate depends on this one). `tests/x86_movsxd_sib_gate.rs`
// re-encodes every entry through the LIVE encoder and sweeps the whole
// destination/base/index/scale/displacement product, and it is a target of the
// local meta-gate (`scripts/soundness_check.sh` TRUST_CG_GATES); the
// ratio-pinning target `coverage_gate_tests` repeats the re-derivation, so the
// pinned ratio cannot stand on a stale capture. Unlike
// `MovRI`, this family has NO per-compile decode-check arm to point at, and this
// module claims none: `x86_64::decode_check` allowlists `MovsxdRMSib` under
// `JUMP_TABLE`, and no pass emits the opcode today (see
// [`X86_MOVSXD_SIB_DEFERRALS`], first entry).
//
// THE TEETH ARE PART OF THE CREDIT. [`movsxd_sib_discharges_valid`] does not
// return `Ok` unless every control refutes FOR ITS STATED REASON CLASS: the byte
// mutants (wrong destination, flipped REX.R/X/B, cleared REX.W, the MOV opcode
// for the MOVSXD opcode, a rotated SIB scale field, a rewritten SIB index/base,
// a dropped SIB byte, a register-direct ModR/M, a corrupted or dropped
// displacement, an appended and a truncated byte, a doubled REX, and every
// redundant legacy prefix), the source-side re-claims (a doubled entry size, a
// shifted displacement, swapped base and index, a sibling destination, a
// re-claimed base or index), the WRONG-MODEL controls that go straight through
// [`compare_denotations`] (a zero-extending model, a scale taken as the raw
// `ss`, the BASE shifted instead of the index, a 64-bit access, a dropped
// displacement, a dropped index, and — the one that matters most here — a
// machine side stated EXACTLY as the source side, which must be refused as
// DEGENERATE), and the hand-written SDM decoder vectors. A control that cannot
// be BUILT is a BATTERY DEFECT and fails the hook; it is never counted as a
// refutation.
//
// AND THE RULES THIS FAMILY'S OWN FACET ORDER PUTS OUT OF REACH ARE DECIDED
// ANYWAY. Two SDM rules this module transcribes are never evaluated by the
// credited MOVSXD r64 family, and a mutation survey found each of them green
// under a deliberately WRONG spelling:
//
//   * THE DESTINATION WIDTH RULE (Vol 1 3.4.1.1). `movsxd_sib_check` forces
//     `dst_bits == 64` at the Extension facet before the Destination facet
//     calls `dst_write_mask`, so the 32-, 16- and 8-bit arms are dead for the
//     credited family. [`DEST_WRITE_MASK_VECTORS`] decodes REAL bytes for all
//     six productions in this decoder's language and pins the width AND the
//     mask of each; the hook runs them.
//   * REX.B DOES NOT CREATE A BASE REGISTER (Vol 2A Tables 2-2 / 2-3). The
//     no-base SIB form and the RIP-relative form are both selected regardless
//     of REX.B, and the original vectors for both had REX.B CLEAR, so a decoder
//     that added `&& !rex_b` to either was refutable by nothing while reading
//     `49 63 04 8D` as `[r13 + rcx*4 + disp32]`. D1b/D1c and D4b/D4c set REX.B,
//     and D1c is stated against the `[r13 + rcx*4]` intent such a decoder would
//     wrongly CREDIT.
//   * THE ANTI-VACUITY GUARD in [`compare_denotations`] protects the
//     sign-extension facet from a narrowed witness family, and nothing ever fed
//     it a family missing a sign case, so deleting it changed no result.
//     [`vacuity_controls_are_refused`] feeds it an all-negative family and an
//     all-non-negative one and demands the exact counts.
//
// WHAT THIS FAMILY DOES NOT ESTABLISH, said plainly (the same list is carried as
// data in [`X86_MOVSXD_SIB_DEFERRALS`] and pinned by the gate test):
//
//   * NOT that anything EMITS this opcode. Nothing does. The active jump-table
//     path uses 8-byte deltas through the already-credited `MovRMSib`, and this
//     row is credited on bytes the ENCODER produces for real operand tuples, not
//     on bytes taken out of a compile. No runtime claim is made or implied.
//   * NOT that instruction selection would choose the right base, index, scale
//     or displacement. A wrong table, a wrong selector or a wrong entry size
//     encodes and decodes perfectly.
//   * NOT a memory-content theorem. `SmtExpr::MemLoad` models memory as a
//     deterministic function of the address; that is what makes a wrong address
//     refutable, and it is NOT a model of aliasing, faulting, #GP on a
//     non-canonical address, or what the table actually holds.
//   * NOT the table ENTRY. That the loaded i32 is `target - table_base` belongs
//     to the #62 dense-mapping gate and the differential fuzz, not here.
//   * NOT that the ISA rules are right. They are TRANSCRIBED from the SDM and
//     are this family's trust base. The `objdump` differential in
//     `trust-cg-codegen/tests/encode_objdump_differential_x86.rs` covers the
//     same bytes with an external disassembler; that is ADJACENT evidence, not
//     part of this obligation.
//   * NOTHING about flags (MOVSXD affects none — SDM "Flags Affected: None" —
//     which is trust base, not something compared here), about instruction
//     placement, reachability or dataflow.
//   * NOT a general x86 decoder, and NOTHING about any other x86-64 RED row.

//! The x86-64 `MOVSXD r64, [base + index*scale + disp]` obligation: an
//! independent SDM-derived decoder for the scaled sign-extending load, the
//! register-write denotation of both the decoded bytes and the machine-IR
//! intent, the typed refutations between them, a captured corpus of real emitted
//! encodings, and the coverage-gate credit hook that demands the negative
//! controls refute.

use std::fmt;

use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::smt::{EvalEnv, SmtExpr};
use crate::x86_encoding_proofs::{SDM_R64, sdm_name, sdm_reg};

/// x86-64 effective addresses and the destination root register are 64 bits.
pub const ADDR_BITS: u32 = 64;

/// The SDM Vol 2A Table 2-3 SIB scale FACTORS, indexed by the raw 2-bit `scale`
/// field: the factor is `1 << ss`. Transcribed, not computed from the encoder.
pub const SDM_SIB_SCALE_FACTOR: [u32; 4] = [1, 2, 4, 8];

// ===========================================================================
// (1) The decoder — a walk of the SDM instruction format, bytes only
// ===========================================================================

/// SDM Vol 2A §2.1.1 legacy prefix groups. None of them is MODELLED: this
/// family's encodings carry no legacy prefix, so each is recognised in order to
/// be REFUSED by name rather than misread as an opcode byte.
const LEGACY_PREFIXES: &[u8] = &[
    0xF0, 0xF2, 0xF3, // group 1 (LOCK / REPNE / REP)
    0x2E, 0x36, 0x3E, 0x26, 0x64, 0x65, // group 2 (segment overrides)
    0x66, // group 3 (operand-size override)
    0x67, // group 4 (address-size override)
];

fn is_legacy_prefix(byte: u8) -> bool {
    LEGACY_PREFIXES.contains(&byte)
}

/// In 64-bit mode the bytes `40..=4F` are REX prefixes, not opcodes
/// (SDM Vol 2A §2.2.1).
fn is_rex(byte: u8) -> bool {
    (0x40..=0x4F).contains(&byte)
}

/// The two one-byte opcodes this decoder's language contains.
///
/// `0x8B` is here on purpose. It is the opcode `MovRMSib` emits, so modelling it
/// means a wrong-mnemonic control refutes on the DECODED MEANING (a 64-bit
/// unextended load) rather than on "unknown opcode", and it means this decoder
/// cannot have been obtained by inverting the single `MovsxdRMSib` arm of
/// `encode.rs`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScaledLoadMnemonic {
    /// `63 /r` — MOVSXD. Sign-extending when REX.W is present.
    Movsxd,
    /// `8B /r` — MOV r, r/m. Never sign-extending.
    Mov,
}

/// Why a byte string is not an instruction in this decoder's language.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScaledLoadDecodeError {
    /// No bytes at all.
    Empty,
    /// A legacy prefix appeared AFTER the REX prefix. SDM Vol 2A §2.2.1: a REX
    /// "must immediately precede the opcode byte".
    PrefixAfterRex(u8),
    /// Two REX prefixes. SDM Vol 2A §2.2.1 allows exactly one.
    DoubledRex,
    /// The byte string ended before a required field.
    Truncated {
        /// Which field was being read.
        field: &'static str,
    },
    /// The opcode byte is outside this decoder's language.
    UnknownOpcode(u8),
    /// The instruction decoded, but did not consume the whole byte string.
    TrailingBytes {
        /// Bytes the decode consumed.
        consumed: usize,
        /// Bytes supplied.
        total: usize,
    },
}

impl fmt::Display for ScaledLoadDecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => f.write_str("empty byte string"),
            Self::PrefixAfterRex(b) => write!(
                f,
                "legacy prefix {b:#04x} after the REX prefix (SDM Vol 2A 2.2.1: REX must \
                 immediately precede the opcode)"
            ),
            Self::DoubledRex => f.write_str("two REX prefixes (SDM Vol 2A 2.2.1 allows one)"),
            Self::Truncated { field } => write!(f, "byte string ends before the {field}"),
            Self::UnknownOpcode(b) => {
                write!(f, "opcode {b:#04x} is not 63 (MOVSXD) or 8B (MOV r,r/m)")
            }
            Self::TrailingBytes { consumed, total } => write!(
                f,
                "decoded {consumed} byte(s) of a {total}-byte string; the remainder is not part \
                 of this instruction"
            ),
        }
    }
}

/// The addressing form ModR/M (and, when present, SIB) selects.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AddressForm {
    /// `mod = 11`: the source is a REGISTER, not memory.
    Register {
        /// The source register's 64-bit root number.
        rm_root: u8,
    },
    /// `mod != 11`, `rm != 100`, not the RIP form: `[base + disp]`, no SIB byte.
    BaseDisp {
        /// The base register's 64-bit root number.
        base: u8,
        /// Sign-extended displacement.
        disp: i64,
    },
    /// `mod = 00`, `rm = 101`: `[RIP + disp32]` (64-bit mode).
    RipRelative {
        /// Sign-extended disp32.
        disp: i64,
    },
    /// `rm = 100`: a SIB memory operand.
    Sib {
        /// `None` for the SDM's no-base form (`SIB.base = 101` with `mod = 00`,
        /// where a disp32 follows and there is no base register).
        base: Option<u8>,
        /// `None` for the SDM's no-index sentinel (`SIB.index = 100` with
        /// `REX.X = 0`). With `REX.X = 1` the same field names R12.
        index: Option<u8>,
        /// The RAW 2-bit SIB `scale` field. The scale FACTOR is `1 << shift`.
        shift: u8,
        /// Sign-extended displacement.
        disp: i64,
    },
}

/// One decoded instruction: every field the SDM walk read, plus the operand
/// size / extension the opcode and REX.W determine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedScaledLoad {
    /// Legacy prefixes seen before the REX, in order. This family's encodings
    /// carry none; a non-empty list is refused as non-canonical.
    pub legacy_prefixes: Vec<u8>,
    /// The REX prefix byte, if present.
    pub rex: Option<u8>,
    /// Which one-byte opcode matched.
    pub mnemonic: ScaledLoadMnemonic,
    /// The raw ModR/M byte.
    pub modrm: u8,
    /// The raw SIB byte, when `ModR/M.rm = 100`.
    pub sib: Option<u8>,
    /// The destination register's 64-bit root number (`ModR/M.reg` + `REX.R<<3`).
    pub dst_root: u8,
    /// The addressing form.
    pub addr: AddressForm,
    /// Width in bits of the memory access itself.
    pub load_bits: u32,
    /// True only for `REX.W + 63 /r` — the sign-extending production.
    pub signed: bool,
    /// Width in bits of the architectural destination operand (64/32/16).
    pub dst_bits: u32,
    /// How many bytes the decode consumed.
    pub len: usize,
}

impl DecodedScaledLoad {
    /// Which bits of the 64-bit ROOT register this instruction writes, per
    /// SDM Vol 1 §3.4.1.1: a 64-bit operand writes all 64; a 32-bit operand
    /// writes a 32-bit result ZERO-EXTENDED to 64, so it too writes all 64; a
    /// 16-bit operand leaves the upper 48 bits UNMODIFIED; an 8-bit operand
    /// leaves the upper 56 UNMODIFIED.
    ///
    /// # This rule is REFUTABLE, not merely transcribed
    ///
    /// [`movsxd_sib_check`] forces `dst_bits == 64` at the Extension facet
    /// before it ever reaches the Destination facet, so for the CREDITED family
    /// only the 64 arm is live and the rest would be unexercised prose — a
    /// mutation of the 32 arm once left the whole gate green. The
    /// [`DEST_WRITE_MASK_VECTORS`] battery decodes REAL byte strings for every
    /// production this decoder's language contains (`REX.W + 63 /r`, `63 /r`,
    /// `66 + 63 /r`, and the three `8B /r` productions) and pins the width AND
    /// the mask each one reports against the SDM rule stated independently of
    /// this table. The hook runs that battery, so every arm below is decided by
    /// something.
    ///
    /// An operand width outside `{64, 32, 16, 8}` does not exist in this
    /// decoder's language — `decoder_operand_widths_are_exactly_64_32_16` pins
    /// that — and claims NOTHING: a zero mask can never equal the source side's
    /// `u64::MAX`, so the Destination facet fails CLOSED rather than inventing a
    /// width rule for a form that was never modelled.
    pub fn dst_write_mask(&self) -> u64 {
        match self.dst_bits {
            64 | 32 => u64::MAX,
            16 => 0xFFFF,
            8 => 0xFF,
            _ => 0,
        }
    }

    /// The SDM-named 64-bit register the destination aliases.
    pub fn dst_name(&self) -> &'static str {
        sdm_name(self.dst_root, 64).unwrap_or("<out-of-range>")
    }

    /// The effective-address expression the DECODED addressing form computes,
    /// over per-register leaves named from the DECODED register NUMBERS.
    ///
    /// `None` for [`AddressForm::Register`] (no memory operand at all) and for
    /// [`AddressForm::RipRelative`] (the address is a link-time quantity this
    /// family does not model) — fail closed, never a vacuous pass.
    ///
    /// The index term is `index << shift`, the SDM's own spelling of the SIB
    /// `scale` field, NOT `index * (1 << shift)`.
    pub fn machine_effective_address(&self) -> Option<SmtExpr> {
        let w = ADDR_BITS;
        match self.addr {
            AddressForm::Register { .. } | AddressForm::RipRelative { .. } => None,
            AddressForm::BaseDisp { base, disp } => {
                Some(reg_leaf(base)?.bvadd(SmtExpr::bv_const(disp as u64, w)))
            }
            AddressForm::Sib {
                base,
                index,
                shift,
                disp,
            } => {
                let mut ea = match base {
                    Some(root) => reg_leaf(root)?,
                    None => SmtExpr::bv_const(0, w),
                };
                if let Some(root) = index {
                    ea = ea.bvadd(reg_leaf(root)?.bvshl(SmtExpr::bv_const(u64::from(shift), w)));
                }
                Some(ea.bvadd(SmtExpr::bv_const(disp as u64, w)))
            }
        }
    }

    /// The register WRITE the decoded bytes perform: the 64-bit root, the bits
    /// of it that change, and the value, as a 64-bit expression.
    ///
    /// The value is the decoded access composed with the decoded extension:
    /// `SignExtend(MemLoad(ea, load_bits, unsigned, load_bits), 64 - load_bits)`
    /// for the sign-extending production, `ZeroExtend(...)` otherwise. The
    /// extension is an EXPLICIT node here; the source side states it as the
    /// `signed` flag of a single load. Two spellings, one function.
    pub fn machine_write(&self) -> Option<RegisterWrite> {
        let ea = self.machine_effective_address()?;
        let raw = SmtExpr::mem_load(ea, self.load_bits, false, self.load_bits);
        let extra = ADDR_BITS - self.load_bits;
        let value = if extra == 0 {
            raw
        } else if self.signed {
            raw.sign_ext(extra)
        } else {
            raw.zero_ext(extra)
        };
        Some(RegisterWrite {
            root: self.dst_root,
            mask: self.dst_write_mask(),
            value,
        })
    }
}

/// The per-register SMT leaf for 64-bit root `root`, named through the SDM
/// register table. `None` for an out-of-range number.
///
/// This is the ONLY path from a decoded register NUMBER to a symbol, and
/// [`intent_write`] reaches the same symbol from the intent's register NAME. A
/// number that names a different register than the intent meant therefore
/// produces a DIFFERENT leaf, which is what makes a wrong base, a wrong index
/// and a base/index swap refutable at all.
fn reg_leaf(root: u8) -> Option<SmtExpr> {
    Some(SmtExpr::var(
        format!("reg_{}", sdm_name(root, 64)?),
        ADDR_BITS,
    ))
}

/// Decode a byte string as a scaled load, using ONLY the bytes.
///
/// The walk is the SDM instruction format: legacy prefixes, REX, one-byte
/// opcode, ModR/M, SIB, displacement — and then the string must be exactly
/// consumed. Forms the x86-64 encoder never emits are modelled deliberately
/// (the no-base SIB, the no-index sentinel, register-direct `mod = 11`,
/// RIP-relative, non-SIB `[base+disp]`, `63 /r` without REX.W, `8B /r`), so this
/// is not an inversion of one encoder arm and the decoder controls in
/// [`sdm_decoder_controls`] refute on MEANING rather than on "unknown opcode".
pub fn sdm_decode_scaled_load(bytes: &[u8]) -> Result<DecodedScaledLoad, ScaledLoadDecodeError> {
    if bytes.is_empty() {
        return Err(ScaledLoadDecodeError::Empty);
    }
    let mut i = 0usize;
    let mut legacy_prefixes = Vec::new();
    while i < bytes.len() && is_legacy_prefix(bytes[i]) {
        legacy_prefixes.push(bytes[i]);
        i += 1;
    }
    let mut rex = None;
    if i < bytes.len() && is_rex(bytes[i]) {
        rex = Some(bytes[i]);
        i += 1;
        if i < bytes.len() && is_rex(bytes[i]) {
            return Err(ScaledLoadDecodeError::DoubledRex);
        }
        if i < bytes.len() && is_legacy_prefix(bytes[i]) {
            return Err(ScaledLoadDecodeError::PrefixAfterRex(bytes[i]));
        }
    }
    let rex_bit = |shift: u32| rex.is_some_and(|r| (r >> shift) & 1 == 1);
    let (rex_w, rex_r, rex_x, rex_b) = (rex_bit(3), rex_bit(2), rex_bit(1), rex_bit(0));

    let opcode = *bytes
        .get(i)
        .ok_or(ScaledLoadDecodeError::Truncated { field: "opcode" })?;
    i += 1;
    let mnemonic = match opcode {
        0x63 => ScaledLoadMnemonic::Movsxd,
        0x8B => ScaledLoadMnemonic::Mov,
        other => return Err(ScaledLoadDecodeError::UnknownOpcode(other)),
    };

    let modrm = *bytes.get(i).ok_or(ScaledLoadDecodeError::Truncated {
        field: "ModR/M byte",
    })?;
    i += 1;
    let mod_field = modrm >> 6;
    let reg_field = (modrm >> 3) & 0b111;
    let rm_field = modrm & 0b111;
    let dst_root = reg_field | (u8::from(rex_r) << 3);

    // Displacement reader, shared by every memory form.
    let read_disp8 = |i: &mut usize| -> Result<i64, ScaledLoadDecodeError> {
        let b = *bytes
            .get(*i)
            .ok_or(ScaledLoadDecodeError::Truncated { field: "disp8" })?;
        *i += 1;
        Ok(i64::from(b as i8))
    };
    let read_disp32 = |i: &mut usize| -> Result<i64, ScaledLoadDecodeError> {
        if *i + 4 > bytes.len() {
            return Err(ScaledLoadDecodeError::Truncated { field: "disp32" });
        }
        let raw = i32::from_le_bytes([bytes[*i], bytes[*i + 1], bytes[*i + 2], bytes[*i + 3]]);
        *i += 4;
        Ok(i64::from(raw))
    };

    let mut sib = None;
    let addr = if mod_field == 0b11 {
        AddressForm::Register {
            rm_root: rm_field | (u8::from(rex_b) << 3),
        }
    } else if rm_field == 0b100 {
        let sib_byte = *bytes
            .get(i)
            .ok_or(ScaledLoadDecodeError::Truncated { field: "SIB byte" })?;
        i += 1;
        sib = Some(sib_byte);
        let shift = sib_byte >> 6;
        let index_field = (sib_byte >> 3) & 0b111;
        let base_field = sib_byte & 0b111;
        // SDM Vol 2A Table 2-3: index = 100b with REX.X = 0 means NO index.
        // With REX.X = 1 the same field names R12.
        let index = if index_field == 0b100 && !rex_x {
            None
        } else {
            Some(index_field | (u8::from(rex_x) << 3))
        };
        // SDM Vol 2A Table 2-3: base = 101b with mod = 00 means NO base and a
        // disp32 follows; REX.B does not rescue it.
        let (base, disp) = if base_field == 0b101 && mod_field == 0b00 {
            (None, read_disp32(&mut i)?)
        } else {
            let b = Some(base_field | (u8::from(rex_b) << 3));
            let d = match mod_field {
                0b00 => 0,
                0b01 => read_disp8(&mut i)?,
                _ => read_disp32(&mut i)?,
            };
            (b, d)
        };
        AddressForm::Sib {
            base,
            index,
            shift,
            disp,
        }
    } else if rm_field == 0b101 && mod_field == 0b00 {
        AddressForm::RipRelative {
            disp: read_disp32(&mut i)?,
        }
    } else {
        let base = rm_field | (u8::from(rex_b) << 3);
        let disp = match mod_field {
            0b00 => 0,
            0b01 => read_disp8(&mut i)?,
            _ => read_disp32(&mut i)?,
        };
        AddressForm::BaseDisp { base, disp }
    };

    // Operand size. SDM Vol 2A §2.2.1: REX.W takes precedence over 66H.
    let has_66 = legacy_prefixes.contains(&0x66);
    let (load_bits, dst_bits, signed) = match (mnemonic, rex_w, has_66) {
        // REX.W + 63 /r — MOVSXD r64, r/m32.
        (ScaledLoadMnemonic::Movsxd, true, _) => (32, 64, true),
        // 66 + 63 /r — MOVSXD r16, r/m16 (a 16-bit move, no extension).
        (ScaledLoadMnemonic::Movsxd, false, true) => (16, 16, false),
        // 63 /r — MOVSXD r32, r/m32 (a 32-bit move; the SDM discourages it).
        (ScaledLoadMnemonic::Movsxd, false, false) => (32, 32, false),
        (ScaledLoadMnemonic::Mov, true, _) => (64, 64, false),
        (ScaledLoadMnemonic::Mov, false, true) => (16, 16, false),
        (ScaledLoadMnemonic::Mov, false, false) => (32, 32, false),
    };

    if i != bytes.len() {
        return Err(ScaledLoadDecodeError::TrailingBytes {
            consumed: i,
            total: bytes.len(),
        });
    }

    Ok(DecodedScaledLoad {
        legacy_prefixes,
        rex,
        mnemonic,
        modrm,
        sib,
        dst_root,
        addr,
        load_bits,
        signed,
        dst_bits,
        len: i,
    })
}

// ===========================================================================
// (2) The register-write denotation, shared by both sides
// ===========================================================================

/// A write to one 64-bit root register: `old -> (old & !mask) | (value & mask)`.
///
/// # Lemma (why comparing these decides the question)
///
/// Two `RegisterWrite`s denote the SAME function of the prior register value iff
/// their `root` and `mask` are equal and their `value` expressions agree on the
/// masked bits for every assignment of the leaves. `root` and `mask` are
/// compared as data; the values are compared by [`compare_denotations`].
#[derive(Debug, Clone, PartialEq)]
pub struct RegisterWrite {
    /// SDM number of the 64-bit root register, `0..=15`.
    pub root: u8,
    /// Which bits of the root change.
    pub mask: u64,
    /// The 64-bit value; only the masked bits are meaningful.
    pub value: SmtExpr,
}

/// The machine-IR intent for one scaled sign-extending load, in the machine
/// IR's own vocabulary: register NAMES, an entry SIZE in bytes and a
/// displacement. No byte, no register number, no SIB field.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ScaledSextLoadIntent {
    /// Destination register name, e.g. `"rax"`.
    pub dst: &'static str,
    /// Base register name — the table base.
    pub base: &'static str,
    /// Index register name — the selector.
    pub index: &'static str,
    /// Size in bytes of one table entry. The index is scaled by this.
    pub entry_bytes: u32,
    /// Byte displacement added to the address.
    pub disp: i64,
}

impl ScaledSextLoadIntent {
    /// A short label for diagnostics.
    pub fn label(&self) -> String {
        format!(
            "MOVSXD {}, dword [{} + {}*{} {:+#x}]",
            self.dst, self.base, self.index, self.entry_bytes, self.disp
        )
    }
}

/// Why an intent is not usable as the source side of this obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnusableIntent(pub String);

impl fmt::Display for UnusableIntent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// The 64-bit root number of a register named in an intent. The name must be a
/// SIXTY-FOUR-BIT general-purpose register: this family addresses memory with
/// 64-bit base and index registers and writes a 64-bit destination, so a
/// narrower or non-GPR name is refused rather than silently widened.
fn intent_root(role: &str, name: &str) -> Result<u8, UnusableIntent> {
    match sdm_reg(name) {
        Some(r) if r.bits == 64 => Ok(r.root),
        Some(r) => Err(UnusableIntent(format!(
            "intent {role} `{name}` is a {}-bit register; this family names 64-bit GPRs",
            r.bits
        ))),
        None => Err(UnusableIntent(format!(
            "intent {role} `{name}` is not a general-purpose register"
        ))),
    }
}

/// The register write the MACHINE IR means, from the intent alone.
///
/// The value is ONE node — a 32-bit SIGNED load widened to 64 bits — and the
/// address is `base + index*entry_bytes + disp` with a MULTIPLY. Both spellings
/// differ from the machine side's on purpose; see the module header.
pub fn intent_write(intent: &ScaledSextLoadIntent) -> Result<RegisterWrite, UnusableIntent> {
    let dst = intent_root("destination", intent.dst)?;
    let base = intent_root("base", intent.base)?;
    let index = intent_root("index", intent.index)?;
    if !SDM_SIB_SCALE_FACTOR.contains(&intent.entry_bytes) {
        return Err(UnusableIntent(format!(
            "intent entry size {} is not an x86 SIB scale factor (1, 2, 4 or 8)",
            intent.entry_bytes
        )));
    }
    let w = ADDR_BITS;
    let base_leaf = reg_leaf(base).ok_or_else(|| UnusableIntent("bad base root".into()))?;
    let index_leaf = reg_leaf(index).ok_or_else(|| UnusableIntent("bad index root".into()))?;
    let scaled = index_leaf.bvmul(SmtExpr::bv_const(u64::from(intent.entry_bytes), w));
    let ea = base_leaf
        .bvadd(scaled)
        .bvadd(SmtExpr::bv_const(intent.disp as u64, w));
    Ok(RegisterWrite {
        root: dst,
        mask: u64::MAX,
        value: SmtExpr::mem_load(ea, 32, true, 64),
    })
}

// ===========================================================================
// (3) The witness family
// ===========================================================================

/// How many witness rows the value comparison runs.
pub const WITNESS_ROWS: usize = 16;

/// The base value of each witness row. Chosen to span zero, small positive
/// offsets, page-sized offsets, the 32-bit boundary and the negative (high-bit)
/// half of the address space.
const WITNESS_ROW_BASE: [u64; WITNESS_ROWS] = [
    0x0000_0000_0000_0000,
    0x0000_0000_0000_0001,
    0x0000_0000_0000_0008,
    0x0000_0000_0000_1000,
    0x0000_0000_0001_0000,
    0x0000_0000_7FFF_FFF0,
    0x0000_0000_8000_0000,
    0x0000_0000_FFFF_FFF8,
    0x0000_0001_0000_0000,
    0x0000_7FFF_FFFF_FFF8,
    0x0000_8000_0000_0000,
    0x1234_5678_9ABC_DEF0,
    0x7FFF_FFFF_FFFF_FFF8,
    0x8000_0000_0000_0000,
    0xDEAD_BEEF_CAFE_0000,
    0xFFFF_FFFF_FFFF_FFF0,
];

/// The per-register stride of each witness row. Every entry is ODD, which is
/// what makes [`witness_reg_value`] injective across the sixteen roots within a
/// row: `stride * (r1 - r2) != 0 (mod 2^64)` for `0 < |r1 - r2| < 16` when
/// `stride` is odd. `witness_rows_separate_every_register` pins it.
const WITNESS_ROW_STRIDE: [u64; WITNESS_ROWS] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_0003,
    0x0000_0000_0000_0011,
    0x0000_0000_0000_0101,
    0x0000_0000_0001_0001,
    0x0000_0000_1000_0001,
    0x0000_0001_0000_0003,
    0x0000_0100_0000_0005,
    0x9E37_79B9_7F4A_7C15,
    0xBF58_476D_1CE4_E5B9,
    0x94D0_49BB_1331_11EB,
    0x2545_F491_4F6C_DD1D,
    0xD6E8_FEB8_6659_FD93,
    0xA076_1D64_78BD_642F,
    0xE703_7ED1_A0B4_28DB,
    0xFFFF_FFFF_FFFF_FFFF,
];

/// The value witness row `row` binds to the 64-bit root register `root`.
///
/// Distinct registers get distinct values within a row (see
/// [`WITNESS_ROW_STRIDE`]), so a swapped or substituted base/index register
/// changes the effective address at every row.
pub fn witness_reg_value(row: usize, root: u8) -> u64 {
    WITNESS_ROW_BASE[row].wrapping_add(
        u64::from(root)
            .wrapping_add(1)
            .wrapping_mul(WITNESS_ROW_STRIDE[row]),
    )
}

/// The evaluation environment for witness row `row`: every one of the sixteen
/// 64-bit roots bound, so ANY leaf either side can name is defined and an
/// unbound-variable evaluation error cannot masquerade as agreement.
///
/// Built once per process. The credit hook runs inside the coverage gate, which
/// audits the whole opcode universe repeatedly; rebuilding sixteen
/// `String`-keyed environments per comparison was the only allocation on that
/// path worth removing.
fn witness_env(row: usize) -> &'static EvalEnv {
    static ENVS: std::sync::OnceLock<Vec<EvalEnv>> = std::sync::OnceLock::new();
    &ENVS.get_or_init(|| {
        (0..WITNESS_ROWS)
            .map(|row| {
                let mut env = EvalEnv::default();
                for (root, name) in SDM_R64.iter().enumerate() {
                    env.insert(format!("reg_{name}"), witness_reg_value(row, root as u8));
                }
                env
            })
            .collect()
    })[row]
}

// ===========================================================================
// (4) Refutations
// ===========================================================================

/// The reason class a refutation belongs to. A negative control states the class
/// it must be refuted for, and [`control_is_refuted_as_stated`] demands exactly
/// that class — a control that refutes for a different reason withholds the
/// credit just as a surviving one does.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ScaledLoadRefutationClass {
    /// The intent itself is unusable (not a 64-bit GPR, not a SIB scale factor).
    IntentShape,
    /// The bytes are not an instruction in this decoder's language.
    Decode,
    /// The bytes decode, but the decode does not consume exactly the string.
    Framing,
    /// The bytes decode and mean the right thing, but carry a legacy prefix this
    /// family's encodings never carry.
    NonCanonical,
    /// The opcode is not MOVSXD.
    Mnemonic,
    /// The production does not sign-extend (REX.W missing, or a MOV).
    Extension,
    /// The memory access is not 32 bits wide.
    AccessWidth,
    /// Wrong destination register, or the write does not cover the whole root.
    Destination,
    /// Not a `[base + index*scale + disp]` memory operand at all.
    AddressShape,
    /// Wrong base register.
    BaseRegister,
    /// Wrong index register.
    IndexRegister,
    /// Wrong scale factor.
    Scale,
    /// Wrong displacement.
    Displacement,
    /// The two value denotations disagree at a witness.
    Value,
    /// The machine side is structurally IDENTICAL to the source side — an
    /// `X == X` that decides nothing, refused rather than credited.
    Degenerate,
    /// The witness family fails to exercise both sign cases of the loaded
    /// doubleword, so the extension facet would pass vacuously.
    VacuousWitnesses,
    /// A side could not be evaluated. Never a legitimate stated class; the
    /// credit hook rejects any control that claims it.
    Unevaluable,
}

/// One refutation of `(intent, bytes)`.
#[derive(Debug, Clone, PartialEq)]
pub enum ScaledLoadRefutation {
    /// The intent is unusable.
    IntentShape(UnusableIntent),
    /// The bytes did not decode.
    Decode(ScaledLoadDecodeError),
    /// The decode did not consume the string exactly.
    Framing(ScaledLoadDecodeError),
    /// A legacy prefix is present.
    NonCanonical {
        /// The prefixes found.
        prefixes: Vec<u8>,
    },
    /// The opcode is not MOVSXD.
    Mnemonic {
        /// What the bytes say.
        decoded: ScaledLoadMnemonic,
    },
    /// The production does not sign-extend.
    Extension {
        /// The decoded destination width.
        dst_bits: u32,
        /// Whether the decoded production sign-extends.
        signed: bool,
    },
    /// The access width is not 32.
    AccessWidth {
        /// The decoded access width.
        decoded: u32,
    },
    /// Wrong destination.
    Destination {
        /// The decoded destination root name.
        decoded: &'static str,
        /// The intended destination name.
        intended: &'static str,
        /// The decoded write mask.
        mask: u64,
    },
    /// Not a base+index*scale memory operand.
    AddressShape {
        /// What the bytes describe.
        found: String,
    },
    /// Wrong base register.
    BaseRegister {
        /// The decoded base name.
        decoded: &'static str,
        /// The intended base name.
        intended: &'static str,
    },
    /// Wrong index register.
    IndexRegister {
        /// The decoded index name.
        decoded: &'static str,
        /// The intended index name.
        intended: &'static str,
    },
    /// Wrong scale factor.
    Scale {
        /// `1 << ss`, from the raw SIB scale field.
        decoded: u32,
        /// The intended entry size in bytes.
        intended: u32,
    },
    /// Wrong displacement.
    Displacement {
        /// The decoded displacement.
        decoded: i64,
        /// The intended displacement.
        intended: i64,
    },
    /// The denotations disagree.
    Value {
        /// Which witness row disagreed.
        row: usize,
        /// The source side's masked value there.
        source: u64,
        /// The machine side's masked value there.
        machine: u64,
    },
    /// The two sides are the same expression.
    Degenerate,
    /// The witness family does not exercise both sign cases.
    VacuousWitnesses {
        /// How many rows produced a NEGATIVE doubleword.
        negative_rows: usize,
        /// How many rows produced a NON-NEGATIVE doubleword.
        non_negative_rows: usize,
    },
    /// A side could not be evaluated.
    Unevaluable {
        /// Which witness row.
        row: usize,
        /// The evaluator's complaint.
        detail: String,
    },
}

impl ScaledLoadRefutation {
    /// The reason class this refutation belongs to.
    pub fn class(&self) -> ScaledLoadRefutationClass {
        use ScaledLoadRefutationClass as C;
        match self {
            Self::IntentShape(_) => C::IntentShape,
            Self::Decode(_) => C::Decode,
            Self::Framing(_) => C::Framing,
            Self::NonCanonical { .. } => C::NonCanonical,
            Self::Mnemonic { .. } => C::Mnemonic,
            Self::Extension { .. } => C::Extension,
            Self::AccessWidth { .. } => C::AccessWidth,
            Self::Destination { .. } => C::Destination,
            Self::AddressShape { .. } => C::AddressShape,
            Self::BaseRegister { .. } => C::BaseRegister,
            Self::IndexRegister { .. } => C::IndexRegister,
            Self::Scale { .. } => C::Scale,
            Self::Displacement { .. } => C::Displacement,
            Self::Value { .. } => C::Value,
            Self::Degenerate => C::Degenerate,
            Self::VacuousWitnesses { .. } => C::VacuousWitnesses,
            Self::Unevaluable { .. } => C::Unevaluable,
        }
    }
}

impl fmt::Display for ScaledLoadRefutation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IntentShape(why) => write!(f, "unusable intent: {why}"),
            Self::Decode(e) => write!(f, "the bytes do not decode: {e}"),
            Self::Framing(e) => write!(f, "framing: {e}"),
            Self::NonCanonical { prefixes } => write!(
                f,
                "the encoding carries legacy prefix(es) {prefixes:02x?}; this family's encodings \
                 carry none"
            ),
            Self::Mnemonic { decoded } => {
                write!(f, "the opcode decodes as {decoded:?}, not MOVSXD")
            }
            Self::Extension { dst_bits, signed } => write!(
                f,
                "the decoded production writes {dst_bits} bits and sign-extends = {signed}; the \
                 intent means a SIGN-EXTENDING load into a 64-bit register"
            ),
            Self::AccessWidth { decoded } => write!(
                f,
                "the memory access decodes as {decoded} bits, not the 32-bit doubleword the \
                 intent means"
            ),
            Self::Destination {
                decoded,
                intended,
                mask,
            } => write!(
                f,
                "the bytes write {decoded} (mask {mask:#018x}); the intent writes all of {intended}"
            ),
            Self::AddressShape { found } => write!(
                f,
                "the addressing form is {found}, not [base + index*scale + disp]"
            ),
            Self::BaseRegister { decoded, intended } => {
                write!(f, "base decodes as {decoded}; the intent means {intended}")
            }
            Self::IndexRegister { decoded, intended } => {
                write!(f, "index decodes as {decoded}; the intent means {intended}")
            }
            Self::Scale { decoded, intended } => write!(
                f,
                "the SIB scale field denotes a factor of {decoded}; the intent means an entry \
                 size of {intended}"
            ),
            Self::Displacement { decoded, intended } => write!(
                f,
                "the displacement decodes as {decoded:+}; the intent means {intended:+}"
            ),
            Self::Value {
                row,
                source,
                machine,
            } => write!(
                f,
                "the denotations disagree at witness row {row}: the intent means \
                 {source:#018x}, the bytes denote {machine:#018x}"
            ),
            Self::Degenerate => f.write_str(
                "the machine side is structurally IDENTICAL to the source side — an X == X that \
                 decides nothing",
            ),
            Self::VacuousWitnesses {
                negative_rows,
                non_negative_rows,
            } => write!(
                f,
                "the witness family produced {negative_rows} negative and {non_negative_rows} \
                 non-negative doublewords; the sign-extension facet needs at least one of each"
            ),
            Self::Unevaluable { row, detail } => {
                write!(f, "witness row {row} could not be evaluated: {detail}")
            }
        }
    }
}

// ===========================================================================
// (5) The comparison
// ===========================================================================

/// Compare a SOURCE and a MACHINE value denotation over the witness family.
///
/// Every control — byte mutant, source re-claim and wrong-model alike — reaches
/// its refutation through THIS function, so "the controls refute" is a statement
/// about the obligation's own comparison and not about some parallel check.
///
/// Three things happen, in order:
///
/// 1. DEGENERACY. A machine side structurally EQUAL to the source side is
///    refused ([`ScaledLoadRefutationClass::Degenerate`]). The whole point of
///    stating the address as a shift and the widening as an explicit node is
///    that the two sides cannot collapse into each other; this enforces it
///    instead of trusting it.
/// 2. NON-VACUITY. The SOURCE side must produce at least one NEGATIVE and one
///    NON-NEGATIVE doubleword across the family, otherwise a zero-extending
///    machine side would agree everywhere and the extension facet would be
///    decided by nothing.
/// 3. AGREEMENT. The masked values must be equal at every row.
pub fn compare_denotations(
    source: &SmtExpr,
    machine: &SmtExpr,
    mask: u64,
) -> Result<WitnessOutcome, ScaledLoadRefutation> {
    if source == machine {
        return Err(ScaledLoadRefutation::Degenerate);
    }
    let mut negative_rows = 0usize;
    let mut source_values = Vec::with_capacity(WITNESS_ROWS);
    for row in 0..WITNESS_ROWS {
        let env = witness_env(row);
        let s = source
            .try_eval(env)
            .map_err(|e| ScaledLoadRefutation::Unevaluable {
                row,
                detail: format!("source side: {e}"),
            })?
            .as_u64();
        if s & 0x8000_0000_0000_0000 != 0 {
            negative_rows += 1;
        }
        source_values.push(s);
    }
    let non_negative_rows = WITNESS_ROWS - negative_rows;
    if negative_rows == 0 || non_negative_rows == 0 {
        return Err(ScaledLoadRefutation::VacuousWitnesses {
            negative_rows,
            non_negative_rows,
        });
    }
    for (row, &s) in source_values.iter().enumerate() {
        let env = witness_env(row);
        let m = machine
            .try_eval(env)
            .map_err(|e| ScaledLoadRefutation::Unevaluable {
                row,
                detail: format!("machine side: {e}"),
            })?
            .as_u64();
        if s & mask != m & mask {
            return Err(ScaledLoadRefutation::Value {
                row,
                source: s & mask,
                machine: m & mask,
            });
        }
    }
    Ok(WitnessOutcome {
        rows: WITNESS_ROWS,
        negative_rows,
    })
}

/// What the witness comparison established.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WitnessOutcome {
    /// Rows compared.
    pub rows: usize,
    /// Rows whose loaded doubleword was NEGATIVE — the rows that exercise the
    /// sign extension. Zero would be vacuous and is refused.
    pub negative_rows: usize,
}

/// What a holding `(intent, bytes)` pair established.
#[derive(Debug, Clone, PartialEq)]
pub struct ScaledLoadHolds {
    /// The decode the machine side was rebuilt from.
    pub decoded: DecodedScaledLoad,
    /// The witness comparison's outcome.
    pub witnesses: WitnessOutcome,
}

/// Decide `(intent, bytes)`.
///
/// The facets are checked in a fixed order, each with its own reason class, and
/// the value denotations are compared LAST. The early facets are not a
/// shortcut around the comparison: they exist so a byte mutation is refuted for
/// the reason it actually broke, and the WRONG-MODEL controls
/// ([`scaled_load_model_controls`]) go straight to [`compare_denotations`] so
/// that comparison is never decorative.
///
/// THE SCALE FACET IS EXACT, not sampled: `base + index*s + disp` equals
/// `base + (index << ss) + disp` for every 64-bit `base`/`index` iff
/// `s == 1 << ss` (module header, "THE EFFECTIVE ADDRESS IS EXACT").
pub fn movsxd_sib_check(
    intent: &ScaledSextLoadIntent,
    bytes: &[u8],
) -> Result<ScaledLoadHolds, ScaledLoadRefutation> {
    let source = intent_write(intent).map_err(ScaledLoadRefutation::IntentShape)?;
    let decoded = sdm_decode_scaled_load(bytes).map_err(|e| match e {
        ScaledLoadDecodeError::Truncated { .. } | ScaledLoadDecodeError::TrailingBytes { .. } => {
            ScaledLoadRefutation::Framing(e)
        }
        other => ScaledLoadRefutation::Decode(other),
    })?;

    if !decoded.legacy_prefixes.is_empty() {
        return Err(ScaledLoadRefutation::NonCanonical {
            prefixes: decoded.legacy_prefixes.clone(),
        });
    }
    if decoded.mnemonic != ScaledLoadMnemonic::Movsxd {
        return Err(ScaledLoadRefutation::Mnemonic {
            decoded: decoded.mnemonic,
        });
    }
    if !decoded.signed || decoded.dst_bits != 64 {
        return Err(ScaledLoadRefutation::Extension {
            dst_bits: decoded.dst_bits,
            signed: decoded.signed,
        });
    }
    if decoded.load_bits != 32 {
        return Err(ScaledLoadRefutation::AccessWidth {
            decoded: decoded.load_bits,
        });
    }
    if decoded.dst_root != source.root || decoded.dst_write_mask() != source.mask {
        return Err(ScaledLoadRefutation::Destination {
            decoded: decoded.dst_name(),
            intended: intent.dst,
            mask: decoded.dst_write_mask(),
        });
    }

    let (base, index, shift, disp) = match decoded.addr {
        AddressForm::Sib {
            base: Some(b),
            index: Some(i),
            shift,
            disp,
        } => (b, i, shift, disp),
        AddressForm::Sib {
            base: None, index, ..
        } => {
            return Err(ScaledLoadRefutation::AddressShape {
                found: format!(
                    "a SIB form with NO base register (SIB.base=101 with mod=00), index={}",
                    index.and_then(|r| sdm_name(r, 64)).unwrap_or("none")
                ),
            });
        }
        AddressForm::Sib { index: None, .. } => {
            return Err(ScaledLoadRefutation::AddressShape {
                found: "a SIB form with NO index register (SIB.index=100 with REX.X=0)".to_string(),
            });
        }
        AddressForm::BaseDisp { base, disp } => {
            return Err(ScaledLoadRefutation::AddressShape {
                found: format!(
                    "the non-SIB form [{} {:+}]",
                    sdm_name(base, 64).unwrap_or("?"),
                    disp
                ),
            });
        }
        AddressForm::RipRelative { disp } => {
            return Err(ScaledLoadRefutation::AddressShape {
                found: format!("RIP-relative [rip {disp:+}]"),
            });
        }
        AddressForm::Register { rm_root } => {
            return Err(ScaledLoadRefutation::AddressShape {
                found: format!(
                    "register-direct (mod=11), source {}",
                    sdm_name(rm_root, 64).unwrap_or("?")
                ),
            });
        }
    };

    let intended_base =
        intent_root("base", intent.base).map_err(ScaledLoadRefutation::IntentShape)?;
    let intended_index =
        intent_root("index", intent.index).map_err(ScaledLoadRefutation::IntentShape)?;
    if base != intended_base {
        return Err(ScaledLoadRefutation::BaseRegister {
            decoded: sdm_name(base, 64).unwrap_or("?"),
            intended: intent.base,
        });
    }
    if index != intended_index {
        return Err(ScaledLoadRefutation::IndexRegister {
            decoded: sdm_name(index, 64).unwrap_or("?"),
            intended: intent.index,
        });
    }
    let factor = SDM_SIB_SCALE_FACTOR[usize::from(shift & 0b11)];
    if factor != intent.entry_bytes {
        return Err(ScaledLoadRefutation::Scale {
            decoded: factor,
            intended: intent.entry_bytes,
        });
    }
    if disp != intent.disp {
        return Err(ScaledLoadRefutation::Displacement {
            decoded: disp,
            intended: intent.disp,
        });
    }

    let machine = decoded
        .machine_write()
        .ok_or_else(|| ScaledLoadRefutation::AddressShape {
            found: "an addressing form with no modelled effective address".to_string(),
        })?;
    let witnesses = compare_denotations(&source.value, &machine.value, source.mask)?;
    Ok(ScaledLoadHolds { decoded, witnesses })
}

// ===========================================================================
// (6) The obligation, as a `ProofObligation`
// ===========================================================================

/// The obligation as a [`ProofObligation`], so the crate's own predicates apply
/// to it: [`ProofObligation::is_genuinely_proven`] must hold (the two sides are
/// structurally distinct) and `verify_by_evaluation` must return `Valid`.
///
/// The credit HOOK does not use this — it uses the cheap, deterministic witness
/// family in [`compare_denotations`], because the hook runs inside the coverage
/// gate. `tests/x86_movsxd_sib_gate.rs` runs the full sampling sweep over the
/// obligation this builds, plus an exhaustive sweep over a contiguous address
/// window. Returns `None` when the intent or the bytes are unusable.
pub fn movsxd_sib_proof_obligation(
    intent: &ScaledSextLoadIntent,
    bytes: &[u8],
) -> Option<ProofObligation> {
    let source = intent_write(intent).ok()?;
    let decoded = sdm_decode_scaled_load(bytes).ok()?;
    let machine = decoded.machine_write()?;
    let mut inputs: Vec<(String, u32)> = Vec::new();
    for name in [intent.base, intent.index] {
        let leaf = format!("reg_{name}");
        if !inputs.iter().any(|(n, _)| *n == leaf) {
            inputs.push((leaf, ADDR_BITS));
        }
    }
    // A control may name a register the intent does not; declare every root the
    // machine side could have reached so the sampler binds it.
    if let AddressForm::Sib { base, index, .. } = decoded.addr {
        for root in [base, index].into_iter().flatten() {
            let leaf = format!("reg_{}", sdm_name(root, 64)?);
            if !inputs.iter().any(|(n, _)| *n == leaf) {
                inputs.push((leaf, ADDR_BITS));
            }
        }
    }
    Some(ProofObligation {
        name: format!(
            "x86_movsxd_sib: {} — emitted bytes denote the intended scaled sign-extending load",
            intent.label()
        ),
        trust_ir_expr: source.value,
        aarch64_expr: machine.value,
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "MovsxdRMSib".to_string(),
            arity: 2,
        },
    })
}

// ===========================================================================
// (7) Encoding facets the corpus must cover
// ===========================================================================

/// One structural property of an encoding. The credit hook requires the corpus
/// to exhibit every one of [`REQUIRED_ENCODING_FACETS`]: a corpus that never
/// sets REX.X, or never uses a `disp32`, would leave those decoder decisions
/// unexercised while the row was green.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum EncodingFacet {
    /// SIB scale field denotes a factor of 1 / 2 / 4 / 8.
    ScaleFactor(u32),
    /// ModR/M.mod = 00 (no displacement bytes).
    NoDisplacement,
    /// ModR/M.mod = 01 with a POSITIVE disp8.
    PositiveDisp8,
    /// ModR/M.mod = 01 with a NEGATIVE disp8.
    NegativeDisp8,
    /// ModR/M.mod = 01 with a ZERO disp8 — the encoding forced by a base whose
    /// low three bits are 101 (RBP / R13), where `mod = 00` would mean no base.
    ForcedZeroDisp8,
    /// ModR/M.mod = 10 with a POSITIVE disp32.
    PositiveDisp32,
    /// ModR/M.mod = 10 with a NEGATIVE disp32.
    NegativeDisp32,
    /// REX.R set (an extended destination register).
    RexR,
    /// REX.X set (an extended index register).
    RexX,
    /// REX.B set (an extended base register).
    RexB,
    /// The index is R12 — `SIB.index = 100` rescued by `REX.X = 1`, the field
    /// value that means NO INDEX when REX.X is clear.
    IndexIsR12,
    /// The base's low three bits are 100 (RSP or R12).
    BaseLow3IsRsp,
    /// The same register is used as BOTH base and index (legal, and it makes a
    /// base/index swap unobservable — which is why the swap controls skip it).
    BaseEqualsIndex,
}

/// Every facet the corpus must exhibit for the hook to credit the row.
pub const REQUIRED_ENCODING_FACETS: &[EncodingFacet] = &[
    EncodingFacet::ScaleFactor(1),
    EncodingFacet::ScaleFactor(2),
    EncodingFacet::ScaleFactor(4),
    EncodingFacet::ScaleFactor(8),
    EncodingFacet::NoDisplacement,
    EncodingFacet::PositiveDisp8,
    EncodingFacet::NegativeDisp8,
    EncodingFacet::ForcedZeroDisp8,
    EncodingFacet::PositiveDisp32,
    EncodingFacet::NegativeDisp32,
    EncodingFacet::RexR,
    EncodingFacet::RexX,
    EncodingFacet::RexB,
    EncodingFacet::IndexIsR12,
    EncodingFacet::BaseLow3IsRsp,
    EncodingFacet::BaseEqualsIndex,
];

/// The facets one holding encoding exhibits, read off the DECODE.
pub fn facets_of(decoded: &DecodedScaledLoad, intent: &ScaledSextLoadIntent) -> Vec<EncodingFacet> {
    let mut out = Vec::new();
    let AddressForm::Sib {
        base: Some(base),
        index: Some(index),
        shift,
        disp,
    } = decoded.addr
    else {
        return out;
    };
    out.push(EncodingFacet::ScaleFactor(
        SDM_SIB_SCALE_FACTOR[usize::from(shift & 0b11)],
    ));
    match decoded.modrm >> 6 {
        0b00 => out.push(EncodingFacet::NoDisplacement),
        0b01 => out.push(match disp {
            0 => EncodingFacet::ForcedZeroDisp8,
            d if d > 0 => EncodingFacet::PositiveDisp8,
            _ => EncodingFacet::NegativeDisp8,
        }),
        _ => out.push(if disp >= 0 {
            EncodingFacet::PositiveDisp32
        } else {
            EncodingFacet::NegativeDisp32
        }),
    }
    let rex = decoded.rex.unwrap_or(0);
    if (rex >> 2) & 1 == 1 {
        out.push(EncodingFacet::RexR);
    }
    if (rex >> 1) & 1 == 1 {
        out.push(EncodingFacet::RexX);
    }
    if rex & 1 == 1 {
        out.push(EncodingFacet::RexB);
    }
    if index == 12 {
        out.push(EncodingFacet::IndexIsR12);
    }
    if base & 0b111 == 0b100 {
        out.push(EncodingFacet::BaseLow3IsRsp);
    }
    if intent.base == intent.index {
        out.push(EncodingFacet::BaseEqualsIndex);
    }
    out
}

// ===========================================================================
// (8) Negative controls
// ===========================================================================

/// Which side of the obligation a control moved.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ControlSide {
    /// The real bytes were mutated; the intent is unchanged.
    Machine,
    /// The same real bytes; a different claim about what they mean.
    Source,
}

/// One byte-or-intent control: a wrong `(intent, bytes)` pairing and the reason
/// class the obligation MUST refute it for.
#[derive(Debug, Clone, PartialEq)]
pub struct ScaledLoadControl {
    /// The control's label; one of [`REQUIRED_CONTROL_LABELS`].
    pub label: &'static str,
    /// Which side moved.
    pub side: ControlSide,
    /// The (possibly re-claimed) intent.
    pub intent: ScaledSextLoadIntent,
    /// The (possibly mutated) bytes.
    pub bytes: Vec<u8>,
    /// The reason class the obligation must refute this control for.
    pub expect: ScaledLoadRefutationClass,
}

/// B1: a different destination in ModR/M.reg.
pub const B1_WRONG_DST_MODRM_REG: &str = "B1 wrong destination (ModR/M.reg low 3 bits)";
/// B2: REX.R toggled — the destination's high register bit.
pub const B2_WRONG_DST_REX_R: &str = "B2 wrong destination (REX.R toggled)";
/// B3: REX.X toggled where the index's low 3 bits are not the no-index sentinel.
pub const B3_WRONG_INDEX_REX_X: &str = "B3 wrong index (REX.X toggled)";
/// B3b: REX.X cleared on an R12 index — the field then means NO INDEX.
pub const B3B_R12_INDEX_LOSES_REX_X: &str =
    "B3b REX.X cleared on an R12 index (SIB.index=100 becomes the no-index sentinel)";
/// B4: REX.B toggled — the base's high register bit.
pub const B4_WRONG_BASE_REX_B: &str = "B4 wrong base (REX.B toggled)";
/// B5: REX.W cleared — the 64-bit sign-extending production becomes a 32-bit move.
pub const B5_REX_W_CLEARED: &str = "B5 REX.W cleared (MOVSXD r64,m32 becomes MOVSXD r32,r/m32)";
/// B6: the MOVSXD opcode replaced by the MOV opcode `MovRMSib` emits.
pub const B6_MOV_FOR_MOVSXD: &str = "B6 opcode 63 (MOVSXD) replaced by 8B (MOV r64,m64)";
/// B7: the SIB scale field rotated.
pub const B7_WRONG_SIB_SCALE: &str = "B7 SIB scale field rotated (wrong scale factor)";
/// B8: the SIB index field rewritten.
pub const B8_WRONG_SIB_INDEX: &str = "B8 SIB index field rewritten";
/// B9: the SIB base field rewritten.
pub const B9_WRONG_SIB_BASE: &str = "B9 SIB base field rewritten";
/// B10: ModR/M.rm moved off 100, so no SIB byte is read.
pub const B10_RM_OFF_SIB: &str = "B10 ModR/M.rm moved off 100 (the SIB byte stops being read)";
/// B11: the whole memory operand replaced by a register-direct one.
pub const B11_REGISTER_DIRECT: &str = "B11 register-direct ModR/M (mod=11), SIB and disp removed";
/// B12: a disp8 incremented.
pub const B12_DISP8_OFF_BY_ONE: &str = "B12 disp8 incremented by 1";
/// B13: a disp32 byte corrupted.
pub const B13_DISP32_BYTE_FLIP: &str = "B13 one disp32 byte ^ 0x80";
/// B14: a non-zero disp8 dropped by rewriting mod to 00.
pub const B14_DISP8_DROPPED: &str = "B14 non-zero disp8 dropped (mod 01 -> 00)";
/// B15: one byte appended.
pub const B15_APPENDED_BYTE: &str = "B15 one byte appended";
/// B16: the last byte dropped.
pub const B16_DROPPED_LAST_BYTE: &str = "B16 last byte dropped";
/// B17: a second REX prefix.
pub const B17_DOUBLED_REX: &str = "B17 a second REX prefix";
/// B18: a 66h operand-size override added.
pub const B18_66_PREFIX: &str = "B18 66h operand-size override added (REX.W still wins)";
/// B19: a segment-override prefix added.
pub const B19_SEGMENT_PREFIX: &str = "B19 64h/65h segment-override prefix added";
/// B20: a LOCK prefix added.
pub const B20_LOCK_PREFIX: &str = "B20 F0h LOCK prefix added";
/// B21: a 67h address-size override added.
pub const B21_ADDRESS_SIZE_PREFIX: &str = "B21 67h address-size override added";
/// B22: the REX prefix moved behind the 66h it must precede the opcode from.
pub const B22_PREFIX_AFTER_REX: &str = "B22 a legacy prefix placed AFTER the REX prefix";
/// S1: the same bytes claimed to carry a doubled entry size.
pub const S1_ENTRY_SIZE_DOUBLED: &str = "S1 intent entry size doubled";
/// S2: the same bytes claimed to carry a shifted displacement.
pub const S2_DISP_PLUS_ONE: &str = "S2 intent displacement + 1";
/// S3: the same bytes claimed to swap base and index.
pub const S3_BASE_INDEX_SWAPPED: &str = "S3 intent base and index swapped";
/// S4: the same bytes claimed to write a sibling destination.
pub const S4_SIBLING_DST: &str = "S4 intent destination re-claimed as a sibling register";
/// S5: the same bytes claimed a different base.
pub const S5_RECLAIMED_BASE: &str = "S5 intent base re-claimed as a different register";
/// S6: the same bytes claimed a different index.
pub const S6_RECLAIMED_INDEX: &str = "S6 intent index re-claimed as a different register";

/// Every byte/source control label. The hook demands each fires at least once
/// over the corpus, so a facet cannot go quietly unexercised.
pub const REQUIRED_CONTROL_LABELS: &[&str] = &[
    B1_WRONG_DST_MODRM_REG,
    B2_WRONG_DST_REX_R,
    B3_WRONG_INDEX_REX_X,
    B3B_R12_INDEX_LOSES_REX_X,
    B4_WRONG_BASE_REX_B,
    B5_REX_W_CLEARED,
    B6_MOV_FOR_MOVSXD,
    B7_WRONG_SIB_SCALE,
    B8_WRONG_SIB_INDEX,
    B9_WRONG_SIB_BASE,
    B10_RM_OFF_SIB,
    B11_REGISTER_DIRECT,
    B12_DISP8_OFF_BY_ONE,
    B13_DISP32_BYTE_FLIP,
    B14_DISP8_DROPPED,
    B15_APPENDED_BYTE,
    B16_DROPPED_LAST_BYTE,
    B17_DOUBLED_REX,
    B18_66_PREFIX,
    B19_SEGMENT_PREFIX,
    B20_LOCK_PREFIX,
    B21_ADDRESS_SIZE_PREFIX,
    B22_PREFIX_AFTER_REX,
    S1_ENTRY_SIZE_DOUBLED,
    S2_DISP_PLUS_ONE,
    S3_BASE_INDEX_SWAPPED,
    S4_SIBLING_DST,
    S5_RECLAIMED_BASE,
    S6_RECLAIMED_INDEX,
];

/// Where the ModR/M byte sits in a decoded encoding (after the prefixes and the
/// one opcode byte). The corpus carries no legacy prefixes, so this is
/// `rex.is_some() + 1`.
fn modrm_index(decoded: &DecodedScaledLoad) -> usize {
    usize::from(decoded.rex.is_some()) + 1
}

/// The negative-control battery for ONE holding `(intent, bytes)` pair.
///
/// Each control is a small SDM-format mutation of the REAL bytes (machine side
/// moved) or a different claim about the same real bytes (source side moved),
/// paired with the reason class it MUST be refuted for. The expected classes
/// are stated from the SDM and from [`movsxd_sib_check`]'s documented facet
/// ORDER, never computed by running the obligation.
///
/// Returns an empty battery if the pair does not itself hold — a control is only
/// meaningful relative to a holding original — and the hook treats an empty
/// battery as a defect.
pub fn scaled_load_controls(intent: &ScaledSextLoadIntent, bytes: &[u8]) -> Vec<ScaledLoadControl> {
    use ScaledLoadRefutationClass as C;
    let Ok(holds) = movsxd_sib_check(intent, bytes) else {
        return Vec::new();
    };
    let decoded = holds.decoded;
    let AddressForm::Sib {
        base: Some(base_root),
        index: Some(index_root),
        shift,
        disp,
    } = decoded.addr
    else {
        return Vec::new();
    };
    let mi = modrm_index(&decoded);
    let si = mi + 1; // the SIB byte
    let mod_field = decoded.modrm >> 6;
    let rex_index = 0usize; // the corpus carries no legacy prefixes
    let mut out = Vec::new();
    let mut push_machine = |label: &'static str, bytes: Vec<u8>, expect| {
        out.push(ScaledLoadControl {
            label,
            side: ControlSide::Machine,
            intent: *intent,
            bytes,
            expect,
        });
    };

    // -- B1/B2: the destination ------------------------------------------
    {
        let mut m = bytes.to_vec();
        m[mi] ^= 0b0000_1000; // ModR/M.reg bit 0
        push_machine(B1_WRONG_DST_MODRM_REG, m, C::Destination);
    }
    if decoded.rex.is_some() {
        let mut m = bytes.to_vec();
        m[rex_index] ^= 0b0000_0100; // REX.R
        push_machine(B2_WRONG_DST_REX_R, m, C::Destination);
    }

    // -- B3/B3b: the index register --------------------------------------
    if decoded.rex.is_some() {
        let index_low3 = index_root & 0b111;
        let mut m = bytes.to_vec();
        m[rex_index] ^= 0b0000_0010; // REX.X
        if index_low3 == 0b100 {
            // The index was R12 (REX.X=1 rescuing SIB.index=100). Clearing
            // REX.X makes the field the SDM's NO-INDEX sentinel.
            push_machine(B3B_R12_INDEX_LOSES_REX_X, m, C::AddressShape);
        } else {
            push_machine(B3_WRONG_INDEX_REX_X, m, C::IndexRegister);
        }
    }

    // -- B4: the base register -------------------------------------------
    // Skipped when flipping REX.B would land on the SDM no-base form; the
    // corpus never encodes `mod = 00` with `SIB.base = 101`, so it never does.
    if decoded.rex.is_some() && !(mod_field == 0b00 && base_root & 0b111 == 0b101) {
        let mut m = bytes.to_vec();
        m[rex_index] ^= 0b0000_0001; // REX.B
        push_machine(B4_WRONG_BASE_REX_B, m, C::BaseRegister);
    }

    // -- B5/B6: the production -------------------------------------------
    if decoded.rex.is_some() {
        let mut m = bytes.to_vec();
        m[rex_index] &= !0b0000_1000; // clear REX.W
        push_machine(B5_REX_W_CLEARED, m, C::Extension);
    }
    {
        let mut m = bytes.to_vec();
        m[mi - 1] = 0x8B; // the opcode byte
        push_machine(B6_MOV_FOR_MOVSXD, m, C::Mnemonic);
    }

    // -- B7/B8/B9: the SIB byte ------------------------------------------
    {
        let mut m = bytes.to_vec();
        let new_shift = (shift + 1) & 0b11;
        m[si] = (new_shift << 6) | (m[si] & 0b0011_1111);
        push_machine(B7_WRONG_SIB_SCALE, m, C::Scale);
    }
    {
        // Rewrite the index field to a value that is NOT the no-index sentinel
        // under this encoding's REX.X, so the control is a wrong REGISTER.
        let rex_x = decoded.rex.is_some_and(|r| (r >> 1) & 1 == 1);
        let current = (bytes[si] >> 3) & 0b111;
        let candidate = (0u8..8)
            .find(|&c| c != current && (rex_x || c != 0b100))
            .expect("a SIB index field value distinct from the original always exists");
        let mut m = bytes.to_vec();
        m[si] = (m[si] & !0b0011_1000) | (candidate << 3);
        push_machine(B8_WRONG_SIB_INDEX, m, C::IndexRegister);
    }
    {
        // Rewrite the base field, avoiding the `mod = 00` no-base form.
        let current = bytes[si] & 0b111;
        let candidate = (0u8..8)
            .find(|&c| c != current && !(mod_field == 0b00 && c == 0b101))
            .expect("a SIB base field value distinct from the original always exists");
        let mut m = bytes.to_vec();
        m[si] = (m[si] & !0b0000_0111) | candidate;
        push_machine(B9_WRONG_SIB_BASE, m, C::BaseRegister);
    }

    // -- B10/B11: the addressing SHAPE -----------------------------------
    {
        // rm = 011 (RBX). No SIB byte is read, so the SIB byte becomes a
        // trailing byte and the encoding stops framing.
        let mut m = bytes.to_vec();
        m[mi] = (m[mi] & !0b0000_0111) | 0b011;
        push_machine(B10_RM_OFF_SIB, m, C::Framing);
    }
    {
        // mod = 11 with the SIB byte and any displacement removed: a
        // register-direct MOVSXD, which frames correctly and is refused for
        // its SHAPE rather than its length.
        let mut m = bytes[..=mi].to_vec();
        m[mi] = 0b1100_0000 | (m[mi] & 0b0011_1111);
        push_machine(B11_REGISTER_DIRECT, m, C::AddressShape);
    }

    // -- B12/B13/B14: the displacement -----------------------------------
    match mod_field {
        0b01 => {
            let di = si + 1;
            let mut m = bytes.to_vec();
            m[di] = m[di].wrapping_add(1);
            push_machine(B12_DISP8_OFF_BY_ONE, m, C::Displacement);
            if disp != 0 && base_root & 0b111 != 0b101 {
                // Dropping the disp8 by rewriting mod to 00 is legal framing
                // for a base whose low 3 bits are not 101, and loses the
                // displacement entirely.
                let mut m = bytes[..di].to_vec();
                m[mi] &= 0b0011_1111;
                push_machine(B14_DISP8_DROPPED, m, C::Displacement);
            }
        }
        0b10 => {
            let di = si + 1;
            let mut m = bytes.to_vec();
            m[di + 3] ^= 0x80; // the disp32's top byte
            push_machine(B13_DISP32_BYTE_FLIP, m, C::Displacement);
        }
        _ => {}
    }

    // -- B15/B16: framing -------------------------------------------------
    {
        let mut m = bytes.to_vec();
        m.push(0x90);
        push_machine(B15_APPENDED_BYTE, m, C::Framing);
    }
    {
        let m = bytes[..bytes.len() - 1].to_vec();
        push_machine(B16_DROPPED_LAST_BYTE, m, C::Framing);
    }

    // -- B17..B22: prefixes ----------------------------------------------
    if decoded.rex.is_some() {
        let mut m = bytes.to_vec();
        m.insert(0, 0x40);
        push_machine(B17_DOUBLED_REX, m, C::Decode);
    }
    for (label, prefix, expect) in [
        (B18_66_PREFIX, 0x66u8, C::NonCanonical),
        (B19_SEGMENT_PREFIX, 0x65, C::NonCanonical),
        (B20_LOCK_PREFIX, 0xF0, C::NonCanonical),
        (B21_ADDRESS_SIZE_PREFIX, 0x67, C::NonCanonical),
    ] {
        let mut m = bytes.to_vec();
        m.insert(0, prefix);
        push_machine(label, m, expect);
    }
    if decoded.rex.is_some() {
        // SDM Vol 2A 2.2.1: the REX must IMMEDIATELY precede the opcode.
        let mut m = bytes.to_vec();
        m.insert(1, 0x66);
        push_machine(B22_PREFIX_AFTER_REX, m, C::Decode);
    }

    // -- S1..S6: the same bytes, a different claim ------------------------
    let mut push_source = |label: &'static str, intent: ScaledSextLoadIntent, expect| {
        out.push(ScaledLoadControl {
            label,
            side: ControlSide::Source,
            intent,
            bytes: bytes.to_vec(),
            expect,
        });
    };
    if intent.entry_bytes < 8 {
        push_source(
            S1_ENTRY_SIZE_DOUBLED,
            ScaledSextLoadIntent {
                entry_bytes: intent.entry_bytes * 2,
                ..*intent
            },
            C::Scale,
        );
    } else {
        push_source(
            S1_ENTRY_SIZE_DOUBLED,
            ScaledSextLoadIntent {
                entry_bytes: 4,
                ..*intent
            },
            C::Scale,
        );
    }
    push_source(
        S2_DISP_PLUS_ONE,
        ScaledSextLoadIntent {
            disp: intent.disp + 1,
            ..*intent
        },
        C::Displacement,
    );
    if intent.base != intent.index {
        push_source(
            S3_BASE_INDEX_SWAPPED,
            ScaledSextLoadIntent {
                base: intent.index,
                index: intent.base,
                ..*intent
            },
            C::BaseRegister,
        );
        push_source(
            S5_RECLAIMED_BASE,
            ScaledSextLoadIntent {
                base: sibling_of(intent.base, &[intent.index]),
                ..*intent
            },
            C::BaseRegister,
        );
        push_source(
            S6_RECLAIMED_INDEX,
            ScaledSextLoadIntent {
                index: sibling_of(intent.index, &[intent.base]),
                ..*intent
            },
            C::IndexRegister,
        );
    }
    push_source(
        S4_SIBLING_DST,
        ScaledSextLoadIntent {
            dst: sibling_of(intent.dst, &[]),
            ..*intent
        },
        C::Destination,
    );
    out
}

/// A 64-bit GPR name different from `name` and from everything in `avoid`.
fn sibling_of(name: &str, avoid: &[&str]) -> &'static str {
    SDM_R64
        .iter()
        .copied()
        .find(|&candidate| candidate != name && !avoid.contains(&candidate))
        .expect("SDM_R64 has sixteen entries; one always differs")
}

/// Run one byte/source control and demand its stated reason class.
///
/// `Ok` only when the control is REFUTED and its refutation class equals the
/// stated one. A control that survives is an `Err` naming it SURVIVED; one that
/// refutes for another reason is an `Err` naming the WRONG REASON; and one
/// claiming [`ScaledLoadRefutationClass::Unevaluable`] is rejected outright,
/// because an evaluation failure is a defect in the obligation, never evidence.
pub fn control_is_refuted_as_stated(c: &ScaledLoadControl) -> Result<(), String> {
    if c.expect == ScaledLoadRefutationClass::Unevaluable {
        return Err(format!(
            "control `{}` claims Unevaluable as its reason class; an evaluation failure is a \
             defect, never a refutation",
            c.label
        ));
    }
    match movsxd_sib_check(&c.intent, &c.bytes) {
        Ok(_) => Err(format!(
            "negative control SURVIVED — `{}`: {} vs bytes {:02x?} was accepted",
            c.label,
            c.intent.label(),
            c.bytes
        )),
        Err(r) if r.class() != c.expect => Err(format!(
            "negative control refuted for the WRONG REASON — `{}`: {} vs bytes {:02x?} must \
             refute as {:?} but refuted as {:?} ({r})",
            c.label,
            c.intent.label(),
            c.bytes,
            c.expect,
            r.class()
        )),
        Err(_) => Ok(()),
    }
}

// ===========================================================================
// (9) Wrong-MODEL controls — straight through the comparison
// ===========================================================================

/// One wrong-model control: a deliberately wrong MACHINE-side denotation, built
/// from the real decode, that [`compare_denotations`] must refute.
///
/// These exist because the facet checks in [`movsxd_sib_check`] run before the
/// comparison, so a byte mutation is (correctly) refuted by a facet. Without
/// these the comparison would never be the thing that refutes anything, and a
/// broken comparison would go unnoticed.
pub struct ScaledLoadModelControl {
    /// The control's label; one of [`REQUIRED_MODEL_CONTROL_LABELS`].
    pub label: &'static str,
    /// What is wrong with the model, in one line.
    pub why: &'static str,
    /// Build the WRONG machine-side value from the real decode. `Err` is a
    /// BATTERY DEFECT — the hook fails rather than counting it.
    pub build: fn(&DecodedScaledLoad, &ScaledSextLoadIntent) -> Result<SmtExpr, String>,
    /// The class [`compare_denotations`] must refute it for.
    pub expect: ScaledLoadRefutationClass,
}

/// W1: a zero-extending machine model where the SDM says sign-extending.
pub const W1_ZERO_EXTENDING: &str = "W1 zero-extending machine model";
/// W2: the raw SIB `scale` field used as the scale FACTOR.
pub const W2_SCALE_IS_RAW_SS: &str = "W2 the raw SIB scale field used as the factor";
/// W3: the BASE shifted instead of the index.
pub const W3_BASE_SHIFTED: &str = "W3 the base shifted instead of the index";
/// W4: a 64-bit access where the SDM says a doubleword.
pub const W4_QWORD_ACCESS: &str = "W4 64-bit access instead of the 32-bit doubleword";
/// W5: the displacement dropped from the effective address.
pub const W5_DISP_DROPPED: &str = "W5 displacement dropped from the effective address";
/// W6: the machine side stated EXACTLY as the source side.
pub const W6_SELF_COMPARISON: &str = "W6 machine side stated exactly as the source side";
/// W7: the index term dropped from the effective address.
pub const W7_INDEX_DROPPED: &str = "W7 index term dropped from the effective address";

/// Every wrong-model label the hook requires to fire.
pub const REQUIRED_MODEL_CONTROL_LABELS: &[&str] = &[
    W1_ZERO_EXTENDING,
    W2_SCALE_IS_RAW_SS,
    W3_BASE_SHIFTED,
    W4_QWORD_ACCESS,
    W5_DISP_DROPPED,
    W6_SELF_COMPARISON,
    W7_INDEX_DROPPED,
];

/// The SIB parts of a decode, or an error naming why the model cannot be built.
fn sib_parts(decoded: &DecodedScaledLoad) -> Result<(u8, u8, u8, i64), String> {
    match decoded.addr {
        AddressForm::Sib {
            base: Some(b),
            index: Some(i),
            shift,
            disp,
        } => Ok((b, i, shift, disp)),
        other => Err(format!(
            "the decode is {other:?}, not a base+index*scale form; this control cannot be built"
        )),
    }
}

fn leaf_or_err(root: u8) -> Result<SmtExpr, String> {
    reg_leaf(root).ok_or_else(|| format!("register number {root} is out of range"))
}

/// Every wrong-model control. `scaled_load_model_controls_for` selects the ones
/// that DISCRIMINATE on a given encoding.
pub fn scaled_load_model_controls() -> Vec<ScaledLoadModelControl> {
    use ScaledLoadRefutationClass as C;
    vec![
        ScaledLoadModelControl {
            label: W1_ZERO_EXTENDING,
            why: "MOVSXD with REX.W sign-extends the doubleword; zero-extension differs whenever \
                  bit 31 of the entry is set",
            build: |d, _| {
                let ea = d
                    .machine_effective_address()
                    .ok_or_else(|| "no modelled effective address".to_string())?;
                Ok(SmtExpr::mem_load(ea, 32, false, 32).zero_ext(32))
            },
            expect: C::Value,
        },
        ScaledLoadModelControl {
            label: W2_SCALE_IS_RAW_SS,
            why: "the SIB scale field is a SHIFT amount, not the factor; reading it as the factor \
                  scales by 0, 1, 2 or 3",
            build: |d, _| {
                let (base, index, shift, disp) = sib_parts(d)?;
                let ea = leaf_or_err(base)?
                    .bvadd(
                        leaf_or_err(index)?.bvmul(SmtExpr::bv_const(u64::from(shift), ADDR_BITS)),
                    )
                    .bvadd(SmtExpr::bv_const(disp as u64, ADDR_BITS));
                Ok(SmtExpr::mem_load(ea, 32, false, 32).sign_ext(32))
            },
            expect: C::Value,
        },
        ScaledLoadModelControl {
            label: W3_BASE_SHIFTED,
            why: "the SIB scale applies to the INDEX; shifting the base instead reads a different \
                  address whenever base != index",
            build: |d, _| {
                let (base, index, shift, disp) = sib_parts(d)?;
                let ea = leaf_or_err(index)?
                    .bvadd(leaf_or_err(base)?.bvshl(SmtExpr::bv_const(u64::from(shift), ADDR_BITS)))
                    .bvadd(SmtExpr::bv_const(disp as u64, ADDR_BITS));
                Ok(SmtExpr::mem_load(ea, 32, false, 32).sign_ext(32))
            },
            expect: C::Value,
        },
        ScaledLoadModelControl {
            label: W4_QWORD_ACCESS,
            why: "MOVSXD reads a DOUBLEWORD; a quadword read takes bits the entry does not have",
            build: |d, _| {
                let ea = d
                    .machine_effective_address()
                    .ok_or_else(|| "no modelled effective address".to_string())?;
                Ok(SmtExpr::mem_load(ea, 64, false, 64))
            },
            expect: C::Value,
        },
        ScaledLoadModelControl {
            label: W5_DISP_DROPPED,
            why: "the displacement is part of the effective address; dropping it reads a \
                  different entry whenever it is non-zero",
            build: |d, _| {
                let (base, index, shift, _) = sib_parts(d)?;
                let ea = leaf_or_err(base)?.bvadd(
                    leaf_or_err(index)?.bvshl(SmtExpr::bv_const(u64::from(shift), ADDR_BITS)),
                );
                Ok(SmtExpr::mem_load(ea, 32, false, 32).sign_ext(32))
            },
            expect: C::Value,
        },
        ScaledLoadModelControl {
            label: W6_SELF_COMPARISON,
            why: "a machine side spelled exactly like the source side decides nothing; the \
                  comparison must refuse it rather than credit it",
            build: |_, intent| {
                let write = intent_write(intent).map_err(|e| e.to_string())?;
                Ok(write.value)
            },
            expect: C::Degenerate,
        },
        ScaledLoadModelControl {
            label: W7_INDEX_DROPPED,
            why: "an effective address without the index term reads the table base entry for \
                  every selector",
            build: |d, _| {
                let (base, _, _, disp) = sib_parts(d)?;
                let ea = leaf_or_err(base)?.bvadd(SmtExpr::bv_const(disp as u64, ADDR_BITS));
                Ok(SmtExpr::mem_load(ea, 32, false, 32).sign_ext(32))
            },
            expect: C::Value,
        },
    ]
}

/// The wrong-model controls that DISCRIMINATE on this encoding.
///
/// W3 needs `base != index` AND a scale above 1: with one register in both roles
/// the shifted-base and shifted-index addresses coincide, and at scale 1 the
/// shift is by zero, so `index + base` and `base + index` are the same address.
/// W5 needs a non-zero displacement. A control that cannot discriminate is
/// OMITTED here rather than run and silently absorbed — every label still has to
/// fire somewhere over the corpus, so omitting one everywhere fails the hook.
pub fn scaled_load_model_controls_for(
    intent: &ScaledSextLoadIntent,
) -> Vec<ScaledLoadModelControl> {
    scaled_load_model_controls()
        .into_iter()
        .filter(|c| match c.label {
            W3_BASE_SHIFTED => intent.base != intent.index && intent.entry_bytes > 1,
            W5_DISP_DROPPED => intent.disp != 0,
            _ => true,
        })
        .collect()
}

/// Run one wrong-model control through [`compare_denotations`] and demand its
/// stated reason class.
///
/// A control that cannot be BUILT, or whose original does not hold, is a BATTERY
/// DEFECT and returns `Err`. Nothing here can swallow a control that compared
/// nothing: every path either compares or fails.
pub fn model_control_is_refuted_as_stated(
    control: &ScaledLoadModelControl,
    intent: &ScaledSextLoadIntent,
    bytes: &[u8],
) -> Result<(), String> {
    let holds = movsxd_sib_check(intent, bytes).map_err(|r| {
        format!(
            "wrong-model control `{}` was run against a pair that does not itself hold ({}): {r}",
            control.label,
            intent.label()
        )
    })?;
    let source = intent_write(intent).map_err(|e| {
        format!(
            "wrong-model control `{}`: the source side could not be built: {e}",
            control.label
        )
    })?;
    let wrong = (control.build)(&holds.decoded, intent).map_err(|why| {
        format!(
            "wrong-model control `{}` COULD NOT BE BUILT for {} ({why}); a control that compares \
             nothing is a battery defect, not a refutation",
            control.label,
            intent.label()
        )
    })?;
    match compare_denotations(&source.value, &wrong, source.mask) {
        Ok(_) => Err(format!(
            "wrong-model control SURVIVED — `{}` ({}) on {}: the wrong model agreed with the \
             intent at every witness",
            control.label,
            control.why,
            intent.label()
        )),
        Err(r) if r.class() != control.expect => Err(format!(
            "wrong-model control refuted for the WRONG REASON — `{}` on {} must refute as {:?} \
             but refuted as {:?} ({r})",
            control.label,
            intent.label(),
            control.expect,
            r.class()
        )),
        Err(_) => Ok(()),
    }
}

// ===========================================================================
// (10) Hand-written SDM vectors
// ===========================================================================

/// A hand-assembled SDM vector: `(why, intent, bytes)`.
pub type SdmVector = (&'static str, ScaledSextLoadIntent, &'static [u8]);

/// The intent every hand vector below is stated against: `MOVSXD RAX, dword
/// [RBX + RCX*4]`, the jump-table shape.
const HAND_INTENT: ScaledSextLoadIntent = ScaledSextLoadIntent {
    dst: "rax",
    base: "rbx",
    index: "rcx",
    entry_bytes: 4,
    disp: 0,
};

/// SDM-legal encodings the x86-64 encoder NEVER emits, which must nevertheless
/// HOLD. They are what shows the decoder is a walk of the SDM format rather than
/// an inversion of `encode.rs`'s form ladder: the encoder picks the shortest
/// displacement form, and these are the longer legal spellings of the same
/// instruction.
pub const SDM_HAND_VECTORS_HOLD: &[SdmVector] = &[
    (
        "the same instruction spelled with an explicit zero disp8 (mod=01), which the \
         encoder shortens to mod=00",
        HAND_INTENT,
        &[0x48, 0x63, 0x44, 0x8B, 0x00],
    ),
    (
        "the same instruction spelled with an explicit zero disp32 (mod=10), two bytes \
         longer than anything the encoder emits",
        HAND_INTENT,
        &[0x48, 0x63, 0x84, 0x8B, 0x00, 0x00, 0x00, 0x00],
    ),
    (
        "a disp8-sized displacement spelled as a disp32 (mod=10, +8), which the encoder \
         would have written as a disp8",
        ScaledSextLoadIntent {
            disp: 8,
            ..HAND_INTENT
        },
        &[0x48, 0x63, 0x84, 0x8B, 0x08, 0x00, 0x00, 0x00],
    ),
];

/// Hand-assembled vectors that must REFUTE, each for a DECODER decision the
/// corpus cannot reach because the encoder never produces it. Without these the
/// no-base form, the no-index sentinel, the register-direct form, the
/// RIP-relative form, the non-SIB form and the REX.W-less production would all
/// be unexercised code in the decoder.
pub fn sdm_decoder_controls() -> Vec<ScaledLoadControl> {
    use ScaledLoadRefutationClass as C;
    let v = |label: &'static str, bytes: Vec<u8>, expect| ScaledLoadControl {
        label,
        side: ControlSide::Machine,
        intent: HAND_INTENT,
        bytes,
        expect,
    };
    // Some vectors must be stated against an intent OTHER than the jump-table
    // one, because the point of the vector is that a WRONG decode would HOLD
    // against that other intent. `v` alone cannot express those.
    let w = |label: &'static str, intent: ScaledSextLoadIntent, bytes: Vec<u8>, expect| {
        ScaledLoadControl {
            label,
            side: ControlSide::Machine,
            intent,
            bytes,
            expect,
        }
    };
    /// `MOVSXD RAX, dword [R13 + RCX*4]` — the intent a decoder that let REX.B
    /// "rescue" `SIB.base = 101` with `mod = 00` would wrongly read out of
    /// `49 63 04 8D`.
    const R13_BASE_INTENT: ScaledSextLoadIntent = ScaledSextLoadIntent {
        dst: "rax",
        base: "r13",
        index: "rcx",
        entry_bytes: 4,
        disp: 0,
    };
    vec![
        // mod=00, rm=100, SIB base=101 => NO base register, disp32 follows.
        v(
            D1_NO_BASE_SIB,
            vec![0x48, 0x63, 0x04, 0x8D, 0x00, 0x00, 0x00, 0x00],
            C::AddressShape,
        ),
        // The SAME form with REX.B SET. SDM Vol 2A Table 2-3: `base = 101b`
        // with `mod = 00` means NO base register whatever REX.B says — REX.B
        // extends a base that EXISTS, and here none does. D1 alone cannot
        // decide this: its REX is 0x48, so REX.B is clear and the `!rex_b` a
        // wrong decoder would add is never evaluated. Under such a decoder
        // these bytes become `[r13 + rcx*4 + disp32]`, the disp32 stops being
        // read, and this control refutes as Framing instead of AddressShape.
        v(
            D1B_NO_BASE_SIB_WITH_REX_B,
            vec![0x49, 0x63, 0x04, 0x8D, 0x00, 0x00, 0x00, 0x00],
            C::AddressShape,
        ),
        // The SHARP form of the same rule: four bytes claimed as
        // `[R13 + RCX*4]`. The SDM says a disp32 FOLLOWS, so the string ENDS
        // before a required field and the pair is refuted for FRAMING. A
        // decoder in which REX.B rescued `base = 101` would decode exactly the
        // claimed instruction and this control would SURVIVE — the one vector
        // in this battery that turns the rule into a false CREDIT rather than a
        // misattributed refutation.
        w(
            D1C_REX_B_DOES_NOT_MAKE_A_BASE,
            R13_BASE_INTENT,
            vec![0x49, 0x63, 0x04, 0x8D],
            C::Framing,
        ),
        // SIB index=100 with REX.X=0 => NO index register.
        v(
            D2_NO_INDEX_SENTINEL,
            vec![0x48, 0x63, 0x04, 0xA3],
            C::AddressShape,
        ),
        // mod=11 => register-direct MOVSXD RAX, EBX.
        v(D3_REGISTER_DIRECT, vec![0x48, 0x63, 0xC3], C::AddressShape),
        // mod=00, rm=101 => RIP-relative.
        v(
            D4_RIP_RELATIVE,
            vec![0x48, 0x63, 0x05, 0x00, 0x00, 0x00, 0x00],
            C::AddressShape,
        ),
        // The SAME form with REX.B SET. SDM Vol 2A Table 2-2 note: in 64-bit
        // mode `mod = 00` with `rm = 101` is RIP-relative, and REX.B does not
        // turn it back into a register base — exactly the D1/D1b rule one
        // ModR/M field over. D4's REX is 0x48, so it cannot decide this either.
        v(
            D4B_RIP_RELATIVE_WITH_REX_B,
            vec![0x49, 0x63, 0x05, 0x00, 0x00, 0x00, 0x00],
            C::AddressShape,
        ),
        // ... and the framing half of that rule: a disp32 FOLLOWS the
        // RIP-relative ModR/M byte, so three bytes end before a required field.
        // A decoder in which REX.B rescued `rm = 101` would read `[r13 + 0]`
        // and refute for its SHAPE instead.
        v(
            D4C_RIP_RELATIVE_NEEDS_DISP32,
            vec![0x49, 0x63, 0x05],
            C::Framing,
        ),
        // mod=00, rm=011 => the non-SIB [RBX] form.
        v(D5_NON_SIB_BASE, vec![0x48, 0x63, 0x03], C::AddressShape),
        // 63 /r without REX.W => MOVSXD r32, r/m32 (a 32-bit move).
        v(D6_NO_REX_W, vec![0x63, 0x04, 0x8B], C::Extension),
        // 66 + 63 /r => the 16-bit production.
        v(
            D7_SIXTEEN_BIT,
            vec![0x66, 0x63, 0x04, 0x8B],
            C::NonCanonical,
        ),
        // REX.W + 8B /r => MOV r64, m64 over the same operands.
        v(D8_MOV_QWORD, vec![0x48, 0x8B, 0x04, 0x8B], C::Mnemonic),
    ]
}

/// D1: the SDM no-base SIB form.
pub const D1_NO_BASE_SIB: &str = "D1 SIB no-base form (base=101 with mod=00)";
/// D1b: the same no-base form with REX.B SET — REX.B does not create a base.
pub const D1B_NO_BASE_SIB_WITH_REX_B: &str =
    "D1b SIB no-base form with REX.B SET (base=101, mod=00, REX.B=1 — still no base)";
/// D1c: four bytes claimed as `[R13 + RCX*4]`; the SDM says a disp32 follows.
pub const D1C_REX_B_DOES_NOT_MAKE_A_BASE: &str =
    "D1c 49 63 04 8D claimed as [r13 + rcx*4] (REX.B cannot rescue base=101 with mod=00)";
/// D2: the SDM no-index sentinel.
pub const D2_NO_INDEX_SENTINEL: &str = "D2 SIB no-index sentinel (index=100 with REX.X=0)";
/// D3: register-direct MOVSXD.
pub const D3_REGISTER_DIRECT: &str = "D3 register-direct MOVSXD (mod=11)";
/// D4: RIP-relative MOVSXD.
pub const D4_RIP_RELATIVE: &str = "D4 RIP-relative MOVSXD (mod=00, rm=101)";
/// D4b: RIP-relative with REX.B SET — REX.B does not turn it into a base.
pub const D4B_RIP_RELATIVE_WITH_REX_B: &str =
    "D4b RIP-relative with REX.B SET (mod=00, rm=101, REX.B=1 — still RIP-relative)";
/// D4c: the RIP-relative form truncated before its mandatory disp32.
pub const D4C_RIP_RELATIVE_NEEDS_DISP32: &str =
    "D4c 49 63 05 (RIP-relative truncated before its mandatory disp32)";
/// D5: the non-SIB `[base]` form.
pub const D5_NON_SIB_BASE: &str = "D5 non-SIB [base] form (rm != 100)";
/// D6: MOVSXD without REX.W.
pub const D6_NO_REX_W: &str = "D6 63 /r without REX.W (MOVSXD r32, r/m32)";
/// D7: the 16-bit MOVSXD production.
pub const D7_SIXTEEN_BIT: &str = "D7 66h + 63 /r (MOVSXD r16, r/m16)";
/// D8: MOV r64, m64 over the same operands.
pub const D8_MOV_QWORD: &str = "D8 REX.W + 8B /r (MOV r64, m64)";

/// Every decoder-control label the hook requires to be present and to refute.
pub const REQUIRED_DECODER_CONTROL_LABELS: &[&str] = &[
    D1_NO_BASE_SIB,
    D1B_NO_BASE_SIB_WITH_REX_B,
    D1C_REX_B_DOES_NOT_MAKE_A_BASE,
    D2_NO_INDEX_SENTINEL,
    D3_REGISTER_DIRECT,
    D4_RIP_RELATIVE,
    D4B_RIP_RELATIVE_WITH_REX_B,
    D4C_RIP_RELATIVE_NEEDS_DISP32,
    D5_NON_SIB_BASE,
    D6_NO_REX_W,
    D7_SIXTEEN_BIT,
    D8_MOV_QWORD,
];

// ===========================================================================
// (10a) Destination WRITE-MASK vectors — the SDM Vol 1 §3.4.1.1 rule, decided
// ===========================================================================

/// One destination write-mask vector: real bytes, and the operand width and
/// root write mask SDM Vol 1 §3.4.1.1 says they produce.
///
/// # Why this battery exists
///
/// [`movsxd_sib_check`] refuses anything whose `dst_bits` is not 64 at the
/// Extension facet, BEFORE the Destination facet ever calls
/// [`DecodedScaledLoad::dst_write_mask`]. So for the credited family the 32-,
/// 16- and 8-bit arms of that rule are unreachable, and a mutation of them left
/// every gate green — the SDM rule the doc comment cited was refutable by
/// nothing. These vectors decode REAL byte strings for every production this
/// decoder's language contains and pin BOTH the width and the mask against the
/// rule stated independently of the decoder's own operand-size table.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DestWriteMaskVector {
    /// The vector's label; one of [`REQUIRED_WRITE_MASK_VECTOR_LABELS`].
    pub label: &'static str,
    /// The SDM rule this vector decides, in one line.
    pub why: &'static str,
    /// The byte string, a legal encoding of the named production.
    pub bytes: &'static [u8],
    /// The architectural destination operand width the SDM gives this
    /// production — transcribed from Vol 2B, not read off the decoder.
    pub expect_dst_bits: u32,
    /// The bits of the 64-bit ROOT this production writes, per Vol 1 §3.4.1.1.
    pub expect_mask: u64,
}

/// X1: `REX.W + 63 /r` — MOVSXD r64, r/m32.
pub const X1_MOVSXD_R64: &str = "X1 REX.W + 63 /r (MOVSXD r64,r/m32) writes all 64 bits";
/// X2: `63 /r` — MOVSXD r32, r/m32. The arm the surviving mutation hit.
pub const X2_MOVSXD_R32: &str =
    "X2 63 /r (MOVSXD r32,r/m32) writes a 32-bit result ZERO-EXTENDED to 64, so all 64 bits";
/// X3: `66 + 63 /r` — MOVSXD r16, r/m16.
pub const X3_MOVSXD_R16: &str =
    "X3 66h + 63 /r (MOVSXD r16,r/m16) leaves the upper 48 bits UNMODIFIED";
/// X4: `REX.W + 8B /r` — MOV r64, m64.
pub const X4_MOV_R64: &str = "X4 REX.W + 8B /r (MOV r64,m64) writes all 64 bits";
/// X5: `8B /r` — MOV r32, m32.
pub const X5_MOV_R32: &str =
    "X5 8B /r (MOV r32,m32) writes a 32-bit result ZERO-EXTENDED to 64, so all 64 bits";
/// X6: `66 + 8B /r` — MOV r16, m16.
pub const X6_MOV_R16: &str = "X6 66h + 8B /r (MOV r16,m16) leaves the upper 48 bits UNMODIFIED";

/// Every write-mask vector the hook requires to be present and to hold.
pub const REQUIRED_WRITE_MASK_VECTOR_LABELS: &[&str] = &[
    X1_MOVSXD_R64,
    X2_MOVSXD_R32,
    X3_MOVSXD_R16,
    X4_MOV_R64,
    X5_MOV_R32,
    X6_MOV_R16,
];

/// The write-mask vectors. Every byte string addresses `[RBX + RCX*4]`
/// (ModR/M `04`, SIB `8B`) so the ONLY thing that varies is the prefix/opcode
/// pair that selects the operand width.
pub const DEST_WRITE_MASK_VECTORS: &[DestWriteMaskVector] = &[
    DestWriteMaskVector {
        label: X1_MOVSXD_R64,
        why: "SDM Vol 2B MOVSXD `REX.W + 63 /r` is MOVSXD r64,r/m32; Vol 1 3.4.1.1: a 64-bit \
              operand gives a 64-bit result",
        bytes: &[0x48, 0x63, 0x04, 0x8B],
        expect_dst_bits: 64,
        expect_mask: u64::MAX,
    },
    DestWriteMaskVector {
        label: X2_MOVSXD_R32,
        why: "SDM Vol 2B MOVSXD `63 /r` is MOVSXD r32,r/m32; Vol 1 3.4.1.1: a 32-bit operand \
              gives a 32-bit result ZERO-EXTENDED to 64 bits, so the whole root changes",
        bytes: &[0x63, 0x04, 0x8B],
        expect_dst_bits: 32,
        expect_mask: u64::MAX,
    },
    DestWriteMaskVector {
        label: X3_MOVSXD_R16,
        why: "SDM Vol 2B MOVSXD `63 /r` with the 66h operand-size override is MOVSXD r16,r/m16; \
              Vol 1 3.4.1.1: a 16-bit operand leaves the upper 48 bits UNMODIFIED",
        bytes: &[0x66, 0x63, 0x04, 0x8B],
        expect_dst_bits: 16,
        expect_mask: 0xFFFF,
    },
    DestWriteMaskVector {
        label: X4_MOV_R64,
        why: "SDM Vol 2B MOV `8B /r` with REX.W is MOV r64,r/m64; Vol 1 3.4.1.1: a 64-bit \
              operand gives a 64-bit result",
        bytes: &[0x48, 0x8B, 0x04, 0x8B],
        expect_dst_bits: 64,
        expect_mask: u64::MAX,
    },
    DestWriteMaskVector {
        label: X5_MOV_R32,
        why: "SDM Vol 2B MOV `8B /r` is MOV r32,r/m32; Vol 1 3.4.1.1: the 32-bit result is \
              ZERO-EXTENDED to 64 bits, so the whole root changes",
        bytes: &[0x8B, 0x04, 0x8B],
        expect_dst_bits: 32,
        expect_mask: u64::MAX,
    },
    DestWriteMaskVector {
        label: X6_MOV_R16,
        why: "SDM Vol 2B MOV `8B /r` with the 66h operand-size override is MOV r16,r/m16; \
              Vol 1 3.4.1.1: a 16-bit operand leaves the upper 48 bits UNMODIFIED",
        bytes: &[0x66, 0x8B, 0x04, 0x8B],
        expect_dst_bits: 16,
        expect_mask: 0xFFFF,
    },
];

/// Decode one write-mask vector and demand the width and mask it states.
///
/// A vector that does not DECODE is a battery DEFECT — it compared nothing —
/// and is an `Err`, never a silent pass.
pub fn write_mask_vector_is_as_stated(v: &DestWriteMaskVector) -> Result<(), String> {
    let decoded = sdm_decode_scaled_load(v.bytes).map_err(|e| {
        format!(
            "write-mask vector `{}` DID NOT DECODE ({:02x?}): {e}; a vector that compares nothing \
             is a battery defect, not evidence",
            v.label, v.bytes
        )
    })?;
    if decoded.dst_bits != v.expect_dst_bits {
        return Err(format!(
            "write-mask vector `{}` ({}): {:02x?} decodes to a {}-bit destination operand; the \
             SDM says {}",
            v.label, v.why, v.bytes, decoded.dst_bits, v.expect_dst_bits
        ));
    }
    let mask = decoded.dst_write_mask();
    if mask != v.expect_mask {
        return Err(format!(
            "write-mask vector `{}` ({}): {:02x?} is modelled as writing {mask:#018x} of the \
             64-bit root; SDM Vol 1 3.4.1.1 says {:#018x}",
            v.label, v.why, v.bytes, v.expect_mask
        ));
    }
    Ok(())
}

// ===========================================================================
// (10b) The VACUITY control — the anti-vacuity guard, decided
// ===========================================================================

/// V1: a witness family whose loaded doubleword is NEGATIVE at every row.
pub const V1_ALL_NEGATIVE: &str = "V1 every witness row loads a NEGATIVE doubleword";
/// V2: a witness family whose loaded doubleword is NON-NEGATIVE at every row.
pub const V2_ALL_NON_NEGATIVE: &str = "V2 every witness row loads a NON-NEGATIVE doubleword";

/// Every vacuity-control label the hook requires to fire.
pub const REQUIRED_VACUITY_CONTROL_LABELS: &[&str] = &[V1_ALL_NEGATIVE, V2_ALL_NON_NEGATIVE];

/// A source/machine pair over a CONSTANT effective address: the loaded
/// doubleword is then the same at every witness row, so the family exercises
/// exactly ONE sign case.
///
/// The two spellings are the obligation's own — a signed load against an
/// explicit sign-extend of a zero-filling load — so the pair is structurally
/// distinct (the [`ScaledLoadRefutationClass::Degenerate`] guard does not fire)
/// and denotes the same value (the AGREEMENT check does not fire). The ONLY
/// thing that can refuse it is the anti-vacuity guard.
fn constant_address_pair(addr: u64) -> (SmtExpr, SmtExpr) {
    let ea = SmtExpr::bv_const(addr, ADDR_BITS);
    let source = SmtExpr::mem_load(ea.clone(), 32, true, 64);
    let machine = SmtExpr::mem_load(ea, 32, false, 32).sign_ext(32);
    (source, machine)
}

/// THE ANTI-VACUITY GUARD, DECIDED. Feed [`compare_denotations`] one witness
/// family that is all-negative and one that is all-non-negative, and require
/// [`ScaledLoadRefutationClass::VacuousWitnesses`] with the exact counts for
/// each. Returns how many vacuity controls RAN.
///
/// # Why this is a control and not a comment
///
/// Nothing in the corpus, the byte battery or the wrong-model battery ever
/// hands `compare_denotations` a family lacking a sign case, so DELETING the
/// guard left all eighteen gate cases green. The guard is what protects the
/// sign-extension facet from a future narrowing of [`WITNESS_ROW_BASE`]: with
/// it gone, a family of only non-negative entries would let the W1
/// zero-extending machine model AGREE everywhere and the extension facet would
/// be decided by nothing. These two controls give it teeth. Both directions are
/// demanded, and the COUNTS are demanded, so a guard weakened to fire only on
/// one side is caught too.
pub fn vacuity_controls_are_refused() -> Result<usize, String> {
    // A deterministic search for one constant address whose doubleword has bit
    // 31 SET and one where it is CLEAR. Which addresses those are is a fact
    // about `SmtExpr::MemLoad`'s address mixer, so it is MEASURED, not assumed;
    // failing to find either is a battery defect.
    let mut negative_addr: Option<u64> = None;
    let mut non_negative_addr: Option<u64> = None;
    for addr in 0u64..4096 {
        let (source, _) = constant_address_pair(addr);
        let value = source
            .try_eval(witness_env(0))
            .map_err(|e| format!("vacuity control: a constant-address load did not evaluate: {e}"))?
            .as_u64();
        if value & 0x8000_0000_0000_0000 != 0 {
            negative_addr.get_or_insert(addr);
        } else {
            non_negative_addr.get_or_insert(addr);
        }
        if negative_addr.is_some() && non_negative_addr.is_some() {
            break;
        }
    }
    let negative_addr = negative_addr.ok_or_else(|| {
        "vacuity control `V1` COULD NOT BE BUILT: no address in the search range loaded a \
         NEGATIVE doubleword"
            .to_string()
    })?;
    let non_negative_addr = non_negative_addr.ok_or_else(|| {
        "vacuity control `V2` COULD NOT BE BUILT: no address in the search range loaded a \
         NON-NEGATIVE doubleword"
            .to_string()
    })?;

    let mut ran = 0usize;
    for (label, addr, expect_negative) in [
        (V1_ALL_NEGATIVE, negative_addr, WITNESS_ROWS),
        (V2_ALL_NON_NEGATIVE, non_negative_addr, 0usize),
    ] {
        let (source, machine) = constant_address_pair(addr);
        if source == machine {
            return Err(format!(
                "vacuity control `{label}` is DEGENERATE by construction; it would be refused for \
                 the wrong reason and would decide nothing about the anti-vacuity guard"
            ));
        }
        match compare_denotations(&source, &machine, u64::MAX) {
            Ok(outcome) => {
                return Err(format!(
                    "VACUITY CONTROL SURVIVED — `{label}` (address {addr:#x}): a witness family \
                     that exercises only ONE sign case was ACCEPTED ({outcome:?}). With that \
                     guard gone, a zero-extending machine model would agree everywhere and the \
                     SIGN-EXTENSION facet would be decided by nothing"
                ));
            }
            Err(ScaledLoadRefutation::VacuousWitnesses {
                negative_rows,
                non_negative_rows,
            }) => {
                if negative_rows != expect_negative
                    || non_negative_rows != WITNESS_ROWS - expect_negative
                {
                    return Err(format!(
                        "vacuity control `{label}` (address {addr:#x}) refuted with \
                         {negative_rows} negative / {non_negative_rows} non-negative rows; the \
                         family was built to give {expect_negative} / {}",
                        WITNESS_ROWS - expect_negative
                    ));
                }
            }
            Err(r) => {
                return Err(format!(
                    "vacuity control `{label}` (address {addr:#x}) refuted as {:?}, not \
                     VacuousWitnesses ({r}); it decides nothing about the anti-vacuity guard",
                    r.class()
                ));
            }
        }
        ran += 1;
    }
    Ok(ran)
}

// ===========================================================================
// (11) The coverage-gate credit hook
// ===========================================================================

/// What the credit hook established, for the gate row's note.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MovsxdSibCredit {
    /// Captured real encodings that hold.
    pub entries: usize,
    /// Distinct encoding facets those encodings cover (all required ones).
    pub facets_seen: usize,
    /// Byte/source controls run — every one refuted for its stated class.
    pub controls_refuted: usize,
    /// Wrong-model controls run through the comparison itself.
    pub model_controls_refuted: usize,
    /// Hand-written SDM decoder controls run.
    pub decoder_controls_refuted: usize,
    /// Hand-written SDM vectors the encoder never emits, all holding.
    pub hand_vectors_held: usize,
    /// Destination WRITE-MASK vectors checked — the SDM Vol 1 §3.4.1.1 rule
    /// decided over every production this decoder's language contains, not only
    /// the 64-bit one the credited family reaches.
    pub write_mask_vectors_checked: usize,
    /// VACUITY controls refuted — the anti-vacuity guard decided in both
    /// directions rather than left as an untested safety net.
    pub vacuity_controls_refuted: usize,
    /// Witness comparisons performed across the corpus.
    pub witness_comparisons: usize,
}

/// THE COVERAGE-GATE CREDIT HOOK for `x86_64::MovsxdRMSib`.
///
/// `Ok` iff ALL of:
///
/// 1. [`EMITTED_X86_MOVSXD_SIB`] is non-empty and EVERY captured encoding holds
///    (an empty set is not a discharged set);
/// 2. FACET COVERAGE, computed from the DECODED encodings: every entry of
///    [`REQUIRED_ENCODING_FACETS`] — all four scale factors, every displacement
///    mode including the base-forced zero disp8, all three REX bits, the R12
///    index that collides with the no-index sentinel, an RSP-low-3 base, and the
///    base-equals-index aliasing;
/// 3. THE TEETH: every control [`scaled_load_controls`] builds over every corpus
///    entry refutes FOR ITS STATED REASON CLASS and every label in
///    [`REQUIRED_CONTROL_LABELS`] fires at least once; every applicable
///    wrong-model control refutes THROUGH [`compare_denotations`] for its stated
///    class, with every label in [`REQUIRED_MODEL_CONTROL_LABELS`] firing and an
///    unbuildable one counted as a battery DEFECT rather than a refutation;
///    every [`sdm_decoder_controls`] entry refutes for its stated class; and
///    every [`SDM_HAND_VECTORS_HOLD`] vector HOLDS;
/// 4. THE RULES THE CREDITED FAMILY DOES NOT REACH are decided anyway: every
///    [`DEST_WRITE_MASK_VECTORS`] entry decodes and reports the operand width
///    and root write mask SDM Vol 1 §3.4.1.1 gives it, for all six productions
///    and not only the 64-bit one the Extension facet lets through; and
///    [`vacuity_controls_are_refused`] gives the anti-vacuity guard teeth in
///    both directions.
///
/// What the hook cannot check is that the corpus is still what the live encoder
/// emits. This crate cannot run the encoder. `x86_movsxd_sib_gate` and
/// `coverage_gate_tests` re-derive the corpus from the live encoder, and both
/// run in the local meta-gate.
///
/// # What crediting the row does NOT say
///
/// Read the credited row as exactly this and nothing more: **for
/// `MOVSXD r64, [base + index*scale + disp]`, the bytes the x86-64 encoder
/// emitted denote, under an independent SDM-derived decode, the same 64-bit
/// destination write — a 32-bit signed load at `base + index*entry_size + disp`
/// — that the machine-IR instruction means**, with the address facet settled for
/// every address and the value facet over the witness family. Everything it does
/// not say is carried as data in [`X86_MOVSXD_SIB_DEFERRALS`], starting with the
/// fact that NOTHING EMITS THIS OPCODE.
pub fn movsxd_sib_discharges_valid() -> Result<MovsxdSibCredit, String> {
    movsxd_sib_credit_over(EMITTED_X86_MOVSXD_SIB)
}

/// The control battery builder the hook runs per corpus entry.
pub type ControlBattery<'a> = &'a dyn Fn(&ScaledSextLoadIntent, &[u8]) -> Vec<ScaledLoadControl>;

/// [`movsxd_sib_discharges_valid`] over an explicit corpus. The gate hook always
/// passes [`EMITTED_X86_MOVSXD_SIB`]; this entry point exists so the gate test
/// can show the hook FAILS CLOSED on an empty corpus, a narrow corpus and a
/// corpus carrying one wrong encoding.
pub fn movsxd_sib_credit_over(corpus: &[EmittedScaledLoad]) -> Result<MovsxdSibCredit, String> {
    movsxd_sib_credit_over_with(
        corpus,
        &scaled_load_controls,
        &sdm_decoder_controls(),
        SDM_HAND_VECTORS_HOLD,
    )
}

/// The credit hook with every ingredient explicit. The gate never calls this
/// directly. It is public so the gate test can hand the hook a battery with a
/// SURVIVING control, a control that refutes for the WRONG REASON, a battery
/// missing a required label, a decoder control that holds, or a hold vector that
/// refutes — and require a refusal for each. Without that seam, a hook whose
/// control check had been forced to `Ok` would still discharge on today's
/// all-refuting controls and no test would notice.
pub fn movsxd_sib_credit_over_with(
    corpus: &[EmittedScaledLoad],
    battery_for: ControlBattery<'_>,
    decoder_controls: &[ScaledLoadControl],
    hand_hold: &[SdmVector],
) -> Result<MovsxdSibCredit, String> {
    if corpus.is_empty() {
        return Err(
            "the captured MOVSXD-SIB corpus is empty — an empty set is not a discharged set"
                .to_string(),
        );
    }
    let mut facets = std::collections::BTreeSet::new();
    let mut labels = std::collections::BTreeSet::new();
    let mut model_labels = std::collections::BTreeSet::new();
    let mut controls_refuted = 0usize;
    let mut model_controls_refuted = 0usize;
    let mut witness_comparisons = 0usize;

    for entry in corpus {
        let intent = entry.intent();
        let holds = movsxd_sib_check(&intent, entry.bytes).map_err(|r| {
            format!(
                "captured encoding REFUTED — {} = {:02x?}: {r}",
                intent.label(),
                entry.bytes
            )
        })?;
        witness_comparisons += holds.witnesses.rows;
        for facet in facets_of(&holds.decoded, &intent) {
            facets.insert(facet);
        }
        let battery = battery_for(&intent, entry.bytes);
        if battery.is_empty() {
            return Err(format!("{}: produced no negative controls", intent.label()));
        }
        for c in &battery {
            control_is_refuted_as_stated(c)?;
            labels.insert(c.label);
            controls_refuted += 1;
        }
        for m in scaled_load_model_controls_for(&intent) {
            model_control_is_refuted_as_stated(&m, &intent, entry.bytes)?;
            model_labels.insert(m.label);
            model_controls_refuted += 1;
        }
    }

    for required in REQUIRED_ENCODING_FACETS {
        if !facets.contains(required) {
            return Err(format!(
                "facet coverage: the corpus exhibits no {required:?} encoding — a narrow corpus \
                 cannot credit the row"
            ));
        }
    }
    for &required in REQUIRED_CONTROL_LABELS {
        if !labels.contains(required) {
            return Err(format!(
                "negative control `{required}` never fired over the corpus — that facet is \
                 unexercised"
            ));
        }
    }
    for &required in REQUIRED_MODEL_CONTROL_LABELS {
        if !model_labels.contains(required) {
            return Err(format!(
                "wrong-model control `{required}` never fired over the corpus — the comparison \
                 itself would be unexercised on that facet"
            ));
        }
    }

    if decoder_controls.is_empty() {
        return Err(
            "no decoder controls were supplied — the no-base, no-index, register-direct, \
             RIP-relative, non-SIB and REX.W-less decoder decisions would be unexercised"
                .to_string(),
        );
    }
    for &required in REQUIRED_DECODER_CONTROL_LABELS {
        if !decoder_controls.iter().any(|c| c.label == required) {
            return Err(format!(
                "decoder control `{required}` is absent — that decoder decision is unexercised"
            ));
        }
    }
    let mut decoder_controls_refuted = 0usize;
    for c in decoder_controls {
        control_is_refuted_as_stated(c)?;
        decoder_controls_refuted += 1;
    }

    if hand_hold.is_empty() {
        return Err("no SDM hand vectors that must HOLD were supplied".to_string());
    }
    for &(why, intent, bytes) in hand_hold {
        if let Err(r) = movsxd_sib_check(&intent, bytes) {
            return Err(format!(
                "SDM hand vector `{why}` ({} = {bytes:02x?}) must HOLD but was refuted: {r}",
                intent.label()
            ));
        }
    }

    // The SDM Vol 1 3.4.1.1 destination width rule, over every production this
    // decoder's language contains. The credited family only ever reaches the
    // 64-bit arm, so without this the rest of that rule would be prose.
    for &required in REQUIRED_WRITE_MASK_VECTOR_LABELS {
        if !DEST_WRITE_MASK_VECTORS.iter().any(|v| v.label == required) {
            return Err(format!(
                "write-mask vector `{required}` is absent — that arm of the SDM Vol 1 3.4.1.1 \
                 destination width rule would be decided by nothing"
            ));
        }
    }
    let mut write_mask_vectors_checked = 0usize;
    for v in DEST_WRITE_MASK_VECTORS {
        write_mask_vector_is_as_stated(v)?;
        write_mask_vectors_checked += 1;
    }

    // The anti-vacuity guard, decided in both directions.
    let vacuity_controls_refuted = vacuity_controls_are_refused()?;
    if vacuity_controls_refuted != REQUIRED_VACUITY_CONTROL_LABELS.len() {
        return Err(format!(
            "only {vacuity_controls_refuted} of {} vacuity controls ran; the anti-vacuity guard \
             is not fully decided",
            REQUIRED_VACUITY_CONTROL_LABELS.len()
        ));
    }

    Ok(MovsxdSibCredit {
        entries: corpus.len(),
        facets_seen: facets.len(),
        controls_refuted,
        model_controls_refuted,
        decoder_controls_refuted,
        hand_vectors_held: hand_hold.len(),
        write_mask_vectors_checked,
        vacuity_controls_refuted,
        witness_comparisons,
    })
}

// ===========================================================================
// (12) Named deferrals — what the credit does NOT claim, as data
// ===========================================================================

/// One thing the scaled-sign-extending-load credit does NOT establish.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct X86MovsxdSibDeferral {
    /// Short identifier, cited in the gate row and in the tests.
    pub id: &'static str,
    /// What is not established.
    pub what: &'static str,
}

/// The non-claims, as data so a test can pin them rather than trusting prose.
pub const X86_MOVSXD_SIB_DEFERRALS: &[X86MovsxdSibDeferral] = &[
    X86MovsxdSibDeferral {
        id: "not-emitted",
        what: "NOT that any path emits this opcode. Nothing does: the active jump-table path \
               uses 8-byte deltas through MovRMSib, and x86_64::decode_check allowlists \
               MovsxdRMSib under JUMP_TABLE, so there is no per-compile check to claim either. \
               The credit is over bytes the ENCODER produces for real operand tuples. No runtime \
               or performance claim follows from it.",
    },
    X86MovsxdSibDeferral {
        id: "not-selection",
        what: "NOT that instruction selection would pick the right base, index, entry size or \
               displacement. A wrong table, a wrong selector or a wrong entry size encodes and \
               decodes perfectly.",
    },
    X86MovsxdSibDeferral {
        id: "not-memory-model",
        what: "NOT a memory-content theorem. SmtExpr::MemLoad models memory as a deterministic \
               function of the address — which is exactly what makes a wrong address refutable — \
               and is NOT a model of aliasing, of faulting, of #GP on a non-canonical address, or \
               of what the table holds.",
    },
    X86MovsxdSibDeferral {
        id: "not-table-entry",
        what: "NOT the table ENTRY. That the loaded i32 is `target - table_base` belongs to the \
               #62 dense-mapping gate and the differential fuzz.",
    },
    X86MovsxdSibDeferral {
        id: "value-over-witnesses",
        what: "The ADDRESS facet is exact for every 64-bit base and index (the scale lemma in the \
               module header); the VALUE facet is decided over the witness family, which is \
               required to exercise both sign cases. The gate target additionally runs the full \
               sampling sweep and an exhaustive sweep over a contiguous 2^16 address window. It \
               is not a for-all theorem over every address.",
    },
    X86MovsxdSibDeferral {
        id: "not-isa-authority",
        what: "NOT that the ISA rules are right. They are TRANSCRIBED from the SDM and are this \
               family's trust base. The objdump differential over the same bytes is adjacent \
               evidence, not part of this obligation, and no silicon differential is.",
    },
    X86MovsxdSibDeferral {
        id: "not-flags-or-placement",
        what: "NOTHING about flags (the SDM's `Flags Affected: None` is trust base, not compared \
               here), about instruction placement, reachability or dataflow.",
    },
    X86MovsxdSibDeferral {
        id: "not-a-decoder",
        what: "NOT a general x86 decoder, and NOTHING about any other x86-64 RED row.",
    },
];

// ===========================================================================
// (13) The captured corpus of REAL emitted encodings
// ===========================================================================

/// One captured encoding: the intent, and the bytes the REAL x86-64 encoder
/// emitted for it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EmittedScaledLoad {
    /// Destination register name.
    pub dst: &'static str,
    /// Base register name.
    pub base: &'static str,
    /// Index register name.
    pub index: &'static str,
    /// SIB scale factor / table entry size in bytes.
    pub scale: u32,
    /// Displacement.
    pub disp: i64,
    /// The bytes the real encoder emitted.
    pub bytes: &'static [u8],
}

impl EmittedScaledLoad {
    /// The machine-IR intent this entry was encoded from.
    pub fn intent(&self) -> ScaledSextLoadIntent {
        ScaledSextLoadIntent {
            dst: self.dst,
            base: self.base,
            index: self.index,
            entry_bytes: self.scale,
            disp: self.disp,
        }
    }
}

/// Build one corpus row.
const fn e(
    dst: &'static str,
    base: &'static str,
    index: &'static str,
    scale: u32,
    disp: i64,
    bytes: &'static [u8],
) -> EmittedScaledLoad {
    EmittedScaledLoad {
        dst,
        base,
        index,
        scale,
        disp,
        bytes,
    }
}

/// The bytes the real x86-64 encoder
/// (`trust_cg_codegen::x86_64::X86Encoder::encode_instruction`) emitted for each
/// `MovsxdRMSib` intent, captured by running it — never typed in by hand.
///
/// # Why a captured corpus exists at all
///
/// The coverage gate's credit hook runs inside this crate, and this crate cannot
/// depend on `trust-cg-codegen` (that crate depends on this one). So the gate
/// cannot run the encoder to get live bytes. It runs over these instead.
///
/// # Why the capture is not a trust-me
///
/// `tests/x86_movsxd_sib_gate.rs::corpus_is_what_the_live_encoder_emits_today`
/// re-encodes EVERY entry through the live encoder and asserts byte identity,
/// and the same re-derivation runs inside `coverage_gate_tests` — the target
/// that PINS the x86-64 ratio — so an encoder change that alters these bytes
/// turns the meta-gate RED rather than leaving a green row standing on a stale
/// capture. The gate target additionally sweeps the WHOLE destination x base x
/// index x scale x displacement product through the live encoder and the
/// obligation, so the credit's independence does not rest on this table being
/// wide.
///
/// # What the selection covers
///
/// Group A (no REX bits beyond W): every scale factor against every displacement
/// mode. Group B: all three of REX.R / REX.X / REX.B at every scale. Group C: an
/// RBP base (whose low three bits force an explicit zero disp8) with an R12
/// index (whose SIB field value is the no-index sentinel, rescued by REX.X).
/// Group D: an RSP base (SIB base field 100). Group E: an R13 base (REX.B and a
/// forced disp8). Group F: one register serving as BOTH base and index.
pub const EMITTED_X86_MOVSXD_SIB: &[EmittedScaledLoad] = &[
    // ---- Group A: dst=rax, base=rax, index=rcx — every scale x every disp mode ----
    e("rax", "rax", "rcx", 1, 0, &[0x48, 0x63, 0x04, 0x08]),
    e("rax", "rax", "rcx", 1, 8, &[0x48, 0x63, 0x44, 0x08, 0x08]),
    e("rax", "rax", "rcx", 1, -8, &[0x48, 0x63, 0x44, 0x08, 0xF8]),
    e(
        "rax",
        "rax",
        "rcx",
        1,
        0x100,
        &[0x48, 0x63, 0x84, 0x08, 0x00, 0x01, 0x00, 0x00],
    ),
    e(
        "rax",
        "rax",
        "rcx",
        1,
        -0x1234,
        &[0x48, 0x63, 0x84, 0x08, 0xCC, 0xED, 0xFF, 0xFF],
    ),
    e("rax", "rax", "rcx", 2, 0, &[0x48, 0x63, 0x04, 0x48]),
    e("rax", "rax", "rcx", 2, 8, &[0x48, 0x63, 0x44, 0x48, 0x08]),
    e("rax", "rax", "rcx", 2, -8, &[0x48, 0x63, 0x44, 0x48, 0xF8]),
    e(
        "rax",
        "rax",
        "rcx",
        2,
        0x100,
        &[0x48, 0x63, 0x84, 0x48, 0x00, 0x01, 0x00, 0x00],
    ),
    e(
        "rax",
        "rax",
        "rcx",
        2,
        -0x1234,
        &[0x48, 0x63, 0x84, 0x48, 0xCC, 0xED, 0xFF, 0xFF],
    ),
    e("rax", "rax", "rcx", 4, 0, &[0x48, 0x63, 0x04, 0x88]),
    e("rax", "rax", "rcx", 4, 8, &[0x48, 0x63, 0x44, 0x88, 0x08]),
    e("rax", "rax", "rcx", 4, -8, &[0x48, 0x63, 0x44, 0x88, 0xF8]),
    e(
        "rax",
        "rax",
        "rcx",
        4,
        0x100,
        &[0x48, 0x63, 0x84, 0x88, 0x00, 0x01, 0x00, 0x00],
    ),
    e(
        "rax",
        "rax",
        "rcx",
        4,
        -0x1234,
        &[0x48, 0x63, 0x84, 0x88, 0xCC, 0xED, 0xFF, 0xFF],
    ),
    e("rax", "rax", "rcx", 8, 0, &[0x48, 0x63, 0x04, 0xC8]),
    e("rax", "rax", "rcx", 8, 8, &[0x48, 0x63, 0x44, 0xC8, 0x08]),
    e("rax", "rax", "rcx", 8, -8, &[0x48, 0x63, 0x44, 0xC8, 0xF8]),
    e(
        "rax",
        "rax",
        "rcx",
        8,
        0x100,
        &[0x48, 0x63, 0x84, 0xC8, 0x00, 0x01, 0x00, 0x00],
    ),
    e(
        "rax",
        "rax",
        "rcx",
        8,
        -0x1234,
        &[0x48, 0x63, 0x84, 0xC8, 0xCC, 0xED, 0xFF, 0xFF],
    ),
    // ---- Group B: dst=r10 (REX.R), base=r12 (REX.B), index=r9 (REX.X) ----
    e("r10", "r12", "r9", 1, 0, &[0x4F, 0x63, 0x14, 0x0C]),
    e("r10", "r12", "r9", 1, 8, &[0x4F, 0x63, 0x54, 0x0C, 0x08]),
    e(
        "r10",
        "r12",
        "r9",
        1,
        -0x1234,
        &[0x4F, 0x63, 0x94, 0x0C, 0xCC, 0xED, 0xFF, 0xFF],
    ),
    e("r10", "r12", "r9", 2, 0, &[0x4F, 0x63, 0x14, 0x4C]),
    e("r10", "r12", "r9", 2, 8, &[0x4F, 0x63, 0x54, 0x4C, 0x08]),
    e(
        "r10",
        "r12",
        "r9",
        2,
        -0x1234,
        &[0x4F, 0x63, 0x94, 0x4C, 0xCC, 0xED, 0xFF, 0xFF],
    ),
    e("r10", "r12", "r9", 4, 0, &[0x4F, 0x63, 0x14, 0x8C]),
    e("r10", "r12", "r9", 4, 8, &[0x4F, 0x63, 0x54, 0x8C, 0x08]),
    e(
        "r10",
        "r12",
        "r9",
        4,
        -0x1234,
        &[0x4F, 0x63, 0x94, 0x8C, 0xCC, 0xED, 0xFF, 0xFF],
    ),
    e("r10", "r12", "r9", 8, 0, &[0x4F, 0x63, 0x14, 0xCC]),
    e("r10", "r12", "r9", 8, 8, &[0x4F, 0x63, 0x54, 0xCC, 0x08]),
    e(
        "r10",
        "r12",
        "r9",
        8,
        -0x1234,
        &[0x4F, 0x63, 0x94, 0xCC, 0xCC, 0xED, 0xFF, 0xFF],
    ),
    // ---- Group C: base=rbp (forced disp8), index=r12 (the no-index field value) ----
    e("rax", "rbp", "r12", 1, 0, &[0x4A, 0x63, 0x44, 0x25, 0x00]),
    e("rax", "rbp", "r12", 1, -8, &[0x4A, 0x63, 0x44, 0x25, 0xF8]),
    e("rax", "rbp", "r12", 4, 0, &[0x4A, 0x63, 0x44, 0xA5, 0x00]),
    e("rax", "rbp", "r12", 4, -8, &[0x4A, 0x63, 0x44, 0xA5, 0xF8]),
    // ---- Group D: base=rsp (SIB base field 100) ----
    e("r10", "rsp", "r14", 1, 0, &[0x4E, 0x63, 0x14, 0x34]),
    e(
        "r10",
        "rsp",
        "r14",
        1,
        0x100,
        &[0x4E, 0x63, 0x94, 0x34, 0x00, 0x01, 0x00, 0x00],
    ),
    e("r10", "rsp", "r14", 8, 0, &[0x4E, 0x63, 0x14, 0xF4]),
    e(
        "r10",
        "rsp",
        "r14",
        8,
        0x100,
        &[0x4E, 0x63, 0x94, 0xF4, 0x00, 0x01, 0x00, 0x00],
    ),
    // ---- Group E: base=r13 (REX.B and a forced disp8), index=rbp ----
    e("rax", "r13", "rbp", 2, 0, &[0x49, 0x63, 0x44, 0x6D, 0x00]),
    e("rax", "r13", "rbp", 2, 8, &[0x49, 0x63, 0x44, 0x6D, 0x08]),
    e("rax", "r13", "rbp", 4, 0, &[0x49, 0x63, 0x44, 0xAD, 0x00]),
    e("rax", "r13", "rbp", 4, 8, &[0x49, 0x63, 0x44, 0xAD, 0x08]),
    // ---- Group F: one register as BOTH base and index ----
    e("rax", "rcx", "rcx", 4, 0, &[0x48, 0x63, 0x04, 0x89]),
];

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn jumptable_bytes() -> Vec<u8> {
        // MOVSXD RAX, dword [RBX + RCX*4] — the jump-table shape.
        vec![0x48, 0x63, 0x04, 0x8B]
    }

    fn jumptable_intent() -> ScaledSextLoadIntent {
        ScaledSextLoadIntent {
            dst: "rax",
            base: "rbx",
            index: "rcx",
            entry_bytes: 4,
            disp: 0,
        }
    }

    #[test]
    fn the_jumptable_shape_holds() {
        let holds = movsxd_sib_check(&jumptable_intent(), &jumptable_bytes())
            .expect("MOVSXD RAX,[RBX+RCX*4] must hold");
        assert_eq!(holds.decoded.load_bits, 32);
        assert!(holds.decoded.signed);
        assert_eq!(holds.witnesses.rows, WITNESS_ROWS);
        assert!(
            holds.witnesses.negative_rows > 0,
            "the witness family must exercise the sign extension"
        );
    }

    #[test]
    fn the_two_sides_are_structurally_distinct() {
        let intent = jumptable_intent();
        let bytes = jumptable_bytes();
        let source = intent_write(&intent).expect("source side");
        let decoded = sdm_decode_scaled_load(&bytes).expect("decode");
        let machine = decoded.machine_write().expect("machine side");
        assert_ne!(
            source.value, machine.value,
            "the source states a multiply and a signed load; the machine states a shift and an \
             explicit sign-extend. If these ever become the same tree the obligation is X == X."
        );
        let obligation =
            movsxd_sib_proof_obligation(&intent, &bytes).expect("obligation must build");
        assert!(
            obligation.is_genuinely_proven(),
            "the crate's own degeneracy predicate must accept this obligation"
        );
    }

    #[test]
    fn witness_rows_separate_every_register() {
        for (row, stride) in WITNESS_ROW_STRIDE.iter().enumerate().take(WITNESS_ROWS) {
            assert_eq!(
                stride & 1,
                1,
                "witness row {row} stride must be ODD for injectivity across the roots"
            );
            let mut seen = std::collections::BTreeSet::new();
            for root in 0u8..16 {
                assert!(
                    seen.insert(witness_reg_value(row, root)),
                    "witness row {row} binds two registers to the same value"
                );
            }
        }
    }

    #[test]
    fn every_corpus_entry_holds() {
        for entry in EMITTED_X86_MOVSXD_SIB {
            let intent = entry.intent();
            movsxd_sib_check(&intent, entry.bytes)
                .unwrap_or_else(|r| panic!("{} = {:02x?}: {r}", intent.label(), entry.bytes));
        }
    }

    #[test]
    fn the_credit_hook_discharges() {
        let credit = movsxd_sib_discharges_valid().expect("the credit hook must discharge");
        assert_eq!(credit.entries, EMITTED_X86_MOVSXD_SIB.len());
        assert_eq!(credit.facets_seen, REQUIRED_ENCODING_FACETS.len());
        assert!(credit.controls_refuted > 500, "{credit:?}");
        assert!(credit.model_controls_refuted > 100, "{credit:?}");
        assert_eq!(
            credit.decoder_controls_refuted,
            REQUIRED_DECODER_CONTROL_LABELS.len()
        );
        assert_eq!(credit.hand_vectors_held, SDM_HAND_VECTORS_HOLD.len());
        assert_eq!(
            credit.write_mask_vectors_checked,
            DEST_WRITE_MASK_VECTORS.len()
        );
        assert_eq!(
            credit.vacuity_controls_refuted,
            REQUIRED_VACUITY_CONTROL_LABELS.len()
        );
    }

    /// SDM Vol 1 §3.4.1.1 over the arms the credited family never reaches. A
    /// mutation of the 32-bit arm — the one that contradicts the rule hardest,
    /// since a 32-bit result is ZERO-EXTENDED to 64 and therefore writes the
    /// whole root — once left all eighteen gate cases green.
    #[test]
    fn every_write_mask_vector_reports_the_sdm_width_rule() {
        for v in DEST_WRITE_MASK_VECTORS {
            write_mask_vector_is_as_stated(v).unwrap_or_else(|e| panic!("{e}"));
        }
        // The runner has teeth: a vector that states the WRONG mask must fail.
        let wrong = DestWriteMaskVector {
            expect_mask: 0x0000_0000_FFFF_FFFF,
            ..DEST_WRITE_MASK_VECTORS[1]
        };
        let err = write_mask_vector_is_as_stated(&wrong)
            .expect_err("a vector stating the wrong mask must fail");
        assert!(err.contains("3.4.1.1"), "{err}");
        // ... and so must one whose bytes do not decode at all, rather than
        // passing because nothing was compared.
        let undecodable = DestWriteMaskVector {
            bytes: &[0x0F, 0x0B],
            ..DEST_WRITE_MASK_VECTORS[0]
        };
        let err = write_mask_vector_is_as_stated(&undecodable)
            .expect_err("a vector that does not decode is a battery defect");
        assert!(err.contains("DID NOT DECODE"), "{err}");
    }

    /// The `_ => 0` arm of [`DecodedScaledLoad::dst_write_mask`] fails CLOSED:
    /// an operand width this decoder does not model claims NOTHING, and a zero
    /// mask can never equal the source side's `u64::MAX`.
    #[test]
    fn an_unmodelled_operand_width_claims_no_write_at_all() {
        let mut decoded =
            sdm_decode_scaled_load(&[0x48, 0x63, 0x04, 0x8B]).expect("the jump-table shape");
        assert_eq!(decoded.dst_write_mask(), u64::MAX);
        decoded.dst_bits = 8;
        assert_eq!(decoded.dst_write_mask(), 0xFF, "SDM Vol 1 3.4.1.1");
        decoded.dst_bits = 128;
        assert_eq!(
            decoded.dst_write_mask(),
            0,
            "an unmodelled destination width must claim no write, so the Destination facet fails \
             closed"
        );
        let source = intent_write(&jumptable_intent()).expect("source side");
        assert_ne!(decoded.dst_write_mask(), source.mask);
    }

    /// The decoder's language yields EXACTLY the operand widths the write-mask
    /// vectors cover. If a new production ever widened it, the `_ => 0` arm
    /// would become reachable and this test would say so.
    #[test]
    fn decoder_operand_widths_are_exactly_64_32_16() {
        let mut widths = std::collections::BTreeSet::new();
        for prefix in [&[][..], &[0x66][..], &[0x67][..], &[0xF3][..]] {
            for rex in [None, Some(0x40u8), Some(0x48), Some(0x4F)] {
                for opcode in [0x63u8, 0x8B] {
                    let mut bytes = prefix.to_vec();
                    bytes.extend(rex);
                    bytes.extend_from_slice(&[opcode, 0x04, 0x8B]);
                    if let Ok(d) = sdm_decode_scaled_load(&bytes) {
                        widths.insert(d.dst_bits);
                    }
                }
            }
        }
        assert_eq!(
            widths,
            [16u32, 32, 64].into_iter().collect(),
            "the decoder's language produced an operand width the write-mask vectors do not cover"
        );
    }

    /// The anti-vacuity guard decides something. Deleting it once left all
    /// eighteen gate cases green.
    #[test]
    fn the_vacuity_controls_refute() {
        let ran = vacuity_controls_are_refused().expect("both vacuity controls must refute");
        assert_eq!(ran, REQUIRED_VACUITY_CONTROL_LABELS.len());
    }

    /// The SDM rule that REX.B does not create a base register is decided by
    /// the D1c vector: those four bytes are NOT `[r13 + rcx*4]`.
    #[test]
    fn rex_b_does_not_rescue_the_no_base_sib_form() {
        // With REX.B set, `base = 101` with `mod = 00` is STILL the no-base
        // form, so a disp32 must follow and four bytes are truncated.
        let err = sdm_decode_scaled_load(&[0x49, 0x63, 0x04, 0x8D])
            .expect_err("SDM Vol 2A Table 2-3: a disp32 follows the no-base SIB form");
        assert!(matches!(
            err,
            ScaledLoadDecodeError::Truncated { field: "disp32" }
        ));
        // With the disp32 present it decodes, and there is still NO base.
        let decoded = sdm_decode_scaled_load(&[0x49, 0x63, 0x04, 0x8D, 0x00, 0x00, 0x00, 0x00])
            .expect("the no-base SIB form decodes");
        assert!(
            matches!(decoded.addr, AddressForm::Sib { base: None, .. }),
            "REX.B extends a base that EXISTS; here none does: {:?}",
            decoded.addr
        );
        // The same rule one ModR/M field over: RIP-relative, REX.B set.
        let decoded = sdm_decode_scaled_load(&[0x49, 0x63, 0x05, 0x00, 0x00, 0x00, 0x00])
            .expect("the RIP-relative form decodes");
        assert!(
            matches!(decoded.addr, AddressForm::RipRelative { .. }),
            "{:?}",
            decoded.addr
        );
    }

    #[test]
    fn the_hook_fails_closed_on_an_empty_corpus() {
        assert!(movsxd_sib_credit_over(&[]).is_err());
    }

    #[test]
    fn the_hook_fails_closed_on_a_narrow_corpus() {
        let narrow = [EMITTED_X86_MOVSXD_SIB[0]];
        let err = movsxd_sib_credit_over(&narrow).expect_err("a one-entry corpus cannot credit");
        assert!(err.contains("facet coverage"), "{err}");
    }

    #[test]
    fn the_self_comparison_control_is_refused_as_degenerate() {
        let intent = jumptable_intent();
        let bytes = jumptable_bytes();
        let control = scaled_load_model_controls()
            .into_iter()
            .find(|c| c.label == W6_SELF_COMPARISON)
            .expect("W6 exists");
        model_control_is_refuted_as_stated(&control, &intent, &bytes)
            .expect("the self-comparison must be refused as DEGENERATE");
    }

    #[test]
    fn the_deferrals_have_unique_ids() {
        let mut ids: Vec<&str> = X86_MOVSXD_SIB_DEFERRALS.iter().map(|d| d.id).collect();
        ids.sort_unstable();
        let before = ids.len();
        ids.dedup();
        assert_eq!(before, ids.len(), "duplicate deferral id");
        assert!(ids.len() >= 8, "the non-claims list shrank");
    }
}
