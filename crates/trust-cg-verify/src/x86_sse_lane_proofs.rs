// trust-cg-verify/x86_sse_lane_proofs.rs - the x86-64 SSE lane-routing family
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: Intel 64 and IA-32 Architectures Software Developer's Manual —
//   Vol 2A §2.1     (instruction format: legacy prefixes, the 0F / 0F 38 opcode
//                    maps, ModR/M, SIB, displacement, immediate),
//   Vol 2A §2.1.1   (the four legacy prefix groups; 66/F2/F3 act as MANDATORY
//                    prefixes selecting a different instruction in the SSE maps),
//   Vol 2A §2.2.1   (REX: `0100WRXB`, and "a REX prefix must immediately precede
//                    the opcode byte" — so a mandatory prefix comes BEFORE it),
//   Vol 2A Table 2-2 / 2-3 (32-bit ModR/M and SIB addressing forms, including
//                    `mod=00 rm=101` = RIP-relative and `rm=100` = SIB escape),
//   Vol 2B "PUNPCKLBW/PUNPCKLWD/PUNPCKLDQ/PUNPCKLQDQ—Unpack Low Data",
//   Vol 2B "PUNPCKHBW/PUNPCKHWD/PUNPCKHDQ/PUNPCKHQDQ—Unpack High Data",
//   Vol 2B "PACKUSWB—Pack with Unsigned Saturation",
//   Vol 2B "PACKSSWB/PACKSSDW—Pack with Signed Saturation",
//   Vol 2B "PSHUFD—Shuffle Packed Doublewords",
//   Vol 2B "PSHUFHW—Shuffle Packed High Words", "PSHUFLW—Shuffle Packed Low Words",
//   Vol 2B "PMOVMSKB—Move Byte Mask",
//   Vol 2B "MOVDQA—Move Aligned Packed Integer Values", "MOVDQU", "MOVQ",
//   Vol 2B "PTEST—Logical Compare",
//   Vol 2B "PBLENDVB—Variable Blend Packed Bytes", "BLENDVPS", "BLENDVPD",
//   Vol 1 §3.4.1.1  (32-bit GPR results are ZERO-EXTENDED to 64 bits).
//
// WHAT THIS FAMILY IS. The ten SSE rows this module credits are LANE ROUTING
// instructions: what each produces is, bit for bit, a rearrangement of the bits
// of its operands (PACKUSWB additionally narrows each 16-bit element, PBLENDVB
// additionally selects per byte, PTEST reduces to flags). That is the whole
// reason they can be modelled EXACTLY rather than sampled: a routing
// instruction's meaning is a total function from result-bit index to "which bit
// of which operand", and two such functions denote the same instruction iff
// their tables are equal. No solver and no random sweep stands between the two
// sides for the nine value rows — the comparison is a decision.
//
//   * MACHINE side: [`sdm_decode_sse`] takes ONLY bytes — no hint from the
//     intent — and walks the SDM instruction format. [`machine_denotation`]
//     then maps the DECODED mnemonic to the SDM's Operation text, transcribed
//     assignment by assignment as a literal 16-entry table (see the
//     `SDM_*` tables in section 4).
//   * SOURCE side: [`intent_denotation`] takes ONLY the machine-IR intent — the
//     trust-cg opcode, the operand register NAMES, and (for PSHUFD) the
//     permutation the instruction selection MEANT. It never sees a byte, a REX
//     bit, an opcode byte or a register number from the encoder. It states the
//     routing PARAMETRICALLY (`spec_interleave(elem_bytes, high)`,
//     `spec_permute_dwords(perm)`, `spec_sign_bit_gather`, …), so a transcription
//     typo on the machine side and a wrong parameter on the source side refute
//     each other.
//   * COMPARISON: both sides are a [`Denotation`]. For the nine value rows that
//     is a `Vec<BitSource>` plus a [`Dest`] — equality of those is equality of
//     the denoted function on EVERY input, not a sample. PTEST reduces to flags
//     rather than bits and is compared by EVALUATION instead; see below.
//
// WHY THE TWO SIDES ARE NOT X == X. This was the exact defect that made the
// pre-existing `PackLowQwords` reconstruction uncreditable (`coverage_gate.rs`
// carries the correction): it built `concat(extract(a), extract(b))` on the
// machine side and the character-for-character identical tree on the source
// side, so it refuted nothing. Here the two sides are built by different
// programs in different vocabularies:
//
//     machine:  bytes -> prefix/REX/map/opcode/ModRM -> SDM mnemonic ->
//               a LITERAL per-opcode transcription table -> bits
//     source:   trust-cg opcode + operand NAMES + intended permutation ->
//               a PARAMETRIC generator over (element width, which half) -> bits
//
// and the only thing joining the two ends is the encoder's own `hw_enc` table,
// which is the thing under test. The wrong-half control (PUNPCKHBW against the
// PUNPCKLBW intent) and the wrong-width control (PUNPCKLDQ against the
// PUNPCKLBW intent) — the two the coverage gate names as missing — both refute
// here, on VALUE, in [`machine_model_controls`].
//
// TWO ROWS ARE WEAKER THAN THAT, AND THE ROW NOTES SAY SO. For MOVDQA
// register-register and for PMOVMSKB the two sides are the same construction in
// two places — `copy_128` against `spec_copy_128` is the identical 16x8 loop,
// `sdm_pmovmskb` against `spec_sign_bit_gather` the identical sixteen sign bits
// plus zero fill. For a row whose meaning IS "bit i of the result is bit i of
// the source" there is no second vocabulary to state it in, so for those two
// rows the ROUTING comparison decides nothing beyond what the other conjuncts
// already decide: the decoded mnemonic and DIRECTION (not MOVQ, not the 7F
// store), the destination (an XMM for MOVDQA, the GPR ROOT for PMOVMSKB, which
// is where the 32-bit write's zero-extension is read), the width, and the
// operand identity. Those four ARE read and each has a refuting wrong-model
// control (MovqZeroUpper, MovdqaStore, IdentityOfDest, ConstantZero;
// MaskFromBit0, MaskReversed, MaskSignExtended, MaskLow8LanesOnly). What a
// same-construction pair cannot catch is a SHARED misreading of the SDM, and
// the only thing in this family that can is the native-silicon differential —
// which is why `tests/x86_sse_lane_gate.rs` issues a real `movdqa` through
// inline asm for the MOVDQA row rather than modelling the copy in Rust, and
// runs `_mm_movemask_epi8` for PMOVMSKB. The other eight rows do not depend on
// that: their two sides are a literal per-opcode table against a parametric
// generator (PUNPCK*), an imm8-derived permutation against a stated one
// (PSHUFD), arithmetic saturation against a bit-pattern narrow (PACKUSWB), a
// per-bit fold against whole-128-bit arithmetic (PTEST), and a per-byte select
// against an independently stated one (PBLENDVB).
//
// HOW THE MACHINE SIDE STAYS INDEPENDENT. This crate cannot depend on
// `trust-cg-codegen` (that crate depends on THIS one), so nothing here can call
// the encoder, and nothing here does:
//
//   * the decoder models a dozen instructions the encoder NEVER emits
//     (PUNPCKLWD, PUNPCKHWD, PUNPCKHDQ, PUNPCKHQDQ, PACKSSWB, PACKSSDW, MOVDQU,
//     MOVQ-zero-upper, PSHUFHW, PSHUFLW, BLENDVPS, BLENDVPD, the MMX forms and
//     the MOVDQA STORE direction), so it cannot have been obtained by inverting
//     `encode.rs`'s dispatch, and a mutated opcode byte lands on a known
//     NEIGHBOUR instruction that refutes on VALUE rather than on "unknown byte";
//   * the coverage-gate credit hook cannot run the encoder either, so it runs
//     over [`EMITTED_X86_SSE_LANE_INSTANCES`] — bytes CAPTURED from the real
//     encoder. `tests/x86_sse_lane_gate.rs` holds `trust-cg-codegen` as a
//     DEV-dependency, re-encodes every entry through the live encoder and fails
//     on any divergence, so the capture cannot rot under a green row.
//
// PACKUSWB'S NARROW IS PROVED EXHAUSTIVELY, NOT SAMPLED. The routing facet
// (which 16-bit element becomes which result byte) is part of the bit table.
// The narrowing function itself is the subject of its own obligation,
// [`saturation_obligation`], which compares the SDM's ARITHMETIC formulation
// (`if s < 0 { 0 } else if s > 255 { 255 } else { s }`) against the machine
// IR's BIT-PATTERN formulation (`if w[15] { 0 } else if w[14:8] != 0 { 255 }
// else { w[7:0] }`) over ALL 65536 inputs. That is exhaustive — every input, no
// sampling — and the PACKSSWB, truncate-without-saturate and unsigned-input
// controls each refute on it.
//
// PTEST IS THE ONE ROW COMPARED BY EVALUATION. Its result is not a routing of
// input bits but a reduction of all 128 of them to flags, so there is no bit
// table to compare. Its machine side is the SDM Operation text as a per-bit
// FOLD over a stated bit range; its source side, [`intent_ptest_flags`], is the
// machine-IR intent stated with whole-128-bit arithmetic. They are compared by
// evaluation over [`ptest_witnesses`]: every ordered pair of single-bit
// operands (128 x 128, which is what reaches ZF=1 and the low/high asymmetry a
// random 128-bit sweep never reaches), the complement families, the boundary
// patterns and a deterministic pseudo-random sweep. That is EXHAUSTIVE over the
// structured domain and STATISTICAL beyond it — evidence, not a formal proof,
// and the row's note says so.
//
// WHAT CREDITING THESE ROWS DOES NOT SAY, said plainly (the same list is
// carried as data in [`X86_SSE_LANE_DEFERRALS`] and pinned by the gate test):
//
//   * NOT that instruction selection chose the RIGHT instruction, permutation,
//     mask or operands for the trust-ir it was lowering. The intent side is
//     the emitted instruction's OWN intent; a lowering that wanted an unpack of
//     the high half and emitted the low one is outside this family. That
//     belongs to the composite sequence proofs and to TV-2.
//   * NOT, for PSHUFD, that the intended permutation recorded in the corpus is
//     the one instruction selection wanted, and NOT that instruction selection
//     PACKS the ORDER fields the way the SDM reads them. This was overclaimed
//     and the claim is now stated at its real width. The corpus's `perm` is
//     transcribed by hand from the isel's own immediate literals, and the live
//     sweep in `tests/x86_sse_lane_gate.rs` HANDS the encoder an immediate it
//     packs by the SDM convention, so the obligation's PSHUFD conjunct cannot
//     see an isel that packed those fields in the wrong order: it would emit a
//     different imm, the hand-transcribed perm would move with it, and both
//     sides would agree. What IS established is (a) that the ENCODER places the
//     immediate it was handed, unmutated, in the `/r ib` slot — the reversed
//     and off-by-one imm8 byte mutants refute — and (b) that the SDM UNPACKING
//     convention `(imm >> 2j) & 3` is the CPU's, anchored on silicon by
//     `_mm_shuffle_epi32` over the immediates the isel spells. The one isel
//     packer that computes an immediate rather than spelling it,
//     `X86InstructionSelector::v4i32_mask_shuffle_imm`, is pinned against the
//     SDM ORDER convention in `x86_sse_lane_gate`; the literal immediates are
//     not, and cannot be without running instruction selection.
//   * NOT that the ISA rules are right. They are TRANSCRIBED from the SDM and
//     are this family's trust base, exactly as `x86_encoding_proofs` says of
//     its own. `tests/x86_sse_lane_gate.rs` adds a NATIVE-SILICON differential
//     on this host for every corpus entry, which defeats a shared misreading of
//     the SDM but is one CPU model, not a proof.
//   * NOT, for PTEST, anything about the consuming Jcc/CMOVcc condition mapping
//     or about whether testing a canonical mask is the right predicate
//     lowering. It claims the six status flags. "Operands unchanged" is not
//     modelled. `AF <- OF <- PF <- SF <- 0` is SDM-transcribed trust base: the
//     silicon differential anchors ZF and CF only.
//   * NOT, for MOVDQA register-register, that a copy was the right thing to
//     emit, and NOT that MOVDQA differs from MOVDQU in VALUE. It does not:
//     the two have the same denotation and differ only in the alignment
//     requirement on a MEMORY operand, which the RR form has not got. The
//     MOVDQA/MOVDQU separation here is the MNEMONIC-identity conjunct, and the
//     `F3`-for-`66` mutant refutes on that conjunct, not on value.
//   * NOT that a folded `xmm, m128` operand is 16-byte aligned. Legacy-SSE
//     128-bit "A" forms #GP on an unaligned m128; the memory-form denotations
//     ASSUME the effective address is aligned and say nothing about the spill
//     slot's alignment. The already-GREEN spill-foldable packed rows
//     (PADD*/PSUB*/PCMP*/PAND…) carry the same uncovered assumption; that is
//     pre-existing gate-wide debt, not something this family introduces.
//   * NOT two-address tie correctness, register allocation, or XMM0 liveness
//     and clobber around PBLENDVB. `post_ra_dataflow` owns those.
//   * NOTHING beyond the captured corpus at gate time. The full 16x16 register
//     sweep and the all-256 imm8 PSHUFD sweep run in the dev-dependency test.
//   * NOTHING about upper YMM/ZMM state, #UD feature gating for the SSE4.1
//     forms, or MXCSR.
//   * NOT a per-instruction certificate in compiles. These opcodes remain
//     per-instruction `Unverified`; wiring them into `x86_opcode_to_source_op`
//     would expose them to the TV-2 ENFORCE path and is deliberately NOT part
//     of the ratio change.
//   * NOT a general x86 decoder, and NOTHING about any other x86-64 RED row.

//! The x86-64 SSE lane-routing family: an independent SDM-derived decoder for
//! the `0F`/`0F 38` packed-integer maps, an exact bit-level routing denotation
//! for both the decoded bytes and the machine-IR intent, the typed refutations
//! between them, an exhaustive obligation for PACKUSWB's unsigned-saturating
//! narrow, an evaluated obligation for PTEST's flag reduction, a captured corpus
//! of real emitted encodings, the negative-control battery, and the
//! coverage-gate credit hook that demands every control refute.

use std::collections::BTreeSet;
use std::fmt;

use trust_cg_ir::X86Opcode;

use crate::x86_encoding_proofs::SDM_R64;

// ===========================================================================
// (1) The instructions this family names
// ===========================================================================

/// The XMM registers in SDM register-number order. `trust-cg-ir` spells them
/// the same way, but this table is the SDM's and the source side reaches the
/// encoder's numbering only THROUGH it.
pub const SDM_XMM: [&str; 16] = [
    "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7", "xmm8", "xmm9", "xmm10",
    "xmm11", "xmm12", "xmm13", "xmm14", "xmm15",
];

/// The SDM register NUMBER of an XMM register named `name`.
pub fn sdm_xmm(name: &str) -> Option<u8> {
    SDM_XMM.iter().position(|&n| n == name).map(|i| i as u8)
}

/// The SDM register NUMBER of a 64-bit GPR named `name` (memory bases).
pub fn sdm_gpr64(name: &str) -> Option<u8> {
    SDM_R64.iter().position(|&n| n == name).map(|i| i as u8)
}

/// Which opcode map a decoded instruction came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum OpMap {
    /// Two-byte opcodes: `0F xx`.
    Map0F,
    /// Three-byte opcodes: `0F 38 xx`.
    Map0F38,
}

/// Every instruction [`sdm_decode_sse`] can name.
///
/// The set is deliberately WIDER than what `encode.rs` emits: the twelve
/// neighbours (PUNPCKLWD/PUNPCKHWD/PUNPCKHDQ/PUNPCKHQDQ, PACKSSWB/PACKSSDW,
/// MOVDQU, MOVQ, PSHUFHW/PSHUFLW, BLENDVPS/BLENDVPD), the MOVDQA STORE
/// direction and the MMX forms exist so that a MUTATED opcode byte or prefix
/// decodes to a known DIFFERENT instruction and refutes on its VALUE or its
/// MNEMONIC, rather than dead-ending in "unknown byte". A decoder that only
/// knew the ten emitted encodings could have been obtained by inverting the
/// encoder; this one could not.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SseMnemonic {
    /// `66 0F 60 /r` — PUNPCKLBW xmm, xmm/m128.
    PunpcklbwX,
    /// `66 0F 61 /r` — PUNPCKLWD xmm, xmm/m128.
    PunpcklwdX,
    /// `66 0F 62 /r` — PUNPCKLDQ xmm, xmm/m128.
    PunpckldqX,
    /// `66 0F 63 /r` — PACKSSWB xmm, xmm/m128.
    PacksswbX,
    /// `66 0F 67 /r` — PACKUSWB xmm, xmm/m128.
    PackuswbX,
    /// `66 0F 68 /r` — PUNPCKHBW xmm, xmm/m128.
    PunpckhbwX,
    /// `66 0F 69 /r` — PUNPCKHWD xmm, xmm/m128.
    PunpckhwdX,
    /// `66 0F 6A /r` — PUNPCKHDQ xmm, xmm/m128.
    PunpckhdqX,
    /// `66 0F 6B /r` — PACKSSDW xmm, xmm/m128.
    PackssdwX,
    /// `66 0F 6C /r` — PUNPCKLQDQ xmm, xmm/m128.
    PunpcklqdqX,
    /// `66 0F 6D /r` — PUNPCKHQDQ xmm, xmm/m128.
    PunpckhqdqX,
    /// `66 0F 6F /r` — MOVDQA xmm, xmm/m128 (destination is the ModRM.reg side).
    MovdqaLoad,
    /// `66 0F 7F /r` — MOVDQA xmm/m128, xmm (destination is the ModRM.r/m side).
    MovdqaStore,
    /// `F3 0F 6F /r` — MOVDQU xmm, xmm/m128.
    MovdquLoad,
    /// `F3 0F 7F /r` — MOVDQU xmm/m128, xmm.
    MovdquStore,
    /// `F3 0F 7E /r` — MOVQ xmm, xmm/m64: low quadword moved, upper ZEROED.
    MovqZeroUpper,
    /// `66 0F 70 /r ib` — PSHUFD xmm, xmm/m128, imm8.
    PshufdX,
    /// `F3 0F 70 /r ib` — PSHUFHW xmm, xmm/m128, imm8.
    PshufhwX,
    /// `F2 0F 70 /r ib` — PSHUFLW xmm, xmm/m128, imm8.
    PshuflwX,
    /// `66 0F D7 /r` — PMOVMSKB r32, xmm (ModRM.reg is a GENERAL-PURPOSE register).
    PmovmskbX,
    /// `66 0F 38 17 /r` — PTEST xmm, xmm/m128.
    PtestX,
    /// `66 0F 38 10 /r` — PBLENDVB xmm, xmm/m128, <XMM0>.
    PblendvbX,
    /// `66 0F 38 14 /r` — BLENDVPS xmm, xmm/m128, <XMM0> (DWORD-granular mask).
    BlendvpsX,
    /// `66 0F 38 15 /r` — BLENDVPD xmm, xmm/m128, <XMM0> (QWORD-granular mask).
    BlendvpdX,
    /// The 64-bit MMX form of a `0F` packed opcode reached WITHOUT the `66`
    /// mandatory prefix: `0F 60 /r` is PUNPCKLBW **mm, mm/m32**, not the XMM
    /// instruction. Carried as one variant with its opcode byte because this
    /// family models no MMX semantics — it only needs the dropped-`66` mutant
    /// to land on a DIFFERENT NAMED instruction and refute at the mnemonic
    /// conjunct.
    MmxForm(u8),
}

impl SseMnemonic {
    /// The SDM name, for refutation messages.
    pub fn name(self) -> String {
        use SseMnemonic as M;
        match self {
            M::PunpcklbwX => "PUNPCKLBW".into(),
            M::PunpcklwdX => "PUNPCKLWD".into(),
            M::PunpckldqX => "PUNPCKLDQ".into(),
            M::PacksswbX => "PACKSSWB".into(),
            M::PackuswbX => "PACKUSWB".into(),
            M::PunpckhbwX => "PUNPCKHBW".into(),
            M::PunpckhwdX => "PUNPCKHWD".into(),
            M::PunpckhdqX => "PUNPCKHDQ".into(),
            M::PackssdwX => "PACKSSDW".into(),
            M::PunpcklqdqX => "PUNPCKLQDQ".into(),
            M::PunpckhqdqX => "PUNPCKHQDQ".into(),
            M::MovdqaLoad => "MOVDQA xmm,xmm/m128".into(),
            M::MovdqaStore => "MOVDQA xmm/m128,xmm".into(),
            M::MovdquLoad => "MOVDQU xmm,xmm/m128".into(),
            M::MovdquStore => "MOVDQU xmm/m128,xmm".into(),
            M::MovqZeroUpper => "MOVQ xmm,xmm/m64".into(),
            M::PshufdX => "PSHUFD".into(),
            M::PshufhwX => "PSHUFHW".into(),
            M::PshuflwX => "PSHUFLW".into(),
            M::PmovmskbX => "PMOVMSKB".into(),
            M::PtestX => "PTEST".into(),
            M::PblendvbX => "PBLENDVB".into(),
            M::BlendvpsX => "BLENDVPS".into(),
            M::BlendvpdX => "BLENDVPD".into(),
            M::MmxForm(b) => format!("MMX form of 0F {b:02X} (64-bit mm operands)"),
        }
    }

    /// True when the ModRM.reg field names a GENERAL-PURPOSE register rather
    /// than an XMM one. PMOVMSKB is the only such instruction here
    /// (Vol 2B "PMOVMSKB—Move Byte Mask": `r32, xmm`).
    pub fn reg_field_is_gpr(self) -> bool {
        matches!(self, SseMnemonic::PmovmskbX)
    }

    /// True when this instruction takes an `imm8` (`/r ib`).
    ///
    /// The MMX form of `0F 70` is PSHUFW (Vol 2B "PSHUFW—Shuffle Packed Words",
    /// `0F 70 /r ib`), which carries an immediate just as its three prefixed
    /// siblings do. Every other MMX form reached here is `/r` only.
    pub fn has_imm8(self) -> bool {
        matches!(
            self,
            SseMnemonic::PshufdX
                | SseMnemonic::PshufhwX
                | SseMnemonic::PshuflwX
                | SseMnemonic::MmxForm(0x70)
        )
    }

    /// True when the r/m operand may be memory. PMOVMSKB is register-only
    /// (its r/m is an XMM register), and so is PBLENDVB as the pipeline builds
    /// it — but PBLENDVB's SDM form does admit `m128`, so only PMOVMSKB is
    /// refused here.
    pub fn rm_may_be_memory(self) -> bool {
        !matches!(self, SseMnemonic::PmovmskbX)
    }
}

// ===========================================================================
// (2) The independent SDM-derived decoder
// ===========================================================================

/// Why a byte sequence is not one of the instructions this family models.
///
/// Every variant is a FAIL-CLOSED outcome: the decoder never guesses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SseDecodeError {
    /// The bytes ran out mid-instruction.
    Truncated {
        /// What the decoder was trying to read.
        want: &'static str,
    },
    /// Bytes remained after a complete instruction.
    TrailingBytes {
        /// How many bytes were left over.
        extra: usize,
    },
    /// Two mandatory SIMD prefixes (`66`/`F2`/`F3`) in one instruction.
    RepeatedMandatoryPrefix,
    /// A mandatory prefix after the REX. Vol 2A §2.2.1: the REX must
    /// IMMEDIATELY precede the opcode (here, the `0F` escape).
    PrefixAfterRex,
    /// `REX.W` set. None of the modelled instructions has a W-promoted form.
    RexWSet,
    /// `REX.X` set without a SIB byte, or a SIB carrying a real index. Scaled
    /// index addressing is not modelled by this family.
    ScaledIndexNotModelled,
    /// The instruction did not start with the `0F` escape.
    NotTwoByteOpcode {
        /// The byte found in its place.
        found: u8,
    },
    /// The `(prefix, map, opcode byte)` triple is not a modelled instruction.
    UnknownOpcode {
        /// The mandatory prefix, if any.
        prefix: Option<u8>,
        /// Which opcode map.
        map: OpMap,
        /// The final opcode byte.
        opcode: u8,
    },
    /// `mod=00, r/m=101`: RIP-relative addressing, not modelled (its effective
    /// address depends on the instruction's own length and placement).
    RipRelativeNotModelled,
    /// `mod=00, base=101` inside a SIB: the no-base `disp32` form, not modelled.
    NoBaseSibNotModelled,
    /// A memory r/m for an instruction whose r/m must be a register.
    MemoryOperandNotAllowed {
        /// The instruction that refuses it.
        mnemonic: SseMnemonic,
    },
}

impl fmt::Display for SseDecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Truncated { want } => write!(f, "truncated: ran out of bytes reading {want}"),
            Self::TrailingBytes { extra } => {
                write!(f, "{extra} byte(s) left over after a complete instruction")
            }
            Self::RepeatedMandatoryPrefix => write!(f, "more than one 66/F2/F3 mandatory prefix"),
            Self::PrefixAfterRex => {
                write!(
                    f,
                    "mandatory prefix after REX (REX must precede the opcode)"
                )
            }
            Self::RexWSet => write!(f, "REX.W set: no modelled form is W-promoted"),
            Self::ScaledIndexNotModelled => write!(f, "scaled-index (SIB index) addressing"),
            Self::NotTwoByteOpcode { found } => {
                write!(f, "expected the 0F escape, found {found:#04x}")
            }
            Self::UnknownOpcode {
                prefix,
                map,
                opcode,
            } => write!(
                f,
                "unmodelled opcode: prefix {prefix:02x?}, {map:?}, byte {opcode:#04x}"
            ),
            Self::RipRelativeNotModelled => write!(f, "RIP-relative memory operand"),
            Self::NoBaseSibNotModelled => write!(f, "SIB with no base register"),
            Self::MemoryOperandNotAllowed { mnemonic } => {
                write!(f, "{} takes no memory operand", mnemonic.name())
            }
        }
    }
}

/// The decoded r/m operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SseRm {
    /// `mod=11`: a register, by SDM number (`REX.B` supplies bit 3).
    Reg(u8),
    /// A `[base + disp]` memory operand.
    Mem {
        /// SDM number of the base register.
        base: u8,
        /// Signed displacement.
        disp: i32,
        /// Whether a SIB byte was present (the RSP/R12 base escape).
        sib: bool,
    },
}

/// One decoded instruction. Every field came from the BYTES.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DecodedSse {
    /// The mandatory SIMD prefix, if any.
    pub prefix: Option<u8>,
    /// Which opcode map.
    pub map: OpMap,
    /// The final opcode byte.
    pub opcode: u8,
    /// The REX byte, if one was present.
    pub rex: Option<u8>,
    /// Which instruction those select.
    pub mnemonic: SseMnemonic,
    /// The ModRM.reg operand's register number (`REX.R` supplies bit 3).
    pub reg: u8,
    /// The ModRM.r/m operand.
    pub rm: SseRm,
    /// The trailing `imm8`, for the `/r ib` forms.
    pub imm8: Option<u8>,
    /// How many bytes the instruction consumed.
    pub len: usize,
}

/// `(prefix, map, opcode)` -> instruction, transcribed from the Vol 2B opcode
/// lines. Nothing in this table was read out of `encode.rs`.
fn sdm_opcode_table(prefix: Option<u8>, map: OpMap, opcode: u8) -> Option<SseMnemonic> {
    use OpMap::{Map0F, Map0F38};
    use SseMnemonic as M;
    match (prefix, map, opcode) {
        (Some(0x66), Map0F, 0x60) => Some(M::PunpcklbwX),
        (Some(0x66), Map0F, 0x61) => Some(M::PunpcklwdX),
        (Some(0x66), Map0F, 0x62) => Some(M::PunpckldqX),
        (Some(0x66), Map0F, 0x63) => Some(M::PacksswbX),
        (Some(0x66), Map0F, 0x67) => Some(M::PackuswbX),
        (Some(0x66), Map0F, 0x68) => Some(M::PunpckhbwX),
        (Some(0x66), Map0F, 0x69) => Some(M::PunpckhwdX),
        (Some(0x66), Map0F, 0x6A) => Some(M::PunpckhdqX),
        (Some(0x66), Map0F, 0x6B) => Some(M::PackssdwX),
        (Some(0x66), Map0F, 0x6C) => Some(M::PunpcklqdqX),
        (Some(0x66), Map0F, 0x6D) => Some(M::PunpckhqdqX),
        (Some(0x66), Map0F, 0x6F) => Some(M::MovdqaLoad),
        (Some(0x66), Map0F, 0x7F) => Some(M::MovdqaStore),
        (Some(0xF3), Map0F, 0x6F) => Some(M::MovdquLoad),
        (Some(0xF3), Map0F, 0x7F) => Some(M::MovdquStore),
        (Some(0xF3), Map0F, 0x7E) => Some(M::MovqZeroUpper),
        (Some(0x66), Map0F, 0x70) => Some(M::PshufdX),
        (Some(0xF3), Map0F, 0x70) => Some(M::PshufhwX),
        (Some(0xF2), Map0F, 0x70) => Some(M::PshuflwX),
        (Some(0x66), Map0F, 0xD7) => Some(M::PmovmskbX),
        (Some(0x66), Map0F38, 0x17) => Some(M::PtestX),
        (Some(0x66), Map0F38, 0x10) => Some(M::PblendvbX),
        (Some(0x66), Map0F38, 0x14) => Some(M::BlendvpsX),
        (Some(0x66), Map0F38, 0x15) => Some(M::BlendvpdX),
        // No mandatory prefix in the `0F` map: the 64-bit MMX forms of the same
        // opcode bytes (Vol 2B gives each of these a `mm, mm/m64` line).
        (None, Map0F, b)
            if matches!(
                b,
                0x60 | 0x61
                    | 0x62
                    | 0x63
                    | 0x67
                    | 0x68
                    | 0x69
                    | 0x6A
                    | 0x6B
                    | 0x6F
                    | 0x7F
                    | 0x70
                    | 0xD7
            ) =>
        {
            Some(M::MmxForm(b))
        }
        _ => None,
    }
}

/// Decode one SSE lane instruction from BYTES ALONE.
///
/// The grammar walked is Vol 2A §2.1's, restricted to the forms this family
/// models: `[66|F2|F3]? [REX]? 0F [38]? opcode ModRM [SIB] [disp8|disp32] [ib]`.
/// Every departure from it is a typed [`SseDecodeError`]; the decoder never
/// guesses and never consults the intent.
pub fn sdm_decode_sse(bytes: &[u8]) -> Result<DecodedSse, SseDecodeError> {
    let mut i = 0usize;

    // (a) Mandatory SIMD prefix. Vol 2A §2.1.1: 66 is the operand-size group,
    //     F2/F3 the repeat group; in the SSE maps they SELECT the instruction.
    let mut prefix: Option<u8> = None;
    while i < bytes.len() && matches!(bytes[i], 0x66 | 0xF2 | 0xF3) {
        if prefix.is_some() {
            return Err(SseDecodeError::RepeatedMandatoryPrefix);
        }
        prefix = Some(bytes[i]);
        i += 1;
    }

    // (b) REX. Vol 2A §2.2.1: `0100WRXB`, and it must IMMEDIATELY precede the
    //     opcode — so a mandatory prefix found after it is malformed.
    let mut rex: Option<u8> = None;
    if i < bytes.len() && (bytes[i] & 0xF0) == 0x40 {
        rex = Some(bytes[i]);
        i += 1;
        if i < bytes.len() && matches!(bytes[i], 0x66 | 0xF2 | 0xF3) {
            return Err(SseDecodeError::PrefixAfterRex);
        }
    }
    let rex_bits = rex.unwrap_or(0);
    if rex_bits & 0x08 != 0 {
        return Err(SseDecodeError::RexWSet);
    }
    let rex_r = u8::from(rex_bits & 0x04 != 0);
    let rex_x = rex_bits & 0x02 != 0;
    let rex_b = u8::from(rex_bits & 0x01 != 0);

    // (c) The `0F` escape and the opcode map.
    if i >= bytes.len() {
        return Err(SseDecodeError::Truncated {
            want: "the 0F escape",
        });
    }
    if bytes[i] != 0x0F {
        return Err(SseDecodeError::NotTwoByteOpcode { found: bytes[i] });
    }
    i += 1;
    if i >= bytes.len() {
        return Err(SseDecodeError::Truncated {
            want: "the opcode byte",
        });
    }
    let (map, opcode) = if bytes[i] == 0x38 {
        i += 1;
        if i >= bytes.len() {
            return Err(SseDecodeError::Truncated {
                want: "the 0F 38 opcode byte",
            });
        }
        (OpMap::Map0F38, bytes[i])
    } else {
        (OpMap::Map0F, bytes[i])
    };
    i += 1;

    let Some(mnemonic) = sdm_opcode_table(prefix, map, opcode) else {
        return Err(SseDecodeError::UnknownOpcode {
            prefix,
            map,
            opcode,
        });
    };

    // (d) ModR/M (Vol 2A Table 2-2).
    if i >= bytes.len() {
        return Err(SseDecodeError::Truncated {
            want: "the ModR/M byte",
        });
    }
    let modrm = bytes[i];
    i += 1;
    let mod_field = modrm >> 6;
    let reg = ((modrm >> 3) & 0x7) | (rex_r << 3);
    let rm_field = modrm & 0x7;

    let rm = if mod_field == 0b11 {
        if rex_x {
            return Err(SseDecodeError::ScaledIndexNotModelled);
        }
        SseRm::Reg(rm_field | (rex_b << 3))
    } else {
        if !mnemonic.rm_may_be_memory() {
            return Err(SseDecodeError::MemoryOperandNotAllowed { mnemonic });
        }
        // (e) SIB, when r/m=100 escapes to it.
        let (base_low3, sib) = if rm_field == 0b100 {
            if i >= bytes.len() {
                return Err(SseDecodeError::Truncated {
                    want: "the SIB byte",
                });
            }
            let sib_byte = bytes[i];
            i += 1;
            let index = (sib_byte >> 3) & 0x7;
            // Vol 2A Table 2-3: index=100 with REX.X clear is the NO-INDEX
            // encoding. Anything else is a scaled index, which this family
            // does not model.
            if index != 0b100 || rex_x {
                return Err(SseDecodeError::ScaledIndexNotModelled);
            }
            let base = sib_byte & 0x7;
            if mod_field == 0b00 && base == 0b101 {
                return Err(SseDecodeError::NoBaseSibNotModelled);
            }
            (base, true)
        } else {
            if rex_x {
                return Err(SseDecodeError::ScaledIndexNotModelled);
            }
            if mod_field == 0b00 && rm_field == 0b101 {
                return Err(SseDecodeError::RipRelativeNotModelled);
            }
            (rm_field, false)
        };
        // (f) Displacement.
        let disp = match mod_field {
            0b00 => 0i32,
            0b01 => {
                if i >= bytes.len() {
                    return Err(SseDecodeError::Truncated { want: "disp8" });
                }
                let d = bytes[i] as i8 as i32;
                i += 1;
                d
            }
            _ => {
                if i + 4 > bytes.len() {
                    return Err(SseDecodeError::Truncated { want: "disp32" });
                }
                let d = i32::from_le_bytes([bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3]]);
                i += 4;
                d
            }
        };
        SseRm::Mem {
            base: base_low3 | (rex_b << 3),
            disp,
            sib,
        }
    };

    // (g) The trailing imm8.
    let imm8 = if mnemonic.has_imm8() {
        if i >= bytes.len() {
            return Err(SseDecodeError::Truncated { want: "imm8" });
        }
        let v = bytes[i];
        i += 1;
        Some(v)
    } else {
        None
    };

    if i != bytes.len() {
        return Err(SseDecodeError::TrailingBytes {
            extra: bytes.len() - i,
        });
    }

    Ok(DecodedSse {
        prefix,
        map,
        opcode,
        rex,
        mnemonic,
        reg,
        rm,
        imm8,
        len: i,
    })
}

/// The length the SDM's MINIMAL encoding of this decoded instruction has.
///
/// Computed in closed form from the decoded FIELDS, never from the byte count:
/// one mandatory prefix, a REX only when some register number exceeds 7, the
/// escape(s), ModR/M, a SIB only when the base's low three bits are `100`, the
/// shortest displacement that encodes `disp`, and the `imm8`. The obligation
/// requires the real encoding to be exactly this long, which is what makes a
/// redundant `REX 0x40`, a `disp32` holding a `disp8` value, or a gratuitous
/// SIB a REFUTATION rather than an equivalent spelling.
pub fn canonical_len(d: &DecodedSse) -> usize {
    let rm_high = match d.rm {
        SseRm::Reg(r) => r >= 8,
        SseRm::Mem { base, .. } => base >= 8,
    };
    let needs_rex = d.reg >= 8 || rm_high;
    let (sib, disp_bytes) = match d.rm {
        SseRm::Reg(_) => (0, 0),
        SseRm::Mem { base, disp, .. } => {
            let base_low3 = base & 0x7;
            let sib = usize::from(base_low3 == 0b100);
            // `mod=00` cannot encode a base whose low three bits are 101
            // (that slot is RIP-relative / no-base), so such a base always
            // carries at least a disp8.
            let disp_bytes = if disp == 0 && base_low3 != 0b101 {
                0
            } else if (-128..=127).contains(&disp) {
                1
            } else {
                4
            };
            (sib, disp_bytes)
        }
    };
    usize::from(d.prefix.is_some())
        + usize::from(needs_rex)
        + match d.map {
            OpMap::Map0F => 2,
            OpMap::Map0F38 => 3,
        }
        + 1
        + sib
        + disp_bytes
        + usize::from(d.imm8.is_some())
}

// ===========================================================================
// (3) The denotation: what an instruction does, exactly
// ===========================================================================

/// One operand a result bit can come from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Operand {
    /// An XMM register, by SDM number.
    Xmm(u8),
    /// A 128-bit memory operand at `[base + disp]`.
    Mem {
        /// SDM number of the base register.
        base: u8,
        /// Signed displacement.
        disp: i32,
    },
}

/// Where an instruction's result is written.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Dest {
    /// An XMM register, by SDM number.
    Xmm(u8),
    /// The 64-bit ROOT of a general-purpose register. A 32-bit write
    /// zero-extends to 64 bits (Vol 1 §3.4.1.1), which is why the destination
    /// is named at 64-bit width and the denotation carries 64 bits.
    Gpr64(u8),
    /// A memory destination at `[base + disp]`.
    Mem {
        /// SDM number of the base register.
        base: u8,
        /// Signed displacement.
        disp: i32,
    },
}

/// A plain reference to one bit of one operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BitRef {
    /// Which operand.
    pub op: Operand,
    /// Which byte of it, counting from the least significant.
    pub byte: u8,
    /// Which bit of that byte, `0..=7`.
    pub bit: u8,
}

/// What ONE bit of the result is, as a total function of the operands.
///
/// Two instructions denote the same function on every input iff their bit
/// vectors are equal, which is what makes comparing these an exact DECISION
/// rather than a sample.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BitSource {
    /// Constant 0.
    Zero,
    /// Bit `bit` of byte `byte` of `op`, copied verbatim.
    Bit {
        /// Which operand.
        op: Operand,
        /// Which byte of it.
        byte: u8,
        /// Which bit of that byte.
        bit: u8,
    },
    /// Bit `bit` of the SATURATING NARROW of element `elem` of `op`.
    ///
    /// The element is `in_bits` wide and the result `out_bits` wide; `unsigned`
    /// picks the unsigned-saturating narrow (PACKUSWB) over the signed one
    /// (PACKSSWB / PACKSSDW). The narrowing FUNCTION itself is not asserted
    /// here — it is the subject of [`saturation_obligation`], which checks it
    /// over every one of its 65536 inputs.
    Sat {
        /// Which operand.
        op: Operand,
        /// Which element of it, counting from the least significant.
        elem: u8,
        /// The source element's width in bits.
        in_bits: u8,
        /// The result element's width in bits.
        out_bits: u8,
        /// Unsigned-saturating (PACKUSWB) rather than signed (PACKSSWB).
        unsigned: bool,
        /// Which bit of the narrowed result.
        bit: u8,
    },
    /// A per-bit select on one CONTROL bit: when bit `ctl_bit` of byte
    /// `ctl_byte` of `ctl` is 1 the result bit is `one`, otherwise `zero`.
    Select {
        /// The operand holding the control bit (XMM0 for the `BLENDV*` family).
        ctl: Operand,
        /// Which byte of it holds the control bit.
        ctl_byte: u8,
        /// Which bit of that byte is the control bit.
        ctl_bit: u8,
        /// The bit taken when the control bit is 1.
        one: BitRef,
        /// The bit taken when the control bit is 0.
        zero: BitRef,
    },
}

/// A value-producing instruction's denotation: a destination and one
/// [`BitSource`] per result bit, least significant first.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueDenot {
    /// Where the result is written.
    pub dest: Dest,
    /// One entry per result bit.
    pub bits: Vec<BitSource>,
}

/// Which operand a flag expression reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FlagOperand {
    /// The ModRM.reg operand — the SDM's `DEST` for PTEST.
    RegField,
    /// The ModRM.r/m operand — the SDM's `SRC` for PTEST.
    RmField,
}

/// One status flag, as the SDM's Operation text states it.
///
/// This is the MACHINE side's vocabulary. The source side does not build these
/// at all: [`intent_ptest_flags`] states the same six flags with whole-128-bit
/// arithmetic, and the two are compared by EVALUATION — see
/// [`ptest_obligation`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FlagExpr {
    /// The SDM's `AF <- OF <- PF <- SF <- 0`.
    Clear,
    /// Constant 1.
    Set,
    /// 1 iff every bit position in `lo..hi` of
    /// `(a [NOT] AND b [NOT])` is zero — the per-bit fold the SDM's
    /// `IF (X AND Y) = 0 THEN flag <- 1` denotes.
    AllClear {
        /// First operand.
        a: FlagOperand,
        /// Complement the first operand.
        a_not: bool,
        /// Second operand.
        b: FlagOperand,
        /// Complement the second operand.
        b_not: bool,
        /// First bit position folded over.
        lo: u16,
        /// One past the last bit position folded over.
        hi: u16,
    },
    /// Bit `bit` of `a AND b` — the scalar `TEST`'s SF, used as a control.
    BitOf {
        /// First operand.
        a: FlagOperand,
        /// Second operand.
        b: FlagOperand,
        /// Which bit.
        bit: u16,
    },
    /// Even parity of the low 8 bits of `a AND b` — the scalar `TEST`'s PF,
    /// used as a control.
    ParityLow8 {
        /// First operand.
        a: FlagOperand,
        /// Second operand.
        b: FlagOperand,
    },
}

/// The six architecturally observable status flags, in the SDM's RFLAGS bit
/// order: CF(0), PF(2), AF(4), ZF(6), SF(7), OF(11).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FlagDenot {
    /// Carry flag.
    pub cf: FlagExpr,
    /// Parity flag.
    pub pf: FlagExpr,
    /// Adjust flag.
    pub af: FlagExpr,
    /// Zero flag.
    pub zf: FlagExpr,
    /// Sign flag.
    pub sf: FlagExpr,
    /// Overflow flag.
    pub of: FlagExpr,
}

impl FlagDenot {
    /// The six flags in RFLAGS order, for evaluation and reporting.
    pub fn as_array(&self) -> [FlagExpr; 6] {
        [self.cf, self.pf, self.af, self.zf, self.sf, self.of]
    }

    /// The flag NAMES in the same order.
    pub const NAMES: [&'static str; 6] = ["CF", "PF", "AF", "ZF", "SF", "OF"];
}

/// What an instruction of this family does.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Denotation {
    /// Writes bits to a destination.
    Value(ValueDenot),
    /// THE MACHINE SIDE of a flag-writing instruction: the SDM Operation text
    /// as a per-bit fold, plus the two operands it reads.
    Flags {
        /// The six status flags.
        denot: FlagDenot,
        /// The ModRM.reg operand (the SDM's `DEST`).
        reg_op: Operand,
        /// The ModRM.r/m operand (the SDM's `SRC`).
        rm_op: Operand,
    },
    /// THE SOURCE SIDE of a flag-writing instruction. It carries only WHICH two
    /// operands the machine IR meant to test: the flag behaviour itself is
    /// [`intent_ptest_flags`], stated with whole-128-bit arithmetic and
    /// deliberately sharing NO term structure with [`FlagDenot`]. The two are
    /// compared by EVALUATION over [`ptest_witnesses`], never structurally,
    /// because a shared term structure would be exactly the `X == X` this
    /// family exists to avoid.
    FlagIntent {
        /// The operand the intent means as the SDM's `DEST`.
        reg_op: Operand,
        /// The operand the intent means as the SDM's `SRC`.
        rm_op: Operand,
    },
}

/// Why an instruction has no denotation in this family.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SseModelError {
    /// A 64-bit MMX form. This family models no MMX semantics: the dropped-`66`
    /// mutant is meant to refute at the MNEMONIC conjunct, on the strength of
    /// the decoder naming a DIFFERENT instruction, and inventing MMX Operation
    /// text here would add trust base for no gain.
    MmxFormNotModelled {
        /// The `0F` opcode byte whose MMX form was reached.
        opcode: u8,
    },
    /// The `imm8` an `/r ib` form needs was absent.
    MissingImm8,
    /// A memory operand where the model requires a register (an XMM source of a
    /// blend's implicit mask, or PMOVMSKB's r/m).
    RegisterOperandRequired,
    /// PMOVMSKB's ModRM.reg is a GPR and cannot serve as an XMM source.
    RegFieldIsGpr,
    /// A flag-model corruption was asked for on an instruction whose machine
    /// model is a VALUE, not flags.
    FlagModelRequired,
}

impl fmt::Display for SseModelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MmxFormNotModelled { opcode } => {
                write!(f, "0F {opcode:02X} without 66 is the 64-bit MMX form")
            }
            Self::MissingImm8 => write!(f, "the /r ib form carries no imm8"),
            Self::RegisterOperandRequired => write!(f, "a register operand is required here"),
            Self::RegFieldIsGpr => write!(f, "the ModRM.reg field names a GPR, not an XMM"),
            Self::FlagModelRequired => {
                write!(f, "this instruction's machine model is a value, not flags")
            }
        }
    }
}

// ===========================================================================
// (4) The MACHINE side: the SDM Operation text, transcribed
// ===========================================================================

/// Which ModRM field an SDM Operation assignment reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Field {
    /// The SDM's `DEST` — the ModRM.reg operand.
    D,
    /// The SDM's `SRC` — the ModRM.r/m operand.
    S,
}

use Field::{D, S};

/// SDM Vol 2B PUNPCKLBW (`66 0F 60 /r`), `INTERLEAVE_BYTES`, transcribed
/// assignment by assignment: `DEST[7:0] <- DEST[7:0]; DEST[15:8] <- SRC[7:0];
/// DEST[23:16] <- DEST[15:8]; ...; DEST[127:120] <- SRC[63:56]`.
const SDM_PUNPCKLBW: [(Field, u8); 16] = [
    (D, 0),
    (S, 0),
    (D, 1),
    (S, 1),
    (D, 2),
    (S, 2),
    (D, 3),
    (S, 3),
    (D, 4),
    (S, 4),
    (D, 5),
    (S, 5),
    (D, 6),
    (S, 6),
    (D, 7),
    (S, 7),
];

/// SDM Vol 2B PUNPCKHBW (`66 0F 68 /r`), `INTERLEAVE_HIGH_BYTES`: the same
/// alternation taken from the HIGH quadword of each operand.
const SDM_PUNPCKHBW: [(Field, u8); 16] = [
    (D, 8),
    (S, 8),
    (D, 9),
    (S, 9),
    (D, 10),
    (S, 10),
    (D, 11),
    (S, 11),
    (D, 12),
    (S, 12),
    (D, 13),
    (S, 13),
    (D, 14),
    (S, 14),
    (D, 15),
    (S, 15),
];

/// SDM Vol 2B PUNPCKLWD (`66 0F 61 /r`), `INTERLEAVE_WORDS`.
const SDM_PUNPCKLWD: [(Field, u8); 16] = [
    (D, 0),
    (D, 1),
    (S, 0),
    (S, 1),
    (D, 2),
    (D, 3),
    (S, 2),
    (S, 3),
    (D, 4),
    (D, 5),
    (S, 4),
    (S, 5),
    (D, 6),
    (D, 7),
    (S, 6),
    (S, 7),
];

/// SDM Vol 2B PUNPCKHWD (`66 0F 69 /r`), `INTERLEAVE_HIGH_WORDS`.
const SDM_PUNPCKHWD: [(Field, u8); 16] = [
    (D, 8),
    (D, 9),
    (S, 8),
    (S, 9),
    (D, 10),
    (D, 11),
    (S, 10),
    (S, 11),
    (D, 12),
    (D, 13),
    (S, 12),
    (S, 13),
    (D, 14),
    (D, 15),
    (S, 14),
    (S, 15),
];

/// SDM Vol 2B PUNPCKLDQ (`66 0F 62 /r`), `INTERLEAVE_DWORDS`:
/// `DEST[31:0] <- DEST[31:0]; DEST[63:32] <- SRC[31:0];
///  DEST[95:64] <- DEST[63:32]; DEST[127:96] <- SRC[63:32]`.
const SDM_PUNPCKLDQ: [(Field, u8); 16] = [
    (D, 0),
    (D, 1),
    (D, 2),
    (D, 3),
    (S, 0),
    (S, 1),
    (S, 2),
    (S, 3),
    (D, 4),
    (D, 5),
    (D, 6),
    (D, 7),
    (S, 4),
    (S, 5),
    (S, 6),
    (S, 7),
];

/// SDM Vol 2B PUNPCKHDQ (`66 0F 6A /r`), `INTERLEAVE_HIGH_DWORDS`.
const SDM_PUNPCKHDQ: [(Field, u8); 16] = [
    (D, 8),
    (D, 9),
    (D, 10),
    (D, 11),
    (S, 8),
    (S, 9),
    (S, 10),
    (S, 11),
    (D, 12),
    (D, 13),
    (D, 14),
    (D, 15),
    (S, 12),
    (S, 13),
    (S, 14),
    (S, 15),
];

/// SDM Vol 2B PUNPCKLQDQ (`66 0F 6C /r`), `INTERLEAVE_QWORDS`:
/// `DEST[63:0] <- DEST[63:0]; DEST[127:64] <- SRC[63:0]`.
const SDM_PUNPCKLQDQ: [(Field, u8); 16] = [
    (D, 0),
    (D, 1),
    (D, 2),
    (D, 3),
    (D, 4),
    (D, 5),
    (D, 6),
    (D, 7),
    (S, 0),
    (S, 1),
    (S, 2),
    (S, 3),
    (S, 4),
    (S, 5),
    (S, 6),
    (S, 7),
];

/// SDM Vol 2B PUNPCKHQDQ (`66 0F 6D /r`), `INTERLEAVE_HIGH_QWORDS`.
const SDM_PUNPCKHQDQ: [(Field, u8); 16] = [
    (D, 8),
    (D, 9),
    (D, 10),
    (D, 11),
    (D, 12),
    (D, 13),
    (D, 14),
    (D, 15),
    (S, 8),
    (S, 9),
    (S, 10),
    (S, 11),
    (S, 12),
    (S, 13),
    (S, 14),
    (S, 15),
];

/// Expand a 16-entry per-RESULT-BYTE routing table into the 128 per-result-bit
/// entries the denotation compares.
fn bytes_table_to_bits(table: &[(Field, u8); 16], d_op: Operand, s_op: Operand) -> Vec<BitSource> {
    let mut bits = Vec::with_capacity(128);
    for &(field, byte) in table {
        let op = match field {
            D => d_op,
            S => s_op,
        };
        for bit in 0..8u8 {
            bits.push(BitSource::Bit { op, byte, bit });
        }
    }
    bits
}

/// A verbatim 16-byte copy of one operand.
fn copy_128(op: Operand) -> Vec<BitSource> {
    (0..16u8)
        .flat_map(|byte| (0..8u8).map(move |bit| BitSource::Bit { op, byte, bit }))
        .collect()
}

/// SDM Vol 2B MOVQ (`F3 0F 7E`): `DEST[63:0] <- SRC[63:0];
/// DEST[127:64] <- 0000000000000000H`.
fn movq_zero_upper(op: Operand) -> Vec<BitSource> {
    let mut bits: Vec<BitSource> = (0..8u8)
        .flat_map(|byte| (0..8u8).map(move |bit| BitSource::Bit { op, byte, bit }))
        .collect();
    bits.resize(128, BitSource::Zero);
    bits
}

/// SDM Vol 2B PSHUFD (`66 0F 70 /r ib`):
/// `DEST[31:0] <- (SRC >> (ORDER[1:0] * 32))[31:0]`, and so on for the three
/// higher doublewords with `ORDER[3:2]`, `ORDER[5:4]`, `ORDER[7:6]`.
///
/// The selector for result doubleword `j` is therefore `(imm >> (2*j)) & 3` —
/// which is the ORDER-FIELD PACKING CONVENTION, and the one facet a
/// `_MM_SHUFFLE`-style argument-order bug corrupts.
fn sdm_pshufd(src: Operand, imm: u8) -> Vec<BitSource> {
    let mut bits = Vec::with_capacity(128);
    for j in 0..4u8 {
        let sel = (imm >> (2 * j)) & 0x3;
        for b in 0..4u8 {
            let byte = 4 * sel + b;
            for bit in 0..8u8 {
                bits.push(BitSource::Bit { op: src, byte, bit });
            }
        }
    }
    bits
}

/// SDM Vol 2B PSHUFHW (`F3 0F 70 /r ib`): `DEST[63:0] <- SRC[63:0]` and the
/// four HIGH words selected by the ORDER fields from the source's high quadword.
fn sdm_pshufhw(src: Operand, imm: u8) -> Vec<BitSource> {
    let mut bits = Vec::with_capacity(128);
    for byte in 0..8u8 {
        for bit in 0..8u8 {
            bits.push(BitSource::Bit { op: src, byte, bit });
        }
    }
    for j in 0..4u8 {
        let sel = (imm >> (2 * j)) & 0x3;
        for b in 0..2u8 {
            let byte = 8 + 2 * sel + b;
            for bit in 0..8u8 {
                bits.push(BitSource::Bit { op: src, byte, bit });
            }
        }
    }
    bits
}

/// SDM Vol 2B PSHUFLW (`F2 0F 70 /r ib`): the four LOW words selected by the
/// ORDER fields, and `DEST[127:64] <- SRC[127:64]`.
fn sdm_pshuflw(src: Operand, imm: u8) -> Vec<BitSource> {
    let mut bits = Vec::with_capacity(128);
    for j in 0..4u8 {
        let sel = (imm >> (2 * j)) & 0x3;
        for b in 0..2u8 {
            let byte = 2 * sel + b;
            for bit in 0..8u8 {
                bits.push(BitSource::Bit { op: src, byte, bit });
            }
        }
    }
    for byte in 8..16u8 {
        for bit in 0..8u8 {
            bits.push(BitSource::Bit { op: src, byte, bit });
        }
    }
    bits
}

/// SDM Vol 2B PMOVMSKB (`66 0F D7 /r`): `DEST[0] <- SRC[7]; DEST[1] <- SRC[15];
/// ...; DEST[15] <- SRC[127]; DEST[31:16] <- ZERO_FILL`, and in 64-bit mode the
/// 32-bit destination zero-extends (Vol 1 §3.4.1.1), so `DEST[63:32]` is zero
/// as well. The denotation is 64 bits wide precisely so that the
/// zero-extension is a compared facet rather than an assumption.
fn sdm_pmovmskb(src: Operand) -> Vec<BitSource> {
    let mut bits: Vec<BitSource> = (0..16u8)
        .map(|i| BitSource::Bit {
            op: src,
            byte: i,
            bit: 7,
        })
        .collect();
    bits.resize(64, BitSource::Zero);
    bits
}

/// The PACK family's routing: the low half of the result narrows every element
/// of `DEST`, the high half every element of `SRC`.
///
/// `in_bits` is the source element width (16 for PACKUSWB/PACKSSWB, 32 for
/// PACKSSDW) and `out_bits` its half.
fn sdm_pack(d_op: Operand, s_op: Operand, in_bits: u8, unsigned: bool) -> Vec<BitSource> {
    let out_bits = in_bits / 2;
    let n = 128 / u32::from(in_bits);
    let mut bits = Vec::with_capacity(128);
    for op in [d_op, s_op] {
        for elem in 0..n as u8 {
            for bit in 0..out_bits {
                bits.push(BitSource::Sat {
                    op,
                    elem,
                    in_bits,
                    out_bits,
                    unsigned,
                    bit,
                });
            }
        }
    }
    bits
}

/// SDM Vol 2B PBLENDVB (`66 0F 38 10 /r`): `MASK <- XMM0; IF (MASK[7] = 1) THEN
/// DEST[7:0] <- SRC[7:0]; ELSE DEST[7:0] <- DEST[7:0];` and so on per byte with
/// `MASK[15]`, `MASK[23]`, ..., `MASK[127]` — i.e. the SIGN BIT of each mask
/// byte. `mask_granule_bytes` is 1 here; BLENDVPS uses 4 and BLENDVPD 8, so the
/// control bit moves to the granule's top byte.
fn sdm_blendv(d_op: Operand, s_op: Operand, mask_granule_bytes: u8) -> Vec<BitSource> {
    let mut bits = Vec::with_capacity(128);
    for byte in 0..16u8 {
        let granule = byte / mask_granule_bytes;
        let ctl_byte = granule * mask_granule_bytes + (mask_granule_bytes - 1);
        for bit in 0..8u8 {
            bits.push(BitSource::Select {
                ctl: Operand::Xmm(0),
                ctl_byte,
                ctl_bit: 7,
                one: BitRef {
                    op: s_op,
                    byte,
                    bit,
                },
                zero: BitRef {
                    op: d_op,
                    byte,
                    bit,
                },
            });
        }
    }
    bits
}

/// SDM Vol 2B PTEST (`66 0F 38 17 /r`), transcribed:
///
/// ```text
/// IF (TEMP128[127:0] BITWISE AND DEST[127:0]) = 0 THEN ZF <- 1; ELSE ZF <- 0;
/// IF (TEMP128[127:0] BITWISE AND NOT DEST[127:0]) = 0 THEN CF <- 1; ELSE CF <- 0;
/// AF <- OF <- PF <- SF <- 0;
/// ```
///
/// with `TEMP128 <- SRC` (the r/m operand) and `DEST` the ModRM.reg operand.
/// The fold runs over all 128 bit positions; the low-half-only control differs
/// exactly in that range.
pub const fn sdm_ptest_flags() -> FlagDenot {
    FlagDenot {
        cf: FlagExpr::AllClear {
            a: FlagOperand::RmField,
            a_not: false,
            b: FlagOperand::RegField,
            b_not: true,
            lo: 0,
            hi: 128,
        },
        pf: FlagExpr::Clear,
        af: FlagExpr::Clear,
        zf: FlagExpr::AllClear {
            a: FlagOperand::RmField,
            a_not: false,
            b: FlagOperand::RegField,
            b_not: false,
            lo: 0,
            hi: 128,
        },
        sf: FlagExpr::Clear,
        of: FlagExpr::Clear,
    }
}

/// The ModRM.reg operand as an XMM source.
fn reg_operand(d: &DecodedSse) -> Result<Operand, SseModelError> {
    if d.mnemonic.reg_field_is_gpr() {
        return Err(SseModelError::RegFieldIsGpr);
    }
    Ok(Operand::Xmm(d.reg))
}

/// The ModRM.r/m operand as a value source.
fn rm_operand(d: &DecodedSse) -> Operand {
    match d.rm {
        SseRm::Reg(r) => Operand::Xmm(r),
        SseRm::Mem { base, disp, .. } => Operand::Mem { base, disp },
    }
}

/// THE MACHINE SIDE: what the DECODED instruction does, from the SDM's
/// Operation text alone.
///
/// Nothing here looks at the machine-IR intent, at a trust-cg opcode, or at the
/// encoder. It sees only a [`DecodedSse`], which itself saw only bytes.
pub fn machine_denotation(d: &DecodedSse) -> Result<Denotation, SseModelError> {
    use SseMnemonic as M;
    let table = |t: &[(Field, u8); 16]| -> Result<Denotation, SseModelError> {
        let dv = reg_operand(d)?;
        let sv = rm_operand(d);
        Ok(Denotation::Value(ValueDenot {
            dest: Dest::Xmm(d.reg),
            bits: bytes_table_to_bits(t, dv, sv),
        }))
    };
    match d.mnemonic {
        M::PunpcklbwX => table(&SDM_PUNPCKLBW),
        M::PunpckhbwX => table(&SDM_PUNPCKHBW),
        M::PunpcklwdX => table(&SDM_PUNPCKLWD),
        M::PunpckhwdX => table(&SDM_PUNPCKHWD),
        M::PunpckldqX => table(&SDM_PUNPCKLDQ),
        M::PunpckhdqX => table(&SDM_PUNPCKHDQ),
        M::PunpcklqdqX => table(&SDM_PUNPCKLQDQ),
        M::PunpckhqdqX => table(&SDM_PUNPCKHQDQ),
        M::PackuswbX | M::PacksswbX | M::PackssdwX => {
            let dv = reg_operand(d)?;
            let sv = rm_operand(d);
            let (in_bits, unsigned) = match d.mnemonic {
                M::PackuswbX => (16u8, true),
                M::PacksswbX => (16u8, false),
                _ => (32u8, false),
            };
            Ok(Denotation::Value(ValueDenot {
                dest: Dest::Xmm(d.reg),
                bits: sdm_pack(dv, sv, in_bits, unsigned),
            }))
        }
        M::MovdqaLoad | M::MovdquLoad => Ok(Denotation::Value(ValueDenot {
            dest: Dest::Xmm(d.reg),
            bits: copy_128(rm_operand(d)),
        })),
        M::MovdqaStore | M::MovdquStore => {
            let dest = match d.rm {
                SseRm::Reg(r) => Dest::Xmm(r),
                SseRm::Mem { base, disp, .. } => Dest::Mem { base, disp },
            };
            Ok(Denotation::Value(ValueDenot {
                dest,
                bits: copy_128(reg_operand(d)?),
            }))
        }
        M::MovqZeroUpper => Ok(Denotation::Value(ValueDenot {
            dest: Dest::Xmm(d.reg),
            bits: movq_zero_upper(rm_operand(d)),
        })),
        M::PshufdX | M::PshufhwX | M::PshuflwX => {
            let imm = d.imm8.ok_or(SseModelError::MissingImm8)?;
            let src = rm_operand(d);
            let bits = match d.mnemonic {
                M::PshufdX => sdm_pshufd(src, imm),
                M::PshufhwX => sdm_pshufhw(src, imm),
                _ => sdm_pshuflw(src, imm),
            };
            Ok(Denotation::Value(ValueDenot {
                dest: Dest::Xmm(d.reg),
                bits,
            }))
        }
        M::PmovmskbX => {
            let SseRm::Reg(src) = d.rm else {
                return Err(SseModelError::RegisterOperandRequired);
            };
            Ok(Denotation::Value(ValueDenot {
                dest: Dest::Gpr64(d.reg),
                bits: sdm_pmovmskb(Operand::Xmm(src)),
            }))
        }
        M::PblendvbX | M::BlendvpsX | M::BlendvpdX => {
            let granule = match d.mnemonic {
                M::PblendvbX => 1u8,
                M::BlendvpsX => 4u8,
                _ => 8u8,
            };
            Ok(Denotation::Value(ValueDenot {
                dest: Dest::Xmm(d.reg),
                bits: sdm_blendv(reg_operand(d)?, rm_operand(d), granule),
            }))
        }
        M::PtestX => Ok(Denotation::Flags {
            denot: sdm_ptest_flags(),
            reg_op: reg_operand(d)?,
            rm_op: rm_operand(d),
        }),
        M::MmxForm(opcode) => Err(SseModelError::MmxFormNotModelled { opcode }),
    }
}

// ===========================================================================
// (5) The SOURCE side: the machine-IR intent, stated parametrically
// ===========================================================================

/// The ten trust-cg x86 opcodes this family credits.
///
/// This enum is the machine-IR vocabulary. It never carries an opcode byte, a
/// prefix or a register number — those live on the machine side only.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SseLaneOp {
    /// `X86Opcode::Punpcklbw`.
    Punpcklbw,
    /// `X86Opcode::Punpckhbw`.
    Punpckhbw,
    /// `X86Opcode::Punpckldq`.
    Punpckldq,
    /// `X86Opcode::Punpcklqdq`.
    Punpcklqdq,
    /// `X86Opcode::Pshufd`.
    Pshufd,
    /// `X86Opcode::MovdqaRR`.
    MovdqaRR,
    /// `X86Opcode::Pmovmskb`.
    Pmovmskb,
    /// `X86Opcode::Packuswb`.
    Packuswb,
    /// `X86Opcode::Pblendvb`.
    Pblendvb,
    /// `X86Opcode::Ptest`.
    Ptest,
}

/// Every row this family owns, in gate order.
pub const SSE_LANE_ROWS: [SseLaneOp; 10] = [
    SseLaneOp::Pshufd,
    SseLaneOp::Pmovmskb,
    SseLaneOp::MovdqaRR,
    SseLaneOp::Punpckldq,
    SseLaneOp::Punpcklqdq,
    SseLaneOp::Punpcklbw,
    SseLaneOp::Punpckhbw,
    SseLaneOp::Ptest,
    SseLaneOp::Pblendvb,
    SseLaneOp::Packuswb,
];

/// The trust-cg opcode this row is.
pub fn x86_opcode_of(op: SseLaneOp) -> X86Opcode {
    match op {
        SseLaneOp::Punpcklbw => X86Opcode::Punpcklbw,
        SseLaneOp::Punpckhbw => X86Opcode::Punpckhbw,
        SseLaneOp::Punpckldq => X86Opcode::Punpckldq,
        SseLaneOp::Punpcklqdq => X86Opcode::Punpcklqdq,
        SseLaneOp::Pshufd => X86Opcode::Pshufd,
        SseLaneOp::MovdqaRR => X86Opcode::MovdqaRR,
        SseLaneOp::Pmovmskb => X86Opcode::Pmovmskb,
        SseLaneOp::Packuswb => X86Opcode::Packuswb,
        SseLaneOp::Pblendvb => X86Opcode::Pblendvb,
        SseLaneOp::Ptest => X86Opcode::Ptest,
    }
}

/// The row an emitted x86 opcode belongs to, if this family owns it.
pub fn sse_lane_op_of(opcode: X86Opcode) -> Option<SseLaneOp> {
    SSE_LANE_ROWS
        .iter()
        .copied()
        .find(|&r| x86_opcode_of(r) == opcode)
}

/// WHICH SDM INSTRUCTION a trust-cg opcode CLAIMS to be.
///
/// Transcribed from the opcode's own documented name in `trust-cg-ir`'s
/// `x86_64_ops.rs` — variant name to SDM NAME, never to bytes. It is the first
/// conjunct of the obligation: a row is refuted outright when the emitted bytes
/// decode to some other instruction, which is how the dropped-`66` (MMX),
/// `F3`-for-`66` (MOVDQU / PSHUFHW) and `6F`-for-`7F` (direction) mutants
/// refute.
pub fn row_mnemonic(op: SseLaneOp) -> SseMnemonic {
    match op {
        SseLaneOp::Punpcklbw => SseMnemonic::PunpcklbwX,
        SseLaneOp::Punpckhbw => SseMnemonic::PunpckhbwX,
        SseLaneOp::Punpckldq => SseMnemonic::PunpckldqX,
        SseLaneOp::Punpcklqdq => SseMnemonic::PunpcklqdqX,
        SseLaneOp::Pshufd => SseMnemonic::PshufdX,
        SseLaneOp::MovdqaRR => SseMnemonic::MovdqaLoad,
        SseLaneOp::Pmovmskb => SseMnemonic::PmovmskbX,
        SseLaneOp::Packuswb => SseMnemonic::PackuswbX,
        SseLaneOp::Pblendvb => SseMnemonic::PblendvbX,
        SseLaneOp::Ptest => SseMnemonic::PtestX,
    }
}

/// The machine IR's second operand: a register by NAME, or a spill slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntentOperand {
    /// A register, by assembly name (`"xmm3"`).
    Reg(&'static str),
    /// A 128-bit memory operand at `[base + disp]`, the base by name.
    Mem {
        /// Base register name (`"rbp"`).
        base: &'static str,
        /// Signed displacement.
        disp: i32,
    },
}

/// What the machine IR MEANT by one emitted instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SseIntent {
    /// Which trust-cg opcode.
    pub op: SseLaneOp,
    /// The destination register's NAME.
    pub dst: &'static str,
    /// The source operand.
    pub src: IntentOperand,
    /// For `Pshufd` only: the permutation instruction selection MEANT — result
    /// doubleword `j` takes source doubleword `perm[j]`. Stated as a
    /// PERMUTATION, never as the imm8, so that the machine side's ORDER-field
    /// packing is a compared facet.
    pub perm: Option<[u8; 4]>,
}

/// Why an intent has no denotation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SseIntentError {
    /// A register name that is not in the SDM tables.
    UnknownRegister(String),
    /// A `Pshufd` intent with no permutation.
    MissingPerm,
    /// A permutation naming a doubleword outside `0..=3`.
    PermOutOfRange([u8; 4]),
    /// A memory operand for a row that has none.
    MemoryOperandNotAllowed(SseLaneOp),
}

impl fmt::Display for SseIntentError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownRegister(n) => write!(f, "unknown register `{n}`"),
            Self::MissingPerm => write!(f, "a Pshufd intent carries no intended permutation"),
            Self::PermOutOfRange(p) => write!(f, "permutation {p:?} names a doubleword above 3"),
            Self::MemoryOperandNotAllowed(op) => write!(f, "{op:?} takes no memory operand"),
        }
    }
}

fn intent_src_operand(src: IntentOperand) -> Result<Operand, SseIntentError> {
    match src {
        IntentOperand::Reg(n) => sdm_xmm(n)
            .map(Operand::Xmm)
            .ok_or_else(|| SseIntentError::UnknownRegister(n.to_string())),
        IntentOperand::Mem { base, disp } => sdm_gpr64(base)
            .map(|b| Operand::Mem { base: b, disp })
            .ok_or_else(|| SseIntentError::UnknownRegister(base.to_string())),
    }
}

/// THE INTENT'S INTERLEAVE, stated parametrically.
///
/// "Take the `8 / elem_bytes` elements of width `elem_bytes` from the LOW
/// quadword (or, when `high`, the HIGH quadword) of each operand and alternate
/// them, destination element first." One generator covers all four PUNPCK rows;
/// the machine side is a LITERAL sixteen-entry transcription per opcode. A
/// transcription typo refutes against this, and a wrong `(elem_bytes, high)`
/// refutes against that.
fn spec_interleave(dst: Operand, src: Operand, elem_bytes: u8, high: bool) -> Vec<BitSource> {
    let per_operand = 8 / elem_bytes;
    let base = if high { 8u8 } else { 0u8 };
    let mut bits = Vec::with_capacity(128);
    for k in 0..per_operand {
        for op in [dst, src] {
            for b in 0..elem_bytes {
                let byte = base + k * elem_bytes + b;
                for bit in 0..8u8 {
                    bits.push(BitSource::Bit { op, byte, bit });
                }
            }
        }
    }
    bits
}

/// THE INTENT'S DOUBLEWORD PERMUTATION: "result doubleword `j` is source
/// doubleword `perm[j]`". Stated over the PERMUTATION, never over an immediate.
fn spec_permute_dwords(src: Operand, perm: [u8; 4]) -> Vec<BitSource> {
    let mut bits = Vec::with_capacity(128);
    for &p in &perm {
        for b in 0..4u8 {
            let byte = 4 * p + b;
            for bit in 0..8u8 {
                bits.push(BitSource::Bit { op: src, byte, bit });
            }
        }
    }
    bits
}

/// THE INTENT'S SIGN-BIT GATHER: "bit `i` of the 32-bit result is the SIGN BIT
/// of byte `i` of the source; the remaining result bits are zero, and a 32-bit
/// destination zero-extends to 64."
fn spec_sign_bit_gather(src: Operand) -> Vec<BitSource> {
    let mut bits = Vec::with_capacity(64);
    for i in 0..16u8 {
        bits.push(BitSource::Bit {
            op: src,
            byte: i,
            bit: 7,
        });
    }
    while bits.len() < 64 {
        bits.push(BitSource::Zero);
    }
    bits
}

/// THE INTENT'S UNSIGNED-SATURATING PACK: "result byte `i` is the
/// unsigned-saturating narrow of word `i` of the destination for the low eight
/// bytes, and of word `i - 8` of the source for the high eight."
///
/// The narrowing FUNCTION is not asserted here; [`saturation_obligation`]
/// settles it over all 65536 inputs.
fn spec_pack_unsigned_narrow(dst: Operand, src: Operand) -> Vec<BitSource> {
    let mut bits = Vec::with_capacity(128);
    for i in 0..16u8 {
        let (op, elem) = if i < 8 { (dst, i) } else { (src, i - 8) };
        for bit in 0..8u8 {
            bits.push(BitSource::Sat {
                op,
                elem,
                in_bits: 16,
                out_bits: 8,
                unsigned: true,
                bit,
            });
        }
    }
    bits
}

/// THE INTENT'S BYTE BLEND: "for each byte position, take the source byte when
/// the corresponding MASK byte is negative, otherwise keep the destination
/// byte; the mask is the implicit XMM0."
fn spec_byte_blend(dst: Operand, src: Operand, mask: Operand) -> Vec<BitSource> {
    let mut bits = Vec::with_capacity(128);
    for byte in 0..16u8 {
        for bit in 0..8u8 {
            bits.push(BitSource::Select {
                ctl: mask,
                ctl_byte: byte,
                ctl_bit: 7,
                one: BitRef { op: src, byte, bit },
                zero: BitRef { op: dst, byte, bit },
            });
        }
    }
    bits
}

/// THE INTENT'S 128-BIT COPY: "every one of the sixteen destination bytes is
/// the source byte at the same index."
fn spec_copy_128(src: Operand) -> Vec<BitSource> {
    let mut bits = Vec::with_capacity(128);
    for byte in 0..16u8 {
        for bit in 0..8u8 {
            bits.push(BitSource::Bit { op: src, byte, bit });
        }
    }
    bits
}

/// THE SOURCE SIDE: what the machine IR MEANT, from the intent alone.
///
/// Nothing here looks at a byte, an opcode byte, a prefix, a REX bit or an
/// encoder register number. The only path from a NAME to a NUMBER is the SDM
/// register tables in section 1.
pub fn intent_denotation(intent: &SseIntent) -> Result<Denotation, SseIntentError> {
    let dst_xmm = || {
        sdm_xmm(intent.dst).ok_or_else(|| SseIntentError::UnknownRegister(intent.dst.to_string()))
    };
    let src_op = intent_src_operand(intent.src)?;
    let reg_only = |op: SseLaneOp| match src_op {
        Operand::Xmm(_) => Ok(()),
        Operand::Mem { .. } => Err(SseIntentError::MemoryOperandNotAllowed(op)),
    };
    match intent.op {
        SseLaneOp::Punpcklbw
        | SseLaneOp::Punpckhbw
        | SseLaneOp::Punpckldq
        | SseLaneOp::Punpcklqdq => {
            let dst = Operand::Xmm(dst_xmm()?);
            let (elem_bytes, high) = match intent.op {
                SseLaneOp::Punpcklbw => (1u8, false),
                SseLaneOp::Punpckhbw => (1u8, true),
                SseLaneOp::Punpckldq => (4u8, false),
                _ => (8u8, false),
            };
            Ok(Denotation::Value(ValueDenot {
                dest: Dest::Xmm(dst_xmm()?),
                bits: spec_interleave(dst, src_op, elem_bytes, high),
            }))
        }
        SseLaneOp::Pshufd => {
            let perm = intent.perm.ok_or(SseIntentError::MissingPerm)?;
            if perm.iter().any(|&p| p > 3) {
                return Err(SseIntentError::PermOutOfRange(perm));
            }
            Ok(Denotation::Value(ValueDenot {
                dest: Dest::Xmm(dst_xmm()?),
                bits: spec_permute_dwords(src_op, perm),
            }))
        }
        SseLaneOp::MovdqaRR => {
            reg_only(intent.op)?;
            Ok(Denotation::Value(ValueDenot {
                dest: Dest::Xmm(dst_xmm()?),
                bits: spec_copy_128(src_op),
            }))
        }
        SseLaneOp::Pmovmskb => {
            reg_only(intent.op)?;
            let dst = sdm_gpr32(intent.dst)
                .ok_or_else(|| SseIntentError::UnknownRegister(intent.dst.to_string()))?;
            Ok(Denotation::Value(ValueDenot {
                dest: Dest::Gpr64(dst),
                bits: spec_sign_bit_gather(src_op),
            }))
        }
        SseLaneOp::Packuswb => Ok(Denotation::Value(ValueDenot {
            dest: Dest::Xmm(dst_xmm()?),
            bits: spec_pack_unsigned_narrow(Operand::Xmm(dst_xmm()?), src_op),
        })),
        SseLaneOp::Pblendvb => {
            reg_only(intent.op)?;
            let dst = Operand::Xmm(dst_xmm()?);
            Ok(Denotation::Value(ValueDenot {
                dest: Dest::Xmm(dst_xmm()?),
                bits: spec_byte_blend(dst, src_op, Operand::Xmm(0)),
            }))
        }
        SseLaneOp::Ptest => Ok(Denotation::FlagIntent {
            reg_op: Operand::Xmm(dst_xmm()?),
            rm_op: src_op,
        }),
    }
}

// ===========================================================================
// (6) PMOVMSKB's destination is a GPR — the intent names it by GPR name
// ===========================================================================

/// The SDM register NUMBER of a 32-bit GPR named `name`.
///
/// `PMOVMSKB r32, xmm` names its destination at 32-bit width in assembly; the
/// DENOTATION is stated over the 64-bit ROOT register, because a 32-bit write
/// zero-extends (Vol 1 3.4.1.1) and that zero-extension is a compared facet.
/// The table is `x86_encoding_proofs`' — the same SDM transcription the
/// MOV-immediate family already stands on, not a second copy of it.
pub fn sdm_gpr32(name: &str) -> Option<u8> {
    crate::x86_encoding_proofs::SDM_R32
        .iter()
        .position(|&n| n == name)
        .map(|i| i as u8)
}

// ===========================================================================
// (7) PACKUSWB's narrow, settled EXHAUSTIVELY
// ===========================================================================

/// SDM Vol 2B PACKUSWB, `SaturateSignedWordToUnsignedByte`, in the SDM's own
/// ARITHMETIC terms: a signed comparison against the two ends of the unsigned
/// byte range.
pub fn sdm_saturate_signed_word_to_unsigned_byte(w: u16) -> u8 {
    let s = w as i16;
    if s < 0 {
        0x00
    } else if s > 0xFF {
        0xFF
    } else {
        (s & 0xFF) as u8
    }
}

/// THE MACHINE IR'S formulation of the same narrow, stated as a BIT PATTERN
/// test: negative iff the sign bit is set; above range iff any bit of `w[14:8]`
/// is set; otherwise the low byte survives.
///
/// The two formulations share no operator: one compares signed integers against
/// `0` and `255`, the other masks three disjoint bit fields. That is what makes
/// [`saturation_obligation`] a comparison rather than a restatement.
pub fn intent_unsigned_narrow_byte(w: u16) -> u8 {
    if w & 0x8000 != 0 {
        0x00
    } else if w & 0x7F00 != 0 {
        0xFF
    } else {
        (w & 0x00FF) as u8
    }
}

/// A wrong narrowing model, for the negative controls.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NarrowControl {
    /// PACKSSWB's SIGNED saturation, clamped to `-128..=127`.
    SignedSaturate,
    /// Truncation with no saturation at all.
    Truncate,
    /// Treating the input as UNSIGNED, so `0x8000` becomes `0xFF` rather
    /// than `0x00`. This is the model a careless reading of "pack with
    /// unsigned saturation" produces.
    UnsignedInput,
    /// Clamping the low end to `1` rather than `0` — an off-by-one at the
    /// boundary that only an exhaustive sweep catches.
    LowBoundOffByOne,
}

impl NarrowControl {
    /// Every control, for the battery.
    pub const ALL: [NarrowControl; 4] = [
        NarrowControl::SignedSaturate,
        NarrowControl::Truncate,
        NarrowControl::UnsignedInput,
        NarrowControl::LowBoundOffByOne,
    ];

    /// Apply the wrong model.
    pub fn apply(self, w: u16) -> u8 {
        let s = w as i16;
        match self {
            Self::SignedSaturate => {
                if s < -128 {
                    0x80
                } else if s > 127 {
                    0x7F
                } else {
                    (s & 0xFF) as u8
                }
            }
            Self::Truncate => (w & 0x00FF) as u8,
            Self::UnsignedInput => {
                if w > 0xFF {
                    0xFF
                } else {
                    w as u8
                }
            }
            Self::LowBoundOffByOne => {
                if s < 0 {
                    0x01
                } else if s > 0xFF {
                    0xFF
                } else {
                    (s & 0xFF) as u8
                }
            }
        }
    }
}

/// THE PACKUSWB NARROW OBLIGATION, over ALL 65536 inputs.
///
/// `Ok(n)` reports how many inputs were checked — every one of them, which is
/// why this is EXHAUSTIVE and not statistical. `Err` names the first input on
/// which the SDM's arithmetic formulation and the machine IR's bit-pattern
/// formulation disagree. Every [`NarrowControl`] must also be REFUTED, i.e.
/// must differ from the SDM model on at least one input; a control that agreed
/// everywhere would mean the obligation cannot tell the two apart and the row
/// is not credited.
pub fn saturation_obligation() -> Result<usize, String> {
    for w in 0..=u16::MAX {
        let sdm = sdm_saturate_signed_word_to_unsigned_byte(w);
        let intent = intent_unsigned_narrow_byte(w);
        if sdm != intent {
            return Err(format!(
                "PACKUSWB narrow DIVERGES at w={w:#06x}: SDM arithmetic gives {sdm:#04x}, the \
                 machine-IR bit-pattern model gives {intent:#04x}"
            ));
        }
    }
    for c in NarrowControl::ALL {
        let witness =
            (0..=u16::MAX).find(|&w| c.apply(w) != sdm_saturate_signed_word_to_unsigned_byte(w));
        if witness.is_none() {
            return Err(format!(
                "narrow control {c:?} SURVIVED — it agrees with the SDM model on all 65536 \
                 inputs, so the obligation cannot distinguish it"
            ));
        }
    }
    Ok(usize::from(u16::MAX) + 1)
}

// ===========================================================================
// (8) PTEST's flag reduction, settled by EVALUATION
// ===========================================================================

/// Evaluate one machine-side [`FlagExpr`] on concrete operand values.
///
/// `reg_val` is the SDM's `DEST` (the ModRM.reg operand) and `rm_val` its
/// `SRC`. [`FlagExpr::AllClear`] is evaluated as the SDM writes it: a FOLD over
/// the individual bit positions in `lo..hi`.
pub fn eval_flag_expr(e: FlagExpr, reg_val: u128, rm_val: u128) -> bool {
    let pick = |o: FlagOperand| match o {
        FlagOperand::RegField => reg_val,
        FlagOperand::RmField => rm_val,
    };
    match e {
        FlagExpr::Clear => false,
        FlagExpr::Set => true,
        FlagExpr::AllClear {
            a,
            a_not,
            b,
            b_not,
            lo,
            hi,
        } => {
            let av = if a_not { !pick(a) } else { pick(a) };
            let bv = if b_not { !pick(b) } else { pick(b) };
            let and = av & bv;
            (lo..hi).all(|i| (and >> i) & 1 == 0)
        }
        FlagExpr::BitOf { a, b, bit } => ((pick(a) & pick(b)) >> bit) & 1 == 1,
        FlagExpr::ParityLow8 { a, b } => ((pick(a) & pick(b)) as u8).count_ones().is_multiple_of(2),
    }
}

/// Evaluate a whole machine-side [`FlagDenot`], in RFLAGS order.
pub fn eval_flag_denot(d: &FlagDenot, reg_val: u128, rm_val: u128) -> [bool; 6] {
    let a = d.as_array();
    [
        eval_flag_expr(a[0], reg_val, rm_val),
        eval_flag_expr(a[1], reg_val, rm_val),
        eval_flag_expr(a[2], reg_val, rm_val),
        eval_flag_expr(a[3], reg_val, rm_val),
        eval_flag_expr(a[4], reg_val, rm_val),
        eval_flag_expr(a[5], reg_val, rm_val),
    ]
}

/// THE SOURCE SIDE of PTEST, stated with WHOLE-128-BIT arithmetic.
///
/// The machine IR's intent for `PTEST dest, src` is "record whether the two
/// values have no bit in common (ZF), and whether the source's set bits are a
/// SUBSET of the destination's (CF); leave the other four status flags clear".
/// No bit index, no fold, no range: the contrast with the machine side's
/// per-bit fold over `lo..hi` is the whole reason a wrong RANGE — the
/// low-half-only control — is refutable.
///
/// Returned in RFLAGS order: `[CF, PF, AF, ZF, SF, OF]`.
pub fn intent_ptest_flags(dest: u128, src: u128) -> [bool; 6] {
    let zf = (src & dest) == 0;
    let cf = (src & !dest) == 0;
    [cf, false, false, zf, false, false]
}

/// The operand pairs PTEST's obligation is evaluated over, as `(DEST, SRC)`.
///
/// A naive random 128-bit sweep NEVER reaches `ZF = 1`: two uniformly random
/// 128-bit values share a set bit with overwhelming probability, so an
/// obligation sampled that way would accept a model that hard-wires `ZF = 0`.
/// The structured families below reach both polarities of both computed flags
/// and, crucially, distinguish the LOW from the HIGH half:
///
///   1. every ordered pair of single-bit operands, `(1 << i, 1 << j)` for all
///      `i, j < 128` — 16384 pairs, exhaustive over that family. `i != j`
///      gives `ZF = 1`; `i == j` gives `ZF = 0`. A model folding only
///      `0..64` disagrees on every pair with `i = j >= 64`;
///   2. every `(!(1 << i), 1 << j)` — 16384 pairs, which is what separates the
///      SDM's `SRC AND NOT DEST` from the transposed `DEST AND NOT SRC`;
///   3. the four all-zero / all-ones corners and the byte-boundary patterns;
///   4. a deterministic pseudo-random sweep, for anything the families miss.
pub fn ptest_witnesses() -> Vec<(u128, u128)> {
    let mut w = Vec::with_capacity(16384 * 2 + 1100);
    for i in 0..128u32 {
        for j in 0..128u32 {
            w.push((1u128 << i, 1u128 << j));
        }
    }
    for i in 0..128u32 {
        for j in 0..128u32 {
            w.push((!(1u128 << i), 1u128 << j));
        }
    }
    w.push((0, 0));
    w.push((!0, !0));
    w.push((0, !0));
    w.push((!0, 0));
    for k in 0..16u32 {
        let byte = 0xFFu128 << (8 * k);
        w.push((byte, byte));
        w.push((byte, !byte));
        w.push((!byte, byte));
    }
    // A deterministic xorshift128 sweep: reproducible, so a failure is
    // reproducible, and seeded away from the structured families above.
    let mut s0: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut s1: u64 = 0xBF58_476D_1CE4_E5B9;
    let mut next = || {
        let mut x = s0;
        let y = s1;
        s0 = y;
        x ^= x << 23;
        s1 = x ^ y ^ (x >> 17) ^ (y >> 26);
        s1.wrapping_add(y)
    };
    for _ in 0..512 {
        let a = (u128::from(next()) << 64) | u128::from(next());
        let b = (u128::from(next()) << 64) | u128::from(next());
        w.push((a, b));
        // Also a pair guaranteed disjoint, so ZF = 1 is reached off the
        // structured families as well.
        w.push((a, !a & b));
    }
    w
}

/// A wrong PTEST flag model, for the negative controls.
///
/// Each is a [`FlagDenot`] that must DIVERGE from [`intent_ptest_flags`] on at
/// least one witness. A control that agreed on every witness would mean the
/// witness family cannot see the facet it corrupts, and the row is not
/// credited.
pub fn ptest_flag_controls() -> Vec<(&'static str, FlagDenot, bool)> {
    let base = sdm_ptest_flags();
    let all_clear = |a, a_not, b, b_not, lo, hi| FlagExpr::AllClear {
        a,
        a_not,
        b,
        b_not,
        lo,
        hi,
    };
    use FlagOperand::{RegField, RmField};
    vec![
        (
            "ZF folded over the LOW HALF only — caught by a single-bit witness \
             pair with i = j >= 64",
            FlagDenot {
                zf: all_clear(RmField, false, RegField, false, 0, 64),
                ..base
            },
            true,
        ),
        (
            "CF's asymmetry TRANSPOSED (DEST AND NOT SRC instead of SRC AND NOT \
             DEST) — caught by the complement family",
            FlagDenot {
                cf: all_clear(RegField, false, RmField, true, 0, 128),
                ..base
            },
            true,
        ),
        (
            "the scalar TEST model: CF cleared, SF the top bit of the AND, PF the \
             parity of its low byte",
            FlagDenot {
                cf: FlagExpr::Clear,
                sf: FlagExpr::BitOf {
                    a: RmField,
                    b: RegField,
                    bit: 127,
                },
                pf: FlagExpr::ParityLow8 {
                    a: RmField,
                    b: RegField,
                },
                ..base
            },
            true,
        ),
        (
            "SF not cleared",
            FlagDenot {
                sf: FlagExpr::BitOf {
                    a: RmField,
                    b: RegField,
                    bit: 127,
                },
                ..base
            },
            true,
        ),
        (
            "PF not cleared",
            FlagDenot {
                pf: FlagExpr::ParityLow8 {
                    a: RmField,
                    b: RegField,
                },
                ..base
            },
            true,
        ),
        (
            "ZF and CF EXCHANGED",
            FlagDenot {
                zf: base.cf,
                cf: base.zf,
                ..base
            },
            true,
        ),
        (
            "ZF hard-wired to 0 — the model a random 128-bit sweep cannot refute",
            FlagDenot {
                zf: FlagExpr::Clear,
                ..base
            },
            true,
        ),
        (
            "CF hard-wired to 1. NOTE: for the SELF-TEST `PTEST m, m` the \
             pipeline actually emits, CF = 1 IS correct — `m AND NOT m` is \
             always zero — so this control is only meaningful against \
             DISTINCT operands, and the witness family supplies them",
            FlagDenot {
                cf: FlagExpr::Set,
                ..base
            },
            true,
        ),
    ]
}

/// THE PTEST FLAG OBLIGATION.
///
/// `Ok(n)` reports how many witnesses agreed — all of them. `Err` names the
/// first witness on which the SDM's per-bit fold and the machine IR's
/// whole-128-bit intent disagree, or names a control that SURVIVED the whole
/// witness family.
///
/// This is the one row of the family compared by EVALUATION rather than by an
/// exact denotation, because a reduction to flags has no bit table. It is
/// exhaustive over the structured families and statistical beyond them —
/// evidence, not a formal proof.
pub fn ptest_obligation() -> Result<usize, String> {
    let machine = sdm_ptest_flags();
    let witnesses = ptest_witnesses();
    ptest_flags_agree(&machine, &witnesses)?;
    for (label, control, _) in ptest_flag_controls() {
        let refuted = witnesses.iter().any(|&(dest, src)| {
            eval_flag_denot(&control, dest, src) != intent_ptest_flags(dest, src)
        });
        if !refuted {
            return Err(format!(
                "PTEST flag control SURVIVED the whole witness family — `{label}`: it agrees with \
                 the intent on all {} witnesses, so the obligation cannot distinguish it",
                witnesses.len()
            ));
        }
    }
    Ok(witnesses.len())
}

/// THE PTEST FLAG OBLIGATION over the model the BYTES decoded to.
///
/// [`denotations_agree`] calls this with the [`FlagDenot`] that
/// [`machine_denotation`] built for the real decoded instruction, so a
/// corrupted `PtestX` arm is a REFUTATION rather than dead data. When that
/// model is literally the SDM transcription the memoised verdict is reused —
/// structural equality with [`sdm_ptest_flags`] is a STRICTER test than
/// agreement on the witness family, so the memo can only ever be taken on a
/// model the full run would also accept.
pub fn ptest_obligation_for(machine: &FlagDenot) -> Result<usize, String> {
    if *machine == sdm_ptest_flags() {
        return ptest_obligation_cached();
    }
    ptest_flags_agree(machine, &ptest_witnesses())
}

/// Evaluate one flag model against [`intent_ptest_flags`] on every witness.
///
/// `Ok(n)` reports how many witnesses agreed — all of them. `Err` names the
/// first witness they disagree on and which flags differ.
pub fn ptest_flags_agree(machine: &FlagDenot, witnesses: &[(u128, u128)]) -> Result<usize, String> {
    for &(dest, src) in witnesses {
        let m = eval_flag_denot(machine, dest, src);
        let i = intent_ptest_flags(dest, src);
        if m != i {
            let which = FlagDenot::NAMES
                .iter()
                .zip(m.iter().zip(i.iter()))
                .filter(|(_, (a, b))| a != b)
                .map(|(n, _)| *n)
                .collect::<Vec<_>>()
                .join(",");
            return Err(format!(
                "PTEST flags DIVERGE on DEST={dest:#034x} SRC={src:#034x}: the SDM per-bit fold \
                 gives {m:?}, the machine-IR whole-128-bit intent gives {i:?} (differing: {which})"
            ));
        }
    }
    Ok(witnesses.len())
}

// ===========================================================================
// (9) The obligation
// ===========================================================================

/// Why the bytes do not denote what the machine IR meant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SseRefutation {
    /// The bytes are not a modelled instruction at all.
    Decode(SseDecodeError),
    /// The encoding is longer than the SDM's minimal spelling of the same
    /// instruction: a redundant REX, an over-wide displacement, a gratuitous
    /// SIB.
    NonCanonicalLength {
        /// The real encoding's length.
        actual: usize,
        /// The minimal length.
        canonical: usize,
    },
    /// The bytes decode to a DIFFERENT instruction than the trust-cg opcode
    /// claims to be.
    WrongMnemonic {
        /// What `row_mnemonic` says the opcode is.
        expected: SseMnemonic,
        /// What the bytes actually are.
        decoded: SseMnemonic,
    },
    /// The decoded instruction has no denotation in this family.
    MachineHasNoModel(SseModelError),
    /// The intent has no denotation.
    IntentHasNoModel(SseIntentError),
    /// One side produces a value and the other flags.
    ShapeMismatch {
        /// What the intent produces.
        intent: &'static str,
        /// What the machine produces.
        machine: &'static str,
    },
    /// The two sides write to different places.
    WrongDest {
        /// Where the intent writes.
        intent: Dest,
        /// Where the bytes write.
        machine: Dest,
    },
    /// The two sides write results of different widths.
    WrongWidth {
        /// The intent's result width in bits.
        intent: usize,
        /// The machine's result width in bits.
        machine: usize,
    },
    /// The two sides route a result bit from different places. This is the
    /// VALUE refutation: a wrong half, a wrong element width, transposed
    /// operands, a corrupted ORDER field, a mask taken from the wrong register.
    DivergentBit {
        /// Which result bit, counting from the least significant.
        index: usize,
        /// What the intent says that bit is.
        intent: BitSource,
        /// What the bytes say it is.
        machine: BitSource,
    },
    /// A flag-writing instruction reads different operands on the two sides.
    WrongFlagOperands {
        /// The intent's `(DEST, SRC)`.
        intent: (Operand, Operand),
        /// The machine's `(DEST, SRC)`.
        machine: (Operand, Operand),
    },
    /// A flag-writing instruction's two sides disagree on some witness.
    DivergentFlags(String),
}

impl fmt::Display for SseRefutation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Decode(e) => write!(f, "decode refused: {e}"),
            Self::NonCanonicalLength { actual, canonical } => write!(
                f,
                "non-canonical encoding: {actual} bytes where the SDM's minimal spelling is \
                 {canonical}"
            ),
            Self::WrongMnemonic { expected, decoded } => write!(
                f,
                "the bytes are {}, but the machine IR named {}",
                decoded.name(),
                expected.name()
            ),
            Self::MachineHasNoModel(e) => write!(f, "the decoded instruction has no model: {e}"),
            Self::IntentHasNoModel(e) => write!(f, "the intent has no model: {e}"),
            Self::ShapeMismatch { intent, machine } => {
                write!(
                    f,
                    "the intent produces {intent}, the bytes produce {machine}"
                )
            }
            Self::WrongDest { intent, machine } => {
                write!(
                    f,
                    "destination differs: intent {intent:?}, bytes {machine:?}"
                )
            }
            Self::WrongWidth { intent, machine } => write!(
                f,
                "result width differs: intent {intent} bits, bytes {machine} bits"
            ),
            Self::DivergentBit {
                index,
                intent,
                machine,
            } => write!(
                f,
                "result bit {index} differs: intent {intent:?}, bytes {machine:?}"
            ),
            Self::WrongFlagOperands { intent, machine } => write!(
                f,
                "flag operands differ: intent {intent:?}, bytes {machine:?}"
            ),
            Self::DivergentFlags(m) => write!(f, "{m}"),
        }
    }
}

/// The reason CLASS a negative control must refute as.
///
/// Every control names one of these, and the hook refuses a control that
/// refutes for a different reason — a mutant that was meant to corrupt the
/// routing but actually made the bytes undecodable proves nothing about the
/// routing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SseRefutationClass {
    /// The bytes are not a modelled instruction.
    Decode,
    /// The encoding is not the minimal spelling.
    Canonicality,
    /// The bytes are some OTHER instruction.
    Mnemonic,
    /// One side has no model.
    Model,
    /// The destinations differ.
    Dest,
    /// The routed VALUE differs.
    Value,
    /// The FLAG effect differs.
    Flags,
}

impl SseRefutation {
    /// Which class this refutation is.
    pub fn class(&self) -> SseRefutationClass {
        match self {
            Self::Decode(_) => SseRefutationClass::Decode,
            Self::NonCanonicalLength { .. } => SseRefutationClass::Canonicality,
            Self::WrongMnemonic { .. } => SseRefutationClass::Mnemonic,
            Self::MachineHasNoModel(_) | Self::IntentHasNoModel(_) => SseRefutationClass::Model,
            Self::WrongDest { .. } => SseRefutationClass::Dest,
            Self::ShapeMismatch { .. } | Self::WrongWidth { .. } | Self::DivergentBit { .. } => {
                SseRefutationClass::Value
            }
            Self::WrongFlagOperands { .. } | Self::DivergentFlags(_) => SseRefutationClass::Flags,
        }
    }
}

/// What one holding obligation established.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SseLaneHolds {
    /// The instruction the bytes decoded to.
    pub decoded: DecodedSse,
    /// How many result bits were compared (0 for a flag row).
    pub bits_compared: usize,
    /// How many flag witnesses agreed (0 for a value row).
    pub flag_witnesses: usize,
}

/// [`ptest_obligation`], computed once per process.
///
/// PTEST's flag model does not depend on WHICH registers an instance names, so
/// the whole witness family is the same computation for every instance; running
/// it once and reusing the verdict is a memoisation, not a weakening.
fn ptest_obligation_cached() -> Result<usize, String> {
    use std::sync::OnceLock;
    static ONCE: OnceLock<Result<usize, String>> = OnceLock::new();
    ONCE.get_or_init(ptest_obligation).clone()
}

/// THE OBLIGATION: do these emitted BYTES denote what this machine-IR
/// instruction MEANT?
///
/// The conjuncts, in order, each refutable on its own:
///
///   1. the bytes DECODE, under the independent SDM-derived decoder;
///   2. the encoding is the SDM's MINIMAL spelling of that instruction;
///   3. the decoded instruction IS the one the trust-cg opcode names;
///   4. both sides have a denotation;
///   5. they write to the SAME destination, a result of the SAME width;
///   6. every result bit is routed from the SAME place — or, for the flag row,
///      the same operands are read and the two flag formulations agree on every
///      witness.
pub fn sse_lane_check(intent: &SseIntent, bytes: &[u8]) -> Result<SseLaneHolds, SseRefutation> {
    let decoded = sdm_decode_sse(bytes).map_err(SseRefutation::Decode)?;

    let canonical = canonical_len(&decoded);
    if decoded.len != canonical {
        return Err(SseRefutation::NonCanonicalLength {
            actual: decoded.len,
            canonical,
        });
    }

    let expected = row_mnemonic(intent.op);
    if decoded.mnemonic != expected {
        return Err(SseRefutation::WrongMnemonic {
            expected,
            decoded: decoded.mnemonic,
        });
    }

    let machine = machine_denotation(&decoded).map_err(SseRefutation::MachineHasNoModel)?;
    let source = intent_denotation(intent).map_err(SseRefutation::IntentHasNoModel)?;

    let (bits_compared, flag_witnesses) = denotations_agree(&source, &machine)?;
    Ok(SseLaneHolds {
        decoded,
        bits_compared,
        flag_witnesses,
    })
}

/// THE COMPARISON, on its own.
///
/// [`sse_lane_check`] is "decode, check the framing, then run THIS"; the
/// wrong-model controls in [`model_control_is_refuted`] run THIS too, against
/// the same source side with a corrupted machine model in between. That is
/// deliberate and was a repair: while the controls compared the two sides with
/// a bare `!=`, a control on the flag row "refuted" merely because
/// `Denotation::Flags` and `Denotation::FlagIntent` are different enum
/// variants, without the operands or the flag model ever being read. A control
/// is only evidence about a facet if it fails the SAME comparison the
/// obligation makes, for a REASON — hence [`SseRefutationClass`] on both
/// batteries.
///
/// Returns `(result bits compared, flag witnesses agreed on)`.
pub fn denotations_agree(
    source: &Denotation,
    machine: &Denotation,
) -> Result<(usize, usize), SseRefutation> {
    match (source, machine) {
        (Denotation::Value(s), Denotation::Value(m)) => {
            if s.dest != m.dest {
                return Err(SseRefutation::WrongDest {
                    intent: s.dest,
                    machine: m.dest,
                });
            }
            if s.bits.len() != m.bits.len() {
                return Err(SseRefutation::WrongWidth {
                    intent: s.bits.len(),
                    machine: m.bits.len(),
                });
            }
            for (index, (sb, mb)) in s.bits.iter().zip(m.bits.iter()).enumerate() {
                if sb != mb {
                    return Err(SseRefutation::DivergentBit {
                        index,
                        intent: *sb,
                        machine: *mb,
                    });
                }
            }
            Ok((s.bits.len(), 0))
        }
        (
            Denotation::FlagIntent {
                reg_op: s_reg,
                rm_op: s_rm,
            },
            Denotation::Flags {
                denot,
                reg_op: m_reg,
                rm_op: m_rm,
            },
        ) => {
            if (s_reg, s_rm) != (m_reg, m_rm) {
                return Err(SseRefutation::WrongFlagOperands {
                    intent: (*s_reg, *s_rm),
                    machine: (*m_reg, *m_rm),
                });
            }
            // THE DECODED MODEL, not the constant. Before this repair the
            // obligation called `ptest_obligation_cached()`, which rebuilds
            // `sdm_ptest_flags()` from scratch, so `machine_denotation`'s
            // `PtestX` arm could have been edited to return any flag model at
            // all and the row would have stayed green — the one place in this
            // family where a machine-side model was carried but never read.
            let witnesses = ptest_obligation_for(denot).map_err(SseRefutation::DivergentFlags)?;
            Ok((0, witnesses))
        }
        (s, m) => Err(SseRefutation::ShapeMismatch {
            intent: match s {
                Denotation::Value(_) => "a value",
                _ => "flags",
            },
            machine: match m {
                Denotation::Value(_) => "a value",
                _ => "flags",
            },
        }),
    }
}

// ===========================================================================
// (10) The captured corpus
// ===========================================================================

/// One real emitted encoding, with the intent that produced it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EmittedSseLane {
    /// Which row.
    pub op: SseLaneOp,
    /// The destination register's name.
    pub dst: &'static str,
    /// The source operand.
    pub src: IntentOperand,
    /// The intended permutation, for `Pshufd`.
    pub perm: Option<[u8; 4]>,
    /// The bytes the REAL encoder emitted.
    pub bytes: &'static [u8],
}

impl EmittedSseLane {
    /// The machine-IR intent this entry carries.
    pub fn intent(&self) -> SseIntent {
        SseIntent {
            op: self.op,
            dst: self.dst,
            src: self.src,
            perm: self.perm,
        }
    }

    /// A short name for messages.
    pub fn label(&self) -> String {
        match self.src {
            IntentOperand::Reg(s) => format!("{:?} {},{}", self.op, self.dst, s),
            IntentOperand::Mem { base, disp } => {
                format!("{:?} {},[{base}{disp:+#x}]", self.op, self.dst)
            }
        }
    }
}

/// REAL ENCODINGS, captured from `trust-cg-codegen`'s x86-64 encoder.
///
/// This crate cannot call that encoder — `trust-cg-codegen` depends on this
/// crate — so the bytes are a CAPTURE, and
/// `tests/support/sse_lane_live_encode.rs` re-encodes every entry through the
/// live encoder and fails on any divergence. It is run by `x86_sse_lane_gate`
/// and by the two `coverage_gate_tests` tests that PIN the x86-64 ratio, so
/// the credited rows cannot rest on a stale capture. (Until that helper
/// existed the re-derivation ran ONLY in `x86_sse_lane_gate`, and the
/// ratio-pinning targets would have stayed green over a capture the encoder
/// had left behind.)
///
/// COVERAGE, per row: the register pairs `(0,1)`, `(1,0)`, `(8,1)`, `(1,9)` and
/// `(15,8)` put both operands on each side of the REX threshold in both
/// directions; PUNPCKLQDQ additionally carries `(1,1)`, the self-pair the
/// pipeline emits as a low-quadword broadcast, and PTEST the `(3,3)` and
/// `(0,0)` self-pairs it emits as a mask test. Every row whose encoder path
/// accepts a memory operand carries the folded `xmm, m128` form as well, over
/// bases that exercise the RSP/R12 SIB escape (`rsp`), the RBP/R13 forced-disp8
/// rule (`rbp`, `r13`), a zero displacement and a `disp32`. PSHUFD carries the
/// nine immediates the instruction selector spells literally plus all sixteen
/// values of its computed `v4i32_mask_shuffle_imm` family.
///
/// THE `perm` FIELD IS THE INTENT, not a reading of the immediate. It records
/// which source doubleword instruction selection MEANT each result doubleword
/// to be; the machine side derives its own permutation from the emitted imm8 by
/// the SDM's ORDER-field convention, and the two are compared. That is what
/// makes a `_MM_SHUFFLE`-style argument-order bug refutable. It is hand
/// transcribed against the isel's immediate literals and is named in the
/// non-claims for exactly that reason.
pub const EMITTED_X86_SSE_LANE_INSTANCES: &[EmittedSseLane] = &[
    EmittedSseLane {
        op: SseLaneOp::Punpcklbw,
        dst: "xmm0",
        src: IntentOperand::Reg("xmm1"),
        perm: None,
        bytes: &[0x66, 0x0F, 0x60, 0xC1],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpcklbw,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm0"),
        perm: None,
        bytes: &[0x66, 0x0F, 0x60, 0xC8],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpcklbw,
        dst: "xmm8",
        src: IntentOperand::Reg("xmm1"),
        perm: None,
        bytes: &[0x66, 0x44, 0x0F, 0x60, 0xC1],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpcklbw,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm9"),
        perm: None,
        bytes: &[0x66, 0x41, 0x0F, 0x60, 0xC9],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpcklbw,
        dst: "xmm15",
        src: IntentOperand::Reg("xmm8"),
        perm: None,
        bytes: &[0x66, 0x45, 0x0F, 0x60, 0xF8],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpcklbw,
        dst: "xmm1",
        src: IntentOperand::Mem {
            base: "rbp",
            disp: -64,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x60, 0x4D, 0xC0],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpcklbw,
        dst: "xmm2",
        src: IntentOperand::Mem {
            base: "rsp",
            disp: 32,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x60, 0x54, 0x24, 0x20],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpcklbw,
        dst: "xmm9",
        src: IntentOperand::Mem {
            base: "r13",
            disp: 0,
        },
        perm: None,
        bytes: &[0x66, 0x45, 0x0F, 0x60, 0x4D, 0x00],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpcklbw,
        dst: "xmm0",
        src: IntentOperand::Mem {
            base: "rax",
            disp: 0,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x60, 0x00],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpcklbw,
        dst: "xmm3",
        src: IntentOperand::Mem {
            base: "rcx",
            disp: 4096,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x60, 0x99, 0x00, 0x10, 0x00, 0x00],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpckhbw,
        dst: "xmm0",
        src: IntentOperand::Reg("xmm1"),
        perm: None,
        bytes: &[0x66, 0x0F, 0x68, 0xC1],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpckhbw,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm0"),
        perm: None,
        bytes: &[0x66, 0x0F, 0x68, 0xC8],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpckhbw,
        dst: "xmm8",
        src: IntentOperand::Reg("xmm1"),
        perm: None,
        bytes: &[0x66, 0x44, 0x0F, 0x68, 0xC1],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpckhbw,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm9"),
        perm: None,
        bytes: &[0x66, 0x41, 0x0F, 0x68, 0xC9],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpckhbw,
        dst: "xmm15",
        src: IntentOperand::Reg("xmm8"),
        perm: None,
        bytes: &[0x66, 0x45, 0x0F, 0x68, 0xF8],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpckhbw,
        dst: "xmm1",
        src: IntentOperand::Mem {
            base: "rbp",
            disp: -64,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x68, 0x4D, 0xC0],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpckhbw,
        dst: "xmm2",
        src: IntentOperand::Mem {
            base: "rsp",
            disp: 32,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x68, 0x54, 0x24, 0x20],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpckhbw,
        dst: "xmm9",
        src: IntentOperand::Mem {
            base: "r13",
            disp: 0,
        },
        perm: None,
        bytes: &[0x66, 0x45, 0x0F, 0x68, 0x4D, 0x00],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpckhbw,
        dst: "xmm0",
        src: IntentOperand::Mem {
            base: "rax",
            disp: 0,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x68, 0x00],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpckhbw,
        dst: "xmm3",
        src: IntentOperand::Mem {
            base: "rcx",
            disp: 4096,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x68, 0x99, 0x00, 0x10, 0x00, 0x00],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpckldq,
        dst: "xmm0",
        src: IntentOperand::Reg("xmm1"),
        perm: None,
        bytes: &[0x66, 0x0F, 0x62, 0xC1],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpckldq,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm0"),
        perm: None,
        bytes: &[0x66, 0x0F, 0x62, 0xC8],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpckldq,
        dst: "xmm8",
        src: IntentOperand::Reg("xmm1"),
        perm: None,
        bytes: &[0x66, 0x44, 0x0F, 0x62, 0xC1],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpckldq,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm9"),
        perm: None,
        bytes: &[0x66, 0x41, 0x0F, 0x62, 0xC9],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpckldq,
        dst: "xmm15",
        src: IntentOperand::Reg("xmm8"),
        perm: None,
        bytes: &[0x66, 0x45, 0x0F, 0x62, 0xF8],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpckldq,
        dst: "xmm1",
        src: IntentOperand::Mem {
            base: "rbp",
            disp: -64,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x62, 0x4D, 0xC0],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpckldq,
        dst: "xmm2",
        src: IntentOperand::Mem {
            base: "rsp",
            disp: 32,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x62, 0x54, 0x24, 0x20],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpckldq,
        dst: "xmm9",
        src: IntentOperand::Mem {
            base: "r13",
            disp: 0,
        },
        perm: None,
        bytes: &[0x66, 0x45, 0x0F, 0x62, 0x4D, 0x00],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpckldq,
        dst: "xmm0",
        src: IntentOperand::Mem {
            base: "rax",
            disp: 0,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x62, 0x00],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpckldq,
        dst: "xmm3",
        src: IntentOperand::Mem {
            base: "rcx",
            disp: 4096,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x62, 0x99, 0x00, 0x10, 0x00, 0x00],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpcklqdq,
        dst: "xmm0",
        src: IntentOperand::Reg("xmm1"),
        perm: None,
        bytes: &[0x66, 0x0F, 0x6C, 0xC1],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpcklqdq,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm0"),
        perm: None,
        bytes: &[0x66, 0x0F, 0x6C, 0xC8],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpcklqdq,
        dst: "xmm8",
        src: IntentOperand::Reg("xmm1"),
        perm: None,
        bytes: &[0x66, 0x44, 0x0F, 0x6C, 0xC1],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpcklqdq,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm9"),
        perm: None,
        bytes: &[0x66, 0x41, 0x0F, 0x6C, 0xC9],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpcklqdq,
        dst: "xmm15",
        src: IntentOperand::Reg("xmm8"),
        perm: None,
        bytes: &[0x66, 0x45, 0x0F, 0x6C, 0xF8],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpcklqdq,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm1"),
        perm: None,
        bytes: &[0x66, 0x0F, 0x6C, 0xC9],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpcklqdq,
        dst: "xmm1",
        src: IntentOperand::Mem {
            base: "rbp",
            disp: -64,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x6C, 0x4D, 0xC0],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpcklqdq,
        dst: "xmm2",
        src: IntentOperand::Mem {
            base: "rsp",
            disp: 32,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x6C, 0x54, 0x24, 0x20],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpcklqdq,
        dst: "xmm9",
        src: IntentOperand::Mem {
            base: "r13",
            disp: 0,
        },
        perm: None,
        bytes: &[0x66, 0x45, 0x0F, 0x6C, 0x4D, 0x00],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpcklqdq,
        dst: "xmm0",
        src: IntentOperand::Mem {
            base: "rax",
            disp: 0,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x6C, 0x00],
    },
    EmittedSseLane {
        op: SseLaneOp::Punpcklqdq,
        dst: "xmm3",
        src: IntentOperand::Mem {
            base: "rcx",
            disp: 4096,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x6C, 0x99, 0x00, 0x10, 0x00, 0x00],
    },
    EmittedSseLane {
        op: SseLaneOp::Packuswb,
        dst: "xmm0",
        src: IntentOperand::Reg("xmm1"),
        perm: None,
        bytes: &[0x66, 0x0F, 0x67, 0xC1],
    },
    EmittedSseLane {
        op: SseLaneOp::Packuswb,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm0"),
        perm: None,
        bytes: &[0x66, 0x0F, 0x67, 0xC8],
    },
    EmittedSseLane {
        op: SseLaneOp::Packuswb,
        dst: "xmm8",
        src: IntentOperand::Reg("xmm1"),
        perm: None,
        bytes: &[0x66, 0x44, 0x0F, 0x67, 0xC1],
    },
    EmittedSseLane {
        op: SseLaneOp::Packuswb,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm9"),
        perm: None,
        bytes: &[0x66, 0x41, 0x0F, 0x67, 0xC9],
    },
    EmittedSseLane {
        op: SseLaneOp::Packuswb,
        dst: "xmm15",
        src: IntentOperand::Reg("xmm8"),
        perm: None,
        bytes: &[0x66, 0x45, 0x0F, 0x67, 0xF8],
    },
    EmittedSseLane {
        op: SseLaneOp::Packuswb,
        dst: "xmm1",
        src: IntentOperand::Mem {
            base: "rbp",
            disp: -64,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x67, 0x4D, 0xC0],
    },
    EmittedSseLane {
        op: SseLaneOp::Packuswb,
        dst: "xmm2",
        src: IntentOperand::Mem {
            base: "rsp",
            disp: 32,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x67, 0x54, 0x24, 0x20],
    },
    EmittedSseLane {
        op: SseLaneOp::Packuswb,
        dst: "xmm9",
        src: IntentOperand::Mem {
            base: "r13",
            disp: 0,
        },
        perm: None,
        bytes: &[0x66, 0x45, 0x0F, 0x67, 0x4D, 0x00],
    },
    EmittedSseLane {
        op: SseLaneOp::Packuswb,
        dst: "xmm0",
        src: IntentOperand::Mem {
            base: "rax",
            disp: 0,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x67, 0x00],
    },
    EmittedSseLane {
        op: SseLaneOp::Packuswb,
        dst: "xmm3",
        src: IntentOperand::Mem {
            base: "rcx",
            disp: 4096,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x67, 0x99, 0x00, 0x10, 0x00, 0x00],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm0",
        src: IntentOperand::Reg("xmm1"),
        perm: Some([0, 0, 0, 0]),
        bytes: &[0x66, 0x0F, 0x70, 0xC1, 0x00],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm0"),
        perm: Some([0, 1, 0, 1]),
        bytes: &[0x66, 0x0F, 0x70, 0xC8, 0x44],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm8",
        src: IntentOperand::Reg("xmm1"),
        perm: Some([2, 3, 0, 1]),
        bytes: &[0x66, 0x44, 0x0F, 0x70, 0xC1, 0x4E],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm9"),
        perm: Some([0, 0, 2, 2]),
        bytes: &[0x66, 0x41, 0x0F, 0x70, 0xC9, 0xA0],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm15",
        src: IntentOperand::Reg("xmm8"),
        perm: Some([2, 3, 2, 3]),
        bytes: &[0x66, 0x45, 0x0F, 0x70, 0xF8, 0xEE],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm0",
        src: IntentOperand::Reg("xmm1"),
        perm: Some([1, 1, 3, 3]),
        bytes: &[0x66, 0x0F, 0x70, 0xC1, 0xF5],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm0"),
        perm: Some([3, 2, 1, 0]),
        bytes: &[0x66, 0x0F, 0x70, 0xC8, 0x1B],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm8",
        src: IntentOperand::Reg("xmm1"),
        perm: Some([0, 0, 0, 2]),
        bytes: &[0x66, 0x44, 0x0F, 0x70, 0xC1, 0x80],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm9"),
        perm: Some([3, 3, 3, 3]),
        bytes: &[0x66, 0x41, 0x0F, 0x70, 0xC9, 0xFF],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm0",
        src: IntentOperand::Reg("xmm1"),
        perm: Some([0, 0, 0, 0]),
        bytes: &[0x66, 0x0F, 0x70, 0xC1, 0x00],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm0"),
        perm: Some([1, 0, 0, 0]),
        bytes: &[0x66, 0x0F, 0x70, 0xC8, 0x01],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm8",
        src: IntentOperand::Reg("xmm1"),
        perm: Some([0, 1, 0, 0]),
        bytes: &[0x66, 0x44, 0x0F, 0x70, 0xC1, 0x04],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm9"),
        perm: Some([1, 1, 0, 0]),
        bytes: &[0x66, 0x41, 0x0F, 0x70, 0xC9, 0x05],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm15",
        src: IntentOperand::Reg("xmm8"),
        perm: Some([0, 0, 1, 0]),
        bytes: &[0x66, 0x45, 0x0F, 0x70, 0xF8, 0x10],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm0",
        src: IntentOperand::Reg("xmm1"),
        perm: Some([1, 0, 1, 0]),
        bytes: &[0x66, 0x0F, 0x70, 0xC1, 0x11],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm0"),
        perm: Some([0, 1, 1, 0]),
        bytes: &[0x66, 0x0F, 0x70, 0xC8, 0x14],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm8",
        src: IntentOperand::Reg("xmm1"),
        perm: Some([1, 1, 1, 0]),
        bytes: &[0x66, 0x44, 0x0F, 0x70, 0xC1, 0x15],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm9"),
        perm: Some([0, 0, 0, 1]),
        bytes: &[0x66, 0x41, 0x0F, 0x70, 0xC9, 0x40],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm15",
        src: IntentOperand::Reg("xmm8"),
        perm: Some([1, 0, 0, 1]),
        bytes: &[0x66, 0x45, 0x0F, 0x70, 0xF8, 0x41],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm0",
        src: IntentOperand::Reg("xmm1"),
        perm: Some([0, 1, 0, 1]),
        bytes: &[0x66, 0x0F, 0x70, 0xC1, 0x44],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm0"),
        perm: Some([1, 1, 0, 1]),
        bytes: &[0x66, 0x0F, 0x70, 0xC8, 0x45],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm8",
        src: IntentOperand::Reg("xmm1"),
        perm: Some([0, 0, 1, 1]),
        bytes: &[0x66, 0x44, 0x0F, 0x70, 0xC1, 0x50],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm9"),
        perm: Some([1, 0, 1, 1]),
        bytes: &[0x66, 0x41, 0x0F, 0x70, 0xC9, 0x51],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm15",
        src: IntentOperand::Reg("xmm8"),
        perm: Some([0, 1, 1, 1]),
        bytes: &[0x66, 0x45, 0x0F, 0x70, 0xF8, 0x54],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm0",
        src: IntentOperand::Reg("xmm1"),
        perm: Some([1, 1, 1, 1]),
        bytes: &[0x66, 0x0F, 0x70, 0xC1, 0x55],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm1",
        src: IntentOperand::Mem {
            base: "rbp",
            disp: -64,
        },
        perm: Some([0, 0, 0, 0]),
        bytes: &[0x66, 0x0F, 0x70, 0x4D, 0xC0, 0x00],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm2",
        src: IntentOperand::Mem {
            base: "rsp",
            disp: 32,
        },
        perm: Some([0, 1, 0, 1]),
        bytes: &[0x66, 0x0F, 0x70, 0x54, 0x24, 0x20, 0x44],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm9",
        src: IntentOperand::Mem {
            base: "r13",
            disp: 0,
        },
        perm: Some([2, 3, 0, 1]),
        bytes: &[0x66, 0x45, 0x0F, 0x70, 0x4D, 0x00, 0x4E],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm0",
        src: IntentOperand::Mem {
            base: "rax",
            disp: 0,
        },
        perm: Some([0, 0, 2, 2]),
        bytes: &[0x66, 0x0F, 0x70, 0x00, 0xA0],
    },
    EmittedSseLane {
        op: SseLaneOp::Pshufd,
        dst: "xmm3",
        src: IntentOperand::Mem {
            base: "rcx",
            disp: 4096,
        },
        perm: Some([2, 3, 2, 3]),
        bytes: &[0x66, 0x0F, 0x70, 0x99, 0x00, 0x10, 0x00, 0x00, 0xEE],
    },
    EmittedSseLane {
        op: SseLaneOp::MovdqaRR,
        dst: "xmm0",
        src: IntentOperand::Reg("xmm1"),
        perm: None,
        bytes: &[0x66, 0x0F, 0x6F, 0xC1],
    },
    EmittedSseLane {
        op: SseLaneOp::MovdqaRR,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm0"),
        perm: None,
        bytes: &[0x66, 0x0F, 0x6F, 0xC8],
    },
    EmittedSseLane {
        op: SseLaneOp::MovdqaRR,
        dst: "xmm8",
        src: IntentOperand::Reg("xmm1"),
        perm: None,
        bytes: &[0x66, 0x44, 0x0F, 0x6F, 0xC1],
    },
    EmittedSseLane {
        op: SseLaneOp::MovdqaRR,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm9"),
        perm: None,
        bytes: &[0x66, 0x41, 0x0F, 0x6F, 0xC9],
    },
    EmittedSseLane {
        op: SseLaneOp::MovdqaRR,
        dst: "xmm15",
        src: IntentOperand::Reg("xmm8"),
        perm: None,
        bytes: &[0x66, 0x45, 0x0F, 0x6F, 0xF8],
    },
    EmittedSseLane {
        op: SseLaneOp::MovdqaRR,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm1"),
        perm: None,
        bytes: &[0x66, 0x0F, 0x6F, 0xC9],
    },
    EmittedSseLane {
        op: SseLaneOp::Pmovmskb,
        dst: "eax",
        src: IntentOperand::Reg("xmm1"),
        perm: None,
        bytes: &[0x66, 0x0F, 0xD7, 0xC1],
    },
    EmittedSseLane {
        op: SseLaneOp::Pmovmskb,
        dst: "r8d",
        src: IntentOperand::Reg("xmm15"),
        perm: None,
        bytes: &[0x66, 0x45, 0x0F, 0xD7, 0xC7],
    },
    EmittedSseLane {
        op: SseLaneOp::Pmovmskb,
        dst: "ecx",
        src: IntentOperand::Reg("xmm9"),
        perm: None,
        bytes: &[0x66, 0x41, 0x0F, 0xD7, 0xC9],
    },
    EmittedSseLane {
        op: SseLaneOp::Pmovmskb,
        dst: "edx",
        src: IntentOperand::Reg("xmm0"),
        perm: None,
        bytes: &[0x66, 0x0F, 0xD7, 0xD0],
    },
    EmittedSseLane {
        op: SseLaneOp::Pmovmskb,
        dst: "r15d",
        src: IntentOperand::Reg("xmm15"),
        perm: None,
        bytes: &[0x66, 0x45, 0x0F, 0xD7, 0xFF],
    },
    EmittedSseLane {
        op: SseLaneOp::Pblendvb,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm2"),
        perm: None,
        bytes: &[0x66, 0x0F, 0x38, 0x10, 0xCA],
    },
    EmittedSseLane {
        op: SseLaneOp::Pblendvb,
        dst: "xmm3",
        src: IntentOperand::Reg("xmm8"),
        perm: None,
        bytes: &[0x66, 0x41, 0x0F, 0x38, 0x10, 0xD8],
    },
    EmittedSseLane {
        op: SseLaneOp::Pblendvb,
        dst: "xmm9",
        src: IntentOperand::Reg("xmm1"),
        perm: None,
        bytes: &[0x66, 0x44, 0x0F, 0x38, 0x10, 0xC9],
    },
    EmittedSseLane {
        op: SseLaneOp::Pblendvb,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm0"),
        perm: None,
        bytes: &[0x66, 0x0F, 0x38, 0x10, 0xC8],
    },
    EmittedSseLane {
        op: SseLaneOp::Pblendvb,
        dst: "xmm0",
        src: IntentOperand::Reg("xmm1"),
        perm: None,
        bytes: &[0x66, 0x0F, 0x38, 0x10, 0xC1],
    },
    EmittedSseLane {
        op: SseLaneOp::Ptest,
        dst: "xmm1",
        src: IntentOperand::Reg("xmm2"),
        perm: None,
        bytes: &[0x66, 0x0F, 0x38, 0x17, 0xCA],
    },
    EmittedSseLane {
        op: SseLaneOp::Ptest,
        dst: "xmm3",
        src: IntentOperand::Reg("xmm3"),
        perm: None,
        bytes: &[0x66, 0x0F, 0x38, 0x17, 0xDB],
    },
    EmittedSseLane {
        op: SseLaneOp::Ptest,
        dst: "xmm8",
        src: IntentOperand::Reg("xmm9"),
        perm: None,
        bytes: &[0x66, 0x45, 0x0F, 0x38, 0x17, 0xC1],
    },
    EmittedSseLane {
        op: SseLaneOp::Ptest,
        dst: "xmm0",
        src: IntentOperand::Reg("xmm0"),
        perm: None,
        bytes: &[0x66, 0x0F, 0x38, 0x17, 0xC0],
    },
    EmittedSseLane {
        op: SseLaneOp::Ptest,
        dst: "xmm15",
        src: IntentOperand::Reg("xmm1"),
        perm: None,
        bytes: &[0x66, 0x44, 0x0F, 0x38, 0x17, 0xF9],
    },
    EmittedSseLane {
        op: SseLaneOp::Ptest,
        dst: "xmm1",
        src: IntentOperand::Mem {
            base: "rbp",
            disp: -64,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x38, 0x17, 0x4D, 0xC0],
    },
    EmittedSseLane {
        op: SseLaneOp::Ptest,
        dst: "xmm2",
        src: IntentOperand::Mem {
            base: "rsp",
            disp: 32,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x38, 0x17, 0x54, 0x24, 0x20],
    },
    EmittedSseLane {
        op: SseLaneOp::Ptest,
        dst: "xmm9",
        src: IntentOperand::Mem {
            base: "r13",
            disp: 0,
        },
        perm: None,
        bytes: &[0x66, 0x45, 0x0F, 0x38, 0x17, 0x4D, 0x00],
    },
    EmittedSseLane {
        op: SseLaneOp::Ptest,
        dst: "xmm0",
        src: IntentOperand::Mem {
            base: "rax",
            disp: 0,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x38, 0x17, 0x00],
    },
    EmittedSseLane {
        op: SseLaneOp::Ptest,
        dst: "xmm3",
        src: IntentOperand::Mem {
            base: "rcx",
            disp: 4096,
        },
        perm: None,
        bytes: &[0x66, 0x0F, 0x38, 0x17, 0x99, 0x00, 0x10, 0x00, 0x00],
    },
];

// ===========================================================================
// (11) The negative controls, part one: BYTE MUTANTS
// ===========================================================================

/// Where each structural byte sits inside a real encoding.
struct ByteLayout {
    /// Index of the REX byte, when one is present.
    rex: Option<usize>,
    /// Index of the final opcode byte.
    opcode: usize,
    /// Index of the ModR/M byte.
    modrm: usize,
}

fn layout(d: &DecodedSse) -> ByteLayout {
    let after_prefix = usize::from(d.prefix.is_some());
    let rex = d.rex.map(|_| after_prefix);
    let escape = after_prefix + usize::from(d.rex.is_some());
    let opcode = escape
        + match d.map {
            OpMap::Map0F => 1,
            OpMap::Map0F38 => 2,
        };
    ByteLayout {
        rex,
        opcode,
        modrm: opcode + 1,
    }
}

/// One deliberately wrong ENCODING, checked through the whole obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SseByteMutant {
    /// What was corrupted.
    pub label: &'static str,
    /// The unchanged intent.
    pub intent: SseIntent,
    /// The corrupted bytes.
    pub bytes: Vec<u8>,
    /// The reason class this control MUST refute as.
    pub expect: SseRefutationClass,
}

/// The byte-mutant labels EVERY row must show, whatever its opcode.
///
/// A battery that silently stopped producing one of these would otherwise
/// leave the row green with a facet no longer defended. Like the wrong-model
/// list, this is enforced PER ROW: `ModRM reg and r/m EXCHANGED` is skipped on
/// an entry whose two ModRM fields already hold the same number, and that is
/// only admissible while another entry OF THE SAME ROW still carries it.
pub const COMMON_BYTE_MUTANT_LABELS: &[&str] = &[
    "prefix 66 -> F3",
    "the 66 prefix DROPPED (the 64-bit MMX form)",
    "ModRM reg and r/m EXCHANGED",
    "ModRM mod cleared to 00 (the register operand becomes MEMORY)",
    "a redundant REX 0x40",
    "the REX placed BEFORE the 66 prefix",
    "a trailing byte",
    "the last byte TRUNCATED",
];

/// The byte-mutant labels each row must show ON TOP of
/// [`COMMON_BYTE_MUTANT_LABELS`]: the ones that name that row's own opcode
/// byte or its immediate.
pub const REQUIRED_BYTE_MUTANTS_PER_ROW: &[(SseLaneOp, &[&str])] = &[
    (SseLaneOp::Punpcklbw, INTERLEAVE_BYTE_LABELS),
    (SseLaneOp::Punpckhbw, INTERLEAVE_BYTE_LABELS),
    (SseLaneOp::Punpckldq, INTERLEAVE_BYTE_LABELS),
    (SseLaneOp::Punpcklqdq, INTERLEAVE_BYTE_LABELS),
    (
        SseLaneOp::Pshufd,
        &[
            "imm8 ORDER fields REVERSED (the _MM_SHUFFLE argument-order bug)",
            "imm8 with one ORDER field off by one",
        ],
    ),
    (
        SseLaneOp::MovdqaRR,
        &[
            "opcode byte: the MOVDQA STORE direction (6F -> 7F)",
            "prefix F3 0F 7E: MOVQ, which ZEROES the upper quadword",
        ],
    ),
    (SseLaneOp::Pmovmskb, &[]),
    (
        SseLaneOp::Packuswb,
        &["opcode byte: the SIGNED pack (PACKSSWB for PACKUSWB)"],
    ),
    (
        SseLaneOp::Pblendvb,
        &[
            "opcode byte: PTEST <-> PBLENDVB (0F 38 17 <-> 0F 38 10)",
            "opcode byte: BLENDVPS, whose mask is DWORD-granular",
        ],
    ),
    (
        SseLaneOp::Ptest,
        &["opcode byte: PTEST <-> PBLENDVB (0F 38 17 <-> 0F 38 10)"],
    ),
];

/// The opcode-byte mutants every one of the four unpack rows must show.
const INTERLEAVE_BYTE_LABELS: &[&str] = &[
    "opcode byte: the OTHER HALF of the interleave",
    "opcode byte: the wrong ELEMENT WIDTH",
];

/// Does the SDM give THIS ROW's opcode byte a 64-bit MMX (`mm, mm/m64`) line,
/// reachable by dropping the mandatory `66`?
///
/// A SECOND, independent reading of the manual, deliberately not sharing a line
/// with [`sdm_opcode_table`] — it is keyed by the trust-cg row rather than by a
/// decoded opcode byte, and it exists so the "66 prefix DROPPED" control has
/// teeth against the decoder's own table. Vol 2B, per row:
///
///   * `PUNPCKLBW`  (0F 60), `PUNPCKHBW` (0F 68), `PUNPCKLDQ` (0F 62),
///     `PACKUSWB`   (0F 67), `MOVQ mm,mm/m64` (0F 6F, the MOVDQA byte),
///     `PSHUFW`     (0F 70, the PSHUFD byte) and `PMOVMSKB r32,mm` (0F D7)
///     all have one;
///   * `PUNPCKLQDQ` (0F 6C) has NONE — an MMX register is 64 bits wide, so a
///     quadword unpack has nothing to interleave, and the SDM gives 0F 6C no
///     unprefixed line at all;
///   * `PTEST` (0F 38 17) and `PBLENDVB` (0F 38 10) are SSE4.1, and the 0F 38
///     map has no unprefixed MMX entries for them.
fn sdm_row_has_mmx_form(op: SseLaneOp) -> bool {
    match op {
        SseLaneOp::Punpcklbw
        | SseLaneOp::Punpckhbw
        | SseLaneOp::Punpckldq
        | SseLaneOp::Packuswb
        | SseLaneOp::MovdqaRR
        | SseLaneOp::Pshufd
        | SseLaneOp::Pmovmskb => true,
        SseLaneOp::Punpcklqdq | SseLaneOp::Ptest | SseLaneOp::Pblendvb => false,
    }
}

/// The interleave partner opcode bytes: `(the other half, the other width)`.
fn interleave_neighbours(op: SseLaneOp) -> Option<(u8, u8)> {
    match op {
        // 0x60 PUNPCKLBW: the other half is 0x68 PUNPCKHBW, the other width
        // 0x61 PUNPCKLWD.
        SseLaneOp::Punpcklbw => Some((0x68, 0x61)),
        // 0x68 PUNPCKHBW: 0x60 PUNPCKLBW and 0x69 PUNPCKHWD.
        SseLaneOp::Punpckhbw => Some((0x60, 0x69)),
        // 0x62 PUNPCKLDQ: 0x6A PUNPCKHDQ and 0x60 PUNPCKLBW.
        SseLaneOp::Punpckldq => Some((0x6A, 0x60)),
        // 0x6C PUNPCKLQDQ: 0x6D PUNPCKHQDQ and 0x62 PUNPCKLDQ.
        SseLaneOp::Punpcklqdq => Some((0x6D, 0x62)),
        _ => None,
    }
}

/// THE BYTE-MUTANT BATTERY for one captured encoding.
///
/// Every mutant keeps the INTENT and corrupts the BYTES, so each one asks the
/// same question: would this obligation have noticed? A mutant that survives
/// means the obligation is not faithful — fix the obligation, never the
/// control.
pub fn sse_byte_mutants(entry: &EmittedSseLane) -> Vec<SseByteMutant> {
    let intent = entry.intent();
    let Ok(d) = sdm_decode_sse(entry.bytes) else {
        return Vec::new();
    };
    let l = layout(&d);
    let mut out = Vec::new();
    let mut push = |label: &'static str, bytes: Vec<u8>, expect: SseRefutationClass| {
        out.push(SseByteMutant {
            label,
            intent,
            bytes,
            expect,
        });
    };
    let with_byte = |i: usize, v: u8| -> Vec<u8> {
        let mut b = entry.bytes.to_vec();
        b[i] = v;
        b
    };

    // --- opcode-byte swaps: each lands on a KNOWN NEIGHBOUR instruction -----
    if let Some((other_half, other_width)) = interleave_neighbours(entry.op) {
        push(
            "opcode byte: the OTHER HALF of the interleave",
            with_byte(l.opcode, other_half),
            SseRefutationClass::Mnemonic,
        );
        push(
            "opcode byte: the wrong ELEMENT WIDTH",
            with_byte(l.opcode, other_width),
            SseRefutationClass::Mnemonic,
        );
    }
    if entry.op == SseLaneOp::Packuswb {
        push(
            "opcode byte: the SIGNED pack (PACKSSWB for PACKUSWB)",
            with_byte(l.opcode, 0x63),
            SseRefutationClass::Mnemonic,
        );
    }
    if entry.op == SseLaneOp::MovdqaRR {
        push(
            "opcode byte: the MOVDQA STORE direction (6F -> 7F)",
            with_byte(l.opcode, 0x7F),
            SseRefutationClass::Mnemonic,
        );
        push(
            "prefix F3 0F 7E: MOVQ, which ZEROES the upper quadword",
            {
                let mut b = with_byte(l.opcode, 0x7E);
                b[0] = 0xF3;
                b
            },
            SseRefutationClass::Mnemonic,
        );
    }
    if entry.op == SseLaneOp::Ptest {
        push(
            "opcode byte: PTEST <-> PBLENDVB (0F 38 17 <-> 0F 38 10)",
            with_byte(l.opcode, 0x10),
            SseRefutationClass::Mnemonic,
        );
    }
    if entry.op == SseLaneOp::Pblendvb {
        push(
            "opcode byte: PTEST <-> PBLENDVB (0F 38 17 <-> 0F 38 10)",
            with_byte(l.opcode, 0x17),
            SseRefutationClass::Mnemonic,
        );
        push(
            "opcode byte: BLENDVPS, whose mask is DWORD-granular",
            with_byte(l.opcode, 0x14),
            SseRefutationClass::Mnemonic,
        );
    }

    // --- mandatory-prefix mutants ------------------------------------------
    // F3 maps to a real instruction for 0x6F (MOVDQU), 0x70 (PSHUFHW) and
    // 0x7E (MOVQ); everywhere else it is an unmodelled encoding.
    let f3_is_known = d.map == OpMap::Map0F && matches!(d.opcode, 0x6F | 0x70 | 0x7E | 0x7F);
    push(
        "prefix 66 -> F3",
        with_byte(0, 0xF3),
        if f3_is_known {
            SseRefutationClass::Mnemonic
        } else {
            SseRefutationClass::Decode
        },
    );
    // Dropping the 66 lands on the 64-bit MMX form where the SDM gives the
    // opcode byte an `mm, mm/m64` line, and on nothing at all otherwise — the
    // quadword unpacks (0F 6C / 0F 6D) have NO MMX form, an MMX register being
    // only 64 bits wide, and the 0F 38 map has no unprefixed entries. Both are
    // refutations, and which one fires is a fact about the ISA.
    //
    // The expectation is stated by [`sdm_row_has_mmx_form`], a SECOND reading
    // of the manual for this row's own opcode, NOT by consulting
    // `sdm_opcode_table`. Reading it off that table (which is what this control
    // used to do) left the control toothless against the table it is testing: a
    // wrong MMX line there would have moved the expectation and the outcome
    // together. Now the two statements have to agree, and a disagreement
    // surfaces as `refuted for the WRONG REASON`.
    push(
        "the 66 prefix DROPPED (the 64-bit MMX form)",
        entry.bytes[1..].to_vec(),
        if sdm_row_has_mmx_form(entry.op) {
            SseRefutationClass::Mnemonic
        } else {
            SseRefutationClass::Decode
        },
    );

    // --- ModR/M mutants ----------------------------------------------------
    let modrm = entry.bytes[l.modrm];
    let (mode, reg3, rm3) = (modrm >> 6, (modrm >> 3) & 7, modrm & 7);
    if mode == 0b11 && reg3 != rm3 {
        push(
            "ModRM reg and r/m EXCHANGED",
            with_byte(l.modrm, (mode << 6) | (rm3 << 3) | reg3),
            // PTEST writes no value, so exchanging its operands is caught by
            // the FLAG operands rather than by a destination.
            if entry.op == SseLaneOp::Ptest {
                SseRefutationClass::Flags
            } else {
                SseRefutationClass::Dest
            },
        );
    }
    if mode == 0b11 && !matches!(rm3, 4 | 5) {
        // The register operand becomes `[base]`. PMOVMSKB has no memory form
        // at all, so it refuses at the DECODER.
        // The `0b00 << 6` is the ModR/M `mod` field written out, not arithmetic.
        #[allow(clippy::identity_op)]
        push(
            "ModRM mod cleared to 00 (the register operand becomes MEMORY)",
            with_byte(l.modrm, (0b00 << 6) | (reg3 << 3) | rm3),
            match entry.op {
                SseLaneOp::Pmovmskb => SseRefutationClass::Decode,
                SseLaneOp::Ptest => SseRefutationClass::Flags,
                _ => SseRefutationClass::Value,
            },
        );
    }

    // --- framing and canonicality ------------------------------------------
    if l.rex.is_none() {
        let mut b = entry.bytes.to_vec();
        b.insert(1, 0x40);
        push("a redundant REX 0x40", b, SseRefutationClass::Canonicality);
    } else {
        let mut b = entry.bytes.to_vec();
        b.swap(0, 1);
        push(
            "the REX placed BEFORE the 66 prefix",
            b,
            SseRefutationClass::Decode,
        );
    }
    {
        let mut b = entry.bytes.to_vec();
        b.push(0x90);
        push("a trailing byte", b, SseRefutationClass::Decode);
    }
    {
        let mut b = entry.bytes.to_vec();
        b.pop();
        push("the last byte TRUNCATED", b, SseRefutationClass::Decode);
    }

    // --- imm8 mutants (PSHUFD) ---------------------------------------------
    if let Some(imm) = d.imm8 {
        let fields = [imm & 3, (imm >> 2) & 3, (imm >> 4) & 3, (imm >> 6) & 3];
        let reversed = fields[0] << 6 | fields[1] << 4 | fields[2] << 2 | fields[3];
        if reversed != imm {
            push(
                "imm8 ORDER fields REVERSED (the _MM_SHUFFLE argument-order bug)",
                with_byte(entry.bytes.len() - 1, reversed),
                SseRefutationClass::Value,
            );
        }
        push(
            "imm8 with one ORDER field off by one",
            with_byte(entry.bytes.len() - 1, imm ^ 0x01),
            SseRefutationClass::Value,
        );
    }

    out
}

/// Run one byte mutant and demand its stated reason class.
pub fn byte_control_is_refuted_as_stated(m: &SseByteMutant) -> Result<(), String> {
    match sse_lane_check(&m.intent, &m.bytes) {
        Ok(_) => Err(format!(
            "negative control SURVIVED — `{}`: {:?} {} vs bytes {:02x?} was ACCEPTED",
            m.label, m.intent.op, m.intent.dst, m.bytes
        )),
        Err(r) if r.class() != m.expect => Err(format!(
            "negative control refuted for the WRONG REASON — `{}`: {:?} {} vs bytes {:02x?} must \
             refute as {:?} but refuted as {:?} ({r})",
            m.label,
            m.intent.op,
            m.intent.dst,
            m.bytes,
            m.expect,
            r.class()
        )),
        Err(_) => Ok(()),
    }
}

// ===========================================================================
// (12) The negative controls, part two: WRONG MODELS
// ===========================================================================

/// A deliberately wrong MACHINE-side model of the real emitted instruction.
///
/// These are the controls that make the credit a VALUE credit rather than a
/// framing one: the bytes stay exactly as the encoder produced them and the
/// intent stays exactly as the machine IR meant it, and only the SDM model in
/// between is corrupted. Each must then DISAGREE with the intent — if a wrong
/// model still matched, the obligation would not be reading the facet the
/// model corrupts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WrongMachineModel {
    /// Model this instruction as some OTHER SDM instruction.
    Mnemonic(SseMnemonic),
    /// The right instruction with its two operands exchanged.
    OperandsSwapped,
    /// The result is just the SOURCE, unrouted (the "identity passthrough").
    IdentityOfSrc,
    /// The result is just the DESTINATION, unrouted.
    IdentityOfDest,
    /// A constant-zero result. Any obligation that cannot refute THIS is
    /// reading nothing at all.
    ConstantZero,
    /// PSHUFD reading the ORDER fields in reverse — the `_MM_SHUFFLE`
    /// argument-order bug, as a MODEL rather than as a corrupted immediate.
    PshufdOrderReversed,
    /// PSHUFD permuting the DESTINATION instead of the source operand.
    PshufdOnDest,
    /// PMOVMSKB gathering bit 0 of each byte instead of the SIGN bit.
    MaskFromBit0,
    /// PMOVMSKB in reversed lane-to-bit order.
    MaskReversed,
    /// PMOVMSKB SIGN-EXTENDING into the upper bits instead of zeroing them —
    /// the facet the 64-bit-wide denotation exists to defend.
    MaskSignExtended,
    /// PMOVMSKB gathering only the low EIGHT lanes (the 64-bit MMX form's
    /// behaviour) and zeroing the rest.
    MaskLow8LanesOnly,
    /// PBLENDVB taking its mask from the EXPLICIT source operand instead of
    /// the implicit XMM0 — the dropped implicit register.
    BlendMaskFromSrc,
    /// PBLENDVB selecting on bit 0 of the mask byte rather than its sign bit.
    /// A whole-byte "is it non-zero" model is caught by the same control, since
    /// both disagree with "bit 7" on a `0x7F` mask byte.
    BlendOnBit0,
    /// PBLENDVB with the true and false arms exchanged.
    BlendArmsSwapped,
    /// PACKUSWB with the destination and source halves exchanged.
    PackHalvesSwapped,
    /// PACKUSWB with the element order reversed within each half.
    PackOrderReversed,
    /// PTEST's decoded flag model with ZF and CF EXCHANGED. The two flags are
    /// the asymmetric pair (`ZF <- (SRC AND DEST) == 0`, `CF <- (SRC AND NOT
    /// DEST) == 0`), so exchanging them is the classic PTEST misreading — and
    /// it is only refutable at all because [`denotations_agree`] evaluates the
    /// model the BYTES decoded to rather than rebuilding the constant.
    PtestFlagsExchanged,
    /// PTEST's decoded flag model with ZF hard-wired to 0 — the model a random
    /// 128-bit sweep cannot refute, since a random pair almost never has
    /// `SRC AND DEST == 0`.
    PtestZfCleared,
}

/// Build a wrong MACHINE-side denotation for the real decoded instruction.
///
/// An `Err` counts as a refutation: a model that cannot even be built is a
/// model the obligation would never have accepted.
pub fn apply_wrong_machine_model(
    d: &DecodedSse,
    w: WrongMachineModel,
) -> Result<Denotation, SseModelError> {
    let dest = Dest::Xmm(d.reg);
    let src = rm_operand(d);
    match w {
        WrongMachineModel::Mnemonic(m) => machine_denotation(&DecodedSse { mnemonic: m, ..*d }),
        WrongMachineModel::OperandsSwapped => {
            let SseRm::Reg(r) = d.rm else {
                return Err(SseModelError::RegisterOperandRequired);
            };
            machine_denotation(&DecodedSse {
                reg: r,
                rm: SseRm::Reg(d.reg),
                ..*d
            })
        }
        WrongMachineModel::IdentityOfSrc => Ok(Denotation::Value(ValueDenot {
            dest,
            bits: copy_128(src),
        })),
        WrongMachineModel::IdentityOfDest => Ok(Denotation::Value(ValueDenot {
            dest,
            bits: copy_128(reg_operand(d)?),
        })),
        WrongMachineModel::ConstantZero => {
            let width = match machine_denotation(d)? {
                Denotation::Value(v) => v.bits.len(),
                _ => 128,
            };
            Ok(Denotation::Value(ValueDenot {
                dest,
                bits: vec![BitSource::Zero; width],
            }))
        }
        WrongMachineModel::PshufdOrderReversed => {
            let imm = d.imm8.ok_or(SseModelError::MissingImm8)?;
            let mut bits = Vec::with_capacity(128);
            for j in 0..4u8 {
                let sel = (imm >> (2 * (3 - j))) & 3;
                for b in 0..4u8 {
                    for bit in 0..8u8 {
                        bits.push(BitSource::Bit {
                            op: src,
                            byte: 4 * sel + b,
                            bit,
                        });
                    }
                }
            }
            Ok(Denotation::Value(ValueDenot { dest, bits }))
        }
        WrongMachineModel::PshufdOnDest => {
            let imm = d.imm8.ok_or(SseModelError::MissingImm8)?;
            Ok(Denotation::Value(ValueDenot {
                dest,
                bits: sdm_pshufd(reg_operand(d)?, imm),
            }))
        }
        WrongMachineModel::MaskFromBit0
        | WrongMachineModel::MaskReversed
        | WrongMachineModel::MaskSignExtended
        | WrongMachineModel::MaskLow8LanesOnly => {
            let SseRm::Reg(s) = d.rm else {
                return Err(SseModelError::RegisterOperandRequired);
            };
            let op = Operand::Xmm(s);
            let mut bits: Vec<BitSource> = Vec::with_capacity(64);
            match w {
                WrongMachineModel::MaskFromBit0 => {
                    for i in 0..16u8 {
                        bits.push(BitSource::Bit {
                            op,
                            byte: i,
                            bit: 0,
                        });
                    }
                }
                WrongMachineModel::MaskReversed => {
                    for i in (0..16u8).rev() {
                        bits.push(BitSource::Bit {
                            op,
                            byte: i,
                            bit: 7,
                        });
                    }
                }
                WrongMachineModel::MaskLow8LanesOnly => {
                    for i in 0..8u8 {
                        bits.push(BitSource::Bit {
                            op,
                            byte: i,
                            bit: 7,
                        });
                    }
                }
                _ => {
                    for i in 0..16u8 {
                        bits.push(BitSource::Bit {
                            op,
                            byte: i,
                            bit: 7,
                        });
                    }
                }
            }
            if w == WrongMachineModel::MaskSignExtended {
                // Bits 16..64 replicate the top gathered bit instead of zero.
                while bits.len() < 64 {
                    bits.push(BitSource::Bit {
                        op,
                        byte: 15,
                        bit: 7,
                    });
                }
            } else {
                bits.resize(64, BitSource::Zero);
            }
            Ok(Denotation::Value(ValueDenot {
                dest: Dest::Gpr64(d.reg),
                bits,
            }))
        }
        WrongMachineModel::BlendMaskFromSrc
        | WrongMachineModel::BlendOnBit0
        | WrongMachineModel::BlendArmsSwapped => {
            let dv = reg_operand(d)?;
            let (ctl, ctl_bit, one, zero) = match w {
                WrongMachineModel::BlendMaskFromSrc => (src, 7u8, src, dv),
                WrongMachineModel::BlendOnBit0 => (Operand::Xmm(0), 0u8, src, dv),
                _ => (Operand::Xmm(0), 7u8, dv, src),
            };
            let mut bits = Vec::with_capacity(128);
            for byte in 0..16u8 {
                for bit in 0..8u8 {
                    bits.push(BitSource::Select {
                        ctl,
                        ctl_byte: byte,
                        ctl_bit,
                        one: BitRef { op: one, byte, bit },
                        zero: BitRef {
                            op: zero,
                            byte,
                            bit,
                        },
                    });
                }
            }
            Ok(Denotation::Value(ValueDenot { dest, bits }))
        }
        WrongMachineModel::PackHalvesSwapped | WrongMachineModel::PackOrderReversed => {
            let dv = reg_operand(d)?;
            let mut bits = Vec::with_capacity(128);
            for i in 0..16u8 {
                let (op, elem) = match w {
                    WrongMachineModel::PackHalvesSwapped => {
                        if i < 8 {
                            (src, i)
                        } else {
                            (dv, i - 8)
                        }
                    }
                    _ => {
                        if i < 8 {
                            (dv, 7 - i)
                        } else {
                            (src, 15 - i)
                        }
                    }
                };
                for bit in 0..8u8 {
                    bits.push(BitSource::Sat {
                        op,
                        elem,
                        in_bits: 16,
                        out_bits: 8,
                        unsigned: true,
                        bit,
                    });
                }
            }
            Ok(Denotation::Value(ValueDenot { dest, bits }))
        }
        WrongMachineModel::PtestFlagsExchanged | WrongMachineModel::PtestZfCleared => {
            let Denotation::Flags {
                denot,
                reg_op,
                rm_op,
            } = machine_denotation(d)?
            else {
                return Err(SseModelError::FlagModelRequired);
            };
            let corrupted = if w == WrongMachineModel::PtestFlagsExchanged {
                FlagDenot {
                    cf: denot.zf,
                    zf: denot.cf,
                    ..denot
                }
            } else {
                FlagDenot {
                    zf: FlagExpr::Clear,
                    ..denot
                }
            };
            Ok(Denotation::Flags {
                denot: corrupted,
                reg_op,
                rm_op,
            })
        }
    }
}

/// One wrong-model control.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SseModelControl {
    /// What is wrong with it.
    pub label: &'static str,
    /// The wrong model.
    pub model: WrongMachineModel,
    /// The reason class this control MUST refute as, in exactly the sense the
    /// byte mutants' `expect` field means it: a control that "refutes" by some
    /// other route than the facet it is named for is not evidence about that
    /// facet. `operands SWAPPED` on PTEST is the case that forced this field —
    /// it used to pass because a `Denotation::Flags` is never `==` a
    /// `Denotation::FlagIntent`, which would have held with the operands left
    /// alone; it must refute as [`SseRefutationClass::Flags`], on the operands.
    pub expect: SseRefutationClass,
}

/// Every wrong-model label the hook requires to have fired ON EACH ROW it names.
///
/// PER ROW, not per family. The flat version of this list was a real hole: the
/// labels were accumulated across the WHOLE corpus and checked once at the end,
/// so a row all of whose entries are degenerate — `PUNPCKLQDQ xmm1,xmm1`, say —
/// could be credited with `operands SWAPPED`, `identity passthrough of the
/// SOURCE` and `identity passthrough of the DESTINATION` never having run
/// against it, because those labels had fired on some OTHER row. `PUNPCKLQDQ`
/// is precisely the row whose credit was withdrawn once before for a vacuous
/// obligation, so "elsewhere" is not good enough. A guard that skips a control
/// on ONE entry is now only admissible if the same control still runs on
/// ANOTHER entry OF THE SAME ROW.
pub const REQUIRED_MODEL_CONTROLS_PER_ROW: &[(SseLaneOp, &[&str])] = &[
    (SseLaneOp::Punpcklbw, UNPACK_MODEL_LABELS),
    (SseLaneOp::Punpckhbw, UNPACK_MODEL_LABELS),
    (SseLaneOp::Punpckldq, UNPACK_MODEL_LABELS),
    (SseLaneOp::Punpcklqdq, UNPACK_MODEL_LABELS),
    (
        SseLaneOp::Pshufd,
        &[
            "a constant-zero result",
            "operands SWAPPED",
            "PSHUFD ORDER fields read in reverse",
            "PSHUFD permuting the DESTINATION",
            "PSHUFHW: only the HIGH half permuted",
            "PSHUFLW: only the LOW half permuted",
        ],
    ),
    (
        SseLaneOp::MovdqaRR,
        &[
            "a constant-zero result",
            "operands SWAPPED",
            "MOVQ: the upper quadword ZEROED instead of copied",
            "identity passthrough of the DESTINATION",
            "the STORE direction: the r/m side written instead",
        ],
    ),
    (
        SseLaneOp::Pmovmskb,
        &[
            "a constant-zero result",
            "operands SWAPPED",
            "PMOVMSKB gathering bit 0 instead of the sign bit",
            "PMOVMSKB in reversed lane order",
            "PMOVMSKB sign-extending the upper bits instead of zeroing",
            "PMOVMSKB over the low 8 lanes only (the MMX form)",
        ],
    ),
    (
        SseLaneOp::Packuswb,
        &[
            "a constant-zero result",
            "operands SWAPPED",
            "identity passthrough of the SOURCE",
            "PACKUSWB with the halves swapped",
            "PACKUSWB with the element order reversed",
            "PACKUSWB modelled as the SIGNED pack",
        ],
    ),
    (
        SseLaneOp::Pblendvb,
        &[
            "a constant-zero result",
            "operands SWAPPED",
            "PBLENDVB taking the mask from the EXPLICIT source, not XMM0",
            "PBLENDVB selecting on bit 0 instead of the sign bit",
            "PBLENDVB with the arms swapped",
            "BLENDVPS: a DWORD-granular mask",
            "BLENDVPD: a QWORD-granular mask",
        ],
    ),
    (
        SseLaneOp::Ptest,
        &[
            "a constant-zero result",
            "operands SWAPPED",
            "PBLENDVB's value model for a flag-only instruction",
            "PTEST with ZF and CF EXCHANGED",
            "PTEST with ZF hard-wired to 0",
        ],
    ),
];

/// The wrong-model labels every one of the four unpack rows must show.
const UNPACK_MODEL_LABELS: &[&str] = &[
    "a constant-zero result",
    "operands SWAPPED",
    "WRONG HALF: the high interleave modelling the low one",
    "WRONG ELEMENT WIDTH: a different unpack granularity",
    "identity passthrough of the SOURCE",
    "identity passthrough of the DESTINATION",
    "the SATURATING PACK for an unpack",
];

/// THE WRONG-MODEL BATTERY for one captured encoding.
///
/// Every control carries the [`SseRefutationClass`] it must refute as, and
/// [`model_control_is_refuted`] runs it through [`denotations_agree`] — the
/// same comparison the obligation makes — so "this control refutes" now means
/// "the obligation would have caught this corruption, for this reason".
pub fn sse_model_controls(entry: &EmittedSseLane) -> Vec<SseModelControl> {
    use SseMnemonic as M;
    use SseRefutationClass as C;
    use WrongMachineModel as W;
    let c = |label, model, expect| SseModelControl {
        label,
        model,
        expect,
    };
    // A constant-zero result is refuted on the routed VALUE everywhere except
    // PMOVMSKB, where the corrupted model also writes the wrong PLACE (an XMM
    // rather than the GPR root the intent names), so the destination conjunct
    // gets there first.
    let zero_class = match entry.op {
        SseLaneOp::Pmovmskb => C::Dest,
        _ => C::Value,
    };
    let mut out = vec![c("a constant-zero result", W::ConstantZero, zero_class)];
    // SOME CONTROLS DEGENERATE ON SOME OPERANDS, and a control that cannot
    // refute is not evidence of anything — the hook would (correctly) refuse
    // the whole credit rather than accept a control that survives. Three
    // operand shapes cause this, and all are REAL emitted forms that must stay
    // in the corpus, so the controls are guarded per entry rather than the
    // entries dropped:
    //
    //   * `dst == src` (the `PUNPCKLQDQ x,x` low-quadword broadcast, the
    //     `PTEST m,m` mask self-test, `MOVDQA x,x`). "Identity passthrough of
    //     the DESTINATION" and "of the SOURCE" are then the SAME function, and
    //     for MOVDQA the STORE direction writes the same register it reads;
    //   * `src == xmm0` for PBLENDVB, where the explicit source IS the implicit
    //     mask, so "take the mask from the explicit source" names the right
    //     register by accident;
    //   * a FOLDED `xmm, m128` operand, where "operands SWAPPED" cannot be
    //     BUILT at all: there is no encoding whose ModRM.reg field is a memory
    //     location. This guard used to be missing, and the control was pushed
    //     anyway: `apply_wrong_machine_model` returned `Err`, and
    //     `model_control_is_refuted` scored an unbuildable model as "refuted by
    //     construction". 35 of the family's controls were vacuous that way, all
    //     of them counted into the number the gate row publishes. A battery may
    //     now only register a control that RUNS.
    //
    // Every guarded label still fires on other entries OF THE SAME ROW, and
    // `REQUIRED_MODEL_CONTROLS_PER_ROW` makes that a precondition of the
    // credit, so this narrows where a control runs and never whether it must
    // refute.
    //
    // "Same operand" is a question about register NUMBERS, not names: PMOVMSKB
    // names a GPR in the ModRM.reg field and an XMM in the r/m field, so
    // `r15d, xmm15` is ModRM `reg = rm = 15` and exchanging the two fields
    // produces the very same instruction.
    let dst_num = sdm_xmm(entry.dst).or_else(|| sdm_gpr32(entry.dst));
    let src_num = match entry.src {
        IntentOperand::Reg(s) => sdm_xmm(s),
        IntentOperand::Mem { .. } => None,
    };
    let rm_is_register = matches!(entry.src, IntentOperand::Reg(_));
    let symmetric_operands = dst_num.is_some() && dst_num == src_num;
    let src_is_the_mask = matches!(entry.src, IntentOperand::Reg("xmm0"));
    match entry.op {
        SseLaneOp::Punpcklbw
        | SseLaneOp::Punpckhbw
        | SseLaneOp::Punpckldq
        | SseLaneOp::Punpcklqdq => {
            let (other_half, other_width) = match entry.op {
                SseLaneOp::Punpcklbw => (M::PunpckhbwX, M::PunpcklwdX),
                SseLaneOp::Punpckhbw => (M::PunpcklbwX, M::PunpckhwdX),
                SseLaneOp::Punpckldq => (M::PunpckhdqX, M::PunpcklbwX),
                _ => (M::PunpckhqdqX, M::PunpckldqX),
            };
            out.push(c(
                "WRONG HALF: the high interleave modelling the low one",
                W::Mnemonic(other_half),
                C::Value,
            ));
            out.push(c(
                "WRONG ELEMENT WIDTH: a different unpack granularity",
                W::Mnemonic(other_width),
                C::Value,
            ));
            if !symmetric_operands {
                out.push(c(
                    "identity passthrough of the SOURCE",
                    W::IdentityOfSrc,
                    C::Value,
                ));
                out.push(c(
                    "identity passthrough of the DESTINATION",
                    W::IdentityOfDest,
                    C::Value,
                ));
            }
            out.push(c(
                "the SATURATING PACK for an unpack",
                W::Mnemonic(M::PackuswbX),
                C::Value,
            ));
        }
        SseLaneOp::Pshufd => {
            // A PALINDROMIC permutation is its own reversal, so the
            // reversed-ORDER model coincides with the right one and cannot
            // refute there. That is a property of the permutation, not a gap in
            // the obligation: the control is registered on every corpus entry
            // whose permutation is not a palindrome, and the hook requires the
            // label to have fired FOR THIS ROW. `tests/x86_sse_lane_gate.rs`
            // additionally sweeps all 256 immediates and requires the reversed
            // permutation to refute for every non-palindromic one.
            let palindrome = entry.perm.is_some_and(|p| p == [p[3], p[2], p[1], p[0]]);
            if !palindrome {
                out.push(c(
                    "PSHUFD ORDER fields read in reverse",
                    W::PshufdOrderReversed,
                    C::Value,
                ));
            }
            if !symmetric_operands {
                out.push(c(
                    "PSHUFD permuting the DESTINATION",
                    W::PshufdOnDest,
                    C::Value,
                ));
            }
            out.push(c(
                "PSHUFHW: only the HIGH half permuted",
                W::Mnemonic(M::PshufhwX),
                C::Value,
            ));
            out.push(c(
                "PSHUFLW: only the LOW half permuted",
                W::Mnemonic(M::PshuflwX),
                C::Value,
            ));
        }
        SseLaneOp::MovdqaRR => {
            out.push(c(
                "MOVQ: the upper quadword ZEROED instead of copied",
                W::Mnemonic(M::MovqZeroUpper),
                C::Value,
            ));
            if !symmetric_operands {
                out.push(c(
                    "identity passthrough of the DESTINATION",
                    W::IdentityOfDest,
                    C::Value,
                ));
                // The STORE direction writes the r/m side, so it is the
                // DESTINATION conjunct that catches it, not the routed bits.
                out.push(c(
                    "the STORE direction: the r/m side written instead",
                    W::Mnemonic(M::MovdqaStore),
                    C::Dest,
                ));
            }
        }
        SseLaneOp::Pmovmskb => {
            out.push(c(
                "PMOVMSKB gathering bit 0 instead of the sign bit",
                W::MaskFromBit0,
                C::Value,
            ));
            out.push(c(
                "PMOVMSKB in reversed lane order",
                W::MaskReversed,
                C::Value,
            ));
            out.push(c(
                "PMOVMSKB sign-extending the upper bits instead of zeroing",
                W::MaskSignExtended,
                C::Value,
            ));
            out.push(c(
                "PMOVMSKB over the low 8 lanes only (the MMX form)",
                W::MaskLow8LanesOnly,
                C::Value,
            ));
        }
        SseLaneOp::Packuswb => {
            if !symmetric_operands {
                out.push(c(
                    "PACKUSWB with the halves swapped",
                    W::PackHalvesSwapped,
                    C::Value,
                ));
            }
            out.push(c(
                "PACKUSWB with the element order reversed",
                W::PackOrderReversed,
                C::Value,
            ));
            out.push(c(
                "PACKUSWB modelled as the SIGNED pack",
                W::Mnemonic(M::PacksswbX),
                C::Value,
            ));
            if !symmetric_operands {
                out.push(c(
                    "identity passthrough of the SOURCE",
                    W::IdentityOfSrc,
                    C::Value,
                ));
            }
        }
        SseLaneOp::Pblendvb => {
            if !src_is_the_mask {
                out.push(c(
                    "PBLENDVB taking the mask from the EXPLICIT source, not XMM0",
                    W::BlendMaskFromSrc,
                    C::Value,
                ));
            }
            out.push(c(
                "PBLENDVB selecting on bit 0 instead of the sign bit",
                W::BlendOnBit0,
                C::Value,
            ));
            if !symmetric_operands {
                out.push(c(
                    "PBLENDVB with the arms swapped",
                    W::BlendArmsSwapped,
                    C::Value,
                ));
            }
            out.push(c(
                "BLENDVPS: a DWORD-granular mask",
                W::Mnemonic(M::BlendvpsX),
                C::Value,
            ));
            out.push(c(
                "BLENDVPD: a QWORD-granular mask",
                W::Mnemonic(M::BlendvpdX),
                C::Value,
            ));
        }
        SseLaneOp::Ptest => {
            // A VALUE model for a flag-only instruction: refuted as a SHAPE
            // mismatch, which `SseRefutationClass` files under `Value`. Stated
            // as such rather than left implicit — the point of the class is
            // that a control which "refutes" by shape alone is not evidence
            // about the FLAGS, and PTEST's flag facets are the two controls
            // below plus the ModRM-exchange byte mutant.
            out.push(c(
                "PBLENDVB's value model for a flag-only instruction",
                W::Mnemonic(M::PblendvbX),
                C::Value,
            ));
            out.push(c(
                "PTEST with ZF and CF EXCHANGED",
                W::PtestFlagsExchanged,
                C::Flags,
            ));
            out.push(c(
                "PTEST with ZF hard-wired to 0",
                W::PtestZfCleared,
                C::Flags,
            ));
        }
    }
    if !symmetric_operands && rm_is_register {
        // Exchanging the two operands moves the DESTINATION for every value
        // row; PTEST writes no value, so it is caught on the FLAG operands.
        out.push(c(
            "operands SWAPPED",
            W::OperandsSwapped,
            match entry.op {
                SseLaneOp::Ptest => C::Flags,
                _ => C::Dest,
            },
        ));
    }
    out
}

/// Run one wrong-model control: the real bytes and the real intent, with a
/// corrupted SDM model between them, must DISAGREE.
pub fn model_control_is_refuted(
    entry: &EmittedSseLane,
    control: &SseModelControl,
) -> Result<(), String> {
    let intent = entry.intent();
    let Ok(d) = sdm_decode_sse(entry.bytes) else {
        return Err(format!(
            "{}: the captured bytes do not decode, so its controls cannot run",
            entry.label()
        ));
    };
    let source = intent_denotation(&intent)
        .map_err(|e| format!("{}: the intent has no model: {e}", entry.label()))?;
    // AN UNBUILDABLE MODEL IS NOT A REFUTATION. This arm used to read
    // `Err(_) => Ok(())`, "a model that cannot be built is refuted by
    // construction", and it silently absorbed 35 controls that never compared
    // anything — every `operands SWAPPED` on a folded `xmm, m128` entry, where
    // there is no encoding with a memory ModRM.reg. Worse, it made the whole
    // mechanism defenceless: neutering one arm of
    // `apply_wrong_machine_model` to return `Err` left every test green while
    // that facet stopped being read. A battery must register only controls
    // that RUN; `sse_model_controls` guards the degenerate shapes by hand.
    let wrong = apply_wrong_machine_model(&d, control.model).map_err(|e| {
        format!(
            "wrong-model control could not be BUILT — `{}` on {}: {e}. An unbuildable model \
             compares nothing and is not evidence about any facet; guard the control in \
             sse_model_controls instead of registering one that cannot run",
            control.label,
            entry.label()
        )
    })?;
    // THROUGH THE REAL COMPARISON, with the declared reason class — not a bare
    // `!=`. `operands SWAPPED` on PTEST used to "refute" because
    // `Denotation::Flags` is never `==` a `Denotation::FlagIntent`, which is
    // true with the operands left alone; it must refute on the flag OPERANDS.
    match denotations_agree(&source, &wrong) {
        Ok(_) => Err(format!(
            "wrong-model control SURVIVED — `{}` on {}: the corrupted SDM model still agrees with \
             the machine-IR intent, so the obligation does not read that facet",
            control.label,
            entry.label()
        )),
        Err(r) if r.class() != control.expect => Err(format!(
            "wrong-model control refuted for the WRONG REASON — `{}` on {}: it must refute as \
             {:?} but refuted as {:?} ({r})",
            control.label,
            entry.label(),
            control.expect,
            r.class()
        )),
        Err(_) => Ok(()),
    }
}

// ===========================================================================
// (13) The coverage-gate credit hook
// ===========================================================================

/// What the credit hook established, for the gate rows' notes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SseLaneCredit {
    /// Captured real encodings that hold.
    pub entries: usize,
    /// Distinct rows covered — all ten are required.
    pub rows_covered: usize,
    /// Entries in the register-register form.
    pub register_forms: usize,
    /// Entries in the folded `xmm, m128` form.
    pub memory_forms: usize,
    /// Result bits compared across the corpus, exactly.
    pub bits_compared: usize,
    /// Byte mutants run — every one refuted for its stated reason class.
    pub byte_mutants_refuted: usize,
    /// Wrong-model controls run — every one disagreed with the intent.
    pub model_controls_refuted: usize,
    /// Inputs the PACKUSWB narrow was checked on: all 65536.
    pub saturation_cases: usize,
    /// Witnesses PTEST's two flag formulations agreed on.
    pub ptest_witnesses: usize,
}

/// The things a green row here does NOT say, carried as DATA so the gate test
/// can pin them and a reader cannot over-read the row. Prose in a header can
/// drift away from what the code does; this list is asserted.
pub const X86_SSE_LANE_DEFERRALS: &[&str] = &[
    "NOT that instruction selection chose the right instruction, permutation, mask or operands \
     for the trust-ir it was lowering — the intent side is the emitted instruction's own intent",
    "NOT, for PSHUFD, that the intended permutation recorded in the corpus is the one instruction \
     selection wanted, and NOT that instruction selection packs its immediate by the SDM's \
     ORDER-field packing convention: the corpus perm is hand transcribed from the isel's \
     immediate literals and the live sweep hands the encoder an imm packed that same way, so an \
     isel-side packing bug moves both sides together. What IS refuted is an ENCODER that mutates \
     the imm8 it was handed, and the SDM UNPACKING convention is anchored on silicon",
    "NOT, for MOVDQA register-register and PMOVMSKB, that the two sides of the ROUTING comparison \
     are structurally distinct: a 128-bit copy and a sign-bit gather are the same construction in \
     both, so for those two rows the comparison decides the mnemonic and direction, the \
     destination, the width and the operand identity — each with a refuting wrong-model control — \
     and a SHARED misreading is caught only by the native-silicon differential",
    "NOT that the SDM transcriptions are right: they are this family's TRUST BASE. The native \
     silicon differential in tests/x86_sse_lane_gate.rs is one CPU model, not a proof",
    "NOT, for PTEST, anything about the consuming Jcc/CMOVcc condition mapping, nor that testing a \
     canonical mask is the right predicate lowering; and `AF <- OF <- PF <- SF <- 0` is \
     SDM-transcribed trust base, anchored on silicon only for ZF and CF",
    "NOT, for MOVDQA register-register, that a copy was the right thing to emit, and NOT that \
     MOVDQA differs from MOVDQU in VALUE — it does not. That separation is the MNEMONIC-identity \
     conjunct",
    "NOT that a folded xmm,m128 operand is 16-byte aligned; the legacy-SSE forms #GP when it is \
     not, and the memory denotations ASSUME alignment. The already-green packed rows carry the \
     same pre-existing gate-wide assumption",
    "NOT two-address tie correctness, register allocation, or XMM0 liveness and clobber around \
     PBLENDVB — post_ra_dataflow owns those",
    "NOTHING beyond the captured corpus at gate time; the full register and imm8 sweeps run in \
     the dev-dependency test",
    "NOTHING about upper YMM/ZMM state, #UD feature gating for the SSE4.1 forms, or MXCSR",
    "NOT a per-instruction certificate in compiles: these opcodes stay per-instruction Unverified \
     until they are wired into x86_opcode_to_source_op, which is deliberately not part of this \
     change",
];

/// The byte-mutant battery builder the hook runs per corpus entry.
pub type SseByteBattery<'a> = &'a dyn Fn(&EmittedSseLane) -> Vec<SseByteMutant>;

/// The wrong-model battery builder the hook runs per corpus entry.
pub type SseModelBattery<'a> = &'a dyn Fn(&EmittedSseLane) -> Vec<SseModelControl>;

/// THE COVERAGE-GATE CREDIT HOOK for the ten SSE lane rows.
///
/// `Ok` iff ALL of:
///
/// 1. [`EMITTED_X86_SSE_LANE_INSTANCES`] is non-empty and EVERY captured
///    encoding holds — an empty set is not a discharged set;
/// 2. ROW COVERAGE: all ten rows appear. A corpus that had quietly lost a row
///    cannot credit it;
/// 3. THE TEETH: every byte mutant and every wrong-model control refutes
///    THROUGH [`denotations_agree`] — the comparison the obligation itself
///    makes — FOR ITS STATED REASON CLASS, and every label in
///    [`COMMON_BYTE_MUTANT_LABELS`], [`REQUIRED_BYTE_MUTANTS_PER_ROW`] and
///    [`REQUIRED_MODEL_CONTROLS_PER_ROW`] fired ON THE ROW IT NAMES. "A lane
///    that cannot show refuting controls has not met the bar" is literally a
///    precondition of green here, not a property of some test elsewhere;
/// 4. [`saturation_obligation`] holds over all 65536 inputs, with its own
///    controls refuted;
/// 5. [`ptest_obligation`] holds over the whole witness family, with its own
///    flag controls refuted.
///
/// What the hook cannot check is that the corpus is still what the live
/// encoder emits: this crate cannot run the encoder. The re-derivation lives in
/// `tests/support/sse_lane_live_encode.rs` and is run by `x86_sse_lane_gate`
/// and by `coverage_gate_tests` (in the two tests that PIN the ratio), both of
/// which run in the local meta-gate. That placement is the point: while the
/// freshness check lived only in `x86_sse_lane_gate`, an encoder change that
/// made these bytes wrong left the ratio-pinning targets green over a stale
/// capture.
///
/// The verdict is computed ONCE per process: the corpus, the batteries and both
/// extra obligations are constants, so every call would otherwise repeat the
/// same several million comparisons for each of the ten rows the gate audits.
pub fn sse_lane_discharges_valid() -> Result<SseLaneCredit, String> {
    use std::sync::OnceLock;
    static ONCE: OnceLock<Result<SseLaneCredit, String>> = OnceLock::new();
    ONCE.get_or_init(|| sse_lane_credit_over(EMITTED_X86_SSE_LANE_INSTANCES))
        .clone()
}

/// [`sse_lane_discharges_valid`] over an explicit corpus. The gate hook always
/// passes [`EMITTED_X86_SSE_LANE_INSTANCES`]; this entry point exists so the
/// gate test can show the hook FAILING CLOSED on an empty corpus, on a corpus
/// missing a row, and on one carrying a wrong encoding.
pub fn sse_lane_credit_over(corpus: &[EmittedSseLane]) -> Result<SseLaneCredit, String> {
    sse_lane_credit_over_with(corpus, &sse_byte_mutants, &sse_model_controls)
}

/// The credit hook with every ingredient explicit.
///
/// It is public so the gate test can hand the hook a battery with a SURVIVING
/// control, a control that refutes for the WRONG REASON, or a battery missing a
/// required label, and require a refusal each time. Without that, a hook whose
/// control check had been weakened would still discharge on today's
/// all-refuting controls and no test would notice.
pub fn sse_lane_credit_over_with(
    corpus: &[EmittedSseLane],
    byte_battery: SseByteBattery<'_>,
    model_battery: SseModelBattery<'_>,
) -> Result<SseLaneCredit, String> {
    if corpus.is_empty() {
        return Err(
            "the captured SSE lane corpus is empty — an empty set is not a discharged set"
                .to_string(),
        );
    }
    let mut rows = BTreeSet::new();
    // PER ROW, not per family: `(row, label)` pairs, so a control that fired on
    // some other row cannot stand in for one that never ran on this one.
    let mut byte_labels: BTreeSet<(SseLaneOp, &'static str)> = BTreeSet::new();
    let mut model_labels: BTreeSet<(SseLaneOp, &'static str)> = BTreeSet::new();
    let mut credit = SseLaneCredit {
        entries: 0,
        rows_covered: 0,
        register_forms: 0,
        memory_forms: 0,
        bits_compared: 0,
        byte_mutants_refuted: 0,
        model_controls_refuted: 0,
        saturation_cases: 0,
        ptest_witnesses: 0,
    };

    for entry in corpus {
        let intent = entry.intent();
        let holds = sse_lane_check(&intent, entry.bytes)
            .map_err(|r| format!("captured encoding REFUTED — {}: {r}", entry.label()))?;
        credit.entries += 1;
        credit.bits_compared += holds.bits_compared;
        rows.insert(entry.op);
        match entry.src {
            IntentOperand::Reg(_) => credit.register_forms += 1,
            IntentOperand::Mem { .. } => credit.memory_forms += 1,
        }

        let battery = byte_battery(entry);
        if battery.is_empty() {
            return Err(format!("{}: produced no byte mutants", entry.label()));
        }
        for m in &battery {
            byte_control_is_refuted_as_stated(m)?;
            byte_labels.insert((entry.op, m.label));
            credit.byte_mutants_refuted += 1;
        }

        let models = model_battery(entry);
        if models.is_empty() {
            return Err(format!(
                "{}: produced no wrong-model controls",
                entry.label()
            ));
        }
        for c in &models {
            model_control_is_refuted(entry, c)?;
            model_labels.insert((entry.op, c.label));
            credit.model_controls_refuted += 1;
        }
    }

    credit.rows_covered = rows.len();
    for row in SSE_LANE_ROWS {
        if !rows.contains(&row) {
            return Err(format!(
                "row {row:?} has no captured encoding — a corpus that does not reach a row cannot \
                 credit it"
            ));
        }
        for want in COMMON_BYTE_MUTANT_LABELS {
            if !byte_labels.contains(&(row, *want)) {
                return Err(format!(
                    "required byte-mutant control `{want}` never fired ON ROW {row:?} — that row's \
                     entries are all degenerate for it, so it is credited with a facet nothing \
                     defended"
                ));
            }
        }
        for (r, wants) in REQUIRED_BYTE_MUTANTS_PER_ROW {
            if *r != row {
                continue;
            }
            for want in *wants {
                if !byte_labels.contains(&(row, *want)) {
                    return Err(format!(
                        "required byte-mutant control `{want}` never fired ON ROW {row:?} — the \
                         battery has stopped defending that facet for this row"
                    ));
                }
            }
        }
        for (r, wants) in REQUIRED_MODEL_CONTROLS_PER_ROW {
            if *r != row {
                continue;
            }
            for want in *wants {
                if !model_labels.contains(&(row, *want)) {
                    return Err(format!(
                        "required wrong-model control `{want}` never fired ON ROW {row:?} — the \
                         battery has stopped defending that facet for this row, and a control that \
                         fired on some OTHER row is not evidence about this one"
                    ));
                }
            }
        }
    }

    credit.saturation_cases = saturation_obligation()?;
    credit.ptest_witnesses = ptest_obligation()?;
    Ok(credit)
}

// ===========================================================================
// (14) Evaluating a denotation, for the native-silicon differential
// ===========================================================================

/// SDM Vol 2B PACKSSWB, `SaturateSignedWordToSignedByte`.
pub fn sdm_saturate_signed_word_to_signed_byte(w: u16) -> u8 {
    let s = w as i16;
    if s < -128 {
        0x80
    } else if s > 127 {
        0x7F
    } else {
        (s & 0xFF) as u8
    }
}

/// SDM Vol 2B PACKSSDW, `SaturateSignedDwordToSignedWord`.
pub fn sdm_saturate_signed_dword_to_signed_word(d: u32) -> u16 {
    let s = d as i32;
    if s < -32768 {
        0x8000
    } else if s > 32767 {
        0x7FFF
    } else {
        (s & 0xFFFF) as u16
    }
}

/// Evaluate ONE [`BitSource`] on concrete operand values.
///
/// `values` supplies the sixteen bytes of each operand, least significant
/// first. This exists so `tests/x86_sse_lane_gate.rs` can run the SDM
/// denotation against what the CPU actually does; the gate credit itself never
/// evaluates a value row, because comparing the denotations decides the
/// question for every input at once.
pub fn eval_bit_source(b: &BitSource, values: &dyn Fn(Operand) -> [u8; 16]) -> bool {
    let bit_of = |op: Operand, byte: u8, bit: u8| (values(op)[byte as usize] >> bit) & 1 == 1;
    match *b {
        BitSource::Zero => false,
        BitSource::Bit { op, byte, bit } => bit_of(op, byte, bit),
        BitSource::Sat {
            op,
            elem,
            in_bits,
            unsigned,
            bit,
            ..
        } => {
            let v = values(op);
            let width = usize::from(in_bits / 8);
            let base = usize::from(elem) * width;
            let mut x: u32 = 0;
            for k in 0..width {
                x |= u32::from(v[base + k]) << (8 * k);
            }
            let out: u32 = if in_bits == 16 {
                let w = x as u16;
                u32::from(if unsigned {
                    sdm_saturate_signed_word_to_unsigned_byte(w)
                } else {
                    sdm_saturate_signed_word_to_signed_byte(w)
                })
            } else {
                u32::from(sdm_saturate_signed_dword_to_signed_word(x))
            };
            (out >> bit) & 1 == 1
        }
        BitSource::Select {
            ctl,
            ctl_byte,
            ctl_bit,
            one,
            zero,
        } => {
            let taken = if bit_of(ctl, ctl_byte, ctl_bit) {
                one
            } else {
                zero
            };
            bit_of(taken.op, taken.byte, taken.bit)
        }
    }
}

/// Evaluate a whole [`ValueDenot`], returning the result bits packed little-end
/// first. A 64-bit GPR result occupies the low 64 bits and the rest are zero.
pub fn eval_value_denot(v: &ValueDenot, values: &dyn Fn(Operand) -> [u8; 16]) -> u128 {
    let mut out = 0u128;
    for (i, b) in v.bits.iter().enumerate() {
        if eval_bit_source(b, values) {
            out |= 1u128 << i;
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_credit_hook_discharges() {
        let credit = sse_lane_discharges_valid().expect("the SSE lane credit must discharge");
        assert_eq!(credit.rows_covered, 10, "all ten rows must be covered");
        assert!(credit.entries >= 100, "corpus: {}", credit.entries);
        assert!(
            credit.memory_forms > 0,
            "the folded m128 form must be covered"
        );
        assert_eq!(credit.saturation_cases, 65536);
        assert!(credit.byte_mutants_refuted > 500);
        assert!(credit.model_controls_refuted > 200);
    }

    #[test]
    fn packuswb_narrow_is_exhaustive_and_its_controls_refute() {
        assert_eq!(saturation_obligation().unwrap(), 65536);
        // The boundary the bit-pattern and arithmetic formulations must agree on.
        assert_eq!(sdm_saturate_signed_word_to_unsigned_byte(0x8000), 0x00);
        assert_eq!(sdm_saturate_signed_word_to_unsigned_byte(0x0100), 0xFF);
        assert_eq!(sdm_saturate_signed_word_to_unsigned_byte(0x00FF), 0xFF);
        assert_eq!(sdm_saturate_signed_word_to_unsigned_byte(0x0080), 0x80);
        // The unsigned-input control differs exactly where a careless reading
        // of "unsigned saturation" goes wrong.
        assert_eq!(NarrowControl::UnsignedInput.apply(0x8000), 0xFF);
    }

    #[test]
    fn ptest_witnesses_reach_both_polarities_of_both_computed_flags() {
        let machine = sdm_ptest_flags();
        let w = ptest_witnesses();
        let mut seen = [false; 4]; // ZF=0, ZF=1, CF=0, CF=1
        for &(dest, src) in &w {
            let f = eval_flag_denot(&machine, dest, src);
            seen[usize::from(f[3])] = true;
            seen[2 + usize::from(f[0])] = true;
        }
        assert!(
            seen.iter().all(|&b| b),
            "the witness family must reach ZF=0, ZF=1, CF=0 and CF=1: {seen:?}"
        );
        assert_eq!(ptest_obligation().unwrap(), w.len());
    }

    #[test]
    fn an_empty_corpus_is_not_a_discharged_corpus() {
        assert!(sse_lane_credit_over(&[]).is_err());
    }

    #[test]
    fn a_corpus_missing_a_row_cannot_credit_that_row() {
        let narrowed: Vec<EmittedSseLane> = EMITTED_X86_SSE_LANE_INSTANCES
            .iter()
            .copied()
            .filter(|e| e.op != SseLaneOp::Ptest)
            .collect();
        let err = sse_lane_credit_over(&narrowed).unwrap_err();
        assert!(err.contains("Ptest"), "{err}");
    }

    #[test]
    fn the_hook_refuses_a_surviving_control() {
        // A battery whose "control" is the CORRECT model must be refused: a
        // control that does not refute means the obligation is not faithful.
        let surviving = |_: &EmittedSseLane| {
            vec![SseModelControl {
                label: "deliberately CORRECT, so it must survive",
                model: WrongMachineModel::Mnemonic(SseMnemonic::PunpcklbwX),
                expect: SseRefutationClass::Value,
            }]
        };
        let err = sse_lane_credit_over_with(
            EMITTED_X86_SSE_LANE_INSTANCES,
            &sse_byte_mutants,
            &surviving,
        )
        .unwrap_err();
        assert!(err.contains("SURVIVED"), "{err}");
    }

    #[test]
    fn the_hook_refuses_a_control_that_refutes_for_the_wrong_reason() {
        let mislabelled = |e: &EmittedSseLane| {
            let mut v = sse_byte_mutants(e);
            for m in &mut v {
                m.expect = SseRefutationClass::Model;
            }
            v
        };
        let err = sse_lane_credit_over_with(
            EMITTED_X86_SSE_LANE_INSTANCES,
            &mislabelled,
            &sse_model_controls,
        )
        .unwrap_err();
        assert!(err.contains("WRONG REASON"), "{err}");
    }

    /// THE ATTACK THAT MOTIVATED THE PER-ROW LABELS, run as a test.
    ///
    /// Reduce PUNPCKLQDQ to the single `xmm1,xmm1` self-pair the pipeline emits
    /// as a low-quadword broadcast. Every operand-identity control degenerates
    /// on that entry — "operands SWAPPED", "identity passthrough of the
    /// SOURCE" and "identity passthrough of the DESTINATION" are all skipped —
    /// and while the required labels were checked per FAMILY the row was still
    /// credited, because those labels had fired on OTHER rows. PUNPCKLQDQ is
    /// the very row whose credit was once withdrawn for a vacuous obligation,
    /// so this must fail, and it must fail naming that row.
    #[test]
    fn a_row_whose_controls_all_degenerate_cannot_be_credited() {
        let narrowed: Vec<EmittedSseLane> = EMITTED_X86_SSE_LANE_INSTANCES
            .iter()
            .copied()
            .filter(|e| {
                e.op != SseLaneOp::Punpcklqdq
                    || (e.dst == "xmm1" && e.src == IntentOperand::Reg("xmm1"))
            })
            .collect();
        assert!(
            narrowed.iter().any(|e| e.op == SseLaneOp::Punpcklqdq),
            "the narrowed corpus must still REACH the row, or this would only be the \
             missing-row check"
        );
        let err = sse_lane_credit_over(&narrowed).unwrap_err();
        assert!(
            err.contains("Punpcklqdq") && err.contains("never fired ON ROW"),
            "{err}"
        );
    }

    /// An unbuildable wrong model is not a refutation. `operands SWAPPED` on a
    /// folded `xmm, m128` entry cannot be built — there is no encoding whose
    /// ModRM.reg field is a memory location — and the hook must say so rather
    /// than count it.
    #[test]
    fn the_hook_refuses_a_control_that_cannot_be_built() {
        let unbuildable = |_: &EmittedSseLane| {
            vec![SseModelControl {
                label: "operands SWAPPED",
                model: WrongMachineModel::OperandsSwapped,
                expect: SseRefutationClass::Dest,
            }]
        };
        let err = sse_lane_credit_over_with(
            EMITTED_X86_SSE_LANE_INSTANCES,
            &sse_byte_mutants,
            &unbuildable,
        )
        .unwrap_err();
        assert!(err.contains("could not be BUILT"), "{err}");
    }

    /// A wrong-model control must refute for the class it declares, exactly as
    /// a byte mutant must.
    #[test]
    fn the_hook_refuses_a_model_control_that_refutes_for_the_wrong_reason() {
        let mislabelled = |e: &EmittedSseLane| {
            let mut v = sse_model_controls(e);
            for c in &mut v {
                c.expect = SseRefutationClass::Model;
            }
            v
        };
        let err = sse_lane_credit_over_with(
            EMITTED_X86_SSE_LANE_INSTANCES,
            &sse_byte_mutants,
            &mislabelled,
        )
        .unwrap_err();
        assert!(err.contains("WRONG REASON"), "{err}");
    }

    /// PTEST's MACHINE-SIDE FLAG MODEL IS READ BY THE OBLIGATION.
    ///
    /// It was not: the comparison destructured `Denotation::Flags { .. }`,
    /// discarded the decoded `denot` and then rebuilt `sdm_ptest_flags()` from
    /// the constant, so `machine_denotation`'s `PtestX` arm could have returned
    /// any flag model at all and the row would have stayed green. Corrupt the
    /// DECODED model and the comparison must refute, on FLAGS.
    #[test]
    fn a_corrupted_ptest_flag_model_refutes_through_the_comparison() {
        let entry = EMITTED_X86_SSE_LANE_INSTANCES
            .iter()
            .find(|e| e.op == SseLaneOp::Ptest && !matches!(e.src, IntentOperand::Mem { .. }))
            .expect("the corpus carries a register-form PTEST");
        let d = sdm_decode_sse(entry.bytes).expect("it decodes");
        let source = intent_denotation(&entry.intent()).expect("the intent has a model");
        // Uncorrupted: it holds.
        let machine = machine_denotation(&d).expect("the bytes have a model");
        denotations_agree(&source, &machine).expect("the real PTEST model must agree");
        // Corrupted: it refutes, on the flags.
        for model in [
            WrongMachineModel::PtestFlagsExchanged,
            WrongMachineModel::PtestZfCleared,
        ] {
            let wrong = apply_wrong_machine_model(&d, model).expect("the control builds");
            assert_ne!(wrong, machine, "{model:?} must actually corrupt something");
            let r = denotations_agree(&source, &wrong)
                .expect_err("a corrupted PTEST flag model must REFUTE");
            assert_eq!(r.class(), SseRefutationClass::Flags, "{model:?}: {r}");
        }
    }

    /// Every credited row is named by both per-row control tables, and every
    /// label those tables demand is one the batteries can actually produce.
    #[test]
    fn the_per_row_control_tables_cover_every_row() {
        for row in SSE_LANE_ROWS {
            assert!(
                REQUIRED_MODEL_CONTROLS_PER_ROW
                    .iter()
                    .any(|(r, _)| *r == row),
                "{row:?} has no required wrong-model controls"
            );
            assert!(
                REQUIRED_BYTE_MUTANTS_PER_ROW.iter().any(|(r, _)| *r == row),
                "{row:?} has no per-row byte-mutant entry"
            );
        }
        let produced: BTreeSet<(SseLaneOp, &'static str)> = EMITTED_X86_SSE_LANE_INSTANCES
            .iter()
            .flat_map(|e| {
                sse_model_controls(e)
                    .into_iter()
                    .map(move |c| (e.op, c.label))
                    .chain(
                        sse_byte_mutants(e)
                            .into_iter()
                            .map(move |m| (e.op, m.label)),
                    )
            })
            .collect();
        for (row, labels) in REQUIRED_MODEL_CONTROLS_PER_ROW
            .iter()
            .chain(REQUIRED_BYTE_MUTANTS_PER_ROW.iter())
        {
            for label in *labels {
                assert!(
                    produced.contains(&(*row, *label)),
                    "{row:?} requires `{label}`, which its battery never produces"
                );
            }
        }
    }

    #[test]
    fn the_hook_refuses_a_battery_missing_a_required_label() {
        let thin = |e: &EmittedSseLane| {
            sse_byte_mutants(e)
                .into_iter()
                .filter(|m| m.label != "a trailing byte")
                .collect::<Vec<_>>()
        };
        let err =
            sse_lane_credit_over_with(EMITTED_X86_SSE_LANE_INSTANCES, &thin, &sse_model_controls)
                .unwrap_err();
        assert!(err.contains("never fired"), "{err}");
    }
}
