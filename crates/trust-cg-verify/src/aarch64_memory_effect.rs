// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Word-bound, decomposed memory-effect obligations for the AArch64 scalar and
//! pair memory rows (ledger `L07-P2`, `X-OPCODES-P1`, `L04-P7`) and the NEON
//! `LD1`/`ST1` single-register post-index transfers (`L04-P6`).
//!
//! # Why a decomposition
//!
//! The two earlier memory obligations were each ONE formula per instruction.
//! [`crate::aarch64_pair_memory_proofs`] states both transfers and the base
//! writeback as a McCarthy read-over-write expansion: every probed byte is an
//! `ite` chain whose conditions are 64-bit address equalities
//! `(= (bvadd base c1) (bvadd base c2))`, a few hundred of them per pair, each
//! of which a bit-blasting prover turns into a 64-bit adder and a 64-bit
//! comparator (the store form measured 11 KB of SMT-LIB and hundreds of
//! thousands of Alethe steps; see the 2026-09-29 report). The
//! instruction-derived scalar obligation
//! ([`crate::aarch64_instruction_word_proofs`]) states a load's bytes as one
//! symbolic value and so says nothing about which bytes are read.
//!
//! This module states the same architectural effect as a set of SMALL
//! obligations whose proofs need only ground bit-vector evaluation, `bvadd`
//! with one symbolic operand, `extract`/`concat`/`sign_extend`, `bvor`/`bvand`
//! of positioned bytes and `ite` over ground conditions. No part contains a
//! shift or multiplication by a symbolic amount, an array, an uninterpreted
//! function, a quantifier or `zero_extend` (spelled as `concat` with zero
//! bits, which the packaged Clean checks; see `zero_extend` below).
//!
//! # Bound to the word
//!
//! The instruction WORD is a 32-bit literal inside every part. The machine side
//! of each part is computed from that literal's bits by SMT terms (`extract` of
//! the fields, sign or zero extension of the immediate, scaling as
//! `concat` with zero bits, the width and extension selected by `ite` over the
//! size/opc/V fields, the addressing mode by `ite` over its two bits), not by a
//! Rust decoder, so a checked certificate of a part is a statement about THAT
//! word. The word is the one [`memory_effect_word`] re-derives from the
//! operands (the pair encoder of [`crate::aarch64_pair_memory_proofs`], the
//! scalar encoder of [`crate::aarch64_instruction_word_proofs`]). ENC-5
//! requires, per compile and in its default `enforce` mode, the emitted word
//! to equal it ([`check_emitted_memory_effect_word`]), so the literal is the
//! word the object carries.
//!
//! The intent side of each part is built from the OPERANDS alone (the byte
//! offset, the transfer width the register class names, the addressing mode
//! the opcode fixes, the register numbers).
//!
//! # The parts
//!
//! For one admitted instruction:
//!
//! * `fields` (ground): every non-immediate field of the word equals the value
//!   the operands name: class bits, `V` (bank), `opc`/`size` (width), the
//!   addressing mode, `L` (direction) and the five-bit register fields `Rt`,
//!   `Rt2` (pairs) and `Rn`.
//! * `address lane i`: the lane's effective address the word computes, over a
//!   symbolic base, equals the one the operands name (`base + offset` for the
//!   offset and pre-index forms and for scalar accesses, `base` for
//!   post-index; lane 1 of a pair is lane 0 plus the word's element size,
//!   against `base + offset + n` from the operands).
//! * `writeback` (pairs, `LD1`/`ST1`): the base register the word leaves
//!   (`base + offset` for pre- and post-index, `base` for the signed-offset
//!   form; for `LD1`/`ST1`, `base` plus the 8 or 16 bytes the `Q` bit
//!   transfers) equals the operands'. `LD1`/`ST1` (multiple structures)
//!   address `X[n]` in every form, so their one lane address is the base the
//!   `fields` part names and they have no `address` part.
//! * `load lane i` (loads; Q lanes in two 64-bit halves): the value the word
//!   writes into its destination register view, assembled from the bytes of a
//!   symbolic 8-byte memory window at the lane address as Arm's little-endian
//!   `Mem[]` places them (byte `k` at bits `8k+7:8k`, zero elsewhere, OR-ed),
//!   and zero- or sign-extended as the word's `opc` says, equals the operands'
//!   value: the window's low `n` bytes as a number, zero-extended to the
//!   register view.
//! * `store lane i` (stores; Q lanes in two halves): the 8-byte window the
//!   word leaves (each byte the data register's byte where the word's size
//!   covers it, the old byte elsewhere) equals the window the operands' store
//!   leaves (the data's low `n` bytes over the old window's high bytes).
//! * A 64-bit `LD1` also states its upper register half (zero) and a 64-bit
//!   `ST1` the 8 bytes after its window (unchanged), so a word that transfers
//!   16 bytes refutes there as well as in `fields`.
//!
//! # The composition, and its assumptions
//!
//! When every part holds, executing the word (Arm DDI 0487 pseudo-code of
//! `LDR`/`STR` (immediate) and `LDP`/`STP`) from ANY register file and memory
//! gives the same registers and memory as the operands' scalarized accesses:
//!
//! 1. `fields` fixes the instruction class, direction, bank, width, addressing
//!    mode and the registers read and written, so both sides read and write the
//!    same registers, and the word writes memory only at the lane addresses for
//!    the lane widths the operands name.
//! 2. `address` and `writeback` fix every address and the base update.
//! 3. Memory is a function of the address (A5), so equal lane addresses read
//!    the same window; the window of each lane is the 8 bytes at its address
//!    (and at address `+ 8` for a Q lane's high half). `load` and `store` fix
//!    each lane's register value and each written byte; bytes outside the lane
//!    windows are written by neither side (by 1).
//!
//! The Rust side applies A6 when it names the parts' variables; everything
//! else is in the certified statements. Assumptions, and where each is
//! discharged:
//!
//! * **A1 little-endian data** (`SCTLR_EL1.E0E = 0`): the platform ABI of
//!   `aarch64-apple-darwin` and `aarch64-unknown-linux-gnu`; stated, not
//!   checked.
//! * **A2 no alignment fault**: an SP-based access needs a 16-byte-aligned SP
//!   under SP alignment checking; other accesses are to Normal memory with
//!   alignment checking off. Stated, not discharged here: the frame layout's
//!   16-byte SP invariant is checked by the frame lowering, not by this module.
//! * **A3 no concurrent writer** between the two lanes of a pair (a pair is not
//!   single-copy atomic as a whole): the source language's data-race freedom;
//!   stated.
//! * **A4 no constrained-unpredictable overlap**: `LDP` with `Rt == Rt2`, and
//!   writeback with a GPR transfer register equal to a non-SP base, are refused
//!   at admission; the two lanes of a pair cover disjoint bytes by
//!   construction.
//! * **A5 Normal memory**: each byte address holds one value, reads have no
//!   side effect and do not fault (congruence of the window variables);
//!   stated.
//! * **A6 register naming**: field 31 is SP in the base position and the zero
//!   register in a transfer position (it reads as zero); other values name
//!   the register with that number in the bank `V` names. Applied by the Rust
//!   side from the `fields` part's values.
//!
//! # What the decomposition is, and is not, worth
//!
//! A checked certificate of every part shows that THIS word performs THE
//! memory access its machine-IR operands name. That is the claim the
//! Formal-only bound-memory rule credits (owner ruling 2026-09-29,
//! [`crate::bound_memory_authority`]), but the rule names its own evidence: a
//! committed certificate of the row's FORM theorem that the independent
//! checker replays. A Clean-checked part is not that evidence, and it is not
//! admitted (OD-39 in docs/decision-record.md), so the function verifier never credits a
//! row on these parts ([`crate::function_verifier::FunctionVerifier::with_memory_effect`]).
//! It applies the decomposition to every admitted row AFTER the row's own lane
//! (the pair lane or the instruction-derived lane) and the rule: a refuted
//! part fails the row, credited or not; a credited row stays credited; an
//! uncredited row keeps its reason and gains
//! [`crate::function_verifier::MEMORY_EFFECT_IS_NOT_CREDIT`] with how many
//! parts have a Clean-checked certificate. Neither the parts nor the form
//! theorems bind the operands to a source instruction or a frame contract: a
//! prologue that saves the wrong register pair, or a load that reads the
//! wrong slot, is certified exactly as well.
//!
//! The exception is a row a source-bound owner binds
//! ([`crate::aarch64_memory_source_binding`]): a frame record of a
//! source-bound leaf frame, or a scalar access of a source-bound memory leaf.
//! Its operands must name exactly the access the owner's source contract
//! names, and it is credited only when every part has a Clean-checked
//! certificate of its exact query, through the same replay the frame and ALU
//! owners use. The parts of an unbound row stay a refutation check and a
//! diagnostic.
//!
//! The live replay that finds out is a diagnostic
//! ([`crate::diag::memory_effect_replay_enabled`], bridge knob
//! `memory-effect-replay`), off by default: its verdict is recorded, never
//! credited, and with the Trust package's AY (9192) every replay ends in an
//! uncertified answer at a measured cost of about a solve and a resident-AY
//! restart per distinct word and process
//! (`reports/2026-09-29-darwin-memory-effect-certificates`).
//!
//! # In-process decision
//!
//! [`decide_in_process`] evaluates a ground part once and decides every
//! symbolic part of an admitted word exactly ([`decide_exactly`]: after
//! folding the word's fields, an address or writeback part is `base + c`
//! against `base + c'`, and a load or store part is a pure bit routing), so no
//! admitted word reaches the sampling lane. That is testing-grade evidence
//! about this module's terms, not a certificate.
//!
//! # Every scalar form (L04-P1)
//!
//! Beyond the general-purpose zero-extending immediates the instruction-
//! derived lane re-derives words for, every attributable scalar form is
//! admitted through the form binder
//! ([`crate::aarch64_scalar_memory_proofs::bind_scalar_memory_instruction`]):
//! `H`/`S`/`D`/`Q` transfers (their word from the scalar form encoder,
//! [`crate::aarch64_scalar_memory_proofs::scalar_memory_word`], which the
//! independent decoder inverts), the sign-extending `LDRSB`/`LDRSH` (the load
//! lane extends as the word's `opc` says), W/X pre- and post-index writeback
//! (an `address` part — the post-index form accesses the unindexed base — and
//! a `writeback` part, both from the word's `imm9` and bits 11:10), and
//! register offset in every packed mode (the `address` part extends the index
//! register from the word's `option` field and shifts it by the access size
//! when `S` is set; register 31 in `Rm` reads as zero). An `H`/`S`/`D` load
//! also states the zeroed upper half of `Vt` and the store the unchanged 8
//! bytes after its window. For the `H`/`S`/`D`/`Q` rows, which the
//! instruction-derived lane does not model, this exact decomposition is the
//! Formal-only rule's clause-2 check ([`crate::bound_memory_authority`]);
//! it is never credit by itself.
//!
//! Not covered: the upper 64 bits of a V register an `S`/`D` pair load
//! writes, memory permissions and ordering, and any relocation or fixup (no
//! admitted word has a hole).

use crate::aarch64_instruction_word_proofs::{instruction_word, scalar_memory_access};
use crate::aarch64_pair_memory_proofs::{PairMode, pair_memory_intent, pair_memory_word};
use crate::lowering_proof::{
    MachineSideProvenance, ProofObligation, TransvalCheckKind, VerificationConfig,
    memoized_verify_by_evaluation,
};
use crate::smt::SmtExpr as E;
use crate::verify::{VerificationResult, VerificationStrength};
use trust_cg_ir::{AArch64Opcode as O, MachInst};

/// Every opcode this module decomposes (in the admitted shapes only).
pub const MEMORY_EFFECT_OPCODES: &[O] = &[
    O::StpRI,
    O::LdpRI,
    O::StpPreIndex,
    O::LdpPostIndex,
    O::NeonStpQPost,
    O::NeonLdpQPost,
    O::NeonSt1Post,
    O::NeonLd1Post,
    O::LdrRI,
    O::StrRI,
    O::LdrbRI,
    O::StrbRI,
    O::LdrhRI,
    O::StrhRI,
    O::LdrsbRI,
    O::LdrshRI,
    O::LdrPreIndex,
    O::LdrPostIndex,
    O::StrPreIndex,
    O::StrPostIndex,
    O::LdrRO,
    O::StrRO,
    O::LdrbRO,
    O::LdrhRO,
    O::StrbRO,
    O::StrhRO,
];

/// Symbolic name of the base register's value before the access.
pub const BASE_INPUT: &str = "base";

// ===========================================================================
// The access the operands name
// ===========================================================================

/// The instruction class and addressing form.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AccessForm {
    /// `LDP`/`STP` in the given addressing mode.
    Pair(PairMode),
    /// `LDR`/`STR` (unsigned scaled immediate, `imm12`).
    ScalarUnsigned,
    /// `LDUR`/`STUR` (unscaled signed immediate, `imm9`).
    ScalarUnscaled,
    /// `LDR`/`STR` immediate pre-index, `[Xn|SP, #simm9]!`: the access at
    /// `base + offset`, then `Xn = base + offset`.
    ScalarPre,
    /// `LDR`/`STR` immediate post-index, `[Xn|SP], #simm9`: the access at
    /// `base`, then `Xn = base + offset`.
    ScalarPost,
    /// `LDR`/`STR` (register), `[Xn|SP, Rm, extend #shift]`: `mode` is the
    /// packed `(option << 1) | S` the operands carry, `index` the `Rm` field
    /// (31 is the zero register).
    ScalarRegister {
        /// `(option << 1) | S`.
        mode: u8,
        /// `Rm`.
        index: u8,
    },
    /// `LD1`/`ST1` (multiple structures, one register) with the immediate
    /// post-index form: the base advances by the bytes transferred. `size` is
    /// the element-size field the operands' arrangement names; in
    /// little-endian it does not change which byte lands where.
    SimdSinglePost {
        /// The arrangement's element-size field (`0` B .. `3` D).
        size: u8,
    },
}

/// One admitted memory access, reduced to what its operands name.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MemoryAccess {
    /// The emitted opcode.
    pub opcode: O,
    /// True for a load.
    pub load: bool,
    /// Class and addressing form.
    pub form: AccessForm,
    /// True when the transfer registers are SIMD&FP (`V = 1`).
    pub simd: bool,
    /// Bytes per transfer lane: 1, 2, 4, 8 or 16.
    pub bytes: u32,
    /// Byte offset the operands carry.
    pub offset: i64,
    /// Five-bit transfer fields (`Rt`, `Rt2`; the second is unused for scalar).
    pub transfer: [u8; 2],
    /// Transfer slot is the zero register (stores only).
    pub zero: [bool; 2],
    /// Five-bit base field (31 is SP).
    pub base: u8,
    /// What a general-purpose load does above the accessed bytes.
    pub extension: LoadExtension,
}

/// The extension a general-purpose scalar load applies above its bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LoadExtension {
    /// Zero-extend (every store, SIMD&FP and pair access too).
    Zero,
    /// `LDRSB`/`LDRSH Wt`: sign-extend to 32 bits, then clear bits 63:32.
    SignTo32,
    /// `LDRSB`/`LDRSH Xt`: sign-extend to 64 bits.
    SignTo64,
}

impl MemoryAccess {
    /// Number of transfer lanes (2 for a pair).
    pub fn lanes(&self) -> usize {
        if matches!(self.form, AccessForm::Pair(_)) {
            2
        } else {
            1
        }
    }

    /// Byte displacement of lane 0's address from the base. The scalar-cell
    /// caller theorem reads accesses through this, not a second decoding.
    pub(crate) fn lane0_displacement(&self) -> i64 {
        match self.form {
            AccessForm::Pair(PairMode::PostIndex)
            | AccessForm::SimdSinglePost { .. }
            | AccessForm::ScalarPost
            | AccessForm::ScalarRegister { .. } => 0,
            _ => self.offset,
        }
    }

    /// Byte displacement written back into the base (`None`: no writeback).
    pub(crate) fn writeback_displacement(&self) -> Option<i64> {
        match self.form {
            AccessForm::Pair(PairMode::PreIndex | PairMode::PostIndex)
            | AccessForm::SimdSinglePost { .. } => Some(self.offset),
            AccessForm::Pair(PairMode::Offset) => Some(0),
            AccessForm::ScalarPre | AccessForm::ScalarPost => Some(self.offset),
            AccessForm::ScalarUnsigned
            | AccessForm::ScalarUnscaled
            | AccessForm::ScalarRegister { .. } => None,
        }
    }

    /// Whether this is one of the scalar forms admitted only through the form
    /// binder (L04-P1): an `H`/`S`/`D`/`Q` transfer, a sign-extending load,
    /// pre/post-index writeback or register offset. A route whose contract
    /// names only a zero-extending general-purpose immediate access (the
    /// source-bound memory leaf) must refuse these.
    pub fn is_binder_scalar_form(&self) -> bool {
        self.is_scalar()
            && (self.simd
                || self.extension != LoadExtension::Zero
                || matches!(
                    self.form,
                    AccessForm::ScalarPre
                        | AccessForm::ScalarPost
                        | AccessForm::ScalarRegister { .. }
                ))
    }

    /// Whether this is a single-register `LDR`/`STR` form.
    fn is_scalar(&self) -> bool {
        matches!(
            self.form,
            AccessForm::ScalarUnsigned
                | AccessForm::ScalarUnscaled
                | AccessForm::ScalarPre
                | AccessForm::ScalarPost
                | AccessForm::ScalarRegister { .. }
        )
    }

    /// Whether this is an `LD1`/`ST1` single-register post-index transfer.
    fn is_simd_single(&self) -> bool {
        matches!(self.form, AccessForm::SimdSinglePost { .. })
    }

    /// 64-bit halves of one lane's register view and memory window.
    fn halves(&self) -> u32 {
        if self.bytes > 8 { 2 } else { 1 }
    }
}

/// The access `inst` names, or `None` when it is not an admitted shape.
///
/// Pairs take [`pair_memory_intent`]'s admission; scalar accesses take the
/// admission [`crate::aarch64_instruction_word_proofs`] re-derives words for.
/// A scalar load into the zero register is refused (its value is discarded,
/// so there is no loaded value to state).
pub fn memory_access(inst: &MachInst) -> Option<MemoryAccess> {
    if matches!(inst.opcode, O::NeonLd1Post | O::NeonSt1Post) {
        return simd_single_post_access(inst);
    }
    if let Some(pair) = pair_memory_intent(inst) {
        return Some(MemoryAccess {
            opcode: inst.opcode,
            load: pair.load,
            form: AccessForm::Pair(pair.mode),
            simd: pair.simd,
            bytes: pair.element_bytes,
            offset: pair.offset,
            transfer: [pair.rt, pair.rt2],
            zero: [pair.zero_transfer(0), pair.zero_transfer(1)],
            base: pair.rn,
            extension: LoadExtension::Zero,
        });
    }
    let Some(scalar) = scalar_memory_access(inst) else {
        return binder_scalar_access(inst);
    };
    if scalar.load && scalar.data_is_zero {
        return None;
    }
    Some(MemoryAccess {
        opcode: inst.opcode,
        load: scalar.load,
        form: if scalar.unsigned_form {
            AccessForm::ScalarUnsigned
        } else {
            AccessForm::ScalarUnscaled
        },
        simd: false,
        bytes: scalar.bytes,
        offset: scalar.offset,
        transfer: [scalar.data, scalar.data],
        zero: [scalar.data_is_zero, scalar.data_is_zero],
        base: scalar.base,
        extension: LoadExtension::Zero,
    })
}

/// The scalar forms the instruction-derived lane does not re-derive here —
/// H/S/D/Q transfers, sign-extending loads, pre/post-index writeback and
/// register offset — through the form binder
/// ([`crate::aarch64_scalar_memory_proofs::bind_scalar_memory_instruction`]),
/// whose word comes from that module's own encoder
/// ([`crate::aarch64_scalar_memory_proofs::scalar_memory_word`]). The binder
/// refuses loads into the zero register, a load overwriting its own base,
/// writeback onto the transfer register, volatile accesses and the literal
/// load.
fn binder_scalar_access(inst: &MachInst) -> Option<MemoryAccess> {
    use crate::aarch64_scalar_memory_proofs::{
        ScalarAddressing, ScalarBank, ScalarExtension, ScalarTransfer,
        bind_scalar_memory_instruction,
    };
    let binding = bind_scalar_memory_instruction(inst).ok()?;
    let form = binding.form;
    let simd = form.bank == ScalarBank::Fpr;
    let load = form.transfer == ScalarTransfer::Load;
    let (access_form, offset) = match form.addressing {
        ScalarAddressing::UnsignedOffset => (AccessForm::ScalarUnsigned, binding.operand),
        ScalarAddressing::Unscaled => (AccessForm::ScalarUnscaled, binding.operand),
        ScalarAddressing::PreIndex => (AccessForm::ScalarPre, binding.operand),
        ScalarAddressing::PostIndex => (AccessForm::ScalarPost, binding.operand),
        ScalarAddressing::RegisterOffset => (
            AccessForm::ScalarRegister {
                mode: u8::try_from(binding.operand).ok()?,
                index: u8::try_from(binding.index_field?).ok()?,
            },
            0,
        ),
        ScalarAddressing::Literal => return None,
    };
    let rt = u8::try_from(binding.rt_field).ok()?;
    // Field 31 is the zero register only for a general-purpose transfer.
    let zero = !simd && binding.rt_field == 31;
    Some(MemoryAccess {
        opcode: inst.opcode,
        load,
        form: access_form,
        simd,
        bytes: form.access_bytes,
        offset,
        transfer: [rt, rt],
        zero: [zero, zero],
        base: u8::try_from(binding.base_field?).ok()?,
        extension: match form.extension {
            ScalarExtension::Zero => LoadExtension::Zero,
            ScalarExtension::SignTo32 => LoadExtension::SignTo32,
            ScalarExtension::SignTo64 => LoadExtension::SignTo64,
        },
    })
}

/// Admit `LD1 {Vt.<T>}, [Xn|SP], #<bytes>` / `ST1` (the immediate post-index
/// form): operands `[Vt, Xn, Imm(arrangement)]`, the arrangement selector
/// `0..=6` (`8B`, `16B`, `4H`, `8H`, `2S`, `4S`, `2D`). `Vt` must be an
/// allocated `Q` register, or a `D` register for a 64-bit arrangement; the base
/// an allocated X register or SP (field 31 in this slot is SP). Anything else is
/// refused.
fn simd_single_post_access(inst: &MachInst) -> Option<MemoryAccess> {
    use trust_cg_ir::aarch64_regs::{XZR, preg_class};
    use trust_cg_ir::{MachOperand, RegClass, regs::SpecialReg};
    let load = inst.opcode == O::NeonLd1Post;
    let [transfer, base, MachOperand::Imm(selector)] = inst.operands.as_slice() else {
        return None;
    };
    let (q, size) = match *selector {
        0 => (false, 0),
        1 => (true, 0),
        2 => (false, 1),
        3 => (true, 1),
        4 => (false, 2),
        5 => (true, 2),
        6 => (true, 3),
        _ => return None,
    };
    let rt = match transfer {
        MachOperand::PReg(p) => match preg_class(*p) {
            RegClass::Fpr128 => p.hw_enc(),
            RegClass::Fpr64 if !q => p.hw_enc(),
            _ => return None,
        },
        _ => return None,
    };
    let base = match base {
        MachOperand::PReg(p) if preg_class(*p) == RegClass::Gpr64 && *p != XZR => p.hw_enc(),
        MachOperand::Special(SpecialReg::SP) => 31,
        _ => return None,
    };
    let bytes = if q { 16 } else { 8 };
    Some(MemoryAccess {
        opcode: inst.opcode,
        load,
        form: AccessForm::SimdSinglePost { size },
        simd: true,
        bytes,
        offset: i64::from(bytes),
        transfer: [rt, rt],
        zero: [false, false],
        base,
        extension: LoadExtension::Zero,
    })
}

/// The word `inst` re-derives to, for an admitted access: the pair encoder's,
/// the scalar encoder's, or the `LD1`/`ST1` layout mirror
/// ([`crate::neon_semantics::neon_ld1_st1_post_word`]). No admitted memory word
/// has a hole.
pub fn memory_effect_word(inst: &MachInst) -> Option<u32> {
    let access = memory_access(inst)?;
    if let AccessForm::SimdSinglePost { size } = access.form {
        return Some(crate::neon_semantics::neon_ld1_st1_post_word(
            access.load,
            access.bytes == 16,
            size,
            access.base,
            access.transfer[0],
        ));
    }
    if let Some(pair) = pair_memory_intent(inst) {
        return pair_memory_word(&pair);
    }
    // The instruction-derived lane's word where it re-derives one (every
    // general-purpose form; ENC-5 already binds the emitted word to it), else
    // the scalar form encoder's (the H/S/D/Q forms).
    if let Some(word) = instruction_word(inst) {
        return (word.hole_mask == 0).then_some(word.word);
    }
    let binding = crate::aarch64_scalar_memory_proofs::bind_scalar_memory_instruction(inst).ok()?;
    crate::aarch64_scalar_memory_proofs::scalar_memory_word(&binding)
}

/// ENC-5's binding of the emitted word to the word the parts carry:
/// `Some(Ok(()))` when `emitted` equals [`memory_effect_word`], `Some(Err(_))`
/// when it differs, `None` when `inst` is not an admitted access (no claim).
pub fn check_emitted_memory_effect_word(
    inst: &MachInst,
    emitted: u32,
) -> Option<Result<(), String>> {
    let expected = memory_effect_word(inst)?;
    Some(if emitted == expected {
        Ok(())
    } else {
        Err(format!(
            "emitted word {emitted:#010x} is not the word {expected:#010x} the memory-effect \
             obligations carry"
        ))
    })
}

// ===========================================================================
// Parts
// ===========================================================================

/// Which fact of the access one part states.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MemoryEffectPart {
    /// Every non-immediate field of the word.
    Fields,
    /// Effective address of transfer lane `lane`.
    Address { lane: u8 },
    /// The base register after the access (pairs).
    Writeback,
    /// Register view `half` (64 bits) a load lane writes.
    Load { lane: u8, half: u8 },
    /// Memory window `half` (8 bytes) a store lane leaves.
    Store { lane: u8, half: u8 },
}

impl std::fmt::Display for MemoryEffectPart {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Fields => write!(f, "fields"),
            Self::Address { lane } => write!(f, "address lane {lane}"),
            Self::Writeback => write!(f, "writeback"),
            Self::Load { lane, half } => write!(f, "load lane {lane} half {half}"),
            Self::Store { lane, half } => write!(f, "store lane {lane} half {half}"),
        }
    }
}

/// One part and its obligation (`trust_ir_expr` is the operands' side,
/// `aarch64_expr` the word's).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemoryEffectObligation {
    /// Which fact it states.
    pub part: MemoryEffectPart,
    /// The obligation, replayed exactly as built.
    pub obligation: ProofObligation,
}

/// Every part of one admitted access, for one word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemoryEffectDecomposition {
    /// The access the operands name.
    pub access: MemoryAccess,
    /// The word every part carries.
    pub word: u32,
    /// The parts, in a fixed order: fields, addresses, writeback, lanes.
    pub parts: Vec<MemoryEffectObligation>,
}

/// The decomposition of `inst` over its re-derived word
/// ([`memory_effect_word`]), or `None` when `inst` is not an admitted access.
pub fn memory_effect(inst: &MachInst) -> Option<MemoryEffectDecomposition> {
    let word = memory_effect_word(inst)?;
    memory_effect_for_word(inst, word)
}

/// The decomposition of `inst` over a caller-supplied word: the seam the
/// negative controls feed mutated words through. The operands' side is the
/// same as [`memory_effect`]'s; only the literal changes.
pub fn memory_effect_for_word(inst: &MachInst, word: u32) -> Option<MemoryEffectDecomposition> {
    let access = memory_access(inst)?;
    Some(decompose(&access, word))
}

fn decompose(access: &MemoryAccess, word: u32) -> MemoryEffectDecomposition {
    let label = format!("A64 memory effect {:?} {word:#010x}", access.opcode);
    let mut parts = vec![part(
        &label,
        MemoryEffectPart::Fields,
        E::bool_const(true),
        fields_conjunction(access, word),
        access.opcode,
    )];
    let base = E::var(BASE_INPUT, 64);
    // An `LD1`/`ST1` (multiple structures) word reads and writes at `X[n]` in
    // both its offset and post-index forms: its one lane address is the base
    // the `fields` part names, so it has no address part.
    let addressed_lanes = if access.is_simd_single() {
        0
    } else {
        access.lanes()
    };
    for lane in 0..addressed_lanes {
        let (intent, machine) = address(access, word, lane, &base);
        parts.push(part(
            &label,
            MemoryEffectPart::Address { lane: lane as u8 },
            intent,
            machine,
            access.opcode,
        ));
    }
    if let Some(displacement) = access.writeback_displacement() {
        let machine = if access.is_simd_single() {
            simd_single_writeback(word, &base)
        } else if access.is_scalar() {
            scalar_writeback(word, &base)
        } else {
            pair_writeback(word, &base)
        };
        parts.push(part(
            &label,
            MemoryEffectPart::Writeback,
            plus(&base, displacement),
            machine,
            access.opcode,
        ));
    }
    for lane in 0..access.lanes() {
        for half in 0..access.halves() {
            let (which, intent, machine) = if access.load {
                let window = window_var(access, lane, half);
                (
                    MemoryEffectPart::Load {
                        lane: lane as u8,
                        half: half as u8,
                    },
                    load_intent(access, &window),
                    load_machine(access, word, half, &window),
                )
            } else {
                let window = window_var(access, lane, half);
                let data = data_value(access, lane, half);
                (
                    MemoryEffectPart::Store {
                        lane: lane as u8,
                        half: half as u8,
                    },
                    store_intent(access, &window, &data),
                    store_machine(access, word, half, &window, &data),
                )
            };
            parts.push(part(&label, which, intent, machine, access.opcode));
        }
    }
    // An `H`/`S`/`D` scalar load writes zero into bits [127:64] of `Vt`, and
    // the store leaves the 8 bytes after its window unchanged: as for a
    // 64-bit `LD1`/`ST1` below, each is a part.
    if access.is_scalar() && access.simd && access.bytes <= 8 {
        let window = E::var("w0h1", 64);
        let q = scalar_simd_is_q(word);
        let (which, intent, machine) = if access.load {
            (
                MemoryEffectPart::Load { lane: 0, half: 1 },
                zeros(64),
                E::ite(q, window_value(&window, 8), zeros(64)),
            )
        } else {
            let data = E::var("d0h1", 64);
            let bytes = (0..8)
                .map(|k| E::ite(q.clone(), byte_of(&data, k), byte_of(&window, k)))
                .collect();
            (
                MemoryEffectPart::Store { lane: 0, half: 1 },
                window.clone(),
                little_endian(bytes, 64),
            )
        };
        parts.push(part(&label, which, intent, machine, access.opcode));
    }
    // A 64-bit `LD1` writes zero into bits [127:64] of `Vt`, and a 64-bit `ST1`
    // leaves the 8 bytes after its window unchanged; each is a part, so a word
    // that transfers 16 bytes refutes in it as well as in `fields`.
    if access.is_simd_single() && access.bytes == 8 {
        let window = E::var("w0h1", 64);
        let (which, intent, machine) = if access.load {
            (
                MemoryEffectPart::Load { lane: 0, half: 1 },
                zeros(64),
                E::ite(simd_single_is_q(word), window_value(&window, 8), zeros(64)),
            )
        } else {
            let data = E::var("d0h1", 64);
            let bytes = (0..8)
                .map(|k| {
                    E::ite(
                        simd_single_is_q(word),
                        byte_of(&data, k),
                        byte_of(&window, k),
                    )
                })
                .collect();
            (
                MemoryEffectPart::Store { lane: 0, half: 1 },
                window.clone(),
                little_endian(bytes, 64),
            )
        };
        parts.push(part(&label, which, intent, machine, access.opcode));
    }
    MemoryEffectDecomposition {
        access: *access,
        word,
        parts,
    }
}

fn part(
    label: &str,
    which: MemoryEffectPart,
    intent: E,
    machine: E,
    opcode: O,
) -> MemoryEffectObligation {
    let mut inputs: Vec<(String, u32)> = Vec::new();
    for expr in [&intent, &machine] {
        collect_vars(expr, &mut inputs);
    }
    inputs.sort();
    MemoryEffectObligation {
        part: which,
        obligation: ProofObligation {
            name: format!("{label}: {which}"),
            trust_ir_expr: intent,
            aarch64_expr: machine,
            inputs,
            preconditions: Vec::new(),
            fp_inputs: Vec::new(),
            category: Some(TransvalCheckKind::MemoryModel),
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode: format!("{opcode:?}"),
                arity: 1,
            },
        },
    }
}

fn collect_vars(expr: &E, out: &mut Vec<(String, u32)>) {
    if let E::Var { name, width } = expr {
        if !out.iter().any(|(seen, _)| seen == name) {
            out.push((name.clone(), *width));
        }
        return;
    }
    expr.for_each_child(&mut |child| collect_vars(child, out));
}

// ---------------------------------------------------------------------------
// Word fields, as SMT terms over the literal
// ---------------------------------------------------------------------------

fn literal(word: u32) -> E {
    E::bv_const(u64::from(word), 32)
}

fn field(word: u32, hi: u32, lo: u32) -> E {
    literal(word).extract(hi, lo)
}

fn field_is(word: u32, hi: u32, lo: u32, value: u64) -> E {
    field(word, hi, lo).eq_expr(E::bv_const(value, hi - lo + 1))
}

fn zeros(width: u32) -> E {
    E::bv_const(0, width)
}

/// `x` zero-extended by `k` bits, spelled `(concat (_ bv0 k) x)`.
///
/// SMT-LIB defines `(_ zero_extend k)` as exactly this concatenation, but the
/// aterm-managed Clean 8606 rejects the `refl` step an AY proof uses to
/// rewrite one spelling into the other (report
/// `2026-09-29-darwin-memory-effect-certificates`, reproducer `clean-01`), so
/// no part contains `zero_extend`.
fn zero_extend(x: E, k: u32) -> E {
    if k == 0 { x } else { zeros(k).concat(x) }
}

/// `x << k` for a constant `k`, as `concat` with `k` zero bits.
fn shl_const(x: E, k: u32) -> E {
    if k == 0 {
        return x;
    }
    let width = x.bv_width();
    x.extract(width - 1 - k, 0).concat(zeros(k))
}

fn plus(base: &E, displacement: i64) -> E {
    if displacement == 0 {
        base.clone()
    } else {
        base.clone().bvadd(E::bv_const(displacement as u64, 64))
    }
}

fn any_of(conditions: Vec<E>) -> E {
    let mut iter = conditions.into_iter();
    let first = iter.next().unwrap_or_else(|| E::bool_const(false));
    iter.fold(first, E::or_expr)
}

/// A pair word's `opc:V` (three bits), which fixes the element size.
fn pair_key(word: u32) -> E {
    field(word, 31, 30).concat(field(word, 26, 26))
}

fn pair_key_is(word: u32, value: u64) -> E {
    pair_key(word).eq_expr(E::bv_const(value, 3))
}

/// The pair word's element size is 8 bytes (X `100`, D `011`) or 16 (Q `101`).
fn pair_at_least_8(word: u32) -> E {
    any_of(vec![
        pair_key_is(word, 0b100),
        pair_key_is(word, 0b011),
        pair_key_is(word, 0b101),
    ])
}

fn pair_is_16(word: u32) -> E {
    pair_key_is(word, 0b101)
}

/// The pair word's byte offset: `SignExtend(imm7) << scale`.
fn pair_offset(word: u32) -> E {
    let imm = field(word, 21, 15).sign_ext(57);
    E::ite(
        pair_is_16(word),
        shl_const(imm.clone(), 4),
        E::ite(
            pair_at_least_8(word),
            shl_const(imm.clone(), 3),
            shl_const(imm, 2),
        ),
    )
}

/// The pair word's element size in bytes, as a 64-bit value.
fn pair_size(word: u32) -> E {
    E::ite(
        pair_is_16(word),
        E::bv_const(16, 64),
        E::ite(
            pair_at_least_8(word),
            E::bv_const(8, 64),
            E::bv_const(4, 64),
        ),
    )
}

fn pair_mode_is(word: u32, bits: u64) -> E {
    field_is(word, 24, 23, bits)
}

fn pair_writeback(word: u32, base: &E) -> E {
    E::ite(
        pair_mode_is(word, 0b10),
        base.clone(),
        base.clone().bvadd(pair_offset(word)),
    )
}

/// A SIMD&FP scalar word transfers 16 bytes (`Q`): `V = 1`, `size = 00` and
/// `opc<1> = 1`.
fn scalar_simd_is_q(word: u32) -> E {
    field_is(word, 26, 26, 1)
        .and_expr(field_is(word, 31, 30, 0b00))
        .and_expr(field_is(word, 23, 23, 1))
}

/// The access-size scale of a scalar word: `size`, or 4 for a `Q` transfer.
fn scalar_scaled(word: u32, x: E) -> E {
    let size = |value| field_is(word, 31, 30, value);
    E::ite(
        scalar_simd_is_q(word),
        shl_const(x.clone(), 4),
        E::ite(
            size(0b11),
            shl_const(x.clone(), 3),
            E::ite(
                size(0b10),
                shl_const(x.clone(), 2),
                E::ite(size(0b01), shl_const(x.clone(), 1), x),
            ),
        ),
    )
}

/// `SignExtend(imm9)` of a scalar word.
fn scalar_imm9(word: u32) -> E {
    field(word, 20, 12).sign_ext(55)
}

/// The address a pre/post-index or register-offset scalar word accesses.
fn scalar_wide_address(word: u32, base: &E) -> E {
    // Register offset: bit 21 set and bits 11:10 = 10.
    let register = field_is(word, 21, 21, 1).and_expr(field_is(word, 11, 10, 0b10));
    let index = E::ite(
        field_is(word, 20, 16, 31),
        zeros(64),
        E::var(INDEX_INPUT, 64),
    );
    let low = index.clone().extract(31, 0);
    let option = |value| field_is(word, 15, 13, value);
    let extended = E::ite(
        option(0b010),
        zero_extend(low.clone(), 32),
        E::ite(option(0b110), low.sign_ext(32), index),
    );
    let shifted = E::ite(
        field_is(word, 12, 12, 1),
        scalar_scaled(word, extended.clone()),
        extended,
    );
    E::ite(
        register,
        base.clone().bvadd(shifted),
        E::ite(
            // Post-index (bits 11:10 = 01) accesses the unindexed base.
            field_is(word, 11, 10, 0b01),
            base.clone(),
            base.clone().bvadd(scalar_imm9(word)),
        ),
    )
}

/// The base a scalar word leaves: `base + SignExtend(imm9)` for the pre- and
/// post-index forms (bits 11:10 = 11 / 01, bit 21 clear), `base` otherwise.
fn scalar_writeback(word: u32, base: &E) -> E {
    let writeback = field_is(word, 21, 21, 0)
        .and_expr(field_is(word, 11, 10, 0b11).or_expr(field_is(word, 11, 10, 0b01)));
    E::ite(
        writeback,
        base.clone().bvadd(scalar_imm9(word)),
        base.clone(),
    )
}

/// The operands' register-offset address: `base` plus the index the packed
/// mode names (`UXTW`, `LSL`/`UXTX`, `SXTW`, `SXTX`), shifted by the access
/// size when `S` is set.
fn register_offset_intent(access: &MemoryAccess, mode: u8, index: u8, base: &E) -> E {
    let index = if index == 31 {
        zeros(64)
    } else {
        E::var(INDEX_INPUT, 64)
    };
    let low = index.clone().extract(31, 0);
    let extended = match mode >> 1 {
        0b010 => zero_extend(low, 32),
        0b110 => low.sign_ext(32),
        _ => index,
    };
    let scaled = if mode & 1 == 1 {
        shl_const(extended, access.bytes.trailing_zeros())
    } else {
        extended
    };
    base.clone().bvadd(scaled)
}

/// Symbolic name of a register-offset access's index register.
pub const INDEX_INPUT: &str = "index";

/// The scalar word's byte offset: `ZeroExtend(imm12) << size` in the unsigned
/// form (bit 24 set), `SignExtend(imm9)` in the unscaled form.
fn scalar_offset(word: u32) -> E {
    let imm12 = zero_extend(field(word, 21, 10), 52);
    let size = |value| field_is(word, 31, 30, value);
    let unsigned = E::ite(
        size(0b11),
        shl_const(imm12.clone(), 3),
        E::ite(
            size(0b10),
            shl_const(imm12.clone(), 2),
            E::ite(size(0b01), shl_const(imm12.clone(), 1), imm12),
        ),
    );
    let unscaled = field(word, 20, 12).sign_ext(55);
    E::ite(field_is(word, 24, 24, 1), unsigned, unscaled)
}

// ---------------------------------------------------------------------------
// fields
// ---------------------------------------------------------------------------

fn mode_bits(mode: PairMode) -> u64 {
    match mode {
        PairMode::PostIndex => 0b01,
        PairMode::Offset => 0b10,
        PairMode::PreIndex => 0b11,
    }
}

fn pair_opc(access: &MemoryAccess) -> u64 {
    match (access.simd, access.bytes) {
        (false, 8) | (true, 16) => 0b10,
        (true, 8) => 0b01,
        _ => 0b00,
    }
}

fn scalar_size(bytes: u32) -> u64 {
    match bytes {
        1 => 0b00,
        2 => 0b01,
        4 => 0b10,
        _ => 0b11,
    }
}

/// `(size, V, opc)` of a scalar access, from the operands.
fn scalar_size_v_opc(access: &MemoryAccess) -> (u64, u64, u64) {
    if access.simd {
        let q = access.bytes == 16;
        let size = if q { 0b00 } else { scalar_size(access.bytes) };
        return (size, 1, u64::from(access.load) | (u64::from(q) << 1));
    }
    let opc = match (access.load, access.extension) {
        (false, _) => 0b00,
        (true, LoadExtension::Zero) => 0b01,
        (true, LoadExtension::SignTo64) => 0b10,
        (true, LoadExtension::SignTo32) => 0b11,
    };
    (scalar_size(access.bytes), 0, opc)
}

/// `(hi, lo, value)` of every non-immediate field, from the operands.
fn intended_fields(access: &MemoryAccess) -> Vec<(u32, u32, u64)> {
    let rt = u64::from(access.transfer[0]);
    let rn = u64::from(access.base);
    match access.form {
        AccessForm::Pair(mode) => vec![
            (31, 30, pair_opc(access)),
            (29, 27, 0b101),
            (26, 26, u64::from(access.simd)),
            (25, 25, 0),
            (24, 23, mode_bits(mode)),
            (22, 22, u64::from(access.load)),
            (14, 10, u64::from(access.transfer[1])),
            (9, 5, rn),
            (4, 0, rt),
        ],
        AccessForm::ScalarUnsigned => {
            let (size, v, opc) = scalar_size_v_opc(access);
            vec![
                (31, 30, size),
                (29, 27, 0b111),
                (26, 26, v),
                (25, 24, 0b01),
                (23, 22, opc),
                (9, 5, rn),
                (4, 0, rt),
            ]
        }
        AccessForm::ScalarUnscaled | AccessForm::ScalarPre | AccessForm::ScalarPost => {
            let (size, v, opc) = scalar_size_v_opc(access);
            let mode = match access.form {
                AccessForm::ScalarPre => 0b11,
                AccessForm::ScalarPost => 0b01,
                _ => 0b00,
            };
            vec![
                (31, 30, size),
                (29, 27, 0b111),
                (26, 26, v),
                (25, 24, 0b00),
                (23, 22, opc),
                (21, 21, 0),
                (11, 10, mode),
                (9, 5, rn),
                (4, 0, rt),
            ]
        }
        AccessForm::ScalarRegister { mode, index } => {
            let (size, v, opc) = scalar_size_v_opc(access);
            vec![
                (31, 30, size),
                (29, 27, 0b111),
                (26, 26, v),
                (25, 24, 0b00),
                (23, 22, opc),
                (21, 21, 1),
                (20, 16, u64::from(index)),
                (15, 13, u64::from(mode >> 1)),
                (12, 12, u64::from(mode & 1)),
                (11, 10, 0b10),
                (9, 5, rn),
                (4, 0, rt),
            ]
        }
        // LD1/ST1 (multiple structures), post-index: `0 Q 0011001 L 0 Rm
        // opcode size Rn Rt` with `Rm = 11111` (immediate) and `opcode = 0111`
        // (one register).
        AccessForm::SimdSinglePost { size } => vec![
            (31, 31, 0),
            (30, 30, u64::from(access.bytes == 16)),
            (29, 23, 0b001_1001),
            (22, 22, u64::from(access.load)),
            (21, 21, 0),
            (20, 16, 0b1_1111),
            (15, 12, 0b0111),
            (11, 10, u64::from(size)),
            (9, 5, rn),
            (4, 0, rt),
        ],
    }
}

fn fields_conjunction(access: &MemoryAccess, word: u32) -> E {
    let mut conjuncts = intended_fields(access)
        .into_iter()
        .map(|(hi, lo, value)| field_is(word, hi, lo, value));
    let first = conjuncts.next().unwrap_or_else(|| E::bool_const(true));
    conjuncts.fold(first, E::and_expr)
}

// ---------------------------------------------------------------------------
// address
// ---------------------------------------------------------------------------

/// `(operands' address, word's address)` of lane `lane`.
fn address(access: &MemoryAccess, word: u32, lane: usize, base: &E) -> (E, E) {
    let intended = match access.form {
        AccessForm::ScalarRegister { mode, index } => {
            register_offset_intent(access, mode, index, base)
        }
        _ => plus(
            base,
            access.lane0_displacement() + lane as i64 * i64::from(access.bytes),
        ),
    };
    let machine = match access.form {
        AccessForm::Pair(_) => {
            let lane0 = E::ite(
                pair_mode_is(word, 0b01),
                base.clone(),
                base.clone().bvadd(pair_offset(word)),
            );
            if lane == 0 {
                lane0
            } else {
                lane0.bvadd(pair_size(word))
            }
        }
        AccessForm::ScalarUnsigned | AccessForm::ScalarUnscaled if access.simd => {
            base.clone().bvadd(E::ite(
                field_is(word, 24, 24, 1),
                scalar_scaled(word, zero_extend(field(word, 21, 10), 52)),
                scalar_imm9(word),
            ))
        }
        AccessForm::ScalarUnsigned | AccessForm::ScalarUnscaled => {
            base.clone().bvadd(scalar_offset(word))
        }
        AccessForm::ScalarPre | AccessForm::ScalarPost | AccessForm::ScalarRegister { .. } => {
            scalar_wide_address(word, base)
        }
        // Never built (the decomposition has no LD1/ST1 address part): the
        // class addresses `X[n]`.
        AccessForm::SimdSinglePost { .. } => base.clone(),
    };
    (intended, machine)
}

/// The `LD1`/`ST1` word's `Q` bit: a 16-byte transfer.
fn simd_single_is_q(word: u32) -> E {
    field_is(word, 30, 30, 1)
}

/// The base an `LD1`/`ST1` word leaves: in the post-index form (bit 23) with
/// an immediate offset, `X[n]` plus the bytes transferred (16 with `Q`, else
/// 8); `X[n]` in the offset form.
fn simd_single_writeback(word: u32, base: &E) -> E {
    E::ite(
        field_is(word, 23, 23, 1),
        base.clone().bvadd(E::ite(
            simd_single_is_q(word),
            E::bv_const(16, 64),
            E::bv_const(8, 64),
        )),
        base.clone(),
    )
}

// ---------------------------------------------------------------------------
// load and store lanes
// ---------------------------------------------------------------------------

fn window_var(access: &MemoryAccess, lane: usize, half: u32) -> E {
    if access.halves() > 1 {
        E::var(format!("w{lane}h{half}"), 64)
    } else {
        E::var(format!("w{lane}"), 64)
    }
}

/// The data register's 64-bit view `half` for store lane `lane`. A repeated
/// store source reads one register, so lane 1 shares lane 0's variable; the
/// zero register reads as zero (A6).
fn data_value(access: &MemoryAccess, lane: usize, half: u32) -> E {
    if access.zero[lane] {
        return zeros(64);
    }
    let slot = if lane == 1 && access.transfer[1] == access.transfer[0] {
        0
    } else {
        lane
    };
    if access.halves() > 1 {
        E::var(format!("d{slot}h{half}"), 64)
    } else {
        E::var(format!("d{slot}"), 64)
    }
}

fn byte_of(x: &E, k: u32) -> E {
    x.clone().extract(8 * k + 7, 8 * k)
}

/// `byte` placed at bits `8k+7:8k` of a `width`-bit value, zero elsewhere.
fn positioned(byte: E, k: u32, width: u32) -> E {
    let mut placed = byte;
    if k > 0 {
        placed = placed.concat(zeros(8 * k));
    }
    let above = width - 8 * (k + 1);
    if above > 0 {
        placed = zeros(above).concat(placed);
    }
    placed
}

/// Arm's little-endian `Mem[]`: the OR of the given bytes, each at its place.
fn little_endian(bytes: Vec<E>, width: u32) -> E {
    let mut iter = bytes
        .into_iter()
        .enumerate()
        .map(|(k, byte)| positioned(byte, k as u32, width));
    let first = iter.next().unwrap_or_else(|| zeros(width));
    iter.fold(first, E::bvor)
}

fn window_value(window: &E, bytes: u32) -> E {
    little_endian((0..bytes).map(|k| byte_of(window, k)).collect(), 8 * bytes)
}

/// The operands' loaded value: the window's low `n` bytes as a number,
/// zero-extended to the 64-bit register view.
fn load_intent(access: &MemoryAccess, window: &E) -> E {
    let n = access.bytes.min(8);
    if n == 8 {
        return window.clone();
    }
    let low = window.clone().extract(8 * n - 1, 0);
    match access.extension {
        LoadExtension::Zero => zero_extend(low, 64 - 8 * n),
        LoadExtension::SignTo64 => low.sign_ext(64 - 8 * n),
        LoadExtension::SignTo32 => zero_extend(low.sign_ext(32 - 8 * n), 32),
    }
}

/// The word's loaded register view `half`, from the window's bytes.
fn load_machine(access: &MemoryAccess, word: u32, half: u32, window: &E) -> E {
    let full = window_value(window, 8);
    let four = window_value(window, 4);
    match access.form {
        AccessForm::SimdSinglePost { .. } => {
            if half == 1 {
                E::ite(simd_single_is_q(word), full, zeros(64))
            } else {
                full
            }
        }
        AccessForm::Pair(_) => {
            if half == 1 {
                return E::ite(pair_is_16(word), full, zeros(64));
            }
            E::ite(
                pair_at_least_8(word),
                full,
                E::ite(
                    // LDPSW (opc 01, V 0) sign-extends each word.
                    pair_key_is(word, 0b010),
                    four.clone().sign_ext(32),
                    zero_extend(four, 32),
                ),
            )
        }
        _ if access.simd => {
            // A SIMD&FP scalar load writes the whole V register: its low
            // `size` bytes (16 for Q), zero above.
            let two = window_value(window, 2);
            if half == 1 {
                return E::ite(scalar_simd_is_q(word), full, zeros(64));
            }
            let size = |value| field_is(word, 31, 30, value);
            E::ite(
                scalar_simd_is_q(word).or_expr(size(0b11)),
                full,
                E::ite(
                    size(0b10),
                    zero_extend(four, 32),
                    E::ite(
                        size(0b01),
                        zero_extend(two, 48),
                        zero_extend(window_value(window, 1), 56),
                    ),
                ),
            )
        }
        AccessForm::ScalarUnsigned
        | AccessForm::ScalarUnscaled
        | AccessForm::ScalarPre
        | AccessForm::ScalarPost
        | AccessForm::ScalarRegister { .. } => {
            let two = window_value(window, 2);
            let one = window_value(window, 1);
            let size = |value| field_is(word, 31, 30, value);
            let opc = |value| field_is(word, 23, 22, value);
            let zero_extended = E::ite(
                size(0b11),
                full,
                E::ite(
                    size(0b10),
                    zero_extend(four.clone(), 32),
                    E::ite(
                        size(0b01),
                        zero_extend(two.clone(), 48),
                        zero_extend(one.clone(), 56),
                    ),
                ),
            );
            // LDRSB/LDRSH/LDRSW to X (opc 10) and LDRSB/LDRSH to W (opc 11).
            let signed_64 = E::ite(
                size(0b10),
                four.sign_ext(32),
                E::ite(
                    size(0b01),
                    two.clone().sign_ext(48),
                    one.clone().sign_ext(56),
                ),
            );
            let signed_32 = zero_extend(E::ite(size(0b01), two.sign_ext(16), one.sign_ext(24)), 32);
            E::ite(
                opc(0b01),
                zero_extended,
                E::ite(opc(0b10), signed_64, signed_32),
            )
        }
    }
}

/// The operands' store: the data's low `n` bytes over the window's high bytes.
fn store_intent(access: &MemoryAccess, window: &E, data: &E) -> E {
    let n = access.bytes.min(8);
    if n == 8 {
        return data.clone();
    }
    let low: u64 = (1u64 << (8 * n)) - 1;
    window
        .clone()
        .bvand(E::bv_const(!low, 64))
        .bvor(data.clone().bvand(E::bv_const(low, 64)))
}

/// Whether the word's access size covers byte `index` of the lane (`index`
/// counts from the lane address, across both halves of a Q lane).
fn covers(access: &MemoryAccess, word: u32, index: u32) -> Option<E> {
    match access.form {
        AccessForm::SimdSinglePost { .. } => (index >= 8).then(|| simd_single_is_q(word)),
        AccessForm::Pair(_) => match index {
            0..=3 => None,
            4..=7 => Some(pair_at_least_8(word)),
            _ => Some(pair_is_16(word)),
        },
        _ if access.simd => {
            let size = field(word, 31, 30);
            let q = scalar_simd_is_q(word);
            match index {
                0 => None,
                1 => Some(q.or_expr(size.bvuge(E::bv_const(0b01, 2)))),
                2 | 3 => Some(q.or_expr(size.bvuge(E::bv_const(0b10, 2)))),
                4..=7 => Some(q.or_expr(size.eq_expr(E::bv_const(0b11, 2)))),
                _ => Some(q),
            }
        }
        AccessForm::ScalarUnsigned
        | AccessForm::ScalarUnscaled
        | AccessForm::ScalarPre
        | AccessForm::ScalarPost
        | AccessForm::ScalarRegister { .. } => {
            let size = field(word, 31, 30);
            match index {
                0 => None,
                1 => Some(size.bvuge(E::bv_const(0b01, 2))),
                2 | 3 => Some(size.bvuge(E::bv_const(0b10, 2))),
                _ => Some(size.eq_expr(E::bv_const(0b11, 2))),
            }
        }
    }
}

/// The window the word's store leaves: the data byte where its size covers
/// the byte, the old byte elsewhere.
fn store_machine(access: &MemoryAccess, word: u32, half: u32, window: &E, data: &E) -> E {
    let bytes = (0..8)
        .map(|k| match covers(access, word, 8 * half + k) {
            None => byte_of(data, k),
            Some(covered) => E::ite(covered, byte_of(data, k), byte_of(window, k)),
        })
        .collect();
    little_endian(bytes, 64)
}

// ===========================================================================
// In-process decision
// ===========================================================================

/// How a part fared in process: never proof credit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InProcess {
    /// No counterexample. `Exhaustive` when it was decided for every input
    /// (a ground part evaluated once, or [`decide_exactly`]); `Statistical`
    /// when only the sampling lane could judge it.
    Holds(VerificationStrength),
    /// A counterexample (the word does not perform the operands' access).
    Refuted(String),
    /// The evaluator could not decide it.
    Undecided(String),
}

/// Decide one part in process: a ground part is evaluated once; a symbolic
/// part by [`decide_exactly`] when its folded sides allow it, and otherwise
/// by the ordinary sampling lane (memoized by content).
pub fn decide_in_process(part: &MemoryEffectObligation, config: &VerificationConfig) -> InProcess {
    let obligation = &part.obligation;
    if obligation.inputs.is_empty() {
        let env = crate::smt::EvalEnv::default();
        return match obligation.negated_equivalence().try_eval(&env) {
            Ok(result) => {
                if result.as_bool() {
                    InProcess::Refuted("the ground part evaluates false".into())
                } else {
                    InProcess::Holds(VerificationStrength::Exhaustive)
                }
            }
            Err(error) => InProcess::Undecided(error.to_string()),
        };
    }
    match decide_exactly(obligation) {
        Some(Ok(())) => return InProcess::Holds(VerificationStrength::Exhaustive),
        Some(Err(why)) => return InProcess::Refuted(why),
        None => {}
    }
    match memoized_verify_by_evaluation(obligation, config) {
        VerificationResult::Valid => InProcess::Holds(
            VerificationStrength::for_obligation_with_config(obligation, config),
        ),
        VerificationResult::Invalid { counterexample } => InProcess::Refuted(counterexample),
        VerificationResult::Unknown { reason } => InProcess::Undecided(reason),
    }
}

/// Whether [`decide_in_process`] reaches the sampling lane for this part (a
/// symbolic part [`decide_exactly`] does not decide). The function verifier
/// pre-warms exactly these.
pub fn needs_sampling(part: &MemoryEffectObligation) -> bool {
    !part.obligation.inputs.is_empty() && decide_exactly(&part.obligation).is_none()
}

/// Decide a symbolic part for every input, or `None` when its shape is
/// outside what this decides (a register-offset address whose folded sides
/// are different terms and that no evaluated witness separates).
///
/// Both sides are first folded (`fold`): every variable-free subterm (the
/// word's fields and everything computed from them alone) is evaluated, and
/// every `ite` on a now-constant condition is replaced by its taken branch.
/// Then:
///
/// * two syntactically identical folded sides are equal for every input (a
///   register-offset address whose word extends and shifts the index exactly
///   as the operands' mode does);
/// * two 64-bit sides of the form `v + c` over the SAME variable `v` (or both
///   constant) are equal for every `v` exactly when their constants are equal
///   modulo 2^64 (the address and writeback parts);
/// * otherwise two pure bit routings (every bit a constant or one input bit;
///   `aarch64_value_decode_proofs::exact_routing_equality`) are equal for
///   every input exactly when their routings are equal, and a differing bit
///   can be driven apart (the load and store parts).
///
/// Each rule is an identity of bit-vector semantics, so `Some(Ok(()))` is a
/// decision for every input and `Some(Err(_))` a definite refutation. Still
/// an in-process decision, never a certificate.
pub fn decide_exactly(obligation: &ProofObligation) -> Option<Result<(), String>> {
    let intent = fold(&obligation.trust_ir_expr)?;
    let machine = fold(&obligation.aarch64_expr)?;
    if let (Some(a), Some(b)) = (linear(&intent), linear(&machine)) {
        if a.0 != b.0 {
            return None;
        }
        return Some(if a.1 == b.1 {
            Ok(())
        } else {
            Err(format!(
                "the operands name displacement {:#x} and the word {:#x} for every base",
                a.1, b.1
            ))
        });
    }
    if intent == machine {
        // The same term after folding: equal for every input.
        return Some(Ok(()));
    }
    if let Some(verdict) =
        crate::aarch64_value_decode_proofs::exact_routing_equality(&intent, &machine)
    {
        return Some(match verdict {
            Ok(()) => Ok(()),
            Err(mismatch) => Err(format!(
                "bit {} is {:?} in the operands' access but {:?} in the word",
                mismatch.bit, mismatch.intended, mismatch.emitted
            )),
        });
    }
    // Two different terms (a register-offset address the word extends or
    // shifts otherwise than the operands): a definite refutation only when
    // an evaluated witness separates them; otherwise undecided.
    witness_refutation(obligation, &intent, &machine).map(Err)
}

/// A point of a small structured grid (wrapping bases, sign-boundary and
/// all-ones indices and windows) where the two folded sides differ.
fn witness_refutation(obligation: &ProofObligation, intent: &E, machine: &E) -> Option<String> {
    const VALUES: [u64; 6] = [
        0,
        1,
        0x0000_0000_8000_0001,
        0x0000_0001_0000_0000,
        0xFFFF_FFFF_FFFF_FFFF,
        0x1234_5678_9ABC_DEF0,
    ];
    let names: Vec<&(String, u32)> = obligation.inputs.iter().collect();
    if names.is_empty() || names.len() > 3 {
        return None;
    }
    let mut assignment = vec![0usize; names.len()];
    loop {
        let mut env = crate::smt::EvalEnv::default();
        for (slot, (name, width)) in names.iter().enumerate() {
            let value = VALUES[assignment[slot]];
            let value = if *width >= 64 {
                value
            } else {
                value & ((1 << width) - 1)
            };
            env.insert(name.clone(), value);
        }
        if let (Ok(a), Ok(b)) = (intent.try_eval(&env), machine.try_eval(&env))
            && a != b
        {
            return Some(format!(
                "the operands' access and the word differ at {:?}",
                names
                    .iter()
                    .zip(&assignment)
                    .map(|((name, _), at)| (name.clone(), VALUES[*at]))
                    .collect::<Vec<_>>()
            ));
        }
        // Next assignment.
        let mut slot = 0;
        loop {
            if slot == assignment.len() {
                return None;
            }
            assignment[slot] += 1;
            if assignment[slot] < VALUES.len() {
                break;
            }
            assignment[slot] = 0;
            slot += 1;
        }
    }
}

fn mentions_a_variable(expr: &E) -> bool {
    if matches!(expr, E::Var { .. }) {
        return true;
    }
    let mut found = false;
    expr.for_each_child(&mut |child| found = found || mentions_a_variable(child));
    found
}

/// `expr` with every variable-free subterm evaluated to a constant (at most
/// 64 bits wide) and every `ite` on a constant condition replaced by its
/// taken branch; `None` for a node outside the vocabulary the parts use.
fn fold(expr: &E) -> Option<E> {
    use crate::smt::EvalResult;
    if !mentions_a_variable(expr) {
        return match expr.try_eval(&crate::smt::EvalEnv::default()).ok()? {
            EvalResult::Bool(value) => Some(E::bool_const(value)),
            EvalResult::Bv(value) if expr.bv_width() <= 64 => {
                Some(E::bv_const(value, expr.bv_width()))
            }
            _ => None,
        };
    }
    Some(match expr {
        E::Var { .. } => expr.clone(),
        E::Ite {
            cond,
            then_expr,
            else_expr,
        } => match fold(cond)? {
            E::BoolConst(true) => fold(then_expr)?,
            E::BoolConst(false) => fold(else_expr)?,
            cond => E::ite(cond, fold(then_expr)?, fold(else_expr)?),
        },
        E::Extract {
            high, low, operand, ..
        } => fold(operand)?.extract(*high, *low),
        E::Concat { hi, lo, .. } => fold(hi)?.concat(fold(lo)?),
        E::SignExtend {
            operand,
            extra_bits,
            ..
        } => fold(operand)?.sign_ext(*extra_bits),
        E::BvAdd { lhs, rhs, .. } => fold(lhs)?.bvadd(fold(rhs)?),
        E::BvAnd { lhs, rhs, .. } => fold(lhs)?.bvand(fold(rhs)?),
        E::BvOr { lhs, rhs, .. } => fold(lhs)?.bvor(fold(rhs)?),
        _ => return None,
    })
}

/// A 64-bit folded side as `(variable, constant)` meaning `variable +
/// constant` (no variable: the constant alone), or `None` when it is not of
/// that form.
fn linear(expr: &E) -> Option<(Option<&str>, u64)> {
    match expr {
        E::Var { name, width: 64 } => Some((Some(name.as_str()), 0)),
        E::BvConst { value, width: 64 } => Some((None, *value)),
        E::BvAdd {
            lhs,
            rhs,
            width: 64,
        } => {
            let (a, b) = (linear(lhs)?, linear(rhs)?);
            let variable = match (a.0, b.0) {
                (Some(_), Some(_)) => return None,
                (variable, None) | (None, variable) => variable,
            };
            Some((variable, a.1.wrapping_add(b.1)))
        }
        _ => None,
    }
}

#[cfg(test)]
#[path = "aarch64_memory_effect_tests.rs"]
mod tests;
