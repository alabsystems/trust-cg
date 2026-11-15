// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// Reference: Arm DDI0602 (2025-03) LDR/STR/LDRB/STRB/LDRH/STRH/LDRSB/LDRSH
//            (immediate: unsigned offset, pre-index, post-index), LDUR/STUR
//            (unscaled), LDR/STR (register), LDR (literal), and
//            crates/trust-cg-codegen/src/aarch64/encode.rs.
//
// Hand re-derivation of the archived trust-cg commit 7af30f92d
// (`scalar_memory_proofs.rs`, never merged) onto this tree's function walk.
// The form theorems and the binder are that commit's; what changed is where
// they are consumed (`FunctionVerifier::try_scalar_memory`) and how they earn
// credit (`crate::bound_memory_authority`, committed certificates only).

//! Operand-bound AArch64 scalar load/store FORM theorems.
//!
//! # Why this module exists
//!
//! Owner ruling 2026-09-29: an AArch64 bound-memory row (a pair `LDP`/`STP`
//! or a scalar `LDR`/`STR`) earns instruction credit ONLY from a formal proof,
//! never from statistical sampling. Before this module no scalar memory row
//! could earn credit at all: the immediate forms are judged by their
//! instruction-derived obligation
//! ([`crate::aarch64_instruction_word_proofs`]), which is decided in process
//! and reported as `INSTRUCTION_DERIVED_IS_NOT_CREDIT`; every other scalar
//! form reached only a withdrawn registry name lookup; and `coverage_gate`
//! keeps all of these opcodes in deferred debt.
//!
//! This module supplies one theorem per concrete architectural FORM,
//! `(LDR|STR) x addressing x register bank x access width x extension`, and a
//! binder that maps a concrete emitted [`MachInst`] to exactly one form or
//! refuses. The 65 forms are listed in [`SCALAR_MEMORY_FORMS`]:
//!
//! * unsigned scaled `imm12` and unscaled signed `imm9` (LDUR/STUR), each for
//!   W/X loads and stores, byte/halfword zero-extending loads, byte/halfword
//!   sign-extending loads to W and to X, and H/S/D/Q loads and stores;
//! * pre-index and post-index `imm9` writeback for W/X loads and stores (the
//!   only writeback transfers the encoder emits);
//! * register offset with the packed `(option << 1) | S` mode for W/X,
//!   byte/halfword and H/S/D/Q loads and stores;
//! * the 64-bit PC-relative literal load.
//!
//! A form theorem states, for ALL base (or PC) values, ALL admitted offsets or
//! index/mode values, ALL transfer register values and ALL memory contents:
//!
//! * STR: the byte at every address `q` after the instruction (the stored
//!   little-endian bytes, every other byte unchanged) and the base register
//!   after the instruction (writeback or unchanged);
//! * LDR: every byte `j` of the destination register (the loaded bytes, then
//!   the architectural zero or sign extension: W destinations clear bits
//!   63:32, H/S/D destinations clear bits 127:width) and the base register.
//!
//! # The two sides
//!
//! * **Machine side** follows the Arm pseudocode from the ENCODED fields:
//!   `imm12 = (off >> scale)<11:0>` re-derived and decoded as
//!   `ZeroExtend(imm12) << scale`; `imm9 = off<8:0>` decoded as
//!   `SignExtend(imm9)`; register offset decodes `option = mode<3:1>` with
//!   `DecodeRegExtend` and shifts by `scale` exactly when `S == 1`; the literal
//!   decodes `SignExtend(imm19) << 2`. Stores are one `w`-byte range write
//!   with a variable-shift byte extraction; loads read `w` bytes and extend
//!   byte-wise from the top loaded byte's sign bit.
//! * **Intent side** is the MachIR operand intent: the literal byte offset (or
//!   the packed-mode table for register offset), a chain of `w` single-byte
//!   stores with constant-index extraction, or an assembled little-endian
//!   scalar that is zero/sign extended as a whole and then projected to byte
//!   `j`.
//!
//! The two sides share no offset decode, byte extraction or extension
//! subexpression, so every obligation is structurally non-degenerate and every
//! applicable [`ScalarMachineMutation`] refutes.
//!
//! # Memory encoding (pure QF_BV, no arrays)
//!
//! As in [`crate::aarch64_pair_memory_forms`]: STR is observed at a free query address
//! `q` over a free original byte `m`, so the frame condition is inside the
//! theorem; LDR reads a single-point memory `M(x) = ite(x == p, c, d)`. Every
//! observed destination byte is a function of ONE memory read (a loaded byte,
//! a sign fill computed from the top loaded byte, or constant zero), and two
//! single-read functions agree on every single-point memory iff they agree on
//! every memory, so the single-point quantification is complete for the stated
//! equality.
//!
//! # Bank-independent stores
//!
//! A STORE theorem does not depend on the register bank: only the accessed
//! bytes of the transfer register are modelled. Equal-width store forms of
//! different banks are therefore the SAME formula under two form names
//! (`str.ui.gpr.w4` and `str.ui.fpr.w4`, and so on, including the pair module's
//! `stp.offset.gpr.w4` / `stp.offset.fpr.w4`). Either name is discharged by the
//! same certificate: the committed bound-memory set
//! ([`crate::bound_memory_authority`]) carries one file per exact query. Load forms are never aliased this way: the
//! destination register width and the extension differ by bank.
//!
//! # Binding and authority
//!
//! [`bind_scalar_memory_operands`] independently re-implements the encoder's
//! admission (it shares no code with `trust-cg-codegen`): exact operand
//! arities, physical W/X/ZR or H/S/D/Q transfers, an X/SP base, the encoder's
//! unsigned-scaled-first offset choice, the closed register-offset mode set
//! with W indices only under UXTW/SXTW, and signed `imm9`/`imm19` ranges. It
//! refuses loads into the zero register, loads that overwrite their own base,
//! writeback aliases, and volatile accesses (their observable access and
//! ordering boundary is not modelled). The emitted word is tied to these
//! MachIR fields by the enforced independent AArch64 decode check (ENC-5,
//! `trust-cg-codegen` `decode_check`). [`bind_scalar_memory_instruction`]
//! refuses to attribute the literal theorem at runtime: `LdrLiteral` is never
//! selected by lowering (`coverage_gate` allowlists it fail-closed), so a
//! literal row is refused rather than credited through a path no compile takes.
//!
//! Credit is Formal-only: [`crate::bound_memory_authority`] credits a bound
//! row only when the row's instruction-derived obligation ran and held (today
//! only GPR `LDR`/`STR{,B,H}` zero-extending immediates have one; every other
//! scalar form stays unverified), the form of the word that obligation judged
//! ([`decode_scalar_memory_word`]) is the bound form, and the exact query of
//! that form theorem has a committed certificate that the independent checker
//! replays in this process. The
//! evaluation sweep is never consulted for these theorems: it is
//! structurally blind to single-point memory (the default 100k sampler
//! accepted 361 of 478 deliberately wrong theorems of this shape, measured
//! 2026-09-29), and a missing certificate leaves the row unverified.
//!
//! # Claim boundary
//!
//! Instruction semantics only. No claim that loaded memory was initialized or
//! mapped, that an address is aligned or in bounds, that a spill slot is
//! disjoint from any other slot, or that a volatile access is preserved.
//! Registers other than `Rt`, `Rn` (and the read-only `Rm`) are untouched by
//! the Arm pseudocode and are not modelled. Faults, tagged addresses and
//! asynchronous aborts are outside the model.

use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr;
use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand, SpecialReg};

// ---------------------------------------------------------------------------
// Forms
// ---------------------------------------------------------------------------

/// Direction of the transfer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScalarTransfer {
    /// Load into the transfer register.
    Load,
    /// Store the transfer register.
    Store,
}

/// Scalar addressing mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScalarAddressing {
    /// `[Xn|SP, #imm12 << scale]`, no writeback.
    UnsignedOffset,
    /// `[Xn|SP, #simm9]` (LDUR/STUR), no writeback.
    Unscaled,
    /// `[Xn|SP, #simm9]!`: access at `base + off`, then `Xn = base + off`.
    PreIndex,
    /// `[Xn|SP], #simm9`: access at `base`, then `Xn = base + off`.
    PostIndex,
    /// `[Xn|SP, Rm, extend #shift]`, no writeback.
    RegisterOffset,
    /// `PC + SignExtend(imm19) << 2`.
    Literal,
}

/// Register bank of the transfer register.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScalarBank {
    /// W/X/ZR transfers; destination register is 64 bits.
    Gpr,
    /// H/S/D/Q transfers; destination register is 128 bits.
    Fpr,
}

/// Extension a load applies above the accessed bytes (stores carry `Zero`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScalarExtension {
    /// Zero-extend to the whole destination register.
    Zero,
    /// Sign-extend to 32 bits, then clear bits 63:32 (a W destination).
    SignTo32,
    /// Sign-extend to 64 bits (an X destination).
    SignTo64,
}

/// One concrete architectural scalar memory form.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ScalarMemoryForm {
    /// Load or store.
    pub transfer: ScalarTransfer,
    /// Addressing mode.
    pub addressing: ScalarAddressing,
    /// Register bank.
    pub bank: ScalarBank,
    /// Accessed bytes: 1, 2, 4 or 8 for GPR; 2, 4, 8 or 16 for FPR.
    pub access_bytes: u32,
    /// Load extension (`Zero` for stores).
    pub extension: ScalarExtension,
}

const fn scalar_form(
    transfer: ScalarTransfer,
    addressing: ScalarAddressing,
    bank: ScalarBank,
    access_bytes: u32,
    extension: ScalarExtension,
) -> ScalarMemoryForm {
    ScalarMemoryForm {
        transfer,
        addressing,
        bank,
        access_bytes,
        extension,
    }
}

use ScalarAddressing::{
    Literal as LIT, PostIndex as POST, PreIndex as PRE, RegisterOffset as RO, Unscaled as UNSCALED,
    UnsignedOffset as UI,
};
use ScalarBank::{Fpr as FPR, Gpr as GPR};
use ScalarExtension::{SignTo32 as SX32, SignTo64 as SX64, Zero as ZX};
use ScalarTransfer::{Load as LOAD, Store as STORE};

/// Every scalar memory form some emitted opcode can express, with its unique
/// lowercase form query. Each query is a substring of exactly one form
/// theorem name; the closing `]` keeps `w1.zx]` distinct from any longer tag.
pub const SCALAR_MEMORY_FORMS: [(ScalarMemoryForm, &str); 65] = [
    (
        scalar_form(LOAD, UI, GPR, 1, ZX),
        "scalarmem[ldr.ui.gpr.w1.zx]",
    ),
    (
        scalar_form(LOAD, UI, GPR, 2, ZX),
        "scalarmem[ldr.ui.gpr.w2.zx]",
    ),
    (
        scalar_form(LOAD, UI, GPR, 4, ZX),
        "scalarmem[ldr.ui.gpr.w4.zx]",
    ),
    (
        scalar_form(LOAD, UI, GPR, 8, ZX),
        "scalarmem[ldr.ui.gpr.w8.zx]",
    ),
    (
        scalar_form(LOAD, UI, GPR, 1, SX32),
        "scalarmem[ldr.ui.gpr.w1.sx32]",
    ),
    (
        scalar_form(LOAD, UI, GPR, 1, SX64),
        "scalarmem[ldr.ui.gpr.w1.sx64]",
    ),
    (
        scalar_form(LOAD, UI, GPR, 2, SX32),
        "scalarmem[ldr.ui.gpr.w2.sx32]",
    ),
    (
        scalar_form(LOAD, UI, GPR, 2, SX64),
        "scalarmem[ldr.ui.gpr.w2.sx64]",
    ),
    (
        scalar_form(LOAD, UI, FPR, 2, ZX),
        "scalarmem[ldr.ui.fpr.w2.zx]",
    ),
    (
        scalar_form(LOAD, UI, FPR, 4, ZX),
        "scalarmem[ldr.ui.fpr.w4.zx]",
    ),
    (
        scalar_form(LOAD, UI, FPR, 8, ZX),
        "scalarmem[ldr.ui.fpr.w8.zx]",
    ),
    (
        scalar_form(LOAD, UI, FPR, 16, ZX),
        "scalarmem[ldr.ui.fpr.w16.zx]",
    ),
    (
        scalar_form(STORE, UI, GPR, 1, ZX),
        "scalarmem[str.ui.gpr.w1]",
    ),
    (
        scalar_form(STORE, UI, GPR, 2, ZX),
        "scalarmem[str.ui.gpr.w2]",
    ),
    (
        scalar_form(STORE, UI, GPR, 4, ZX),
        "scalarmem[str.ui.gpr.w4]",
    ),
    (
        scalar_form(STORE, UI, GPR, 8, ZX),
        "scalarmem[str.ui.gpr.w8]",
    ),
    (
        scalar_form(STORE, UI, FPR, 2, ZX),
        "scalarmem[str.ui.fpr.w2]",
    ),
    (
        scalar_form(STORE, UI, FPR, 4, ZX),
        "scalarmem[str.ui.fpr.w4]",
    ),
    (
        scalar_form(STORE, UI, FPR, 8, ZX),
        "scalarmem[str.ui.fpr.w8]",
    ),
    (
        scalar_form(STORE, UI, FPR, 16, ZX),
        "scalarmem[str.ui.fpr.w16]",
    ),
    (
        scalar_form(LOAD, UNSCALED, GPR, 1, ZX),
        "scalarmem[ldr.unscaled.gpr.w1.zx]",
    ),
    (
        scalar_form(LOAD, UNSCALED, GPR, 2, ZX),
        "scalarmem[ldr.unscaled.gpr.w2.zx]",
    ),
    (
        scalar_form(LOAD, UNSCALED, GPR, 4, ZX),
        "scalarmem[ldr.unscaled.gpr.w4.zx]",
    ),
    (
        scalar_form(LOAD, UNSCALED, GPR, 8, ZX),
        "scalarmem[ldr.unscaled.gpr.w8.zx]",
    ),
    (
        scalar_form(LOAD, UNSCALED, GPR, 1, SX32),
        "scalarmem[ldr.unscaled.gpr.w1.sx32]",
    ),
    (
        scalar_form(LOAD, UNSCALED, GPR, 1, SX64),
        "scalarmem[ldr.unscaled.gpr.w1.sx64]",
    ),
    (
        scalar_form(LOAD, UNSCALED, GPR, 2, SX32),
        "scalarmem[ldr.unscaled.gpr.w2.sx32]",
    ),
    (
        scalar_form(LOAD, UNSCALED, GPR, 2, SX64),
        "scalarmem[ldr.unscaled.gpr.w2.sx64]",
    ),
    (
        scalar_form(LOAD, UNSCALED, FPR, 2, ZX),
        "scalarmem[ldr.unscaled.fpr.w2.zx]",
    ),
    (
        scalar_form(LOAD, UNSCALED, FPR, 4, ZX),
        "scalarmem[ldr.unscaled.fpr.w4.zx]",
    ),
    (
        scalar_form(LOAD, UNSCALED, FPR, 8, ZX),
        "scalarmem[ldr.unscaled.fpr.w8.zx]",
    ),
    (
        scalar_form(LOAD, UNSCALED, FPR, 16, ZX),
        "scalarmem[ldr.unscaled.fpr.w16.zx]",
    ),
    (
        scalar_form(STORE, UNSCALED, GPR, 1, ZX),
        "scalarmem[str.unscaled.gpr.w1]",
    ),
    (
        scalar_form(STORE, UNSCALED, GPR, 2, ZX),
        "scalarmem[str.unscaled.gpr.w2]",
    ),
    (
        scalar_form(STORE, UNSCALED, GPR, 4, ZX),
        "scalarmem[str.unscaled.gpr.w4]",
    ),
    (
        scalar_form(STORE, UNSCALED, GPR, 8, ZX),
        "scalarmem[str.unscaled.gpr.w8]",
    ),
    (
        scalar_form(STORE, UNSCALED, FPR, 2, ZX),
        "scalarmem[str.unscaled.fpr.w2]",
    ),
    (
        scalar_form(STORE, UNSCALED, FPR, 4, ZX),
        "scalarmem[str.unscaled.fpr.w4]",
    ),
    (
        scalar_form(STORE, UNSCALED, FPR, 8, ZX),
        "scalarmem[str.unscaled.fpr.w8]",
    ),
    (
        scalar_form(STORE, UNSCALED, FPR, 16, ZX),
        "scalarmem[str.unscaled.fpr.w16]",
    ),
    (
        scalar_form(LOAD, PRE, GPR, 4, ZX),
        "scalarmem[ldr.pre.gpr.w4.zx]",
    ),
    (
        scalar_form(LOAD, PRE, GPR, 8, ZX),
        "scalarmem[ldr.pre.gpr.w8.zx]",
    ),
    (
        scalar_form(STORE, PRE, GPR, 4, ZX),
        "scalarmem[str.pre.gpr.w4]",
    ),
    (
        scalar_form(STORE, PRE, GPR, 8, ZX),
        "scalarmem[str.pre.gpr.w8]",
    ),
    (
        scalar_form(LOAD, POST, GPR, 4, ZX),
        "scalarmem[ldr.post.gpr.w4.zx]",
    ),
    (
        scalar_form(LOAD, POST, GPR, 8, ZX),
        "scalarmem[ldr.post.gpr.w8.zx]",
    ),
    (
        scalar_form(STORE, POST, GPR, 4, ZX),
        "scalarmem[str.post.gpr.w4]",
    ),
    (
        scalar_form(STORE, POST, GPR, 8, ZX),
        "scalarmem[str.post.gpr.w8]",
    ),
    (
        scalar_form(LOAD, RO, GPR, 1, ZX),
        "scalarmem[ldr.ro.gpr.w1.zx]",
    ),
    (
        scalar_form(LOAD, RO, GPR, 2, ZX),
        "scalarmem[ldr.ro.gpr.w2.zx]",
    ),
    (
        scalar_form(LOAD, RO, GPR, 4, ZX),
        "scalarmem[ldr.ro.gpr.w4.zx]",
    ),
    (
        scalar_form(LOAD, RO, GPR, 8, ZX),
        "scalarmem[ldr.ro.gpr.w8.zx]",
    ),
    (
        scalar_form(LOAD, RO, FPR, 2, ZX),
        "scalarmem[ldr.ro.fpr.w2.zx]",
    ),
    (
        scalar_form(LOAD, RO, FPR, 4, ZX),
        "scalarmem[ldr.ro.fpr.w4.zx]",
    ),
    (
        scalar_form(LOAD, RO, FPR, 8, ZX),
        "scalarmem[ldr.ro.fpr.w8.zx]",
    ),
    (
        scalar_form(LOAD, RO, FPR, 16, ZX),
        "scalarmem[ldr.ro.fpr.w16.zx]",
    ),
    (
        scalar_form(STORE, RO, GPR, 1, ZX),
        "scalarmem[str.ro.gpr.w1]",
    ),
    (
        scalar_form(STORE, RO, GPR, 2, ZX),
        "scalarmem[str.ro.gpr.w2]",
    ),
    (
        scalar_form(STORE, RO, GPR, 4, ZX),
        "scalarmem[str.ro.gpr.w4]",
    ),
    (
        scalar_form(STORE, RO, GPR, 8, ZX),
        "scalarmem[str.ro.gpr.w8]",
    ),
    (
        scalar_form(STORE, RO, FPR, 2, ZX),
        "scalarmem[str.ro.fpr.w2]",
    ),
    (
        scalar_form(STORE, RO, FPR, 4, ZX),
        "scalarmem[str.ro.fpr.w4]",
    ),
    (
        scalar_form(STORE, RO, FPR, 8, ZX),
        "scalarmem[str.ro.fpr.w8]",
    ),
    (
        scalar_form(STORE, RO, FPR, 16, ZX),
        "scalarmem[str.ro.fpr.w16]",
    ),
    (
        scalar_form(LOAD, LIT, GPR, 8, ZX),
        "scalarmem[ldr.literal.gpr.w8.zx]",
    ),
];

impl ScalarMemoryForm {
    /// The unique form query for this form, or `None` for a combination
    /// no emitted opcode can express.
    pub fn query(&self) -> Option<&'static str> {
        SCALAR_MEMORY_FORMS
            .iter()
            .find(|(candidate, _)| candidate == self)
            .map(|(_, query)| *query)
    }

    /// Bytes of the destination/source register (`X` = 8, `V` = 16).
    pub fn register_bytes(&self) -> u32 {
        match self.bank {
            ScalarBank::Gpr => 8,
            ScalarBank::Fpr => 16,
        }
    }

    fn scale_log2(&self) -> u32 {
        self.access_bytes.trailing_zeros()
    }

    /// Low register bytes a load defines from memory or its sign: the access
    /// width for zero extension, 4 for a W sign extension, 8 for an X one.
    fn extension_bytes(&self) -> u32 {
        match self.extension {
            ScalarExtension::Zero => self.access_bytes,
            ScalarExtension::SignTo32 => 4,
            ScalarExtension::SignTo64 => 8,
        }
    }

    fn mnemonic(&self) -> &'static str {
        match (self.transfer, self.bank, self.access_bytes, self.extension) {
            (LOAD, GPR, 1, ZX) => "LDRB Wt",
            (LOAD, GPR, 2, ZX) => "LDRH Wt",
            (LOAD, GPR, 4, _) => "LDR Wt",
            (LOAD, GPR, 8, _) => "LDR Xt",
            (LOAD, GPR, 1, SX32) => "LDRSB Wt",
            (LOAD, GPR, 1, SX64) => "LDRSB Xt",
            (LOAD, GPR, 2, SX32) => "LDRSH Wt",
            (LOAD, GPR, 2, SX64) => "LDRSH Xt",
            (LOAD, FPR, 2, _) => "LDR Ht",
            (LOAD, FPR, 4, _) => "LDR St",
            (LOAD, FPR, 8, _) => "LDR Dt",
            (LOAD, FPR, 16, _) => "LDR Qt",
            (STORE, GPR, 1, _) => "STRB Wt",
            (STORE, GPR, 2, _) => "STRH Wt",
            (STORE, GPR, 4, _) => "STR Wt",
            (STORE, GPR, 8, _) => "STR Xt",
            (STORE, FPR, 2, _) => "STR Ht",
            (STORE, FPR, 4, _) => "STR St",
            (STORE, FPR, 8, _) => "STR Dt",
            (STORE, FPR, 16, _) => "STR Qt",
            _ => "?",
        }
    }

    /// Form theorem name. Its lowercase form contains [`Self::query`].
    pub fn proof_name(&self) -> String {
        let query = self
            .query()
            .expect("proof_name requires a legal scalar form");
        let tag = &query["scalarmem".len()..];
        let scale = self.scale_log2();
        let address = match self.addressing {
            UI => format!("[Xn|SP, #imm12<<{scale}]"),
            UNSCALED => "[Xn|SP, #simm9] unscaled".to_string(),
            PRE => "[Xn|SP, #simm9]!".to_string(),
            POST => "[Xn|SP], #simm9".to_string(),
            RO => format!("[Xn|SP, Rm, UXTW|LSL|SXTW|SXTX #0|#{scale}]"),
            LIT => "PC+simm19*4".to_string(),
        };
        let w = self.access_bytes;
        let effect = match (self.transfer, self.extension) {
            (STORE, _) => format!("{w} LE bytes at S, every other byte unchanged"),
            (LOAD, ZX) => format!("Rt = ZeroExtend({w} LE bytes at S)"),
            (LOAD, SX32) => format!("Rt = ZeroExtend(SignExtend32({w} LE bytes at S))"),
            (LOAD, SX64) => format!("Rt = SignExtend64({w} LE bytes at S)"),
        };
        let base = match self.addressing {
            PRE | POST => "; Xn'=Xn+off",
            LIT => "",
            _ => "; Xn unchanged",
        };
        format!(
            "ScalarMem{tag}: {} {address} == {effect}{base} (decoded fields, operand-bound)",
            self.mnemonic()
        )
    }
}

/// The 65 faithful scalar-memory form obligations, in table order.
pub fn all_scalar_memory_proofs() -> Vec<ProofObligation> {
    SCALAR_MEMORY_FORMS
        .iter()
        .map(|(form, _)| proof_scalar_memory(form).expect("table forms are legal"))
        .collect()
}

/// The faithful obligation for `form` (`None` for an illegal form).
pub fn proof_scalar_memory(form: &ScalarMemoryForm) -> Option<ProofObligation> {
    proof_scalar_memory_with_mutation(form, ScalarMachineMutation::None)
}

// ---------------------------------------------------------------------------
// Obligation construction
// ---------------------------------------------------------------------------

/// A deliberate defect injected into the MACHINE side only.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScalarMachineMutation {
    /// The faithful machine semantics.
    None,
    /// Post-index access at the indexed address; any other form accesses the
    /// unindexed base (or PC).
    WrongAddressingMode,
    /// The decoder scales the offset (or register index) one step too far.
    WrongScale,
    /// Access address displaced by one byte.
    OffsetPlusOne,
    /// Writeback dropped (pre/post) or invented (no-writeback forms).
    WritebackFlipped,
    /// One byte fewer is transferred.
    ShortAccess,
    /// A store writes one byte beyond the access width.
    ExtraStoredByte,
    /// A load leaves register bytes above the extension uncleared.
    NoZeroExtend,
    /// Zero extension replaced by sign extension to X, or the reverse.
    WrongExtension,
    /// Sign extension to W replaced by sign extension to X, or the reverse.
    SignWidthSwap,
    /// Bytes transferred big-endian.
    BigEndian,
    /// Register index zero- and sign-extension swapped.
    WrongIndexExtend,
    /// Register index shift ignored when `S == 1`.
    IgnoreIndexShift,
}

impl ScalarMachineMutation {
    /// Every defect the refutation controls exercise.
    pub const DEFECTS: [ScalarMachineMutation; 12] = [
        ScalarMachineMutation::WrongAddressingMode,
        ScalarMachineMutation::WrongScale,
        ScalarMachineMutation::OffsetPlusOne,
        ScalarMachineMutation::WritebackFlipped,
        ScalarMachineMutation::ShortAccess,
        ScalarMachineMutation::ExtraStoredByte,
        ScalarMachineMutation::NoZeroExtend,
        ScalarMachineMutation::WrongExtension,
        ScalarMachineMutation::SignWidthSwap,
        ScalarMachineMutation::BigEndian,
        ScalarMachineMutation::WrongIndexExtend,
        ScalarMachineMutation::IgnoreIndexShift,
    ];

    /// Whether this defect changes the semantics of `form`.
    pub fn applies_to(self, form: &ScalarMemoryForm) -> bool {
        use ScalarMachineMutation as M;
        match self {
            M::None | M::WrongAddressingMode | M::WrongScale | M::OffsetPlusOne => true,
            M::WritebackFlipped => form.addressing != LIT,
            M::ShortAccess | M::BigEndian => form.access_bytes > 1,
            M::ExtraStoredByte => form.transfer == STORE,
            M::NoZeroExtend => {
                form.transfer == LOAD && form.extension_bytes() < form.register_bytes()
            }
            M::WrongExtension => form.transfer == LOAD && form.bank == GPR && form.access_bytes < 8,
            M::SignWidthSwap => form.transfer == LOAD && form.extension != ZX,
            M::WrongIndexExtend => form.addressing == RO,
            M::IgnoreIndexShift => form.addressing == RO && form.access_bytes > 1,
        }
    }
}

fn c64(value: u64) -> SmtExpr {
    SmtExpr::bv_const(value, 64)
}

fn c8(value: u64) -> SmtExpr {
    SmtExpr::bv_const(value, 8)
}

/// A register value as 64-bit limbs (`hi` only for 16-byte stores).
#[derive(Clone)]
struct RegisterLimbs {
    lo: SmtExpr,
    hi: Option<SmtExpr>,
}

/// Machine byte extraction: `(v >> (k * 8))<7:0>` over limbs.
fn machine_register_byte(value: &RegisterLimbs, k: SmtExpr) -> SmtExpr {
    let lo = value
        .lo
        .clone()
        .bvlshr(k.clone().bvshl(c64(3)))
        .extract(7, 0);
    match &value.hi {
        None => lo,
        Some(hi) => SmtExpr::ite(
            k.clone().bvult(c64(8)),
            lo,
            hi.clone()
                .bvlshr(k.bvsub(c64(8)).bvshl(c64(3)))
                .extract(7, 0),
        ),
    }
}

/// Intent byte extraction at a constant index.
fn intent_register_byte_at(value: &RegisterLimbs, index: u32) -> SmtExpr {
    let limb = if index < 8 {
        value.lo.clone()
    } else {
        value
            .hi
            .clone()
            .expect("16-byte access requires a high limb")
    };
    let bit = (index % 8) * 8;
    limb.extract(bit + 7, bit)
}

/// Machine and intent access addresses, plus the base register after the
/// instruction as `(machine, intent)` (`None` for the literal form).
struct Addresses {
    machine_access: SmtExpr,
    intent_access: SmtExpr,
    base_after: Option<(SmtExpr, SmtExpr)>,
}

fn push_input(inputs: &mut Vec<(String, u32)>, name: &str, width: u32) -> SmtExpr {
    inputs.push((name.to_string(), width));
    SmtExpr::var(name, width)
}

fn addresses(
    form: &ScalarMemoryForm,
    mutation: ScalarMachineMutation,
    inputs: &mut Vec<(String, u32)>,
    preconditions: &mut Vec<SmtExpr>,
) -> Addresses {
    use ScalarMachineMutation as M;
    let scale = form.scale_log2();
    let w64 = c64(u64::from(form.access_bytes));

    if form.addressing == LIT {
        let pc = push_input(inputs, "smem_pc", 64);
        let k = push_input(inputs, "smem_imm19", 19);
        // Intent: the MachIR word offset, in bytes.
        let off = k.sign_ext(45).bvmul(c64(4));
        // Encoder field imm19 = (off / 4)<18:0>; Arm: SignExtend(imm19) << 2.
        let imm19 = off.clone().bvashr(c64(2)).extract(18, 0);
        let shift = if mutation == M::WrongScale { 3 } else { 2 };
        let decoded = imm19.sign_ext(45).bvshl(c64(shift));
        let mut machine_access = if mutation == M::WrongAddressingMode {
            pc.clone()
        } else {
            pc.clone().bvadd(decoded)
        };
        if mutation == M::OffsetPlusOne {
            machine_access = machine_access.bvadd(c64(1));
        }
        return Addresses {
            machine_access,
            intent_access: pc.bvadd(off),
            base_after: None,
        };
    }

    let base = push_input(inputs, "smem_base", 64);
    let (intent_offset, machine_offset) = match form.addressing {
        UI => {
            let k = push_input(inputs, "smem_imm12", 12);
            let off = k.zero_ext(52).bvmul(w64.clone());
            // Encoder field imm12 = (off / size)<11:0>; Arm: ZeroExtend(imm12) << scale.
            let imm12 = off.clone().bvlshr(c64(u64::from(scale))).extract(11, 0);
            let shift = if mutation == M::WrongScale {
                scale + 1
            } else {
                scale
            };
            (off, imm12.zero_ext(52).bvshl(c64(u64::from(shift))))
        }
        UNSCALED | PRE | POST => {
            let k = push_input(inputs, "smem_imm9", 9);
            let off = k.sign_ext(55);
            // Encoder field imm9 = off<8:0>; Arm: SignExtend(imm9).
            let decoded = off.clone().extract(8, 0).sign_ext(55);
            let decoded = if mutation == M::WrongScale {
                decoded.bvshl(c64(u64::from(scale.max(1))))
            } else {
                decoded
            };
            (off, decoded)
        }
        RO => {
            let index = push_input(inputs, "smem_index", 64);
            let mode = push_input(inputs, "smem_mode", 4);
            let mode_is = |value: u64| mode.clone().eq_expr(SmtExpr::bv_const(value, 4));
            let mut admitted = mode_is(4);
            for value in [5, 6, 7, 12, 13, 14, 15] {
                admitted = admitted.or_expr(mode_is(value));
            }
            preconditions.push(admitted);
            // Intent: the packed MachIR mode `(option << 1) | S` as a table
            // of index expressions, scaled by multiplication.
            let low = index.clone().extract(31, 0);
            let intent = SmtExpr::ite(
                mode_is(4),
                low.clone().zero_ext(32),
                SmtExpr::ite(
                    mode_is(5),
                    low.clone().zero_ext(32).bvmul(w64.clone()),
                    SmtExpr::ite(
                        mode_is(6),
                        index.clone(),
                        SmtExpr::ite(
                            mode_is(7),
                            index.clone().bvmul(w64.clone()),
                            SmtExpr::ite(
                                mode_is(12),
                                low.clone().sign_ext(32),
                                SmtExpr::ite(
                                    mode_is(13),
                                    low.sign_ext(32).bvmul(w64.clone()),
                                    SmtExpr::ite(
                                        mode_is(14),
                                        index.clone(),
                                        index.clone().bvmul(w64.clone()),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            );
            // Machine: DecodeRegExtend(option), ExtendReg(m, type, shift).
            let one = SmtExpr::bv_const(1, 1);
            let option = mode.clone().extract(3, 1);
            let signed_when = if mutation == M::WrongIndexExtend {
                SmtExpr::bv_const(0, 1)
            } else {
                one.clone()
            };
            let signed = option.clone().extract(2, 2).eq_expr(signed_when);
            let full = option.extract(0, 0).eq_expr(one.clone());
            let low = index.clone().extract(31, 0);
            let narrow = SmtExpr::ite(signed, low.clone().sign_ext(32), low.zero_ext(32));
            let extended = SmtExpr::ite(full, index, narrow);
            let shift = if mutation == M::WrongScale {
                scale + 1
            } else {
                scale
            };
            let amount = if mutation == M::IgnoreIndexShift {
                c64(0)
            } else {
                SmtExpr::ite(
                    mode.extract(0, 0).eq_expr(one),
                    c64(u64::from(shift)),
                    c64(0),
                )
            };
            (intent, extended.bvshl(amount))
        }
        LIT => unreachable!("literal handled above"),
    };

    let machine_indexed = base.clone().bvadd(machine_offset);
    let intent_indexed = base.clone().bvadd(intent_offset);
    let post = form.addressing == POST;
    let access_at_base = post != (mutation == M::WrongAddressingMode);
    let mut machine_access = if access_at_base {
        base.clone()
    } else {
        machine_indexed.clone()
    };
    if mutation == M::OffsetPlusOne {
        machine_access = machine_access.bvadd(c64(1));
    }
    let intent_access = if post {
        base.clone()
    } else {
        intent_indexed.clone()
    };
    let writeback = matches!(form.addressing, PRE | POST);
    let machine_after = if writeback != (mutation == M::WritebackFlipped) {
        machine_indexed
    } else {
        base.clone()
    };
    let intent_after = if writeback { intent_indexed } else { base };
    Addresses {
        machine_access,
        intent_access,
        base_after: Some((machine_after, intent_after)),
    }
}

/// Build the obligation for `form` with the given machine-side `mutation`.
/// Returns `None` for an illegal form or a mutation that does not apply.
pub fn proof_scalar_memory_with_mutation(
    form: &ScalarMemoryForm,
    mutation: ScalarMachineMutation,
) -> Option<ProofObligation> {
    use ScalarMachineMutation as M;
    form.query()?;
    if !mutation.applies_to(form) {
        return None;
    }
    let w = form.access_bytes;
    let mut inputs = Vec::new();
    let mut preconditions = Vec::new();
    let addr = addresses(form, mutation, &mut inputs, &mut preconditions);

    let (intent_byte, machine_byte) = match form.transfer {
        ScalarTransfer::Store => {
            let lo = push_input(&mut inputs, "smem_rt_lo", 64);
            let hi = (w > 8).then(|| push_input(&mut inputs, "smem_rt_hi", 64));
            let value = RegisterLimbs { lo, hi };
            let q = push_input(&mut inputs, "smem_q", 64);
            let m = push_input(&mut inputs, "smem_m", 8);

            // Machine: one `w`-byte range write at the decoded address.
            let rel = q.clone().bvsub(addr.machine_access.clone());
            let length = match mutation {
                M::ExtraStoredByte => w + 1,
                M::ShortAccess => w - 1,
                _ => w,
            };
            let index = if mutation == M::BigEndian {
                c64(u64::from(w) - 1).bvsub(rel.clone())
            } else {
                rel.clone()
            };
            let machine = SmtExpr::ite(
                rel.bvult(c64(u64::from(length))),
                machine_register_byte(&value, index),
                m.clone(),
            );

            // Intent: `w` single-byte stores at S, S+1, ..., constant bytes.
            let mut intent = m;
            for i in 0..w {
                intent = SmtExpr::ite(
                    q.clone()
                        .eq_expr(addr.intent_access.clone().bvadd(c64(u64::from(i)))),
                    intent_register_byte_at(&value, i),
                    intent,
                );
            }
            (intent, machine)
        }
        ScalarTransfer::Load => {
            let p = push_input(&mut inputs, "smem_p", 64);
            let c = push_input(&mut inputs, "smem_c", 8);
            let d = push_input(&mut inputs, "smem_d", 8);
            let j = push_input(&mut inputs, "smem_j", 8);
            preconditions.push(j.clone().bvult(c8(u64::from(form.register_bytes()))));
            let read =
                |address: SmtExpr| SmtExpr::ite(address.eq_expr(p.clone()), c.clone(), d.clone());
            let jz = j.clone().zero_ext(56);

            // Machine: data = Mem[address, w]; Rt byte j is data byte j below
            // the access width, then the extension fill, then zero.
            let effective = if mutation == M::ShortAccess { w - 1 } else { w };
            let data_index = if mutation == M::BigEndian {
                c64(u64::from(w) - 1).bvsub(jz.clone())
            } else {
                jz.clone()
            };
            let data = read(addr.machine_access.clone().bvadd(data_index));
            let top = read(
                addr.machine_access
                    .clone()
                    .bvadd(c64(u64::from(effective) - 1)),
            );
            let kind = match (form.extension, mutation) {
                (ZX, M::WrongExtension) => SX64,
                (SX32 | SX64, M::WrongExtension) => ZX,
                (SX32, M::SignWidthSwap) => SX64,
                (SX64, M::SignWidthSwap) => SX32,
                (extension, _) => extension,
            };
            let (limit, fill) = match kind {
                ZX => (effective, c8(0)),
                SX32 | SX64 => (
                    if kind == SX32 { 4 } else { 8 },
                    SmtExpr::ite(
                        top.extract(7, 7).eq_expr(SmtExpr::bv_const(1, 1)),
                        c8(0xff),
                        c8(0),
                    ),
                ),
            };
            let cleared = if mutation == M::NoZeroExtend {
                read(addr.machine_access.clone().bvadd(jz.clone()))
            } else {
                c8(0)
            };
            let upper = SmtExpr::ite(j.clone().bvult(c8(u64::from(limit))), fill, cleared);
            let machine = SmtExpr::ite(j.bvult(c8(u64::from(effective))), data, upper);

            // Intent: LE-assembled scalar, extended as a whole, byte j.
            let assemble = |start: &SmtExpr, from: u32, count: u32| {
                let mut value = read(start.clone().bvadd(c64(u64::from(from))));
                for k in 1..count {
                    let byte = read(start.clone().bvadd(c64(u64::from(from + k))));
                    value = byte.concat(value);
                }
                value
            };
            let lo_bytes = w.min(8);
            let raw = assemble(&addr.intent_access, 0, lo_bytes);
            let lo = match form.extension {
                ZX if lo_bytes < 8 => raw.zero_ext((8 - lo_bytes) * 8),
                ZX => raw,
                SX32 => raw.sign_ext(32 - w * 8).zero_ext(32),
                SX64 => raw.sign_ext(64 - w * 8),
            };
            let lo_byte = lo.bvlshr(jz.clone().bvshl(c64(3))).extract(7, 0);
            let intent = if form.register_bytes() == 8 {
                lo_byte
            } else {
                let hi = if w == 16 {
                    assemble(&addr.intent_access, 8, 8)
                } else {
                    c64(0)
                };
                SmtExpr::ite(
                    jz.clone().bvult(c64(8)),
                    lo_byte,
                    hi.bvlshr(jz.bvsub(c64(8)).bvshl(c64(3))).extract(7, 0),
                )
            };
            (intent, machine)
        }
    };

    let (intent, machine) = match addr.base_after {
        Some((machine_after, intent_after)) => {
            let sel = push_input(&mut inputs, "smem_sel", 8);
            let first = sel.eq_expr(c8(0));
            (
                SmtExpr::ite(first.clone(), intent_byte.zero_ext(56), intent_after),
                SmtExpr::ite(first, machine_byte.zero_ext(56), machine_after),
            )
        }
        None => (intent_byte.zero_ext(56), machine_byte.zero_ext(56)),
    };

    let name = if mutation == M::None {
        form.proof_name()
    } else {
        format!("{} [refutation control: {mutation:?}]", form.proof_name())
    };
    Some(ProofObligation {
        name,
        trust_ir_expr: intent,
        aarch64_expr: machine,
        inputs,
        preconditions,
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::MemoryModel),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    })
}

// ---------------------------------------------------------------------------
// Instruction binding
// ---------------------------------------------------------------------------

/// A concrete scalar memory instruction bound to exactly one form.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ScalarMemoryBinding {
    /// The architectural form whose theorem this instruction instantiates.
    pub form: ScalarMemoryForm,
    /// `Rt` register field (31 is ZR for GPR, a real register for FPR).
    pub rt_field: u32,
    /// `Rn` field (31 is SP); `None` for the literal form.
    pub base_field: Option<u32>,
    /// `Rm` field (31 is ZR) for register offset.
    pub index_field: Option<u32>,
    /// Immediate forms: the literal byte offset. Register offset: the packed
    /// `(option << 1) | S` mode. Literal: the signed `imm19` word offset.
    pub operand: i64,
}

impl ScalarMemoryBinding {
    /// The unique form query for the bound form.
    pub fn query(&self) -> &'static str {
        self.form
            .query()
            .expect("a binding only ever carries a legal form")
    }

    /// The theorem variable, and its value, that this binding instantiates:
    /// the quantified offset field (`imm12`, `imm9`, `imm19`) or mode.
    pub fn theorem_operand_assignment(&self) -> (&'static str, u64) {
        let w = u64::from(self.form.access_bytes);
        match self.form.addressing {
            UI => ("smem_imm12", (self.operand as u64) / w),
            UNSCALED | PRE | POST => ("smem_imm9", (self.operand as u64) & 0x1ff),
            RO => ("smem_mode", self.operand as u64),
            LIT => ("smem_imm19", (self.operand as u64) & 0x7_ffff),
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum WidthRule {
    /// `LDR`/`STR`: the width follows the transfer register class.
    Register,
    /// Byte/halfword: the width is fixed by the opcode.
    Narrow { bytes: u32, signed: bool },
}

#[derive(Debug, Clone, Copy)]
enum OpcodeShape {
    Immediate {
        transfer: ScalarTransfer,
        width: WidthRule,
    },
    Writeback {
        transfer: ScalarTransfer,
        pre: bool,
    },
    RegisterOffset {
        transfer: ScalarTransfer,
        narrow: Option<u32>,
    },
    Literal,
    Volatile,
}

fn scalar_opcode_shape(opcode: AArch64Opcode) -> Option<OpcodeShape> {
    use AArch64Opcode as O;
    use OpcodeShape::*;
    let narrow = |bytes, signed| WidthRule::Narrow { bytes, signed };
    Some(match opcode {
        O::LdrRI => Immediate {
            transfer: LOAD,
            width: WidthRule::Register,
        },
        O::StrRI => Immediate {
            transfer: STORE,
            width: WidthRule::Register,
        },
        O::LdrbRI => Immediate {
            transfer: LOAD,
            width: narrow(1, false),
        },
        O::LdrhRI => Immediate {
            transfer: LOAD,
            width: narrow(2, false),
        },
        O::LdrsbRI => Immediate {
            transfer: LOAD,
            width: narrow(1, true),
        },
        O::LdrshRI => Immediate {
            transfer: LOAD,
            width: narrow(2, true),
        },
        O::StrbRI => Immediate {
            transfer: STORE,
            width: narrow(1, false),
        },
        O::StrhRI => Immediate {
            transfer: STORE,
            width: narrow(2, false),
        },
        O::LdrPreIndex => Writeback {
            transfer: LOAD,
            pre: true,
        },
        O::LdrPostIndex => Writeback {
            transfer: LOAD,
            pre: false,
        },
        O::StrPreIndex => Writeback {
            transfer: STORE,
            pre: true,
        },
        O::StrPostIndex => Writeback {
            transfer: STORE,
            pre: false,
        },
        O::LdrRO => RegisterOffset {
            transfer: LOAD,
            narrow: None,
        },
        O::StrRO => RegisterOffset {
            transfer: STORE,
            narrow: None,
        },
        O::LdrbRO => RegisterOffset {
            transfer: LOAD,
            narrow: Some(1),
        },
        O::LdrhRO => RegisterOffset {
            transfer: LOAD,
            narrow: Some(2),
        },
        O::StrbRO => RegisterOffset {
            transfer: STORE,
            narrow: Some(1),
        },
        O::StrhRO => RegisterOffset {
            transfer: STORE,
            narrow: Some(2),
        },
        O::LdrLiteral => Literal,
        O::VolatileLdrRI
        | O::VolatileLdrbRI
        | O::VolatileLdrhRI
        | O::VolatileStrRI
        | O::VolatileStrbRI
        | O::VolatileStrhRI => Volatile,
        _ => return None,
    })
}

/// True for every scalar load/store opcode this module binds or explicitly
/// refuses (including the volatile aliases).
pub fn is_scalar_memory_opcode(opcode: AArch64Opcode) -> bool {
    scalar_opcode_shape(opcode).is_some()
}

/// Every form the binder can attribute to an instruction of `opcode` (its
/// legal forms), in [`SCALAR_MEMORY_FORMS`] order; `None` for an opcode the
/// binder never attributes (a non-scalar opcode, a volatile alias, or the
/// literal load, which is never attributed at runtime).
///
/// It is derived from the binder's admission rules: an `LDR`/`STR` immediate
/// takes a W/X or H/S/D/Q transfer in the unsigned scaled or unscaled form; a
/// byte/halfword immediate takes a W/X transfer, sign-extending to W or to X
/// for `LDRSB`/`LDRSH`; writeback takes W/X; register offset takes W/X and
/// H/S/D/Q (byte/halfword: the zero-extending GPR form).
pub fn scalar_opcode_forms(opcode: AArch64Opcode) -> Option<Vec<ScalarMemoryForm>> {
    let shape = scalar_opcode_shape(opcode)?;
    let admits = |form: &ScalarMemoryForm| -> bool {
        match shape {
            OpcodeShape::Immediate { transfer, width } => {
                if form.transfer != transfer || !matches!(form.addressing, UI | UNSCALED) {
                    return false;
                }
                match width {
                    WidthRule::Register => {
                        form.extension == ZX
                            && match form.bank {
                                GPR => matches!(form.access_bytes, 4 | 8),
                                FPR => true,
                            }
                    }
                    WidthRule::Narrow { bytes, signed } => {
                        form.bank == GPR
                            && form.access_bytes == bytes
                            && (if transfer == LOAD && signed {
                                form.extension != ZX
                            } else {
                                form.extension == ZX
                            })
                    }
                }
            }
            OpcodeShape::Writeback { transfer, pre } => {
                form.transfer == transfer
                    && form.addressing == if pre { PRE } else { POST }
                    && form.bank == GPR
                    && matches!(form.access_bytes, 4 | 8)
            }
            OpcodeShape::RegisterOffset { transfer, narrow } => {
                form.transfer == transfer
                    && form.addressing == RO
                    && form.extension == ZX
                    && match narrow {
                        Some(bytes) => form.bank == GPR && form.access_bytes == bytes,
                        None => form.bank == FPR || matches!(form.access_bytes, 4 | 8),
                    }
            }
            OpcodeShape::Literal | OpcodeShape::Volatile => false,
        }
    };
    let forms: Vec<ScalarMemoryForm> = SCALAR_MEMORY_FORMS
        .iter()
        .map(|(form, _)| *form)
        .filter(admits)
        .collect();
    (!forms.is_empty()).then_some(forms)
}

/// A representative instruction of `opcode` that the binder attributes to
/// `form`: transfer register 1 (W/X by the form, or the H/S/D/Q register),
/// base X2, index X3 (register offset, LSL by the access size), and an
/// offset the encoder places in the form's field (`#access` for the unsigned
/// scaled form, `#-8` unscaled, `#-16` writeback). `None` when `form` is not a
/// legal form of `opcode`.
pub fn representative_scalar_instruction(
    opcode: AArch64Opcode,
    form: &ScalarMemoryForm,
) -> Option<MachInst> {
    use trust_cg_ir::PReg;
    if !scalar_opcode_forms(opcode)?.contains(form) {
        return None;
    }
    let w = i64::from(form.access_bytes);
    let rt = match (form.bank, form.access_bytes, form.extension) {
        (FPR, 2, _) => 165 + 1,
        (FPR, 4, _) => 128 + 1,
        (FPR, 8, _) => 96 + 1,
        (FPR, _, _) => 64 + 1,
        (GPR, 8, _) | (GPR, _, SX64) => 1,
        (GPR, _, _) => 32 + 1,
    };
    let rt = MachOperand::PReg(PReg::new(rt));
    let base = MachOperand::PReg(PReg::new(2));
    let operands = match form.addressing {
        UI => vec![rt, base, MachOperand::Imm(w)],
        UNSCALED => vec![rt, base, MachOperand::Imm(-8)],
        PRE | POST => vec![rt, base, MachOperand::Imm(-16)],
        RO => vec![
            rt,
            base,
            MachOperand::PReg(PReg::new(3)),
            MachOperand::Imm(if form.access_bytes > 1 { 7 } else { 6 }),
        ],
        LIT => return None,
    };
    let inst = MachInst::new(opcode, operands);
    (bind_scalar_memory_instruction(&inst).ok()?.form == *form).then_some(inst)
}

/// Physical W/X/ZR transfer: (register bytes, field).
fn gpr_transfer(operand: &MachOperand) -> Option<(u32, u32)> {
    match operand {
        MachOperand::PReg(reg) => match reg.encoding() {
            e @ 0..=30 => Some((8, u32::from(e))),
            e @ 32..=62 => Some((4, u32::from(e - 32))),
            160 => Some((8, 31)),
            161 => Some((4, 31)),
            _ => None,
        },
        MachOperand::Special(SpecialReg::XZR) => Some((8, 31)),
        MachOperand::Special(SpecialReg::WZR) => Some((4, 31)),
        _ => None,
    }
}

/// Physical H/S/D/Q transfer: (access bytes, field). Field 31 is a real
/// register; B registers have no scalar memory encoding here.
fn fpr_transfer(operand: &MachOperand) -> Option<(u32, u32)> {
    match operand {
        MachOperand::PReg(reg) => match reg.encoding() {
            e @ 64..=95 => Some((16, u32::from(e - 64))),
            e @ 96..=127 => Some((8, u32::from(e - 96))),
            e @ 128..=159 => Some((4, u32::from(e - 128))),
            e @ 165..=196 => Some((2, u32::from(e - 165))),
            _ => None,
        },
        _ => None,
    }
}

/// Canonical X register or SP base field.
fn base_register(operand: &MachOperand) -> Option<u32> {
    match operand {
        MachOperand::PReg(reg) if reg.encoding() <= 31 => Some(u32::from(reg.encoding())),
        MachOperand::Special(SpecialReg::SP) => Some(31),
        _ => None,
    }
}

const BASE_REFUSAL: &str = "scalar memory base must be a canonical X register or SP";

fn bind_immediate(
    inst: &MachInst,
    transfer: ScalarTransfer,
    width: WidthRule,
) -> Result<ScalarMemoryBinding, String> {
    let (t, base_field, offset) = match inst.operands.as_slice() {
        [t, MachOperand::MemOp { base, offset }] => {
            if base.encoding() > 31 {
                return Err(BASE_REFUSAL.into());
            }
            (t, u32::from(base.encoding()), *offset)
        }
        [t, base] => (t, base_register(base).ok_or(BASE_REFUSAL)?, 0),
        [t, base, MachOperand::Imm(offset)] => {
            (t, base_register(base).ok_or(BASE_REFUSAL)?, *offset)
        }
        _ => {
            return Err(
                "immediate memory requires exactly [Rt, Xn|SP], [Rt, Xn|SP, #imm] or \
                 [Rt, MemOp{Xn|SP, #imm}]"
                    .into(),
            );
        }
    };
    let (bank, access_bytes, extension, rt_field) = match width {
        WidthRule::Register => {
            if let Some((bytes, field)) = gpr_transfer(t) {
                (GPR, bytes, ZX, field)
            } else if let Some((bytes, field)) = fpr_transfer(t) {
                (FPR, bytes, ZX, field)
            } else {
                return Err(
                    "LDR/STR transfer must be a physical W/X/ZR or H/S/D/Q register (never \
                     SP/WSP, a B register or unresolved)"
                        .into(),
                );
            }
        }
        WidthRule::Narrow { bytes, signed } => {
            let Some((register_bytes, field)) = gpr_transfer(t) else {
                return Err("byte/halfword transfer must be a physical W/X/ZR register".into());
            };
            let extension = match (transfer, signed, register_bytes) {
                (LOAD, true, 4) => SX32,
                (LOAD, true, _) => SX64,
                _ => ZX,
            };
            (GPR, bytes, extension, field)
        }
    };
    let w = i64::from(access_bytes);
    // The encoder's choice: unsigned scaled imm12 whenever it fits, else imm9.
    let addressing = if offset >= 0 && offset % w == 0 && offset / w <= 0xfff {
        UI
    } else if (-256..=255).contains(&offset) {
        UNSCALED
    } else {
        return Err(format!(
            "immediate memory offset {offset} fits neither unsigned imm12 scaled by {w} nor \
             signed imm9"
        ));
    };
    Ok(ScalarMemoryBinding {
        form: scalar_form(transfer, addressing, bank, access_bytes, extension),
        rt_field,
        base_field: Some(base_field),
        index_field: None,
        operand: offset,
    })
}

fn bind_writeback(
    inst: &MachInst,
    transfer: ScalarTransfer,
    pre: bool,
) -> Result<ScalarMemoryBinding, String> {
    let [t, base, MachOperand::Imm(offset)] = inst.operands.as_slice() else {
        return Err("scalar writeback requires exactly [Rt, Xn|SP, #simm9]".into());
    };
    let Some((access_bytes, rt_field)) = gpr_transfer(t) else {
        return Err("scalar writeback transfer must be a physical W/X/ZR register".into());
    };
    let base_field = base_register(base).ok_or(BASE_REFUSAL)?;
    if !(-256..=255).contains(offset) {
        return Err(format!(
            "scalar writeback offset {offset} is outside signed imm9"
        ));
    }
    Ok(ScalarMemoryBinding {
        form: scalar_form(
            transfer,
            if pre { PRE } else { POST },
            GPR,
            access_bytes,
            ZX,
        ),
        rt_field,
        base_field: Some(base_field),
        index_field: None,
        operand: *offset,
    })
}

fn bind_register_offset(
    inst: &MachInst,
    transfer: ScalarTransfer,
    narrow: Option<u32>,
) -> Result<ScalarMemoryBinding, String> {
    let (t, base, index, mode) = match inst.operands.as_slice() {
        [t, base, index] => (t, base, index, 6),
        [t, base, index, MachOperand::Imm(mode)] => (t, base, index, *mode),
        _ => {
            return Err(
                "register-offset memory requires exactly [Rt, Xn|SP, Rm] or \
                 [Rt, Xn|SP, Rm, #mode]"
                    .into(),
            );
        }
    };
    if !matches!(mode, 4 | 5 | 6 | 7 | 12 | 13 | 14 | 15) {
        return Err(format!(
            "register-offset mode {mode} is not one of UXTW/LSL/SXTW/SXTX with S in {{0,1}}"
        ));
    }
    let base_field = base_register(base).ok_or(BASE_REFUSAL)?;
    let Some((index_bytes, index_field)) = gpr_transfer(index) else {
        return Err("register-offset index must be a physical W/X/ZR register".into());
    };
    if index_bytes == 4 && index_field != 31 && matches!(mode, 6 | 7 | 14 | 15) {
        return Err(
            "LSL/SXTX register-offset index requires an X register or the zero register".into(),
        );
    }
    let (bank, access_bytes, rt_field) = match narrow {
        Some(bytes) => {
            let Some((_, field)) = gpr_transfer(t) else {
                return Err(
                    "byte/halfword register-offset transfer must be a physical W/X/ZR register"
                        .into(),
                );
            };
            (GPR, bytes, field)
        }
        None => {
            if let Some((bytes, field)) = gpr_transfer(t) {
                (GPR, bytes, field)
            } else if let Some((bytes, field)) = fpr_transfer(t) {
                (FPR, bytes, field)
            } else {
                return Err(
                    "register-offset transfer must be a physical W/X/ZR or H/S/D/Q register".into(),
                );
            }
        }
    };
    Ok(ScalarMemoryBinding {
        form: scalar_form(transfer, RO, bank, access_bytes, ZX),
        rt_field,
        base_field: Some(base_field),
        index_field: Some(index_field),
        operand: mode,
    })
}

fn bind_literal(inst: &MachInst) -> Result<ScalarMemoryBinding, String> {
    let [t, MachOperand::Imm(word_offset)] = inst.operands.as_slice() else {
        return Err("literal load requires exactly [Xt, #imm19]".into());
    };
    let Some((8, rt_field)) = gpr_transfer(t) else {
        return Err(
            "literal load binds only an X transfer (the encoder emits the 64-bit literal form)"
                .into(),
        );
    };
    if !(-(1i64 << 18)..(1i64 << 18)).contains(word_offset) {
        return Err(format!(
            "literal word offset {word_offset} is outside signed imm19"
        ));
    }
    Ok(ScalarMemoryBinding {
        form: scalar_form(LOAD, LIT, GPR, 8, ZX),
        rt_field,
        base_field: None,
        index_field: None,
        operand: *word_offset,
    })
}

/// Bind a concrete scalar memory instruction's OPERANDS to its form, or
/// explain the refusal. This is the operand-exact binding only; use
/// [`bind_scalar_memory_instruction`] for runtime attribution, which also
/// requires an enforced decode-check arm for the emitted word.
pub fn bind_scalar_memory_operands(inst: &MachInst) -> Result<ScalarMemoryBinding, String> {
    let Some(shape) = scalar_opcode_shape(inst.opcode) else {
        return Err(format!("{:?} is not a scalar-memory opcode", inst.opcode));
    };
    let binding = match shape {
        OpcodeShape::Volatile => {
            return Err(
                "volatile memory access: the observable access and ordering boundary is not \
                 modelled, so no form theorem is attributed"
                    .into(),
            );
        }
        OpcodeShape::Immediate { transfer, width } => bind_immediate(inst, transfer, width)?,
        OpcodeShape::Writeback { transfer, pre } => bind_writeback(inst, transfer, pre)?,
        OpcodeShape::RegisterOffset { transfer, narrow } => {
            bind_register_offset(inst, transfer, narrow)?
        }
        OpcodeShape::Literal => bind_literal(inst)?,
    };
    let bound = binding.form;
    if bound.transfer == LOAD && bound.bank == GPR && binding.rt_field == 31 {
        return Err(
            "a load into the zero register discards its value; that effect is not modelled, so \
             the instruction is refused"
                .into(),
        );
    }
    if bound.bank == GPR
        && let Some(base) = binding.base_field
        && base != 31
        && base == binding.rt_field
    {
        if matches!(bound.addressing, PRE | POST) {
            return Err(
                "scalar writeback base overlaps the transfer register (unpredictable)".into(),
            );
        }
        if bound.transfer == LOAD {
            return Err(
                "a load that overwrites its own base register is refused; the bound register \
                 model keeps the base value"
                    .into(),
            );
        }
    }
    if bound.query().is_none() {
        return Err(format!("no legal scalar memory form for {bound:?}"));
    }
    Ok(binding)
}

/// Runtime attribution: the operand binding, restricted to forms the walk
/// may attribute. Literal loads are refused: lowering never selects
/// `LdrLiteral` (`coverage_gate` allowlists it fail-closed), so no compile
/// needs the literal theorem and none is attributed.
pub fn bind_scalar_memory_instruction(inst: &MachInst) -> Result<ScalarMemoryBinding, String> {
    let binding = bind_scalar_memory_operands(inst)?;
    if binding.form.addressing == LIT {
        return Err(
            "LdrLiteral is never selected by lowering (fail-closed allowlisted in \
             coverage_gate), so no form theorem is attributed to a literal load"
                .into(),
        );
    }
    Ok(binding)
}

/// The binding a load/store-register WORD denotes, decoded from its bits
/// (Arm DDI 0487 C4.1, "Loads and stores": the unsigned-immediate,
/// unscaled-immediate, immediate pre-/post-indexed and register-offset
/// classes), or `None` when the word is not an instance of an attributable
/// scalar form (another class, an unprivileged or prefetch encoding, a form
/// with no theorem such as `LDRSW`, or a literal load).
///
/// ```text
/// size | 111 | V | 01 | opc | imm12          | Rn | Rt   unsigned offset
/// size | 111 | V | 00 | opc | 0 | imm9 | 00  | Rn | Rt   unscaled
/// size | 111 | V | 00 | opc | 0 | imm9 | 01  | Rn | Rt   post-index
/// size | 111 | V | 00 | opc | 0 | imm9 | 11  | Rn | Rt   pre-index
/// size | 111 | V | 00 | opc | 1 | Rm | option | S | 10 | Rn | Rt   register offset
/// ```
///
/// Independent of [`bind_scalar_memory_operands`]: the Formal-only
/// bound-memory rule ([`crate::bound_memory_authority`]) requires this to
/// equal, field for field, the binding of the instruction whose
/// instruction-derived obligation judged the word.
pub fn decode_scalar_memory_word(word: u32) -> Option<ScalarMemoryBinding> {
    if (word >> 27) & 0b111 != 0b111 {
        return None;
    }
    let size = word >> 30;
    let simd = (word >> 26) & 1 == 1;
    let opc = (word >> 22) & 0b11;
    let (transfer, bank, access_bytes, extension) = match (simd, size, opc) {
        (false, _, 0b00) => (STORE, GPR, 1 << size, ZX),
        (false, _, 0b01) => (LOAD, GPR, 1 << size, ZX),
        (false, 0..=2, 0b10) => (LOAD, GPR, 1 << size, SX64),
        (false, 0 | 1, 0b11) => (LOAD, GPR, 1 << size, SX32),
        (true, 0, 0b10) => (STORE, FPR, 16, ZX),
        (true, 0, 0b11) => (LOAD, FPR, 16, ZX),
        (true, _, 0b00) => (STORE, FPR, 1 << size, ZX),
        (true, _, 0b01) => (LOAD, FPR, 1 << size, ZX),
        _ => return None,
    };
    let rt_field = word & 0x1f;
    let base_field = (word >> 5) & 0x1f;
    let sext9 = |bits: u32| -> i64 { i64::from(((bits << 23) as i32) >> 23) };
    let (addressing, index_field, operand) = match (word >> 24) & 0b11 {
        0b01 => (
            UI,
            None,
            i64::from((word >> 10) & 0xfff) * i64::from(access_bytes),
        ),
        0b00 if (word >> 21) & 1 == 0 => {
            let imm9 = sext9((word >> 12) & 0x1ff);
            match (word >> 10) & 0b11 {
                0b00 => (UNSCALED, None, imm9),
                0b01 => (POST, None, imm9),
                0b11 => (PRE, None, imm9),
                _ => return None,
            }
        }
        0b00 if (word >> 10) & 0b11 == 0b10 => (
            RO,
            Some((word >> 16) & 0x1f),
            i64::from((((word >> 13) & 0b111) << 1) | ((word >> 12) & 1)),
        ),
        _ => return None,
    };
    let form = scalar_form(transfer, addressing, bank, access_bytes, extension);
    form.query()?;
    Some(ScalarMemoryBinding {
        form,
        rt_field,
        base_field: Some(base_field),
        index_field,
        operand,
    })
}

/// The word of a scalar memory binding, from this module's own encoder (Arm
/// DDI 0487 C4.1, "Loads and stores": the unsigned-immediate,
/// unscaled-immediate, immediate pre-/post-indexed and register-offset
/// classes; the diagrams in [`decode_scalar_memory_word`]'s documentation).
/// `None` for the literal form, a binding without a base, or an offset that
/// does not fit the form's field. It shares no code with `trust-cg-codegen`'s
/// encoder; [`decode_scalar_memory_word`] inverts it.
pub fn scalar_memory_word(binding: &ScalarMemoryBinding) -> Option<u32> {
    let form = binding.form;
    let base = binding.base_field?;
    let (size, v, opc): (u32, u32, u32) = match (form.bank, form.transfer, form.extension) {
        (FPR, transfer, _) => {
            let (size, q) = match form.access_bytes {
                2 => (0b01, false),
                4 => (0b10, false),
                8 => (0b11, false),
                _ => (0b00, true),
            };
            let opc = u32::from(transfer == LOAD) | (u32::from(q) << 1);
            (size, 1, opc)
        }
        (GPR, STORE, _) => (form.access_bytes.trailing_zeros(), 0, 0b00),
        (GPR, LOAD, ZX) => (form.access_bytes.trailing_zeros(), 0, 0b01),
        (GPR, LOAD, SX64) => (form.access_bytes.trailing_zeros(), 0, 0b10),
        (GPR, LOAD, SX32) => (form.access_bytes.trailing_zeros(), 0, 0b11),
    };
    let head = (size << 30) | (0b111 << 27) | (v << 26) | (opc << 22);
    let tail = (base << 5) | binding.rt_field;
    let imm9 = |offset: i64| -> Option<u32> {
        (-256..=255)
            .contains(&offset)
            .then_some((offset as u32) & 0x1ff)
    };
    Some(match form.addressing {
        UI => {
            let w = i64::from(form.access_bytes);
            if binding.operand < 0 || binding.operand % w != 0 || binding.operand / w > 0xfff {
                return None;
            }
            head | (0b01 << 24) | (((binding.operand / w) as u32) << 10) | tail
        }
        UNSCALED => head | (imm9(binding.operand)? << 12) | tail,
        POST => head | (imm9(binding.operand)? << 12) | (0b01 << 10) | tail,
        PRE => head | (imm9(binding.operand)? << 12) | (0b11 << 10) | tail,
        RO => {
            let mode = u32::try_from(binding.operand)
                .ok()
                .filter(|mode| *mode <= 15)?;
            head | (1 << 21)
                | (binding.index_field? << 16)
                | ((mode >> 1) << 13)
                | ((mode & 1) << 12)
                | (0b10 << 10)
                | tail
        }
        LIT => return None,
    })
}

// ---------------------------------------------------------------------------
// In-process refutation search
// ---------------------------------------------------------------------------

fn preconditions_hold(ob: &ProofObligation, env: &crate::smt::EvalEnv) -> bool {
    ob.preconditions.iter().all(|p| {
        p.try_eval(env)
            .expect("scalar precondition must evaluate")
            .as_bool()
    })
}

fn sext(value: u64, bits: u32) -> i64 {
    ((value << (64 - bits)) as i64) >> (64 - bits)
}

/// Independent reference byte offset of a quantified offset field.
fn reference_offset(form: &ScalarMemoryForm, field: u64, index: u64) -> u64 {
    let w = u64::from(form.access_bytes);
    let low = index & 0xffff_ffff;
    match form.addressing {
        UI => field * w,
        UNSCALED | PRE | POST => sext(field, 9) as u64,
        RO => match field {
            4 => low,
            5 => low * w,
            6 | 14 => index,
            7 | 15 => index.wrapping_mul(w),
            12 => sext(low, 32) as u64,
            13 => (sext(low, 32) as u64).wrapping_mul(w),
            other => panic!("mode {other}"),
        },
        LIT => (sext(field, 19) as u64).wrapping_mul(4),
    }
}

/// Deterministic structured grid around the intended access: every
/// accessed byte and both neighbours, extreme offsets/modes, sign-bit
/// indices, wrapping bases, both sign polarities of the loaded byte and
/// every destination byte. Returns the first disagreeing point.
///
/// `None` is NOT evidence that a form theorem holds (only a replayed
/// certificate is): it is the in-process refutation search the machine
/// defects ([`ScalarMachineMutation::DEFECTS`]) must not survive.
pub fn grid_counterexample(ob: &ProofObligation, form: &ScalarMemoryForm) -> Option<String> {
    let w = u64::from(form.access_bytes);
    let (field_name, fields): (&str, Vec<u64>) = match form.addressing {
        UI => ("smem_imm12", vec![0, 1, 2, 0xfff]),
        UNSCALED | PRE | POST => (
            "smem_imm9",
            [-256i64, -1, 0, 1, 255]
                .iter()
                .map(|v| (*v as u64) & 0x1ff)
                .collect(),
        ),
        RO => ("smem_mode", vec![4, 5, 6, 7, 12, 13, 14, 15]),
        LIT => (
            "smem_imm19",
            [-(1i64 << 18), -1, 0, 1, (1 << 18) - 1]
                .iter()
                .map(|v| (*v as u64) & 0x7_ffff)
                .collect(),
        ),
    };
    let indices: &[u64] = if form.addressing == RO {
        &[3, 0x8000_0001, u64::MAX]
    } else {
        &[0]
    };
    let sels: &[u64] = if form.addressing == LIT {
        &[0]
    } else {
        &[0, 1]
    };
    let anchor = if form.addressing == LIT {
        "smem_pc"
    } else {
        "smem_base"
    };
    for base in [0x0000_7fff_f000_1000u64, 0, u64::MAX - 5] {
        for &field in &fields {
            for &index in indices {
                let offset = reference_offset(form, field, index);
                let access = if form.addressing == POST {
                    base
                } else {
                    base.wrapping_add(offset)
                };
                for delta in -2i64..(w as i64 + 2) {
                    let probe = access.wrapping_add(delta as u64);
                    for &sel in sels {
                        let mut env = crate::smt::EvalEnv::default();
                        env.insert(anchor.into(), base);
                        env.insert(field_name.into(), field);
                        env.insert("smem_index".into(), index);
                        env.insert("smem_sel".into(), sel);
                        let mut points = Vec::new();
                        match form.transfer {
                            STORE => {
                                env.insert("smem_rt_lo".into(), 0x0807_0605_0403_0201);
                                env.insert("smem_rt_hi".into(), 0x100f_0e0d_0c0b_0a09);
                                env.insert("smem_q".into(), probe);
                                env.insert("smem_m".into(), 0xaa);
                                points.push(env);
                            }
                            LOAD => {
                                env.insert("smem_p".into(), probe);
                                for (c, d) in [(0x5a, 0xc3), (0xa5, 0x3c)] {
                                    for j in 0..u64::from(form.register_bytes()) {
                                        let mut point = env.clone();
                                        point.insert("smem_c".into(), c);
                                        point.insert("smem_d".into(), d);
                                        point.insert("smem_j".into(), j);
                                        points.push(point);
                                    }
                                }
                            }
                        }
                        for point in &points {
                            if !preconditions_hold(ob, point) {
                                continue;
                            }
                            let intent = ob.trust_ir_expr.try_eval(point).expect("intent");
                            let machine = ob.aarch64_expr.try_eval(point).expect("machine");
                            if intent != machine {
                                return Some(format!(
                                    "base={base:#x} {field_name}={field:#x} index={index:#x} \
                                     probe={probe:#x} sel={sel}: intent={intent:?} \
                                     machine={machine:?}"
                                ));
                            }
                        }
                    }
                }
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::PReg;

    #[test]
    fn sixty_five_forms_have_unique_queries_names_and_are_non_degenerate() {
        let proofs = all_scalar_memory_proofs();
        assert_eq!(proofs.len(), 65);
        let pair_names: Vec<String> =
            crate::aarch64_pair_memory_forms::all_pair_memory_form_proofs()
                .into_iter()
                .map(|proof| proof.name.to_lowercase())
                .collect();
        let mut names = std::collections::BTreeSet::new();
        let mut forms = std::collections::HashSet::new();
        for ((form, query), proof) in SCALAR_MEMORY_FORMS.iter().zip(&proofs) {
            assert!(forms.insert(*form), "duplicate form {form:?}");
            assert!(!proof.is_degenerate(), "{} is X==X", proof.name);
            assert!(names.insert(proof.name.clone()), "duplicate {}", proof.name);
            assert!(proof.name.starts_with("ScalarMem["), "{}", proof.name);
            assert_eq!(*query, query.to_lowercase());
            let matching = proofs
                .iter()
                .filter(|other| other.name.to_lowercase().contains(query))
                .count();
            assert_eq!(matching, 1, "{query} must select exactly one form theorem");
            assert!(!pair_names.iter().any(|name| name.contains(query)));
            assert_eq!(form.query(), Some(*query));
            assert!(form.access_bytes.is_power_of_two());
            assert!(form.access_bytes <= form.register_bytes());
        }
    }

    #[test]
    fn every_faithful_form_agrees_on_the_structured_grid() {
        for (form, _) in SCALAR_MEMORY_FORMS {
            let ob = proof_scalar_memory(&form).unwrap();
            assert_eq!(grid_counterexample(&ob, &form), None, "{}", ob.name);
        }
    }

    #[test]
    fn every_applicable_machine_defect_is_refuted_on_the_grid() {
        let mut applied = 0;
        for (form, _) in SCALAR_MEMORY_FORMS {
            for mutation in ScalarMachineMutation::DEFECTS {
                let Some(ob) = proof_scalar_memory_with_mutation(&form, mutation) else {
                    assert!(
                        !mutation.applies_to(&form),
                        "{form:?} {mutation:?} must build"
                    );
                    continue;
                };
                applied += 1;
                assert!(
                    grid_counterexample(&ob, &form).is_some(),
                    "{form:?}: defect {mutation:?} was NOT refuted"
                );
            }
        }
        // Per family (derived by hand from `applies_to`): unsigned offset 139,
        // unscaled 139, pre-index 28, post-index 28, register offset 139,
        // literal 5.
        assert_eq!(applied, 139 + 139 + 28 + 28 + 139 + 5);
    }

    /// AY decides a representative form from every addressing family, and a
    /// representative defect set yields genuine counterexamples. A faithful
    /// verdict other than `Verified` is tolerated only as an incomplete proof
    /// certificate or a timeout (never refutation, never an error), and at
    /// least one form must actually be decided so an all-timeout host cannot
    /// pass vacuously. The certificate route for all 65 forms is
    /// `regen_bound_memory_certs`.
    #[test]
    fn scalar_obligations_never_refute_and_defects_refute_with_ay_when_available() {
        use ScalarMachineMutation as M;
        if !crate::ay_bridge::ay_available() {
            eprintln!(
                "SKIP (unqualified): AY + independent checker unavailable: {:?}",
                crate::ay_bridge::proof_toolchain_unavailable_reason()
            );
            return;
        }
        let config = crate::ay_bridge::AYConfig::default();
        let mut failures = Vec::new();
        let mut decided = 0usize;
        let representatives = [
            scalar_form(LOAD, UI, GPR, 8, ZX),
            scalar_form(LOAD, UNSCALED, GPR, 1, SX32),
            scalar_form(STORE, PRE, GPR, 8, ZX),
            scalar_form(LOAD, POST, GPR, 4, ZX),
            scalar_form(STORE, RO, FPR, 16, ZX),
            scalar_form(LOAD, RO, GPR, 2, ZX),
        ];
        for form in representatives {
            let ob = proof_scalar_memory(&form).unwrap();
            match crate::ay_bridge::verify_with_ay(&ob, &config) {
                crate::ay_bridge::AYResult::Verified => decided += 1,
                crate::ay_bridge::AYResult::Unknown(reason)
                    if reason.contains("incomplete AY proof certificate")
                        || reason.contains("unusable AY proof evidence")
                        || reason.contains("incomplete self-check-rejected") =>
                {
                    decided += 1;
                }
                crate::ay_bridge::AYResult::Timeout => {}
                other => failures.push(format!("{}: {other:?}", ob.name)),
            }
        }
        if decided == 0 {
            failures.push("no representative scalar form was decided by the solver".into());
        }
        for (form, defects) in [
            (
                scalar_form(LOAD, UNSCALED, GPR, 1, SX32),
                vec![M::WrongExtension, M::SignWidthSwap, M::OffsetPlusOne],
            ),
            (
                scalar_form(STORE, PRE, GPR, 8, ZX),
                vec![
                    M::WritebackFlipped,
                    M::ExtraStoredByte,
                    M::WrongAddressingMode,
                ],
            ),
            (
                scalar_form(LOAD, RO, GPR, 2, ZX),
                vec![M::WrongIndexExtend, M::IgnoreIndexShift, M::BigEndian],
            ),
        ] {
            for mutation in defects {
                let ob = proof_scalar_memory_with_mutation(&form, mutation).unwrap();
                let result = crate::ay_bridge::verify_with_ay(&ob, &config);
                if !matches!(result, crate::ay_bridge::AYResult::CounterExample(_)) {
                    failures.push(format!(
                        "{}: expected counterexample, got {result:?}",
                        ob.name
                    ));
                }
            }
        }
        assert!(failures.is_empty(), "{failures:#?}");
    }

    /// Measurement aid: `SCALAR_MEM_SMT2_DIR=<dir> cargo test -- --ignored
    /// dump_scalar_memory_smt2` writes each form's exact AY query.
    #[test]
    #[ignore]
    fn dump_scalar_memory_smt2() {
        let Some(dir) = std::env::var_os("SCALAR_MEM_SMT2_DIR") else {
            return;
        };
        let dir = std::path::PathBuf::from(dir);
        std::fs::create_dir_all(&dir).unwrap();
        let config = crate::ay_bridge::AYConfig::default();
        for (form, query) in SCALAR_MEMORY_FORMS {
            let tag = query.trim_start_matches("scalarmem[").trim_end_matches(']');
            let ob = proof_scalar_memory(&form).unwrap();
            std::fs::write(
                dir.join(format!("{tag}.smt2")),
                crate::ay_bridge::generate_smt2_query(&ob, &config),
            )
            .unwrap();
        }
    }

    fn p(encoding: u16) -> MachOperand {
        MachOperand::PReg(PReg::new(encoding))
    }

    fn imm(value: i64) -> MachOperand {
        MachOperand::Imm(value)
    }

    fn mem(base: u16, offset: i64) -> MachOperand {
        MachOperand::MemOp {
            base: PReg::new(base),
            offset,
        }
    }

    fn at(opcode: AArch64Opcode, operands: Vec<MachOperand>) -> MachInst {
        MachInst::new(opcode, operands)
    }

    #[test]
    fn representative_spellings_bind_exact_forms_and_fields() {
        use AArch64Opcode as O;
        let sp = || MachOperand::Special(SpecialReg::SP);
        let xzr = MachOperand::Special(SpecialReg::XZR);
        type Fields = (u32, Option<u32>, Option<u32>, i64);
        let cases: Vec<(MachInst, &str, Fields)> = vec![
            // ldr x0, [x1, #16]
            (
                at(O::LdrRI, vec![p(0), p(1), imm(16)]),
                "scalarmem[ldr.ui.gpr.w8.zx]",
                (0, Some(1), None, 16),
            ),
            // ldr w0, [sp] (two-operand zero offset)
            (
                at(O::LdrRI, vec![p(32), sp()]),
                "scalarmem[ldr.ui.gpr.w4.zx]",
                (0, Some(31), None, 0),
            ),
            // ldur x16, [x29, #-8] (post-frame spill reload spelling)
            (
                at(O::LdrRI, vec![p(16), mem(29, -8)]),
                "scalarmem[ldr.unscaled.gpr.w8.zx]",
                (16, Some(29), None, -8),
            ),
            // stur x17, [x29, #-16] (post-frame spill store spelling)
            (
                at(O::StrRI, vec![p(17), mem(29, -16)]),
                "scalarmem[str.unscaled.gpr.w8]",
                (17, Some(29), None, -16),
            ),
            // an unaligned non-negative offset takes the unscaled encoding
            (
                at(O::LdrRI, vec![p(0), p(1), imm(12)]),
                "scalarmem[ldr.unscaled.gpr.w8.zx]",
                (0, Some(1), None, 12),
            ),
            // the largest scaled X offset
            (
                at(O::LdrRI, vec![p(0), p(1), imm(4095 * 8)]),
                "scalarmem[ldr.ui.gpr.w8.zx]",
                (0, Some(1), None, 32760),
            ),
            // ldrb with W and X carriers
            (
                at(O::LdrbRI, vec![p(32), p(1), imm(4095)]),
                "scalarmem[ldr.ui.gpr.w1.zx]",
                (0, Some(1), None, 4095),
            ),
            (
                at(O::LdrbRI, vec![p(3), p(1), imm(1)]),
                "scalarmem[ldr.ui.gpr.w1.zx]",
                (3, Some(1), None, 1),
            ),
            // ldrsb/ldrsh select the extension from the destination bank
            (
                at(O::LdrsbRI, vec![p(32), p(1)]),
                "scalarmem[ldr.ui.gpr.w1.sx32]",
                (0, Some(1), None, 0),
            ),
            (
                at(O::LdrsbRI, vec![p(0), p(1), imm(-1)]),
                "scalarmem[ldr.unscaled.gpr.w1.sx64]",
                (0, Some(1), None, -1),
            ),
            (
                at(O::LdrshRI, vec![p(34), p(1), imm(2)]),
                "scalarmem[ldr.ui.gpr.w2.sx32]",
                (2, Some(1), None, 2),
            ),
            (
                at(O::LdrshRI, vec![p(2), p(1), imm(3)]),
                "scalarmem[ldr.unscaled.gpr.w2.sx64]",
                (2, Some(1), None, 3),
            ),
            // narrow stores
            (
                at(O::StrhRI, vec![p(33), p(2), imm(2)]),
                "scalarmem[str.ui.gpr.w2]",
                (1, Some(2), None, 2),
            ),
            (
                at(O::StrbRI, vec![xzr.clone(), sp(), imm(7)]),
                "scalarmem[str.ui.gpr.w1]",
                (31, Some(31), None, 7),
            ),
            // FP banks: Q, H, D, S (FP field 31 is a real register)
            (
                at(O::LdrRI, vec![p(65), sp(), imm(16)]),
                "scalarmem[ldr.ui.fpr.w16.zx]",
                (1, Some(31), None, 16),
            ),
            (
                at(O::StrRI, vec![p(168), p(0), imm(-2)]),
                "scalarmem[str.unscaled.fpr.w2]",
                (3, Some(0), None, -2),
            ),
            (
                at(O::LdrRI, vec![p(104), p(29), imm(8)]),
                "scalarmem[ldr.ui.fpr.w8.zx]",
                (8, Some(29), None, 8),
            ),
            (
                at(O::StrRI, vec![p(159), p(1)]),
                "scalarmem[str.ui.fpr.w4]",
                (31, Some(1), None, 0),
            ),
            // storing the base register's own value is legal
            (
                at(O::StrRI, vec![p(0), p(0), imm(8)]),
                "scalarmem[str.ui.gpr.w8]",
                (0, Some(0), None, 8),
            ),
            // writeback
            (
                at(O::StrPreIndex, vec![p(30), sp(), imm(-16)]),
                "scalarmem[str.pre.gpr.w8]",
                (30, Some(31), None, -16),
            ),
            (
                at(O::LdrPostIndex, vec![p(30), sp(), imm(16)]),
                "scalarmem[ldr.post.gpr.w8.zx]",
                (30, Some(31), None, 16),
            ),
            (
                at(O::LdrPreIndex, vec![p(32), p(1), imm(-256)]),
                "scalarmem[ldr.pre.gpr.w4.zx]",
                (0, Some(1), None, -256),
            ),
            (
                at(O::StrPostIndex, vec![p(34), p(3), imm(255)]),
                "scalarmem[str.post.gpr.w4]",
                (2, Some(3), None, 255),
            ),
            // register offset
            (
                at(O::LdrRO, vec![p(0), p(1), p(2)]),
                "scalarmem[ldr.ro.gpr.w8.zx]",
                (0, Some(1), Some(2), 6),
            ),
            (
                at(O::LdrRO, vec![p(32), p(1), p(34), imm(5)]),
                "scalarmem[ldr.ro.gpr.w4.zx]",
                (0, Some(1), Some(2), 5),
            ),
            (
                at(O::StrbRO, vec![p(3), sp(), p(36), imm(12)]),
                "scalarmem[str.ro.gpr.w1]",
                (3, Some(31), Some(4), 12),
            ),
            (
                at(O::LdrhRO, vec![p(35), p(1), p(2), imm(15)]),
                "scalarmem[ldr.ro.gpr.w2.zx]",
                (3, Some(1), Some(2), 15),
            ),
            (
                at(O::StrRO, vec![p(64), p(0), p(1), imm(7)]),
                "scalarmem[str.ro.fpr.w16]",
                (0, Some(0), Some(1), 7),
            ),
            // a load into the index register reads the index first: legal
            (
                at(O::LdrRO, vec![p(2), p(1), p(2), imm(7)]),
                "scalarmem[ldr.ro.gpr.w8.zx]",
                (2, Some(1), Some(2), 7),
            ),
            // WZR is a known 64-bit zero index under LSL
            (
                at(O::LdrRO, vec![p(0), p(1), p(161)]),
                "scalarmem[ldr.ro.gpr.w8.zx]",
                (0, Some(1), Some(31), 6),
            ),
        ];
        for (inst, query, fields) in cases {
            let binding = bind_scalar_memory_instruction(&inst)
                .unwrap_or_else(|why| panic!("{inst:?} must bind: {why}"));
            assert_eq!(binding.query(), query, "{inst:?}");
            assert_eq!(
                (
                    binding.rt_field,
                    binding.base_field,
                    binding.index_field,
                    binding.operand
                ),
                fields,
                "{inst:?}"
            );
        }
    }

    #[test]
    fn malformed_aliased_volatile_literal_and_unpredictable_accesses_refuse() {
        use AArch64Opcode as O;
        use trust_cg_ir::RegClass;
        use trust_cg_ir::regs::VReg;
        let sp = || MachOperand::Special(SpecialReg::SP);
        let refused: Vec<(&str, MachInst)> = vec![
            ("operand-less", at(O::LdrRI, vec![])),
            ("one operand", at(O::StrRI, vec![p(0)])),
            (
                "unresolved vreg",
                at(
                    O::LdrRI,
                    vec![
                        MachOperand::VReg(VReg::new(7, RegClass::Gpr64)),
                        p(1),
                        imm(0),
                    ],
                ),
            ),
            ("SP transfer", at(O::StrRI, vec![p(31), p(1), imm(0)])),
            ("WSP transfer", at(O::StrRI, vec![p(63), p(1), imm(0)])),
            ("W base", at(O::LdrRI, vec![p(0), p(33), imm(0)])),
            ("XZR base", at(O::LdrRI, vec![p(0), p(160), imm(0)])),
            (
                "register operand on immediate form",
                at(O::LdrRI, vec![p(0), p(1), p(2)]),
            ),
            (
                "offset beyond imm12",
                at(O::LdrRI, vec![p(0), p(1), imm(4096 * 8)]),
            ),
            (
                "offset below imm9",
                at(O::LdrRI, vec![p(0), p(1), imm(-257)]),
            ),
            (
                "unaligned beyond imm9",
                at(O::LdrRI, vec![p(0), p(1), imm(257)]),
            ),
            (
                "MemOp out of range",
                at(O::StrRI, vec![p(0), mem(29, -300)]),
            ),
            ("MemOp non-X base", at(O::StrRI, vec![p(0), mem(40, 0)])),
            (
                "byte load into FP",
                at(O::LdrbRI, vec![p(104), p(1), imm(0)]),
            ),
            (
                "B register transfer",
                at(O::LdrRI, vec![p(197), p(1), imm(0)]),
            ),
            ("load into XZR", at(O::LdrRI, vec![p(160), p(1), imm(0)])),
            (
                "ldrb into WZR",
                at(
                    O::LdrbRI,
                    vec![MachOperand::Special(SpecialReg::WZR), p(1), imm(0)],
                ),
            ),
            (
                "load overwrites base",
                at(O::LdrRI, vec![p(1), p(1), imm(8)]),
            ),
            (
                "W load overwrites base",
                at(O::LdrRI, vec![p(33), p(1), imm(8)]),
            ),
            (
                "RO load overwrites base",
                at(O::LdrRO, vec![p(1), p(1), p(2)]),
            ),
            (
                "pre writeback alias",
                at(O::StrPreIndex, vec![p(1), p(1), imm(-8)]),
            ),
            (
                "post writeback alias via W",
                at(O::LdrPostIndex, vec![p(33), p(1), imm(8)]),
            ),
            (
                "writeback below imm9",
                at(O::StrPreIndex, vec![p(0), sp(), imm(-257)]),
            ),
            (
                "writeback MemOp",
                at(O::LdrPostIndex, vec![p(0), mem(31, 8)]),
            ),
            (
                "writeback FP transfer",
                at(O::StrPreIndex, vec![p(104), sp(), imm(-16)]),
            ),
            (
                "writeback omitted offset",
                at(O::StrPostIndex, vec![p(0), sp()]),
            ),
            (
                "RO undefined mode",
                at(O::LdrRO, vec![p(0), p(1), p(2), imm(8)]),
            ),
            (
                "RO W index under LSL",
                at(O::LdrRO, vec![p(0), p(1), p(34)]),
            ),
            (
                "RO W index under SXTX",
                at(O::LdrRO, vec![p(0), p(1), p(34), imm(15)]),
            ),
            ("RO SP index", at(O::LdrRO, vec![p(0), p(1), p(31)])),
            (
                "RO narrow FP transfer",
                at(O::LdrbRO, vec![p(168), p(1), p(2)]),
            ),
            (
                "volatile load",
                at(O::VolatileLdrRI, vec![p(0), p(1), imm(0)]),
            ),
            (
                "volatile store",
                at(O::VolatileStrbRI, vec![p(32), p(1), imm(0)]),
            ),
            (
                "literal (never selected)",
                at(O::LdrLiteral, vec![p(0), imm(4)]),
            ),
            (
                "not scalar memory",
                at(O::LdpRI, vec![p(0), p(1), p(2), imm(0)]),
            ),
        ];
        for (label, inst) in refused {
            assert!(
                bind_scalar_memory_instruction(&inst).is_err(),
                "{label}: {inst:?} must refuse"
            );
        }
        // Literal operands bind exactly (for the cross-check) but are never
        // attributed at runtime.
        let literal = at(O::LdrLiteral, vec![p(0), imm(-(1 << 18))]);
        assert_eq!(
            bind_scalar_memory_operands(&literal).map(|b| (b.query(), b.operand)),
            Ok(("scalarmem[ldr.literal.gpr.w8.zx]", -(1 << 18)))
        );
        assert!(bind_scalar_memory_instruction(&literal).is_err());
        for bad in [
            at(O::LdrLiteral, vec![p(0), imm(1 << 18)]),
            at(O::LdrLiteral, vec![p(32), imm(4)]),
            at(O::LdrLiteral, vec![p(0), p(1)]),
        ] {
            assert!(bind_scalar_memory_operands(&bad).is_err(), "{bad:?}");
        }
        // Boundary controls bind.
        for (inst, query) in [
            (
                at(O::StrPreIndex, vec![p(0), sp(), imm(-256)]),
                "scalarmem[str.pre.gpr.w8]",
            ),
            (
                at(O::StrPostIndex, vec![p(0), sp(), imm(255)]),
                "scalarmem[str.post.gpr.w8]",
            ),
            (
                at(O::LdrRI, vec![p(0), p(1), imm(255)]),
                "scalarmem[ldr.unscaled.gpr.w8.zx]",
            ),
            (
                at(O::LdrRI, vec![p(0), p(1), imm(-256)]),
                "scalarmem[ldr.unscaled.gpr.w8.zx]",
            ),
            (
                at(O::LdrRI, vec![p(64), p(1), imm(4095 * 16)]),
                "scalarmem[ldr.ui.fpr.w16.zx]",
            ),
            // FP transfers never alias the GPR base, even with equal numbers.
            (
                at(O::LdrRI, vec![p(97), p(1), imm(8)]),
                "scalarmem[ldr.ui.fpr.w8.zx]",
            ),
        ] {
            assert_eq!(
                bind_scalar_memory_instruction(&inst).map(|b| b.query()),
                Ok(query),
                "{inst:?}"
            );
        }
    }

    /// A store theorem is bank-independent, so equal-width store forms are one
    /// formula under two names; a load theorem never is. Pinned because a
    /// portable certificate set must carry one file per exact query, and
    /// because an accidental collision between two LOAD forms would mean one
    /// of them is not modelling its register width or extension.
    #[test]
    fn equal_width_store_forms_alias_across_banks_and_loads_never_do() {
        let same = |left: &ScalarMemoryForm, right: &ScalarMemoryForm| {
            let (a, b) = (
                proof_scalar_memory(left).unwrap(),
                proof_scalar_memory(right).unwrap(),
            );
            a.trust_ir_expr == b.trust_ir_expr
                && a.aarch64_expr == b.aarch64_expr
                && a.inputs == b.inputs
                && a.preconditions == b.preconditions
        };
        for addressing in [UI, UNSCALED, RO] {
            for bytes in [2, 4, 8] {
                assert!(
                    same(
                        &scalar_form(STORE, addressing, GPR, bytes, ZX),
                        &scalar_form(STORE, addressing, FPR, bytes, ZX)
                    ),
                    "{addressing:?} w{bytes} stores must be one formula"
                );
                assert!(
                    !same(
                        &scalar_form(LOAD, addressing, GPR, bytes, ZX),
                        &scalar_form(LOAD, addressing, FPR, bytes, ZX)
                    ),
                    "{addressing:?} w{bytes} loads must differ by bank"
                );
            }
        }
        // Different widths, addressing modes or extensions are never aliases.
        assert!(!same(
            &scalar_form(STORE, UI, GPR, 4, ZX),
            &scalar_form(STORE, UI, GPR, 8, ZX)
        ));
        assert!(!same(
            &scalar_form(STORE, UI, GPR, 8, ZX),
            &scalar_form(STORE, UNSCALED, GPR, 8, ZX)
        ));
        assert!(!same(
            &scalar_form(LOAD, UI, GPR, 1, SX32),
            &scalar_form(LOAD, UI, GPR, 1, SX64)
        ));
    }

    /// The encoder inverts the independent decoder on every legal form's
    /// representative bindings (extreme offsets, every register-offset mode,
    /// SP and register 30), and a single-bit flip never round-trips.
    #[test]
    fn the_scalar_encoder_is_inverted_by_the_decoder() {
        let mut checked = 0;
        for (form, _) in SCALAR_MEMORY_FORMS {
            let operands: Vec<i64> = match form.addressing {
                UI => vec![
                    0,
                    i64::from(form.access_bytes),
                    0xfff * i64::from(form.access_bytes),
                ],
                UNSCALED | PRE | POST => vec![-256, -1, 0, 1, 255],
                RO => vec![4, 5, 6, 7, 12, 13, 14, 15],
                LIT => continue,
            };
            for operand in operands {
                for (rt, base, index) in [(0, 31, 30), (30, 7, 31)] {
                    let binding = ScalarMemoryBinding {
                        form,
                        rt_field: rt,
                        base_field: Some(base),
                        index_field: (form.addressing == RO).then_some(index),
                        operand,
                    };
                    let word = scalar_memory_word(&binding).expect("encodable");
                    assert_eq!(
                        decode_scalar_memory_word(word),
                        Some(binding),
                        "{word:#010x}"
                    );
                    for bit in 0..32 {
                        assert_ne!(decode_scalar_memory_word(word ^ (1 << bit)), Some(binding));
                    }
                    checked += 1;
                }
            }
        }
        assert!(checked > 300, "{checked}");
    }

    #[test]
    fn opcode_shape_table_covers_every_deferred_scalar_memory_opcode() {
        use AArch64Opcode as O;
        let mut covered = 0;
        for &opcode in crate::coverage_gate::ALL_AARCH64_OPCODES {
            let reason = crate::coverage_gate::aarch64_deferred_value_op_reason(opcode);
            let scalar_debt = reason.is_some_and(|reason| {
                reason.starts_with("emitted scalar load")
                    || reason.starts_with("emitted scalar store")
                    || reason.starts_with("emitted volatile load")
                    || reason.starts_with("emitted volatile store")
                    || reason.starts_with("emitted writeback memory form")
            });
            if scalar_debt {
                covered += 1;
                assert!(
                    is_scalar_memory_opcode(opcode),
                    "{opcode:?} is unbound scalar debt"
                );
            }
        }
        // L04-P1 credited every scalar memory row and its volatile twin.
        assert_eq!(covered, 0, "the deferred scalar memory table changed");
        assert!(is_scalar_memory_opcode(O::LdrLiteral));
        for opcode in [
            O::LdpRI,
            O::StpPreIndex,
            O::LdrswRO,
            O::LdrGot,
            O::STRXui,
            O::NeonLd1Post,
            O::AddRI,
        ] {
            assert!(!is_scalar_memory_opcode(opcode), "{opcode:?}");
        }
    }
}
