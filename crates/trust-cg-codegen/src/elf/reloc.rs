// trust-cg-codegen/elf/reloc.rs - ELF64 relocation types and encoding
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: ARM IHI 0056B, "ELF for the Arm 64-bit Architecture"
// Reference: System V AMD64 ABI, "Relocation Types"
//
// Elf64_Rela layout (24 bytes, little-endian):
//   r_offset: u64  — location at which to apply the relocation
//   r_info:   u64  — symbol index (upper 32) | relocation type (lower 32)
//   r_addend: i64  — constant addend used to compute the value

//! ELF64 relocation types and encoding for AArch64 and x86-64.
//!
//! This module defines the relocation entry structure (`Elf64Rela`) and
//! relocation type enums for both target architectures. Each relocation entry
//! is 24 bytes and uses the SHT_RELA format (with explicit addend).

use super::constants::*;
use super::header::ElfMachine;

/// The byte width of the field a relocation patches, per the target's psABI,
/// or `None` when `reloc_type` is not a relocation this machine defines.
///
/// A relocation whose type the emitter cannot recognize has NO known field
/// width, so nothing can check that it fits its section: the ELF writer
/// refuses such a record rather than guess (see
/// [`crate::elf::ElfWriter::write_checked`]). A marker relocation
/// (`R_*_NONE`, `R_RISCV_RELAX`, `R_AARCH64_TLSDESC_CALL`) patches no bytes
/// and has width 0.
pub fn elf_relocation_field_width(machine: ElfMachine, reloc_type: u32) -> Option<u64> {
    match machine {
        ElfMachine::AArch64 => AArch64RelocType::from_type_val(reloc_type).map(|kind| match kind {
            AArch64RelocType::None | AArch64RelocType::TlsdescCall => 0,
            // Every remaining AArch64 data relocation is a 64-bit word; every
            // instruction relocation patches one 4-byte instruction.
            AArch64RelocType::Abs64 => 8,
            _ => 4,
        }),
        ElfMachine::X86_64 => X86_64RelocType::from_type_val(reloc_type).map(|kind| match kind {
            X86_64RelocType::None => 0,
            X86_64RelocType::Abs8 | X86_64RelocType::Pc8 => 1,
            X86_64RelocType::Abs16 | X86_64RelocType::Pc16 => 2,
            X86_64RelocType::Abs64
            | X86_64RelocType::DtpMod64
            | X86_64RelocType::DtpOff64
            | X86_64RelocType::TpOff64
            | X86_64RelocType::Pc64
            | X86_64RelocType::IRelative => 8,
            // Everything else in the x86-64 psABI patches a 4-byte field.
            _ => 4,
        }),
        ElfMachine::Riscv64 => RiscvRelocType::from_type_val(reloc_type).map(|kind| match kind {
            RiscvRelocType::None | RiscvRelocType::Relax => 0,
            // `R_RISCV_CALL`/`R_RISCV_CALL_PLT` patch the AUIPC+JALR PAIR.
            RiscvRelocType::Abs64 | RiscvRelocType::Call | RiscvRelocType::CallPlt => 8,
            // One 4-byte instruction.
            RiscvRelocType::Jal | RiscvRelocType::PcRelHi20 | RiscvRelocType::PcRelLo12I => 4,
        }),
    }
}

/// AArch64 ELF relocation types.
///
/// These correspond to the R_AARCH64_* constants defined in the AArch64 ELF ABI.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum AArch64RelocType {
    /// No relocation.
    None = R_AARCH64_NONE,
    /// S + A — 64-bit absolute data relocation.
    Abs64 = R_AARCH64_ABS64,
    /// S + A — 32-bit absolute data relocation.
    Abs32 = R_AARCH64_ABS32,
    /// S + A - P — 32-bit signed PC-relative data word (`.eh_frame`
    /// `DW_EH_PE_pcrel|sdata4` pointers: FDE pc-begin, LSDA, personality).
    Prel32 = R_AARCH64_PREL32,
    /// Page(S + A) - Page(P) — ADRP instruction, 21-bit PC-relative page offset.
    AdrPrelPgHi21 = R_AARCH64_ADR_PREL_PG_HI21,
    /// (S + A) & 0xFFF — ADD instruction, 12-bit page offset (no check).
    AddAbsLo12Nc = R_AARCH64_ADD_ABS_LO12_NC,
    /// S + A - P — B instruction, 26-bit PC-relative branch.
    Jump26 = R_AARCH64_JUMP26,
    /// S + A - P — BL instruction, 26-bit PC-relative call.
    Call26 = R_AARCH64_CALL26,
    /// (S + A) & 0xFFF — LDR/STR 8-bit unsigned offset.
    Ldst8AbsLo12Nc = R_AARCH64_LDST8_ABS_LO12_NC,
    /// (S + A) & 0xFFF >> 1 — LDR/STR 16-bit unsigned offset.
    Ldst16AbsLo12Nc = R_AARCH64_LDST16_ABS_LO12_NC,
    /// (S + A) & 0xFFF >> 2 — LDR/STR 32-bit unsigned offset.
    Ldst32AbsLo12Nc = R_AARCH64_LDST32_ABS_LO12_NC,
    /// (S + A) & 0xFFF >> 3 — LDR/STR 64-bit unsigned offset.
    Ldst64AbsLo12Nc = R_AARCH64_LDST64_ABS_LO12_NC,
    /// (S + A) & 0xFFF >> 4 — LDR/STR 128-bit unsigned offset.
    Ldst128AbsLo12Nc = R_AARCH64_LDST128_ABS_LO12_NC,
    /// Page(G(S)) - Page(P) — ADRP to GOT entry page.
    AdrGotPage = R_AARCH64_ADR_GOT_PAGE,
    /// G(S) & 0xFFF — LD64 from GOT entry, 12-bit page offset.
    Ld64GotLo12Nc = R_AARCH64_LD64_GOT_LO12_NC,
    /// Page(G(S)) - Page(P) — ADRP to TLS IE GOT entry.
    TlsieAdrGottprelPage21 = R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21,
    /// G(S) & 0xFFF — LD64 from TLS IE GOT entry.
    TlsieLd64GottprelLo12Nc = R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC,
    /// TPREL(S + A) bits [23:12] — ADD shifted imm12 for TLS local-exec.
    TlsleAddTprelHi12 = R_AARCH64_TLSLE_ADD_TPREL_HI12,
    /// TPREL(S + A) bits [11:0] — ADD imm12 for TLS local-exec.
    TlsleAddTprelLo12 = R_AARCH64_TLSLE_ADD_TPREL_LO12,
    /// TPREL(S + A) bits [11:0] — unchecked ADD imm12 for TLS local-exec.
    TlsleAddTprelLo12Nc = R_AARCH64_TLSLE_ADD_TPREL_LO12_NC,
    /// Page(G(GTLSDESC(S + A))) - Page(P) — ADRP to the TLS descriptor page.
    TlsdescAdrPage21 = R_AARCH64_TLSDESC_ADR_PAGE21,
    /// G(GTLSDESC(S + A)) & 0xFF8 — LDR of the descriptor resolver word.
    TlsdescLd64Lo12 = R_AARCH64_TLSDESC_LD64_LO12,
    /// G(GTLSDESC(S + A)) & 0xFFF — ADD forming the descriptor address.
    TlsdescAddLo12 = R_AARCH64_TLSDESC_ADD_LO12,
    /// Marker on the descriptor call's BLR for linker relaxation (no value).
    TlsdescCall = R_AARCH64_TLSDESC_CALL,
}

/// The psABI overflow window of a checked AArch64 relocation's resolved value
/// `X`.
///
/// `X` is the kind's psABI operation: `S + A - P` for `CALL26`/`JUMP26` and
/// `PREL32`, a 4 KiB page delta for the `ADRP` kinds (`page_relative`:
/// `Page(S + A) - Page(P)`, or `Page(G(..)) - Page(P)` for a GOT slot),
/// `S + A` for `ABS32` and `TPREL(S + A)` for `TLSLE_ADD_TPREL_HI12`/`_LO12`.
/// A value outside `[min, max]` is a link-time overflow unless the static
/// linker reaches the target another way (for `CALL26`/`JUMP26` the psABI
/// lets it insert a range-extension veneer that may clobber IP0/IP1).
/// [`AArch64RelocType::relocation_limit`] names who refuses an out-of-window
/// value for each kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RelocationWindow {
    /// Smallest admitted value in bytes.
    pub min: i64,
    /// Largest admitted value in bytes.
    pub max: i64,
    /// Whether the value is a 4 KiB page delta.
    pub page_relative: bool,
}

impl RelocationWindow {
    /// Whether `value` lies inside the window.
    pub fn contains(self, value: i64) -> bool {
        (self.min..=self.max).contains(&value)
    }
}

/// Size of the AArch64 thread control block that precedes the executable's
/// TLS block (TLS variant 1): the executable's first thread-local sits at
/// least this many bytes above the thread pointer, so `TPREL(S + A)` of a
/// thread-local at offset `o` of its object's TLS section is at least
/// `16 + o + A`.
pub const AARCH64_TLS_TCB_BYTES: i64 = 16;

/// Who refuses a checked AArch64 relocation's out-of-window value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WindowDischarge {
    /// trust-cg refuses a value its own object layout fixes: a `CALL26`,
    /// `JUMP26` or direct `ADRP` to a function in the object's own text
    /// (`PipelineError::RelocationWindowExceeded`). The static linker checks
    /// every other value; for `CALL26`/`JUMP26` it may instead reach the
    /// target through a range-extension veneer.
    ObjectLayoutThenLinker,
    /// trust-cg refuses when its own object fixes a lower bound on the value
    /// above the window (`ABS32`: the DWARF section-offset addend, since the
    /// linked section symbol is never negative; `TLSLE_ADD_TPREL_HI12`: the
    /// thread control block, the thread-local's offset in this object's TLS
    /// section and the addend, [`AARCH64_TLS_TCB_BYTES`]). The static linker
    /// checks the linked value.
    ObjectLowerBoundThenLinker,
    /// Only the static linker places the target (a GOT slot), so the
    /// linker's overflow check discharges the window. GNU ld 2.42 writes an
    /// out-of-window GOT page delta truncated without a diagnostic, so
    /// trust-cg's link driver also re-reads the linked image and refuses one
    /// in which some place a GOT slot can lie is out of reach of its code
    /// (`link_driver::got_page_window_output_refusals`). For the TLS kinds
    /// the linker may instead relax the access to local exec in an
    /// executable, whose 32-bit `TPREL` GNU ld 2.42 writes truncated; the
    /// driver refuses an executable whose thread-local block reaches `2^32`
    /// above the thread pointer ([`AArch64RelocType::relocation_limit`]).
    LinkerThenLinkedImage,
    /// Only the static linker places the target (the code or data an
    /// `.eh_frame` pointer names), so the linker's overflow check
    /// discharges the window. gold 2.42 and LLD 22.1.6 apply an earlier,
    /// wider bound and write an out-of-window value without a diagnostic,
    /// so trust-cg's link driver also decodes the `.eh_frame` of every
    /// staged Linux image as an unwinder reads it (what `PT_GNU_EH_FRAME`
    /// and section names locate, and every `.eh_frame` input the link map
    /// places, whatever its output section is called) and refuses one whose
    /// pointers do not resolve into the memory they must name (the staged
    /// image check of `link_driver::run_link`).
    LinkerThenEhFrameImage,
    /// trust-cg never emits this kind; the window is recorded for the
    /// relocation reader only.
    NotEmitted,
}

/// The psABI overflow disposition of one AArch64 relocation kind: its window
/// and who discharges it, or why it has none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelocationLimit {
    /// The psABI checks the resolved value against `window`.
    Window {
        /// The checked range of the resolved value.
        window: RelocationWindow,
        /// Who refuses an out-of-window value.
        discharge: WindowDischarge,
    },
    /// No overflow check (`_NC` and the descriptor low-12 forms): the field
    /// takes low bits of an address whose page `paired_with` checks. The
    /// scaled `LDST*_ABS_LO12_NC` forms also need `S + A` aligned to their
    /// access size ([`AArch64RelocType::lo12_access_size`]), which trust-cg
    /// guarantees before it fuses an access; the GOT and descriptor loads
    /// need an 8-byte-aligned slot, which the linker lays out.
    LowBitsOfPair {
        /// The checked page relocation that carries the high part.
        paired_with: AArch64RelocType,
    },
    /// The field is as wide as the value (`ABS64`): every value fits.
    FullWidth,
    /// The relocation patches no value (`NONE`, the `TLSDESC_CALL` marker).
    NoValue,
}

impl AArch64RelocType {
    /// The overflow disposition of this relocation (IHI0056 "Relocation
    /// types": the aaelf64 source whose change history runs to 2026Q3, read
    /// 2026-09-23). The match is exhaustive on purpose: a new kind cannot be
    /// emitted without a disposition.
    ///
    /// Windows (`X` as in [`RelocationWindow`]):
    ///
    /// * `CALL26`/`JUMP26`: `-2^27 <= X < 2^27` on a word-aligned
    ///   displacement (+-128 MiB);
    /// * the `ADRP` page kinds (`ADR_PREL_PG_HI21`, `ADR_GOT_PAGE`,
    ///   `TLSIE_ADR_GOTTPREL_PAGE21`, `TLSDESC_ADR_PAGE21`):
    ///   `-2^32 <= X < 2^32` on a page delta (+-4 GiB). In an executable
    ///   whose own thread-local an initial-exec (`TLSIE_*`) or descriptor
    ///   (`TLSDESC_*`) sequence reaches, the static linker may relax it to
    ///   local exec: GNU ld 2.42 rewrites it as `movz xd, #:tprel_g1:` and
    ///   `movk xd, #:tprel_g0_nc:`, a relaxed form whose window is
    ///   `0 <= TPREL(S + A) < 2^32` (the 16-byte TCB aligned up to the
    ///   `PT_TLS` alignment plus the thread-local's offset in the block).
    ///   GNU ld does not check it and writes a larger `TPREL` truncated;
    ///   gold 2.42 and LLD 22.1.6 refuse such a link. The window is the
    ///   linker's layout, so the link driver refuses an executable image
    ///   whose `PT_TLS` reaches `2^32` above the thread pointer
    ///   (`link_driver`'s `[TCG-LINK-TLS-TPREL-UNPROVEN]`, a conservative
    ///   refusal: the image does not record which accesses were relaxed);
    /// * `ABS32`: `-2^31 <= X < 2^32`;
    /// * `PREL32`: `-2^31 <= X < 2^31`, the signed bound aaelf64 2026Q2
    ///   gave PC-relative data relocations (earlier releases allowed
    ///   `X < 2^32`). trust-cg emits it only for `.eh_frame` pointers, whose
    ///   `sdata4` readers take the value as signed. The object fixes no
    ///   bound on it; GNU ld 2.42 applies the signed bound, but gold 2.42
    ///   and LLD 22.1.6 apply the earlier one, so the link driver decodes
    ///   the linked image's `.eh_frame` (wherever the link map places its
    ///   input) and refuses a pointer that does not resolve where an
    ///   unwinder must find it;
    /// * `TLSLE_ADD_TPREL_HI12`: `0 <= X < 2^24`; `TLSLE_ADD_TPREL_LO12`:
    ///   `0 <= X < 2^12` (never emitted).
    pub fn relocation_limit(self) -> RelocationLimit {
        const BRANCH26: RelocationWindow = RelocationWindow {
            min: -(1 << 27),
            max: (1 << 27) - 4,
            page_relative: false,
        };
        const PAGE21: RelocationWindow = RelocationWindow {
            min: -(1 << 32),
            max: (1 << 32) - 4096,
            page_relative: true,
        };
        let window = |window, discharge| RelocationLimit::Window { window, discharge };
        let low_bits = |paired_with| RelocationLimit::LowBitsOfPair { paired_with };
        match self {
            Self::None | Self::TlsdescCall => RelocationLimit::NoValue,
            Self::Abs64 => RelocationLimit::FullWidth,
            Self::Abs32 => window(
                RelocationWindow {
                    min: -(1 << 31),
                    max: (1 << 32) - 1,
                    page_relative: false,
                },
                WindowDischarge::ObjectLowerBoundThenLinker,
            ),
            Self::Prel32 => window(
                RelocationWindow {
                    min: -(1 << 31),
                    max: (1 << 31) - 1,
                    page_relative: false,
                },
                WindowDischarge::LinkerThenEhFrameImage,
            ),
            Self::Call26 | Self::Jump26 => {
                window(BRANCH26, WindowDischarge::ObjectLayoutThenLinker)
            }
            Self::AdrPrelPgHi21 => window(PAGE21, WindowDischarge::ObjectLayoutThenLinker),
            Self::AdrGotPage | Self::TlsieAdrGottprelPage21 | Self::TlsdescAdrPage21 => {
                window(PAGE21, WindowDischarge::LinkerThenLinkedImage)
            }
            Self::AddAbsLo12Nc
            | Self::Ldst8AbsLo12Nc
            | Self::Ldst16AbsLo12Nc
            | Self::Ldst32AbsLo12Nc
            | Self::Ldst64AbsLo12Nc
            | Self::Ldst128AbsLo12Nc => low_bits(Self::AdrPrelPgHi21),
            Self::Ld64GotLo12Nc => low_bits(Self::AdrGotPage),
            Self::TlsieLd64GottprelLo12Nc => low_bits(Self::TlsieAdrGottprelPage21),
            Self::TlsdescLd64Lo12 | Self::TlsdescAddLo12 => low_bits(Self::TlsdescAdrPage21),
            Self::TlsleAddTprelHi12 => window(
                RelocationWindow {
                    min: 0,
                    max: (1 << 24) - 1,
                    page_relative: false,
                },
                WindowDischarge::ObjectLowerBoundThenLinker,
            ),
            Self::TlsleAddTprelLo12 => window(
                RelocationWindow {
                    min: 0,
                    max: (1 << 12) - 1,
                    page_relative: false,
                },
                WindowDischarge::NotEmitted,
            ),
            Self::TlsleAddTprelLo12Nc => low_bits(Self::TlsleAddTprelHi12),
        }
    }

    /// The overflow window the psABI checks for this relocation, or `None`
    /// when it defines none (the unchecked low-12 forms, `ABS64` and the
    /// markers); [`Self::relocation_limit`] gives every kind's disposition.
    pub fn displacement_window(self) -> Option<RelocationWindow> {
        match self.relocation_limit() {
            RelocationLimit::Window { window, .. } => Some(window),
            RelocationLimit::LowBitsOfPair { .. }
            | RelocationLimit::FullWidth
            | RelocationLimit::NoValue => None,
        }
    }

    /// The psABI name of this relocation (`R_AARCH64_*`).
    pub fn psabi_name(self) -> &'static str {
        match self {
            Self::None => "R_AARCH64_NONE",
            Self::Abs64 => "R_AARCH64_ABS64",
            Self::Abs32 => "R_AARCH64_ABS32",
            Self::Prel32 => "R_AARCH64_PREL32",
            Self::AdrPrelPgHi21 => "R_AARCH64_ADR_PREL_PG_HI21",
            Self::AddAbsLo12Nc => "R_AARCH64_ADD_ABS_LO12_NC",
            Self::Jump26 => "R_AARCH64_JUMP26",
            Self::Call26 => "R_AARCH64_CALL26",
            Self::Ldst8AbsLo12Nc => "R_AARCH64_LDST8_ABS_LO12_NC",
            Self::Ldst16AbsLo12Nc => "R_AARCH64_LDST16_ABS_LO12_NC",
            Self::Ldst32AbsLo12Nc => "R_AARCH64_LDST32_ABS_LO12_NC",
            Self::Ldst64AbsLo12Nc => "R_AARCH64_LDST64_ABS_LO12_NC",
            Self::Ldst128AbsLo12Nc => "R_AARCH64_LDST128_ABS_LO12_NC",
            Self::AdrGotPage => "R_AARCH64_ADR_GOT_PAGE",
            Self::Ld64GotLo12Nc => "R_AARCH64_LD64_GOT_LO12_NC",
            Self::TlsieAdrGottprelPage21 => "R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21",
            Self::TlsieLd64GottprelLo12Nc => "R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC",
            Self::TlsleAddTprelHi12 => "R_AARCH64_TLSLE_ADD_TPREL_HI12",
            Self::TlsleAddTprelLo12 => "R_AARCH64_TLSLE_ADD_TPREL_LO12",
            Self::TlsleAddTprelLo12Nc => "R_AARCH64_TLSLE_ADD_TPREL_LO12_NC",
            Self::TlsdescAdrPage21 => "R_AARCH64_TLSDESC_ADR_PAGE21",
            Self::TlsdescLd64Lo12 => "R_AARCH64_TLSDESC_LD64_LO12",
            Self::TlsdescAddLo12 => "R_AARCH64_TLSDESC_ADD_LO12",
            Self::TlsdescCall => "R_AARCH64_TLSDESC_CALL",
        }
    }

    /// The access size in bytes a `LDST*_ABS_LO12_NC` relocation scales its
    /// low-12-bit field by. The linker writes `((S + A) & 0xFFF) >> log2(size)`
    /// into the scaled unsigned-offset field, so `S + A` must be a multiple of
    /// the size or the low bits are lost (lld refuses such a site; the value
    /// lemma in `trust_cg_verify::aarch64_elf_reloc_proofs` carries the
    /// alignment as a precondition).
    pub fn lo12_access_size(self) -> Option<u32> {
        match self {
            Self::Ldst8AbsLo12Nc => Some(1),
            Self::Ldst16AbsLo12Nc => Some(2),
            Self::Ldst32AbsLo12Nc => Some(4),
            Self::Ldst64AbsLo12Nc => Some(8),
            Self::Ldst128AbsLo12Nc => Some(16),
            _ => None,
        }
    }

    /// Return the numeric relocation type value.
    pub fn to_type_val(self) -> u32 {
        self as u32
    }

    /// Decode a numeric value to an AArch64 relocation type.
    pub fn from_type_val(val: u32) -> Option<Self> {
        match val {
            R_AARCH64_NONE => Some(Self::None),
            R_AARCH64_ABS64 => Some(Self::Abs64),
            R_AARCH64_ABS32 => Some(Self::Abs32),
            R_AARCH64_PREL32 => Some(Self::Prel32),
            R_AARCH64_ADR_PREL_PG_HI21 => Some(Self::AdrPrelPgHi21),
            R_AARCH64_ADD_ABS_LO12_NC => Some(Self::AddAbsLo12Nc),
            R_AARCH64_JUMP26 => Some(Self::Jump26),
            R_AARCH64_CALL26 => Some(Self::Call26),
            R_AARCH64_LDST8_ABS_LO12_NC => Some(Self::Ldst8AbsLo12Nc),
            R_AARCH64_LDST16_ABS_LO12_NC => Some(Self::Ldst16AbsLo12Nc),
            R_AARCH64_LDST32_ABS_LO12_NC => Some(Self::Ldst32AbsLo12Nc),
            R_AARCH64_LDST64_ABS_LO12_NC => Some(Self::Ldst64AbsLo12Nc),
            R_AARCH64_LDST128_ABS_LO12_NC => Some(Self::Ldst128AbsLo12Nc),
            R_AARCH64_ADR_GOT_PAGE => Some(Self::AdrGotPage),
            R_AARCH64_LD64_GOT_LO12_NC => Some(Self::Ld64GotLo12Nc),
            R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21 => Some(Self::TlsieAdrGottprelPage21),
            R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC => Some(Self::TlsieLd64GottprelLo12Nc),
            R_AARCH64_TLSLE_ADD_TPREL_HI12 => Some(Self::TlsleAddTprelHi12),
            R_AARCH64_TLSLE_ADD_TPREL_LO12 => Some(Self::TlsleAddTprelLo12),
            R_AARCH64_TLSLE_ADD_TPREL_LO12_NC => Some(Self::TlsleAddTprelLo12Nc),
            R_AARCH64_TLSDESC_ADR_PAGE21 => Some(Self::TlsdescAdrPage21),
            R_AARCH64_TLSDESC_LD64_LO12 => Some(Self::TlsdescLd64Lo12),
            R_AARCH64_TLSDESC_ADD_LO12 => Some(Self::TlsdescAddLo12),
            R_AARCH64_TLSDESC_CALL => Some(Self::TlsdescCall),
            _ => None,
        }
    }
}

/// x86-64 ELF relocation types.
///
/// These correspond to the R_X86_64_* constants defined in the AMD64 ABI.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum X86_64RelocType {
    /// No relocation.
    None = R_X86_64_NONE,
    /// S + A — 64-bit absolute address.
    Abs64 = R_X86_64_64,
    /// S + A - P — 32-bit PC-relative.
    Pc32 = R_X86_64_PC32,
    /// G + A — 32-bit GOT offset.
    Got32 = R_X86_64_GOT32,
    /// L + A - P — 32-bit PLT-relative.
    Plt32 = R_X86_64_PLT32,
    /// G + GOT + A - P — 32-bit GOT-relative PC offset.
    GotPcRel = R_X86_64_GOTPCREL,
    /// (zero-extended) S + A — 32-bit unsigned absolute.
    Abs32 = R_X86_64_32,
    /// (sign-extended) S + A — 32-bit signed absolute.
    Abs32S = R_X86_64_32S,
    /// S + A — 16-bit absolute.
    Abs16 = R_X86_64_16,
    /// S + A - P — 16-bit PC-relative.
    Pc16 = R_X86_64_PC16,
    /// S + A — 8-bit absolute.
    Abs8 = R_X86_64_8,
    /// S + A - P — 8-bit PC-relative.
    Pc8 = R_X86_64_PC8,
    /// ID of the module containing the TLS symbol (GD/LD models).
    DtpMod64 = R_X86_64_DTPMOD64,
    /// 64-bit offset of the TLS symbol within its module's TLS block.
    DtpOff64 = R_X86_64_DTPOFF64,
    /// 64-bit offset of the TLS symbol relative to the thread pointer.
    TpOff64 = R_X86_64_TPOFF64,
    /// PC-relative offset to the GD GOT entry pair (general dynamic TLS model).
    TlsGd = R_X86_64_TLSGD,
    /// PC-relative offset to the LD GOT entry (local dynamic TLS model).
    TlsLd = R_X86_64_TLSLD,
    /// 32-bit offset of the TLS symbol within its module's TLS block.
    DtpOff32 = R_X86_64_DTPOFF32,
    /// PC-relative offset to the IE GOT entry holding the TP offset (initial exec).
    GotTpOff = R_X86_64_GOTTPOFF,
    /// 32-bit offset of the TLS symbol relative to the thread pointer (local exec).
    TpOff32 = R_X86_64_TPOFF32,
    /// S + A - P — 64-bit PC-relative.
    Pc64 = R_X86_64_PC64,
    /// Indirect (ifunc) relocation resolved at load time.
    IRelative = R_X86_64_IRELATIVE,
    /// Relaxable GOT-relative PC offset.
    GotPcRelX = R_X86_64_GOTPCRELX,
    /// Relaxable GOT-relative PC offset with REX prefix.
    RexGotPcRelX = R_X86_64_REX_GOTPCRELX,
}

impl X86_64RelocType {
    /// Return the numeric relocation type value.
    pub fn to_type_val(self) -> u32 {
        self as u32
    }

    /// Decode a numeric value to an x86-64 relocation type.
    pub fn from_type_val(val: u32) -> Option<Self> {
        match val {
            R_X86_64_NONE => Some(Self::None),
            R_X86_64_64 => Some(Self::Abs64),
            R_X86_64_PC32 => Some(Self::Pc32),
            R_X86_64_GOT32 => Some(Self::Got32),
            R_X86_64_PLT32 => Some(Self::Plt32),
            R_X86_64_GOTPCREL => Some(Self::GotPcRel),
            R_X86_64_32 => Some(Self::Abs32),
            R_X86_64_32S => Some(Self::Abs32S),
            R_X86_64_16 => Some(Self::Abs16),
            R_X86_64_PC16 => Some(Self::Pc16),
            R_X86_64_8 => Some(Self::Abs8),
            R_X86_64_PC8 => Some(Self::Pc8),
            R_X86_64_DTPMOD64 => Some(Self::DtpMod64),
            R_X86_64_DTPOFF64 => Some(Self::DtpOff64),
            R_X86_64_TPOFF64 => Some(Self::TpOff64),
            R_X86_64_TLSGD => Some(Self::TlsGd),
            R_X86_64_TLSLD => Some(Self::TlsLd),
            R_X86_64_DTPOFF32 => Some(Self::DtpOff32),
            R_X86_64_GOTTPOFF => Some(Self::GotTpOff),
            R_X86_64_TPOFF32 => Some(Self::TpOff32),
            R_X86_64_PC64 => Some(Self::Pc64),
            R_X86_64_IRELATIVE => Some(Self::IRelative),
            R_X86_64_GOTPCRELX => Some(Self::GotPcRelX),
            R_X86_64_REX_GOTPCRELX => Some(Self::RexGotPcRelX),
            _ => None,
        }
    }
}

/// RISC-V ELF relocation types.
///
/// These correspond to the R_RISCV_* constants defined in the RISC-V ELF psABI.
/// Only the subset needed for cross-function direct calls and absolute data
/// references is modeled; unknown types are passed through `Elf64Rela::new`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum RiscvRelocType {
    /// No relocation.
    None = R_RISCV_NONE,
    /// S + A — 64-bit absolute data relocation.
    Abs64 = R_RISCV_64,
    /// S + A - P — 21-bit PC-relative `JAL`.
    Jal = R_RISCV_JAL,
    /// S + A - P — AUIPC+JALR call (older non-PLT form).
    Call = R_RISCV_CALL,
    /// S + A - P — AUIPC+JALR call via PLT (modern direct-call form).
    CallPlt = R_RISCV_CALL_PLT,
    /// High 20 bits of a PC-relative reference (AUIPC of a pcrel pair).
    PcRelHi20 = R_RISCV_PCREL_HI20,
    /// Low 12 bits of a PC-relative reference (I-type half of a pcrel pair).
    PcRelLo12I = R_RISCV_PCREL_LO12_I,
    /// Marks an instruction sequence as relaxable by the linker.
    Relax = R_RISCV_RELAX,
}

impl RiscvRelocType {
    /// Return the numeric relocation type value.
    pub fn to_type_val(self) -> u32 {
        self as u32
    }

    /// Decode a numeric value to a RISC-V relocation type.
    pub fn from_type_val(val: u32) -> Option<Self> {
        match val {
            R_RISCV_NONE => Some(Self::None),
            R_RISCV_64 => Some(Self::Abs64),
            R_RISCV_JAL => Some(Self::Jal),
            R_RISCV_CALL => Some(Self::Call),
            R_RISCV_CALL_PLT => Some(Self::CallPlt),
            R_RISCV_PCREL_HI20 => Some(Self::PcRelHi20),
            R_RISCV_PCREL_LO12_I => Some(Self::PcRelLo12I),
            R_RISCV_RELAX => Some(Self::Relax),
            _ => None,
        }
    }
}

/// An ELF64 relocation entry with addend (Elf64_Rela).
///
/// Layout (24 bytes, little-endian):
/// ```text
/// Offset  Size  Field
/// 0        8    r_offset  — location within the section to apply the relocation
/// 8        8    r_info    — symbol table index (upper 32 bits) | type (lower 32 bits)
/// 16       8    r_addend  — constant addend for computing the relocation value
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Elf64Rela {
    /// Byte offset within the section where the relocation applies.
    pub r_offset: u64,
    /// Symbol table index of the referenced symbol.
    pub symbol_index: u32,
    /// Relocation type (architecture-specific).
    pub reloc_type: u32,
    /// Constant addend.
    pub r_addend: i64,
}

impl Elf64Rela {
    /// Create a new relocation entry.
    pub fn new(offset: u64, symbol_index: u32, reloc_type: u32, addend: i64) -> Self {
        Self {
            r_offset: offset,
            symbol_index,
            reloc_type,
            r_addend: addend,
        }
    }

    /// Create an AArch64 relocation entry.
    pub fn aarch64(offset: u64, symbol_index: u32, kind: AArch64RelocType, addend: i64) -> Self {
        Self::new(offset, symbol_index, kind.to_type_val(), addend)
    }

    /// Create an x86-64 relocation entry.
    pub fn x86_64(offset: u64, symbol_index: u32, kind: X86_64RelocType, addend: i64) -> Self {
        Self::new(offset, symbol_index, kind.to_type_val(), addend)
    }

    /// Create a RISC-V relocation entry.
    pub fn riscv(offset: u64, symbol_index: u32, kind: RiscvRelocType, addend: i64) -> Self {
        Self::new(offset, symbol_index, kind.to_type_val(), addend)
    }

    /// Compute the packed r_info field.
    pub fn r_info(&self) -> u64 {
        elf64_r_info(self.symbol_index, self.reloc_type)
    }

    /// Encode to 24-byte little-endian representation.
    pub fn encode(&self) -> [u8; ELF64_RELA_SIZE] {
        let mut buf = [0u8; ELF64_RELA_SIZE];
        buf[0..8].copy_from_slice(&self.r_offset.to_le_bytes());
        buf[8..16].copy_from_slice(&self.r_info().to_le_bytes());
        buf[16..24].copy_from_slice(&self.r_addend.to_le_bytes());
        buf
    }

    /// Decode from 24-byte little-endian representation.
    pub fn decode(bytes: &[u8; ELF64_RELA_SIZE]) -> Self {
        let r_offset = u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]);
        let r_info = u64::from_le_bytes([
            bytes[8], bytes[9], bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15],
        ]);
        let r_addend = i64::from_le_bytes([
            bytes[16], bytes[17], bytes[18], bytes[19], bytes[20], bytes[21], bytes[22], bytes[23],
        ]);

        Self {
            r_offset,
            symbol_index: elf64_r_sym(r_info),
            reloc_type: elf64_r_type(r_info),
            r_addend,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn displacement_windows_match_the_psabi_field_widths() {
        let call = AArch64RelocType::Call26.displacement_window().unwrap();
        // imm26 holds a signed word offset: 2^25 words either way.
        assert!(call.contains(-(128 << 20)) && call.contains((128 << 20) - 4));
        assert!(!call.contains(128 << 20) && !call.contains(-(128 << 20) - 4));
        assert_eq!(AArch64RelocType::Jump26.displacement_window(), Some(call));
        for kind in [
            AArch64RelocType::AdrPrelPgHi21,
            AArch64RelocType::AdrGotPage,
            AArch64RelocType::TlsieAdrGottprelPage21,
        ] {
            let page = kind.displacement_window().unwrap();
            // immhi:immlo holds a signed 21-bit page count: 2^20 pages each way.
            assert!(page.page_relative);
            assert!(page.contains(-(4_i64 << 30)) && page.contains((4_i64 << 30) - 4096));
            assert!(!page.contains(4_i64 << 30));
        }
        for unchecked in [
            AArch64RelocType::AddAbsLo12Nc,
            AArch64RelocType::Ld64GotLo12Nc,
            AArch64RelocType::Ldst64AbsLo12Nc,
            AArch64RelocType::Abs64,
        ] {
            assert_eq!(unchecked.displacement_window(), None, "{unchecked:?}");
        }
    }

    /// Every relocation kind the AArch64 ELF writer can serialize has a
    /// pinned disposition. The enumeration is derived from the writer's own
    /// type list: `write_checked` refuses any record whose type
    /// `from_type_val` does not decode (`elf_relocation_field_width` has no
    /// width for it), so the decodable codes are exactly the kinds that can
    /// reach an object, and a newly decodable kind fails this test until it
    /// is pinned here. Codes and windows are literals from aaelf64 2026Q3
    /// (`PREL32` has the signed bound 2026Q2 introduced).
    #[test]
    fn every_serializable_aarch64_relocation_kind_has_a_pinned_limit() {
        use RelocationLimit as L;
        use WindowDischarge as D;
        let w = |min: i64, max: i64, page_relative: bool, discharge| L::Window {
            window: RelocationWindow {
                min,
                max,
                page_relative,
            },
            discharge,
        };
        let pair = |paired_with| L::LowBitsOfPair { paired_with };
        let page = |discharge| w(-(1 << 32), (1 << 32) - 4096, true, discharge);
        let pinned: [(u32, &str, RelocationLimit); 24] = [
            (0, "R_AARCH64_NONE", L::NoValue),
            (257, "R_AARCH64_ABS64", L::FullWidth),
            (
                258,
                "R_AARCH64_ABS32",
                w(
                    -(1 << 31),
                    (1 << 32) - 1,
                    false,
                    D::ObjectLowerBoundThenLinker,
                ),
            ),
            (
                261,
                "R_AARCH64_PREL32",
                w(-(1 << 31), (1 << 31) - 1, false, D::LinkerThenEhFrameImage),
            ),
            (
                275,
                "R_AARCH64_ADR_PREL_PG_HI21",
                page(D::ObjectLayoutThenLinker),
            ),
            (
                277,
                "R_AARCH64_ADD_ABS_LO12_NC",
                pair(AArch64RelocType::AdrPrelPgHi21),
            ),
            (
                278,
                "R_AARCH64_LDST8_ABS_LO12_NC",
                pair(AArch64RelocType::AdrPrelPgHi21),
            ),
            (
                282,
                "R_AARCH64_JUMP26",
                w(-(1 << 27), (1 << 27) - 4, false, D::ObjectLayoutThenLinker),
            ),
            (
                283,
                "R_AARCH64_CALL26",
                w(-(1 << 27), (1 << 27) - 4, false, D::ObjectLayoutThenLinker),
            ),
            (
                284,
                "R_AARCH64_LDST16_ABS_LO12_NC",
                pair(AArch64RelocType::AdrPrelPgHi21),
            ),
            (
                285,
                "R_AARCH64_LDST32_ABS_LO12_NC",
                pair(AArch64RelocType::AdrPrelPgHi21),
            ),
            (
                286,
                "R_AARCH64_LDST64_ABS_LO12_NC",
                pair(AArch64RelocType::AdrPrelPgHi21),
            ),
            (
                299,
                "R_AARCH64_LDST128_ABS_LO12_NC",
                pair(AArch64RelocType::AdrPrelPgHi21),
            ),
            (
                311,
                "R_AARCH64_ADR_GOT_PAGE",
                page(D::LinkerThenLinkedImage),
            ),
            (
                312,
                "R_AARCH64_LD64_GOT_LO12_NC",
                pair(AArch64RelocType::AdrGotPage),
            ),
            (
                541,
                "R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21",
                page(D::LinkerThenLinkedImage),
            ),
            (
                542,
                "R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC",
                pair(AArch64RelocType::TlsieAdrGottprelPage21),
            ),
            (
                549,
                "R_AARCH64_TLSLE_ADD_TPREL_HI12",
                w(0, (1 << 24) - 1, false, D::ObjectLowerBoundThenLinker),
            ),
            (
                550,
                "R_AARCH64_TLSLE_ADD_TPREL_LO12",
                w(0, (1 << 12) - 1, false, D::NotEmitted),
            ),
            (
                551,
                "R_AARCH64_TLSLE_ADD_TPREL_LO12_NC",
                pair(AArch64RelocType::TlsleAddTprelHi12),
            ),
            (
                562,
                "R_AARCH64_TLSDESC_ADR_PAGE21",
                page(D::LinkerThenLinkedImage),
            ),
            (
                563,
                "R_AARCH64_TLSDESC_LD64_LO12",
                pair(AArch64RelocType::TlsdescAdrPage21),
            ),
            (
                564,
                "R_AARCH64_TLSDESC_ADD_LO12",
                pair(AArch64RelocType::TlsdescAdrPage21),
            ),
            (569, "R_AARCH64_TLSDESC_CALL", L::NoValue),
        ];

        // The writer's type list: every code it decodes (and so accepts).
        let decodable: Vec<(u32, AArch64RelocType)> = (0..=u32::from(u16::MAX))
            .filter_map(|code| AArch64RelocType::from_type_val(code).map(|kind| (code, kind)))
            .collect();
        assert_eq!(
            decodable.iter().map(|(code, _)| *code).collect::<Vec<_>>(),
            pinned.iter().map(|(code, _, _)| *code).collect::<Vec<_>>(),
            "every decodable AArch64 relocation code must be pinned, and only those"
        );
        for ((code, kind), (_, name, limit)) in decodable.iter().zip(&pinned) {
            assert_eq!(kind.to_type_val(), *code, "{kind:?}");
            assert_eq!(kind.psabi_name(), *name, "{code}");
            assert_eq!(kind.relocation_limit(), *limit, "{name}");
            assert!(
                elf_relocation_field_width(ElfMachine::AArch64, *code).is_some(),
                "{name}: the checked writer accepts it"
            );
            match *limit {
                L::Window { window, discharge } => {
                    assert_eq!(kind.displacement_window(), Some(window), "{name}");
                    // Both edges are admitted and the values just outside
                    // are not (a page or branch window is also a multiple of
                    // its granule, so `max` is the last reachable value).
                    assert!(window.contains(window.min) && window.contains(window.max));
                    assert!(!window.contains(window.min - 1), "{name}");
                    assert!(!window.contains(window.max + 1), "{name}");
                    assert_eq!(
                        discharge == D::NotEmitted,
                        *kind == AArch64RelocType::TlsleAddTprelLo12,
                        "{name}: only the checked TPREL_LO12 is never emitted"
                    );
                }
                L::LowBitsOfPair { paired_with } => {
                    assert_eq!(kind.displacement_window(), None, "{name}");
                    // The high part of every unchecked low-12 form is range
                    // checked by an emitted page (or HI12) relocation.
                    assert!(
                        matches!(
                            paired_with.relocation_limit(),
                            L::Window { discharge, .. } if discharge != D::NotEmitted
                        ),
                        "{name} pairs with the checked {paired_with:?}"
                    );
                }
                L::FullWidth | L::NoValue => {
                    assert_eq!(kind.displacement_window(), None, "{name}");
                }
            }
        }
        // The three kinds this closure item named: modeled, not `None`.
        for kind in [
            AArch64RelocType::TlsdescAdrPage21,
            AArch64RelocType::Abs32,
            AArch64RelocType::TlsleAddTprelHi12,
        ] {
            assert!(kind.displacement_window().is_some(), "{kind:?}");
        }
    }

    #[test]
    fn lo12_access_sizes_follow_the_ldst_scale() {
        let sizes: Vec<_> = [
            AArch64RelocType::Ldst8AbsLo12Nc,
            AArch64RelocType::Ldst16AbsLo12Nc,
            AArch64RelocType::Ldst32AbsLo12Nc,
            AArch64RelocType::Ldst64AbsLo12Nc,
            AArch64RelocType::Ldst128AbsLo12Nc,
        ]
        .into_iter()
        .map(|kind| kind.lo12_access_size())
        .collect();
        assert_eq!(sizes, [Some(1), Some(2), Some(4), Some(8), Some(16)]);
        assert_eq!(AArch64RelocType::AddAbsLo12Nc.lo12_access_size(), None);
    }

    #[test]
    fn test_rela_encode_decode_roundtrip() {
        let rela = Elf64Rela::aarch64(0x100, 5, AArch64RelocType::Call26, 0);
        let encoded = rela.encode();
        assert_eq!(encoded.len(), 24);
        let decoded = Elf64Rela::decode(&encoded);
        assert_eq!(rela, decoded);
    }

    #[test]
    fn test_rela_with_addend() {
        let rela = Elf64Rela::aarch64(0x10, 2, AArch64RelocType::AdrPrelPgHi21, 0x1000);
        let encoded = rela.encode();
        let decoded = Elf64Rela::decode(&encoded);
        assert_eq!(decoded.r_addend, 0x1000);
        assert_eq!(decoded.symbol_index, 2);
        assert_eq!(decoded.reloc_type, R_AARCH64_ADR_PREL_PG_HI21);
    }

    #[test]
    fn test_rela_negative_addend() {
        let rela = Elf64Rela::x86_64(0x20, 1, X86_64RelocType::Pc32, -4);
        let encoded = rela.encode();
        let decoded = Elf64Rela::decode(&encoded);
        assert_eq!(decoded.r_addend, -4);
    }

    #[test]
    fn test_r_info_encoding() {
        let rela = Elf64Rela::new(0, 10, R_AARCH64_CALL26, 0);
        let info = rela.r_info();
        assert_eq!(elf64_r_sym(info), 10);
        assert_eq!(elf64_r_type(info), R_AARCH64_CALL26);
    }

    #[test]
    fn test_aarch64_reloc_types() {
        let types = [
            (AArch64RelocType::None, R_AARCH64_NONE),
            (AArch64RelocType::Abs64, R_AARCH64_ABS64),
            (AArch64RelocType::AdrPrelPgHi21, R_AARCH64_ADR_PREL_PG_HI21),
            (AArch64RelocType::AddAbsLo12Nc, R_AARCH64_ADD_ABS_LO12_NC),
            (AArch64RelocType::Jump26, R_AARCH64_JUMP26),
            (AArch64RelocType::Call26, R_AARCH64_CALL26),
            (
                AArch64RelocType::Ldst64AbsLo12Nc,
                R_AARCH64_LDST64_ABS_LO12_NC,
            ),
            (AArch64RelocType::AdrGotPage, R_AARCH64_ADR_GOT_PAGE),
            (AArch64RelocType::Ld64GotLo12Nc, R_AARCH64_LD64_GOT_LO12_NC),
            (
                AArch64RelocType::TlsieAdrGottprelPage21,
                R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21,
            ),
            (
                AArch64RelocType::TlsieLd64GottprelLo12Nc,
                R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC,
            ),
            (
                AArch64RelocType::TlsleAddTprelHi12,
                R_AARCH64_TLSLE_ADD_TPREL_HI12,
            ),
            (
                AArch64RelocType::TlsleAddTprelLo12,
                R_AARCH64_TLSLE_ADD_TPREL_LO12,
            ),
            (
                AArch64RelocType::TlsleAddTprelLo12Nc,
                R_AARCH64_TLSLE_ADD_TPREL_LO12_NC,
            ),
        ];

        for (kind, expected_val) in &types {
            assert_eq!(kind.to_type_val(), *expected_val);
            assert_eq!(AArch64RelocType::from_type_val(*expected_val), Some(*kind));
        }

        // TLSDESC codes pinned as literals from the AArch64 ELF ABI
        // (IHI 0056, "Relocations for thread-local storage"), independent of
        // the named constants above.
        for (kind, code) in [
            (AArch64RelocType::TlsdescAdrPage21, 0x232),
            (AArch64RelocType::TlsdescLd64Lo12, 0x233),
            (AArch64RelocType::TlsdescAddLo12, 0x234),
            (AArch64RelocType::TlsdescCall, 0x239),
        ] {
            assert_eq!(kind.to_type_val(), code, "{kind:?}");
            assert_eq!(AArch64RelocType::from_type_val(code), Some(kind));
            let rela = Elf64Rela::aarch64(0x20, 7, kind, 0);
            assert_eq!(Elf64Rela::decode(&rela.encode()), rela);
        }
        // Codes around them that the emitter never produces stay unknown.
        for code in [0x231, 0x235, 0x236, 0x237, 0x238, 0x23a] {
            assert_eq!(AArch64RelocType::from_type_val(code), None, "{code:#x}");
        }
    }

    #[test]
    fn test_x86_64_reloc_types() {
        let types = [
            (X86_64RelocType::None, R_X86_64_NONE),
            (X86_64RelocType::Abs64, R_X86_64_64),
            (X86_64RelocType::Pc32, R_X86_64_PC32),
            (X86_64RelocType::Got32, R_X86_64_GOT32),
            (X86_64RelocType::Plt32, R_X86_64_PLT32),
            (X86_64RelocType::GotPcRel, R_X86_64_GOTPCREL),
            (X86_64RelocType::Abs32, R_X86_64_32),
            (X86_64RelocType::Abs32S, R_X86_64_32S),
            (X86_64RelocType::GotPcRelX, R_X86_64_GOTPCRELX),
            (X86_64RelocType::RexGotPcRelX, R_X86_64_REX_GOTPCRELX),
        ];

        for (kind, expected_val) in &types {
            assert_eq!(kind.to_type_val(), *expected_val);
            assert_eq!(X86_64RelocType::from_type_val(*expected_val), Some(*kind));
        }
    }

    /// Assert the numeric codes for the x86-64 TLS and modern relocations match
    /// the published System V AMD64 ABI values, and that an Elf64_Rela built for
    /// each one round-trips through encode/decode with the correct packed
    /// `r_info = (sym << 32) | type` layout.
    #[test]
    fn test_x86_64_tls_and_modern_reloc_types() {
        // (kind, ABI numeric code) — verified against the x86-64 psABI.
        let types: [(X86_64RelocType, u32); 12] = [
            (X86_64RelocType::DtpMod64, 16),
            (X86_64RelocType::DtpOff64, 17),
            (X86_64RelocType::TpOff64, 18),
            (X86_64RelocType::TlsGd, 19),
            (X86_64RelocType::TlsLd, 20),
            (X86_64RelocType::DtpOff32, 21),
            (X86_64RelocType::GotTpOff, 22),
            (X86_64RelocType::TpOff32, 23),
            (X86_64RelocType::Pc64, 24),
            (X86_64RelocType::IRelative, 37),
            (X86_64RelocType::GotPcRelX, 41),
            (X86_64RelocType::RexGotPcRelX, 42),
        ];

        // Cross-check against the named constants too.
        assert_eq!(R_X86_64_DTPMOD64, 16);
        assert_eq!(R_X86_64_DTPOFF64, 17);
        assert_eq!(R_X86_64_TPOFF64, 18);
        assert_eq!(R_X86_64_TLSGD, 19);
        assert_eq!(R_X86_64_TLSLD, 20);
        assert_eq!(R_X86_64_DTPOFF32, 21);
        assert_eq!(R_X86_64_GOTTPOFF, 22);
        assert_eq!(R_X86_64_TPOFF32, 23);
        assert_eq!(R_X86_64_PC64, 24);
        assert_eq!(R_X86_64_IRELATIVE, 37);
        assert_eq!(R_X86_64_GOTPCRELX, 41);
        assert_eq!(R_X86_64_REX_GOTPCRELX, 42);

        for (kind, expected_val) in &types {
            // 1. Numeric code matches the ABI value exactly.
            assert_eq!(kind.to_type_val(), *expected_val, "code for {kind:?}");
            assert_eq!(X86_64RelocType::from_type_val(*expected_val), Some(*kind));

            // 2. The ELF writer emits a correct Elf64_Rela entry for it:
            //    r_offset preserved, r_info = (sym << 32) | type, addend preserved.
            let sym = 0x1234u32;
            let rela = Elf64Rela::x86_64(0x40, sym, *kind, 0);
            let info = rela.r_info();
            assert_eq!(elf64_r_sym(info), sym, "r_info sym for {kind:?}");
            assert_eq!(
                elf64_r_type(info),
                *expected_val,
                "r_info type for {kind:?}"
            );
            assert_eq!(info, ((sym as u64) << 32) | (*expected_val as u64));

            let encoded = rela.encode();
            assert_eq!(encoded.len(), ELF64_RELA_SIZE);
            // Bytes 8..16 of the Elf64_Rela are the little-endian r_info field.
            let info_bytes = u64::from_le_bytes([
                encoded[8],
                encoded[9],
                encoded[10],
                encoded[11],
                encoded[12],
                encoded[13],
                encoded[14],
                encoded[15],
            ]);
            assert_eq!(info_bytes, info, "encoded r_info bytes for {kind:?}");

            let decoded = Elf64Rela::decode(&encoded);
            assert_eq!(decoded, rela, "roundtrip for {kind:?}");
            assert_eq!(decoded.reloc_type, *expected_val);
        }
    }

    #[test]
    fn test_unknown_reloc_type() {
        assert_eq!(AArch64RelocType::from_type_val(9999), None);
        assert_eq!(X86_64RelocType::from_type_val(9999), None);
        assert_eq!(RiscvRelocType::from_type_val(9999), None);
    }

    /// Assert the numeric codes for the RISC-V relocations match the published
    /// RISC-V ELF psABI values, and that an Elf64_Rela built for each one
    /// round-trips through encode/decode with the correct packed
    /// `r_info = (sym << 32) | type` layout. Getting `R_RISCV_CALL_PLT`'s code
    /// wrong would silently emit an unrecognized/wrong relocation type — exactly
    /// the fail-closed-prohibited miscompile for a cross-function call.
    #[test]
    fn test_riscv_reloc_types() {
        let types: [(RiscvRelocType, u32); 8] = [
            (RiscvRelocType::None, 0),
            (RiscvRelocType::Abs64, 2),
            (RiscvRelocType::Jal, 17),
            (RiscvRelocType::Call, 18),
            (RiscvRelocType::CallPlt, 19),
            (RiscvRelocType::PcRelHi20, 23),
            (RiscvRelocType::PcRelLo12I, 24),
            (RiscvRelocType::Relax, 51),
        ];

        // Cross-check the named constants too.
        assert_eq!(R_RISCV_NONE, 0);
        assert_eq!(R_RISCV_64, 2);
        assert_eq!(R_RISCV_JAL, 17);
        assert_eq!(R_RISCV_CALL, 18);
        assert_eq!(R_RISCV_CALL_PLT, 19);
        assert_eq!(R_RISCV_PCREL_HI20, 23);
        assert_eq!(R_RISCV_PCREL_LO12_I, 24);
        assert_eq!(R_RISCV_RELAX, 51);

        for (kind, expected_val) in &types {
            assert_eq!(kind.to_type_val(), *expected_val, "code for {kind:?}");
            assert_eq!(RiscvRelocType::from_type_val(*expected_val), Some(*kind));

            let sym = 0x2222u32;
            let rela = Elf64Rela::riscv(0x80, sym, *kind, 0);
            let info = rela.r_info();
            assert_eq!(elf64_r_sym(info), sym, "r_info sym for {kind:?}");
            assert_eq!(
                elf64_r_type(info),
                *expected_val,
                "r_info type for {kind:?}"
            );

            let encoded = rela.encode();
            assert_eq!(encoded.len(), ELF64_RELA_SIZE);
            let decoded = Elf64Rela::decode(&encoded);
            assert_eq!(decoded, rela, "roundtrip for {kind:?}");
            assert_eq!(decoded.reloc_type, *expected_val);
        }
    }

    #[test]
    fn test_x86_64_rela_roundtrip() {
        let rela = Elf64Rela::x86_64(0x50, 3, X86_64RelocType::Plt32, -4);
        let encoded = rela.encode();
        let decoded = Elf64Rela::decode(&encoded);
        assert_eq!(decoded.r_offset, 0x50);
        assert_eq!(decoded.symbol_index, 3);
        assert_eq!(decoded.reloc_type, R_X86_64_PLT32);
        assert_eq!(decoded.r_addend, -4);
    }

    #[test]
    fn test_gotpcrel_roundtrip() {
        let rela = Elf64Rela::x86_64(0x30, 7, X86_64RelocType::GotPcRel, -4);
        let encoded = rela.encode();
        let decoded = Elf64Rela::decode(&encoded);
        assert_eq!(rela, decoded);
    }

    #[test]
    fn test_aarch64_got_roundtrip() {
        let rela = Elf64Rela::aarch64(0x00, 4, AArch64RelocType::AdrGotPage, 0);
        let encoded = rela.encode();
        let decoded = Elf64Rela::decode(&encoded);
        assert_eq!(rela, decoded);

        let rela = Elf64Rela::aarch64(0x04, 4, AArch64RelocType::Ld64GotLo12Nc, 0);
        let encoded = rela.encode();
        let decoded = Elf64Rela::decode(&encoded);
        assert_eq!(rela, decoded);
    }

    #[test]
    fn test_aarch64_tls_roundtrip() {
        let rela = Elf64Rela::aarch64(0x00, 6, AArch64RelocType::TlsieAdrGottprelPage21, 0);
        let encoded = rela.encode();
        let decoded = Elf64Rela::decode(&encoded);
        assert_eq!(rela, decoded);

        let rela = Elf64Rela::aarch64(0x04, 6, AArch64RelocType::TlsieLd64GottprelLo12Nc, 0);
        let encoded = rela.encode();
        let decoded = Elf64Rela::decode(&encoded);
        assert_eq!(rela, decoded);

        let rela = Elf64Rela::aarch64(0x08, 6, AArch64RelocType::TlsleAddTprelHi12, 0);
        let encoded = rela.encode();
        let decoded = Elf64Rela::decode(&encoded);
        assert_eq!(rela, decoded);

        let rela = Elf64Rela::aarch64(0x0c, 6, AArch64RelocType::TlsleAddTprelLo12, 0);
        let encoded = rela.encode();
        let decoded = Elf64Rela::decode(&encoded);
        assert_eq!(rela, decoded);

        let rela = Elf64Rela::aarch64(0x10, 6, AArch64RelocType::TlsleAddTprelLo12Nc, 0);
        let encoded = rela.encode();
        let decoded = Elf64Rela::decode(&encoded);
        assert_eq!(rela, decoded);
    }
}
