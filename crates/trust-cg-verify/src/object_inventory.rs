//! Object-file evidence inventories used by proof-promotion gates.
//!
//! This module intentionally does not parse object files. Codegen owns object
//! emission and feeds the relocations it emits into this target-typed evidence
//! shape so certified-output paths can reject uncovered object metadata instead
//! of certifying instruction proofs alone.

/// Target-specific relocation kind emitted into an object file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ObjectRelocationKind {
    /// ELF `R_AARCH64_ABS64`.
    AArch64ElfAbs64,
    /// ELF `R_AARCH64_CALL26`.
    AArch64ElfCall26,
    /// ELF `R_AARCH64_JUMP26`.
    AArch64ElfJump26,
    /// ELF `R_AARCH64_ADR_PREL_PG_HI21`.
    AArch64ElfAdrPrelPgHi21,
    /// ELF `R_AARCH64_ADD_ABS_LO12_NC`.
    AArch64ElfAddAbsLo12Nc,
    /// ELF `R_AARCH64_PREL32` (32-bit signed PC-relative data word; the
    /// `.eh_frame` `DW_EH_PE_pcrel|sdata4` pointer relocation).
    AArch64ElfPrel32,
    /// ELF `R_AARCH64_ADR_GOT_PAGE`.
    AArch64ElfAdrGotPage,
    /// ELF `R_AARCH64_LD64_GOT_LO12_NC`.
    AArch64ElfLd64GotLo12Nc,
    /// ELF `R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21`.
    AArch64ElfTlsieAdrGottprelPage21,
    /// ELF `R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC`.
    AArch64ElfTlsieLd64GottprelLo12Nc,
    /// ELF `R_AARCH64_TLSLE_ADD_TPREL_HI12`.
    AArch64ElfTlsleAddTprelHi12,
    /// ELF `R_AARCH64_TLSLE_ADD_TPREL_LO12`.
    AArch64ElfTlsleAddTprelLo12,
    /// ELF `R_AARCH64_TLSLE_ADD_TPREL_LO12_NC`.
    AArch64ElfTlsleAddTprelLo12Nc,
    /// AArch64 ELF relocation kind not yet modeled by a named inventory row.
    AArch64ElfOther(u32),
    /// Mach-O `ARM64_RELOC_PAGE21` (ADRP PC-relative page).
    AArch64MachOPage21,
    /// Mach-O `ARM64_RELOC_PAGEOFF12` (ADD/LDR page offset).
    AArch64MachOPageoff12,
    /// Mach-O `ARM64_RELOC_GOT_LOAD_PAGE21`.
    AArch64MachOGotLoadPage21,
    /// Mach-O `ARM64_RELOC_GOT_LOAD_PAGEOFF12`.
    AArch64MachOGotLoadPageoff12,
    /// Mach-O `ARM64_RELOC_BRANCH26`.
    AArch64MachOBranch26,
    /// Mach-O `ARM64_RELOC_UNSIGNED`.
    AArch64MachOUnsigned,
    /// Mach-O `ARM64_RELOC_SUBTRACTOR`.
    AArch64MachOSubtractor,
    /// Mach-O `ARM64_RELOC_TLVP_LOAD_PAGE21`.
    AArch64MachOTlvpLoadPage21,
    /// Mach-O `ARM64_RELOC_TLVP_LOAD_PAGEOFF12`.
    AArch64MachOTlvpLoadPageoff12,
    /// AArch64 Mach-O relocation kind not yet modeled by a named inventory row.
    AArch64MachOOther(u8),
    /// ELF `R_X86_64_64`.
    X86_64ElfAbs64,
    /// ELF `R_X86_64_PC32`.
    X86_64ElfPc32,
    /// ELF `R_X86_64_GOT32`.
    X86_64ElfGot32,
    /// ELF `R_X86_64_PLT32`.
    X86_64ElfPlt32,
    /// ELF `R_X86_64_GOTPCREL`.
    X86_64ElfGotPcRel,
    /// ELF `R_X86_64_32`.
    X86_64ElfAbs32,
    /// ELF `R_X86_64_32S`.
    X86_64ElfAbs32S,
    /// ELF `R_X86_64_16`.
    X86_64ElfAbs16,
    /// ELF `R_X86_64_PC16`.
    X86_64ElfPc16,
    /// ELF `R_X86_64_8`.
    X86_64ElfAbs8,
    /// ELF `R_X86_64_PC8`.
    X86_64ElfPc8,
    /// ELF `R_X86_64_GOTPCRELX`.
    X86_64ElfGotPcRelX,
    /// ELF `R_X86_64_REX_GOTPCRELX`.
    X86_64ElfRexGotPcRelX,
    /// x86-64 ELF relocation kind not yet modeled by a named inventory row.
    X86_64ElfOther(u32),
    /// Mach-O `X86_64_RELOC_UNSIGNED`.
    X86_64MachOUnsigned,
    /// Mach-O `X86_64_RELOC_SIGNED`.
    X86_64MachOSigned,
    /// Mach-O `X86_64_RELOC_BRANCH`.
    X86_64MachOBranch,
    /// Mach-O `X86_64_RELOC_GOT_LOAD`.
    X86_64MachOGotLoad,
    /// Mach-O `X86_64_RELOC_GOT`.
    X86_64MachOGot,
    /// Mach-O `X86_64_RELOC_SUBTRACTOR`.
    X86_64MachOSubtractor,
    /// Mach-O `X86_64_RELOC_SIGNED_1`.
    X86_64MachOSigned1,
    /// Mach-O `X86_64_RELOC_SIGNED_2`.
    X86_64MachOSigned2,
    /// Mach-O `X86_64_RELOC_SIGNED_4`.
    X86_64MachOSigned4,
    /// Mach-O `X86_64_RELOC_TLV`.
    X86_64MachOTlv,
    /// x86-64 Mach-O relocation kind not yet modeled by a named inventory row.
    X86_64MachOOther(u8),
    /// COFF `IMAGE_REL_AMD64_REL32`.
    X86_64CoffRel32,
    /// COFF `IMAGE_REL_AMD64_ADDR32NB`.
    X86_64CoffAddr32Nb,
    /// x86-64 COFF relocation kind not yet modeled by a named inventory row.
    X86_64CoffOther(u16),
}

impl std::fmt::Display for ObjectRelocationKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AArch64ElfAbs64 => f.write_str("AArch64 ELF R_AARCH64_ABS64"),
            Self::AArch64ElfCall26 => f.write_str("AArch64 ELF R_AARCH64_CALL26"),
            Self::AArch64ElfJump26 => f.write_str("AArch64 ELF R_AARCH64_JUMP26"),
            Self::AArch64ElfAdrPrelPgHi21 => f.write_str("AArch64 ELF R_AARCH64_ADR_PREL_PG_HI21"),
            Self::AArch64ElfAddAbsLo12Nc => f.write_str("AArch64 ELF R_AARCH64_ADD_ABS_LO12_NC"),
            Self::AArch64ElfPrel32 => f.write_str("AArch64 ELF R_AARCH64_PREL32"),
            Self::AArch64ElfAdrGotPage => f.write_str("AArch64 ELF R_AARCH64_ADR_GOT_PAGE"),
            Self::AArch64ElfLd64GotLo12Nc => f.write_str("AArch64 ELF R_AARCH64_LD64_GOT_LO12_NC"),
            Self::AArch64ElfTlsieAdrGottprelPage21 => {
                f.write_str("AArch64 ELF R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21")
            }
            Self::AArch64ElfTlsieLd64GottprelLo12Nc => {
                f.write_str("AArch64 ELF R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC")
            }
            Self::AArch64ElfTlsleAddTprelHi12 => {
                f.write_str("AArch64 ELF R_AARCH64_TLSLE_ADD_TPREL_HI12")
            }
            Self::AArch64ElfTlsleAddTprelLo12 => {
                f.write_str("AArch64 ELF R_AARCH64_TLSLE_ADD_TPREL_LO12")
            }
            Self::AArch64ElfTlsleAddTprelLo12Nc => {
                f.write_str("AArch64 ELF R_AARCH64_TLSLE_ADD_TPREL_LO12_NC")
            }
            Self::AArch64ElfOther(kind) => write!(f, "AArch64 ELF relocation {kind}"),
            Self::AArch64MachOPage21 => f.write_str("AArch64 Mach-O ARM64_RELOC_PAGE21"),
            Self::AArch64MachOPageoff12 => f.write_str("AArch64 Mach-O ARM64_RELOC_PAGEOFF12"),
            Self::AArch64MachOGotLoadPage21 => {
                f.write_str("AArch64 Mach-O ARM64_RELOC_GOT_LOAD_PAGE21")
            }
            Self::AArch64MachOGotLoadPageoff12 => {
                f.write_str("AArch64 Mach-O ARM64_RELOC_GOT_LOAD_PAGEOFF12")
            }
            Self::AArch64MachOBranch26 => f.write_str("AArch64 Mach-O ARM64_RELOC_BRANCH26"),
            Self::AArch64MachOUnsigned => f.write_str("AArch64 Mach-O ARM64_RELOC_UNSIGNED"),
            Self::AArch64MachOSubtractor => f.write_str("AArch64 Mach-O ARM64_RELOC_SUBTRACTOR"),
            Self::AArch64MachOTlvpLoadPage21 => {
                f.write_str("AArch64 Mach-O ARM64_RELOC_TLVP_LOAD_PAGE21")
            }
            Self::AArch64MachOTlvpLoadPageoff12 => {
                f.write_str("AArch64 Mach-O ARM64_RELOC_TLVP_LOAD_PAGEOFF12")
            }
            Self::AArch64MachOOther(kind) => write!(f, "AArch64 Mach-O relocation {kind}"),
            Self::X86_64ElfAbs64 => f.write_str("x86-64 ELF R_X86_64_64"),
            Self::X86_64ElfPc32 => f.write_str("x86-64 ELF R_X86_64_PC32"),
            Self::X86_64ElfGot32 => f.write_str("x86-64 ELF R_X86_64_GOT32"),
            Self::X86_64ElfPlt32 => f.write_str("x86-64 ELF R_X86_64_PLT32"),
            Self::X86_64ElfGotPcRel => f.write_str("x86-64 ELF R_X86_64_GOTPCREL"),
            Self::X86_64ElfAbs32 => f.write_str("x86-64 ELF R_X86_64_32"),
            Self::X86_64ElfAbs32S => f.write_str("x86-64 ELF R_X86_64_32S"),
            Self::X86_64ElfAbs16 => f.write_str("x86-64 ELF R_X86_64_16"),
            Self::X86_64ElfPc16 => f.write_str("x86-64 ELF R_X86_64_PC16"),
            Self::X86_64ElfAbs8 => f.write_str("x86-64 ELF R_X86_64_8"),
            Self::X86_64ElfPc8 => f.write_str("x86-64 ELF R_X86_64_PC8"),
            Self::X86_64ElfGotPcRelX => f.write_str("x86-64 ELF R_X86_64_GOTPCRELX"),
            Self::X86_64ElfRexGotPcRelX => f.write_str("x86-64 ELF R_X86_64_REX_GOTPCRELX"),
            Self::X86_64ElfOther(kind) => write!(f, "x86-64 ELF relocation {kind}"),
            Self::X86_64MachOUnsigned => f.write_str("x86-64 Mach-O X86_64_RELOC_UNSIGNED"),
            Self::X86_64MachOSigned => f.write_str("x86-64 Mach-O X86_64_RELOC_SIGNED"),
            Self::X86_64MachOBranch => f.write_str("x86-64 Mach-O X86_64_RELOC_BRANCH"),
            Self::X86_64MachOGotLoad => f.write_str("x86-64 Mach-O X86_64_RELOC_GOT_LOAD"),
            Self::X86_64MachOGot => f.write_str("x86-64 Mach-O X86_64_RELOC_GOT"),
            Self::X86_64MachOSubtractor => f.write_str("x86-64 Mach-O X86_64_RELOC_SUBTRACTOR"),
            Self::X86_64MachOSigned1 => f.write_str("x86-64 Mach-O X86_64_RELOC_SIGNED_1"),
            Self::X86_64MachOSigned2 => f.write_str("x86-64 Mach-O X86_64_RELOC_SIGNED_2"),
            Self::X86_64MachOSigned4 => f.write_str("x86-64 Mach-O X86_64_RELOC_SIGNED_4"),
            Self::X86_64MachOTlv => f.write_str("x86-64 Mach-O X86_64_RELOC_TLV"),
            Self::X86_64MachOOther(kind) => write!(f, "x86-64 Mach-O relocation {kind}"),
            Self::X86_64CoffRel32 => f.write_str("x86-64 COFF IMAGE_REL_AMD64_REL32"),
            Self::X86_64CoffAddr32Nb => f.write_str("x86-64 COFF IMAGE_REL_AMD64_ADDR32NB"),
            Self::X86_64CoffOther(kind) => write!(f, "x86-64 COFF relocation {kind}"),
        }
    }
}

impl ObjectRelocationKind {
    /// Named ordinary (non-TLS) AArch64 ELF relocation rows modeled by this
    /// inventory.
    ///
    /// Naming a row is not proof authority. These rows remain fail-closed until
    /// target-specific proof obligations are discharged and explicitly wired
    /// into [`ObjectRelocationProofRegistry`].
    pub fn aarch64_elf_named_non_tls_rows() -> &'static [Self] {
        &[
            Self::AArch64ElfAbs64,
            Self::AArch64ElfCall26,
            Self::AArch64ElfJump26,
            Self::AArch64ElfAdrPrelPgHi21,
            Self::AArch64ElfAddAbsLo12Nc,
            Self::AArch64ElfPrel32,
            Self::AArch64ElfAdrGotPage,
            Self::AArch64ElfLd64GotLo12Nc,
        ]
    }

    /// Named AArch64 ELF TLS relocation rows modeled by this inventory.
    ///
    /// These rows are independent of the ordinary ELF rows returned by
    /// [`Self::aarch64_elf_named_non_tls_rows`].
    /// They let proof-required promotion report precise TLS relocation gaps
    /// instead of collapsing known TLS ABI rows into `AArch64ElfOther`.
    pub fn aarch64_elf_named_tls_rows() -> &'static [Self] {
        &[
            Self::AArch64ElfTlsieAdrGottprelPage21,
            Self::AArch64ElfTlsieLd64GottprelLo12Nc,
            Self::AArch64ElfTlsleAddTprelHi12,
            Self::AArch64ElfTlsleAddTprelLo12,
            Self::AArch64ElfTlsleAddTprelLo12Nc,
        ]
    }

    /// Named AArch64 Mach-O relocation rows modeled by this inventory.
    ///
    /// These are target-typed evidence labels only. Returning them here does
    /// not register proof coverage or make proof-required promotion safe.
    pub fn aarch64_macho_named_rows() -> &'static [Self] {
        &[
            Self::AArch64MachOPage21,
            Self::AArch64MachOPageoff12,
            Self::AArch64MachOGotLoadPage21,
            Self::AArch64MachOGotLoadPageoff12,
            Self::AArch64MachOBranch26,
            Self::AArch64MachOUnsigned,
            Self::AArch64MachOSubtractor,
            Self::AArch64MachOTlvpLoadPage21,
            Self::AArch64MachOTlvpLoadPageoff12,
        ]
    }

    /// Named x86-64 ELF relocation rows modeled by this inventory.
    ///
    /// These are target-typed evidence labels only. Returning them here does
    /// not register proof coverage or make proof-required promotion safe.
    pub fn x86_64_elf_named_rows() -> &'static [Self] {
        &[
            Self::X86_64ElfAbs64,
            Self::X86_64ElfPc32,
            Self::X86_64ElfGot32,
            Self::X86_64ElfPlt32,
            Self::X86_64ElfGotPcRel,
            Self::X86_64ElfAbs32,
            Self::X86_64ElfAbs32S,
            Self::X86_64ElfAbs16,
            Self::X86_64ElfPc16,
            Self::X86_64ElfAbs8,
            Self::X86_64ElfPc8,
            Self::X86_64ElfGotPcRelX,
            Self::X86_64ElfRexGotPcRelX,
        ]
    }

    /// Named x86-64 Mach-O relocation rows modeled by this inventory.
    ///
    /// These are target-typed evidence labels only. Returning them here does
    /// not register proof coverage or make proof-required promotion safe.
    pub fn x86_64_macho_named_rows() -> &'static [Self] {
        &[
            Self::X86_64MachOUnsigned,
            Self::X86_64MachOSigned,
            Self::X86_64MachOBranch,
            Self::X86_64MachOGotLoad,
            Self::X86_64MachOGot,
            Self::X86_64MachOSubtractor,
            Self::X86_64MachOSigned1,
            Self::X86_64MachOSigned2,
            Self::X86_64MachOSigned4,
            Self::X86_64MachOTlv,
        ]
    }

    /// Named x86-64 COFF relocation rows modeled by this inventory.
    ///
    /// These are target-typed evidence labels only. Returning them here does
    /// not register proof coverage or make proof-required promotion safe.
    pub fn x86_64_coff_named_rows() -> &'static [Self] {
        &[Self::X86_64CoffRel32, Self::X86_64CoffAddr32Nb]
    }

    /// The object container format this relocation kind belongs to.
    ///
    /// Used by the inventory to demand a CONTAINER-MATCHED independent
    /// per-object binding: a Mach-O reparse run can never bind an ELF row and
    /// vice versa, even if a registry were (wrongly) cross-populated.
    pub fn container(self) -> ObjectContainer {
        match self {
            Self::AArch64ElfAbs64
            | Self::AArch64ElfCall26
            | Self::AArch64ElfJump26
            | Self::AArch64ElfAdrPrelPgHi21
            | Self::AArch64ElfAddAbsLo12Nc
            | Self::AArch64ElfPrel32
            | Self::AArch64ElfAdrGotPage
            | Self::AArch64ElfLd64GotLo12Nc
            | Self::AArch64ElfTlsieAdrGottprelPage21
            | Self::AArch64ElfTlsieLd64GottprelLo12Nc
            | Self::AArch64ElfTlsleAddTprelHi12
            | Self::AArch64ElfTlsleAddTprelLo12
            | Self::AArch64ElfTlsleAddTprelLo12Nc
            | Self::AArch64ElfOther(_)
            | Self::X86_64ElfAbs64
            | Self::X86_64ElfPc32
            | Self::X86_64ElfGot32
            | Self::X86_64ElfPlt32
            | Self::X86_64ElfGotPcRel
            | Self::X86_64ElfAbs32
            | Self::X86_64ElfAbs32S
            | Self::X86_64ElfAbs16
            | Self::X86_64ElfPc16
            | Self::X86_64ElfAbs8
            | Self::X86_64ElfPc8
            | Self::X86_64ElfGotPcRelX
            | Self::X86_64ElfRexGotPcRelX
            | Self::X86_64ElfOther(_) => ObjectContainer::Elf,
            Self::AArch64MachOPage21
            | Self::AArch64MachOPageoff12
            | Self::AArch64MachOGotLoadPage21
            | Self::AArch64MachOGotLoadPageoff12
            | Self::AArch64MachOBranch26
            | Self::AArch64MachOUnsigned
            | Self::AArch64MachOSubtractor
            | Self::AArch64MachOTlvpLoadPage21
            | Self::AArch64MachOTlvpLoadPageoff12
            | Self::AArch64MachOOther(_)
            | Self::X86_64MachOUnsigned
            | Self::X86_64MachOSigned
            | Self::X86_64MachOBranch
            | Self::X86_64MachOGotLoad
            | Self::X86_64MachOGot
            | Self::X86_64MachOSubtractor
            | Self::X86_64MachOSigned1
            | Self::X86_64MachOSigned2
            | Self::X86_64MachOSigned4
            | Self::X86_64MachOTlv
            | Self::X86_64MachOOther(_) => ObjectContainer::MachO,
            Self::X86_64CoffRel32 | Self::X86_64CoffAddr32Nb | Self::X86_64CoffOther(_) => {
                ObjectContainer::Coff
            }
        }
    }
}

/// The object container format a relocation kind (or a per-object binding)
/// belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObjectContainer {
    /// ELF relocatable object.
    Elf,
    /// Mach-O relocatable object.
    MachO,
    /// COFF relocatable object.
    Coff,
}

/// Proof status for one emitted object relocation kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelocationInventoryStatus {
    /// The relocation has a verified object-emission proof.
    Verified,
    /// The relocation was emitted but lacks proof coverage.
    Unverified,
}

impl RelocationInventoryStatus {
    /// Returns true when this relocation row is safe for proof-required promotion.
    pub fn is_promotable(self) -> bool {
        matches!(self, Self::Verified)
    }
}

impl std::fmt::Display for RelocationInventoryStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Verified => f.write_str("verified"),
            Self::Unverified => f.write_str("unverified"),
        }
    }
}

/// Registry of object relocation proofs available to proof-promotion gates.
///
/// A row appears here only after a target-specific proof obligation has been
/// discharged and explicitly bound to the emitted relocation kind. Merely
/// naming or implementing a relocation is not proof authority.
///
/// The authority set is intentionally private; callers cannot forge a
/// production `Verified` row:
///
/// ```compile_fail
/// use trust_cg_verify::{ObjectRelocationKind, ObjectRelocationProofRegistry};
/// use std::collections::BTreeMap;
///
/// let registry = ObjectRelocationProofRegistry {
///     verified: BTreeMap::from([(ObjectRelocationKind::X86_64ElfPlt32, "forged")]),
/// };
/// # let _ = registry;
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjectRelocationProofRegistry {
    /// Kind -> the standing solver-backed value-proof lane covering it (the
    /// module path of the obligation collector). A row here is NECESSARY but
    /// not SUFFICIENT for a `Verified` inventory entry: the report must also
    /// carry a per-object independent binding (see [`ObjectProofBinding`]).
    verified: std::collections::BTreeMap<ObjectRelocationKind, &'static str>,
}

/// The per-object independent-check binding a report was built with.
///
/// This is the second half of the Certified composition the 2026-07-19
/// fail-closed restore (`54762bc4`) demanded: a solver-backed value formula
/// alone is Trusted evidence (the solver is in its TCB) and is NOT bound to
/// any particular emitted object. The ENC-9 Mach-O reparse gate closes both
/// gaps for relocation RECORDS: it independently re-parses the exact bytes
/// of THIS object and compares every relocation record field against intent,
/// failing the write closed on any mismatch. A kind whose value semantics
/// are solver-proved AND whose records were independently reparse-checked on
/// this object is promotable; anything less stays fail-closed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObjectProofBinding {
    /// The ENC-9 Mach-O reparse gate ran at Enforce over this exact object's
    /// bytes (the write would have failed closed on any record mismatch).
    /// Binds Mach-O rows ONLY.
    MachOReparseEnforced,
    /// The ELF reparse gate (the ENC-9 sibling in `elf::reparse`) ran at
    /// Enforce over this exact object's bytes: an independent, spec-driven
    /// ELF64 reader re-parsed the emitted `Elf64_Rela` records (`r_offset`,
    /// symbol index, type, explicit `r_addend`), symbols, and section bytes,
    /// and the write would have failed closed on any mismatch. Binds ELF
    /// rows ONLY.
    ElfReparseEnforced,
    /// No independent per-object record check is bound (fail-closed: every
    /// row reports `Unverified` regardless of registry coverage).
    Unbound,
}

impl ObjectProofBinding {
    /// The container whose relocation records this binding's independent
    /// check re-parsed, if any. A binding can only upgrade rows of its OWN
    /// container; everything else stays fail-closed.
    fn bound_container(self) -> Option<ObjectContainer> {
        match self {
            Self::MachOReparseEnforced => Some(ObjectContainer::MachO),
            Self::ElfReparseEnforced => Some(ObjectContainer::Elf),
            Self::Unbound => None,
        }
    }

    /// Human-readable name of the independent gate backing this binding.
    fn gate_name(self) -> &'static str {
        match self {
            Self::MachOReparseEnforced => "ENC-9 reparse-enforced object",
            Self::ElfReparseEnforced => "ELF reparse-enforced object",
            Self::Unbound => "unbound",
        }
    }
}

impl ObjectRelocationProofRegistry {
    /// Empty registry used by fail-closed callers and tests.
    pub fn empty() -> Self {
        Self {
            verified: std::collections::BTreeMap::new(),
        }
    }

    /// Production proof-authority registry for AArch64 ELF relocations.
    ///
    /// Each row cites the standing solver-backed value-proof lane for its
    /// kind ([`crate::aarch64_elf_reloc_proofs`]), registered in the
    /// [`crate::proof_database`] object-emission family; the lane's six
    /// refutable negative controls are asserted Invalid by its own
    /// `verify_by_evaluation` tests (controls are never DB-registered,
    /// matching every precedent lane). The lane models the AArch64 psABI Rela semantics —
    /// explicit `r_addend`, `P` = `r_offset`, linker-resolved `S`/`G` — so a
    /// wrong pc-relativity, page mask, or low-12 recomposition refutes. As
    /// on the x86-64 ELF side, a registry row alone still reports
    /// `Unverified`: promotion additionally requires the report to be built
    /// with [`ObjectProofBinding::ElfReparseEnforced`] — the shared
    /// per-object ELF reparse gate — which is what upgrades Trusted formula
    /// evidence into an object-bound Certified verdict. (The historical
    /// emptiness rationale — "the inventory cannot bind a gate report to the
    /// object" — is exactly the composition `ObjectProofBinding` now
    /// provides, the same one the x86-64 ELF rows entered under.)
    ///
    /// The four EMITTED TLSLE/TLSIE kinds cite their own value lane
    /// ([`crate::aarch64_elf_tls_reloc_proofs`], DB-registered in the same
    /// object-emission family). Their ABI range constraints are modeled
    /// INSIDE the obligations as preconditions (e.g. the TPREL `0 <= X <
    /// 2^24` window carried by `preconditions: vec![in_range]`), each with a
    /// paired DROP-the-precondition negative control that REFUTES — so the
    /// registry row does not need to express them, exactly as the ordinary
    /// rows do not express CALL26's ±128MiB window. In both cases the
    /// psABI makes the LINKER's overflow check discharge the precondition at
    /// resolution time; the reparse-enforced binding pins what the emitter
    /// wrote. (An earlier revision kept these rows out on the belief the
    /// registry had to carry the range preconditions itself — inherited
    /// caution, retired when the obligations landed them internally.)
    ///
    /// The FIFTH named TLS kind — the checked non-NC
    /// `R_AARCH64_TLSLE_ADD_TPREL_LO12` — stays OUT: never emitted, and the
    /// lane carries NO obligation for it (its own doc says so). A row for it
    /// would be authority backed by zero proofs.
    pub fn aarch64_elf_production() -> Self {
        const LANE: &str = "trust_cg_verify::aarch64_elf_reloc_proofs";
        const TLS_LANE: &str = "trust_cg_verify::aarch64_elf_tls_reloc_proofs";
        let mut verified = std::collections::BTreeMap::new();
        verified.insert(ObjectRelocationKind::AArch64ElfCall26, LANE);
        verified.insert(ObjectRelocationKind::AArch64ElfJump26, LANE);
        verified.insert(ObjectRelocationKind::AArch64ElfPrel32, LANE);
        verified.insert(ObjectRelocationKind::AArch64ElfAbs64, LANE);
        verified.insert(ObjectRelocationKind::AArch64ElfAdrPrelPgHi21, LANE);
        verified.insert(ObjectRelocationKind::AArch64ElfAddAbsLo12Nc, LANE);
        verified.insert(ObjectRelocationKind::AArch64ElfAdrGotPage, LANE);
        verified.insert(ObjectRelocationKind::AArch64ElfLd64GotLo12Nc, LANE);
        verified.insert(
            ObjectRelocationKind::AArch64ElfTlsieAdrGottprelPage21,
            TLS_LANE,
        );
        verified.insert(
            ObjectRelocationKind::AArch64ElfTlsieLd64GottprelLo12Nc,
            TLS_LANE,
        );
        verified.insert(ObjectRelocationKind::AArch64ElfTlsleAddTprelHi12, TLS_LANE);
        // The CHECKED (non-NC) R_AARCH64_TLSLE_ADD_TPREL_LO12 stays OUT: the
        // backend never emits it and `aarch64_elf_tls_reloc_proofs` carries NO
        // obligation for it — a registry row would be Certified authority
        // backed by zero proofs (review finding). It fails closed even with
        // the reparse binding.
        verified.insert(
            ObjectRelocationKind::AArch64ElfTlsleAddTprelLo12Nc,
            TLS_LANE,
        );
        Self { verified }
    }

    /// Production proof-authority registry for AArch64 Mach-O relocations.
    ///
    /// Each row cites the standing solver-backed value-proof lane for its
    /// kind ([`crate::aarch64_macho_data_reloc_proofs`] for the page/pageoff,
    /// GOT, UNSIGNED and SUBTRACTOR rows,
    /// [`crate::aarch64_macho_call_reloc_proofs`] for the BRANCH26 row, and
    /// [`crate::aarch64_macho_tlvp_reloc_proofs`] for the TLVP rows),
    /// registered in the [`crate::proof_database`] object-emission family
    /// with negative controls and discharged by the strict proof gate. A
    /// registry row alone still reports `Unverified`: promotion additionally
    /// requires the report to be built with
    /// [`ObjectProofBinding::MachOReparseEnforced`] — the per-object ENC-9
    /// independent record check — which is what upgrades Trusted formula
    /// evidence into an object-bound Certified verdict. This is exactly the
    /// authority composition `348021a1` established for the x86-64 Mach-O
    /// rows (and `54762bc4` demanded): lane + container-bound ENC-9 reparse.
    ///
    /// `AArch64MachOOther(_)` has NO value proof and stays out (fail-closed).
    pub fn aarch64_macho_production() -> Self {
        const DATA_LANE: &str = "trust_cg_verify::aarch64_macho_data_reloc_proofs";
        const CALL_LANE: &str = "trust_cg_verify::aarch64_macho_call_reloc_proofs";
        const TLVP_LANE: &str = "trust_cg_verify::aarch64_macho_tlvp_reloc_proofs";
        let mut verified = std::collections::BTreeMap::new();
        verified.insert(ObjectRelocationKind::AArch64MachOPage21, DATA_LANE);
        verified.insert(ObjectRelocationKind::AArch64MachOPageoff12, DATA_LANE);
        verified.insert(ObjectRelocationKind::AArch64MachOGotLoadPage21, DATA_LANE);
        verified.insert(
            ObjectRelocationKind::AArch64MachOGotLoadPageoff12,
            DATA_LANE,
        );
        verified.insert(ObjectRelocationKind::AArch64MachOUnsigned, DATA_LANE);
        verified.insert(ObjectRelocationKind::AArch64MachOSubtractor, DATA_LANE);
        verified.insert(ObjectRelocationKind::AArch64MachOBranch26, CALL_LANE);
        verified.insert(ObjectRelocationKind::AArch64MachOTlvpLoadPage21, TLVP_LANE);
        verified.insert(
            ObjectRelocationKind::AArch64MachOTlvpLoadPageoff12,
            TLVP_LANE,
        );
        Self { verified }
    }

    /// Production proof-authority registry for x86-64 ELF relocations.
    ///
    /// Each row cites the standing solver-backed value-proof lane for its
    /// kind ([`crate::elf_data_reloc_proofs`] for the data rows,
    /// [`crate::elf_call_reloc_proofs`] for the direct-call PLT32 row),
    /// registered in the [`crate::proof_database`] object-emission family
    /// with negative controls. The lanes model the psABI Rela semantics —
    /// explicit `r_addend`, field-START `P`, and the baked `-4` bridge to
    /// the CPU's field-END RIP — so a wrong addend/anchor/pc-relativity
    /// refutes. A registry row alone still reports `Unverified`: promotion
    /// additionally requires the report to be built with
    /// [`ObjectProofBinding::ElfReparseEnforced`] — the per-object ELF
    /// reparse gate (the ENC-9 sibling) — which is what upgrades Trusted
    /// formula evidence into an object-bound Certified verdict (the
    /// composition the `54762bc4` fail-closed restore required).
    ///
    /// Every other named ELF row (`GOT32`, the 8/16/32-bit absolutes and
    /// pc-rels, `GOTPCRELX`/`REX_GOTPCRELX`) has NO value proof, is never
    /// emitted, and stays out (fail-closed).
    pub fn x86_64_elf_production() -> Self {
        const DATA_LANE: &str = "trust_cg_verify::elf_data_reloc_proofs";
        const CALL_LANE: &str = "trust_cg_verify::elf_call_reloc_proofs";
        let mut verified = std::collections::BTreeMap::new();
        verified.insert(ObjectRelocationKind::X86_64ElfAbs64, DATA_LANE);
        verified.insert(ObjectRelocationKind::X86_64ElfPc32, DATA_LANE);
        verified.insert(ObjectRelocationKind::X86_64ElfGotPcRel, DATA_LANE);
        verified.insert(ObjectRelocationKind::X86_64ElfPlt32, CALL_LANE);
        Self { verified }
    }

    /// Production proof-authority registry for x86-64 Mach-O relocations.
    ///
    /// Each row cites the standing solver-backed value-proof lane for its
    /// kind ([`crate::macho_data_reloc_proofs`] for the data rows,
    /// [`crate::macho_call_reloc_proofs`] for the direct-call BRANCH row),
    /// registered in the [`crate::proof_database`] MachOEmission family with
    /// negative controls. A registry row alone still reports `Unverified`:
    /// promotion additionally requires the report to be built with
    /// [`ObjectProofBinding::MachOReparseEnforced`] — the per-object ENC-9
    /// independent record check — which is what upgrades Trusted formula
    /// evidence into an object-bound Certified verdict (the composition the
    /// `54762bc4` fail-closed restore required).
    ///
    /// `X86_64MachOTlv` has NO value proof and stays out (fail-closed).
    pub fn x86_64_macho_production() -> Self {
        const DATA_LANE: &str = "trust_cg_verify::macho_data_reloc_proofs";
        const CALL_LANE: &str = "trust_cg_verify::macho_call_reloc_proofs";
        let mut verified = std::collections::BTreeMap::new();
        verified.insert(ObjectRelocationKind::X86_64MachOUnsigned, DATA_LANE);
        verified.insert(ObjectRelocationKind::X86_64MachOSigned, DATA_LANE);
        verified.insert(ObjectRelocationKind::X86_64MachOSigned1, DATA_LANE);
        verified.insert(ObjectRelocationKind::X86_64MachOSigned2, DATA_LANE);
        verified.insert(ObjectRelocationKind::X86_64MachOSigned4, DATA_LANE);
        verified.insert(ObjectRelocationKind::X86_64MachOGotLoad, DATA_LANE);
        verified.insert(ObjectRelocationKind::X86_64MachOGot, DATA_LANE);
        verified.insert(ObjectRelocationKind::X86_64MachOSubtractor, DATA_LANE);
        verified.insert(ObjectRelocationKind::X86_64MachOBranch, CALL_LANE);
        Self { verified }
    }

    /// Returns true when this registry contains a proof row for `kind`.
    pub fn contains(&self, kind: ObjectRelocationKind) -> bool {
        self.verified.contains_key(&kind)
    }

    /// The proof-lane citation for `kind`, if registered.
    pub fn lane(&self, kind: ObjectRelocationKind) -> Option<&'static str> {
        self.verified.get(&kind).copied()
    }

    /// Iterator over verified relocation kinds in deterministic order.
    pub fn verified_kinds(&self) -> impl Iterator<Item = ObjectRelocationKind> + '_ {
        self.verified.keys().copied()
    }
}

impl Default for ObjectRelocationProofRegistry {
    fn default() -> Self {
        Self::empty()
    }
}

/// One emitted object relocation row in the proof inventory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelocationInventoryEntry {
    /// Deterministic row index supplied by the object emitter.
    pub index: usize,
    /// Target-specific relocation kind.
    pub kind: ObjectRelocationKind,
    /// Proof coverage status for this relocation kind.
    pub status: RelocationInventoryStatus,
    /// Human-readable proof or gap detail.
    pub detail: String,
}

/// Target-aware inventory of emitted object relocations and their proof coverage.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjectRelocationInventoryReport {
    /// Object or module name covered by this inventory.
    pub object_name: String,
    /// All emitted relocation rows.
    pub entries: Vec<RelocationInventoryEntry>,
}

impl ObjectRelocationInventoryReport {
    /// Build an inventory from emitted relocation kinds, a proof registry,
    /// and the per-object independent-check binding.
    ///
    /// A row is `Verified` only when BOTH halves of the Certified
    /// composition hold: a standing solver-backed value proof is registered
    /// for its kind AND this object's relocation records were independently
    /// re-parsed at Enforce by the gate of the SAME container (ENC-9 for
    /// Mach-O rows, the ELF reparse gate for ELF rows — a cross-container
    /// binding binds nothing). With [`ObjectProofBinding::Unbound`], every
    /// row stays `Unverified` regardless of registry coverage — switching a
    /// reparse gate off (`TCG_NO_MACHO_REPARSE` / `TCG_NO_ELF_REPARSE`)
    /// therefore re-fails promotion closed.
    pub fn from_emitted_kinds_with_registry_and_binding(
        object_name: impl Into<String>,
        emitted: impl IntoIterator<Item = ObjectRelocationKind>,
        registry: &ObjectRelocationProofRegistry,
        binding: ObjectProofBinding,
    ) -> Self {
        let entries = emitted
            .into_iter()
            .enumerate()
            .map(|(index, kind)| {
                let container_bound = binding.bound_container() == Some(kind.container());
                let (status, detail) = match (registry.lane(kind), container_bound) {
                    (Some(lane), true) => (
                        RelocationInventoryStatus::Verified,
                        format!(
                            "solver-backed value proof ({lane}) + {}",
                            binding.gate_name()
                        ),
                    ),
                    (Some(lane), false) => (
                        RelocationInventoryStatus::Unverified,
                        format!(
                            "solver lane {lane} registered but object lacks an independent reparse binding for its container"
                        ),
                    ),
                    (None, _) => (
                        RelocationInventoryStatus::Unverified,
                        "no object relocation proof is registered".to_string(),
                    ),
                };
                RelocationInventoryEntry {
                    index,
                    kind,
                    status,
                    detail,
                }
            })
            .collect();

        Self {
            object_name: object_name.into(),
            entries,
        }
    }

    /// Build an inventory from emitted relocation kinds and a proof registry
    /// with NO per-object binding — every row fail-closed `Unverified`.
    /// Callers that run an independent per-object record check must use
    /// [`Self::from_emitted_kinds_with_registry_and_binding`].
    pub fn from_emitted_kinds_with_registry(
        object_name: impl Into<String>,
        emitted: impl IntoIterator<Item = ObjectRelocationKind>,
        registry: &ObjectRelocationProofRegistry,
    ) -> Self {
        Self::from_emitted_kinds_with_registry_and_binding(
            object_name,
            emitted,
            registry,
            ObjectProofBinding::Unbound,
        )
    }

    /// Returns rows that block proof-required promotion.
    pub fn uncovered_relocations(&self) -> Vec<&RelocationInventoryEntry> {
        self.entries
            .iter()
            .filter(|entry| !entry.status.is_promotable())
            .collect()
    }

    /// Returns true when every emitted relocation has verified proof coverage.
    pub fn is_promotable(&self) -> bool {
        self.uncovered_relocations().is_empty()
    }

    /// Builds a concise fail-closed rejection reason for proof promotion.
    pub fn promotion_rejection_reason(&self) -> Option<String> {
        let uncovered = self.uncovered_relocations();
        let first = uncovered.first()?;
        Some(format!(
            "object relocation inventory found {} uncovered relocation kind(s); first in {}[{}] is {} ({})",
            uncovered.len(),
            self.object_name,
            first.index,
            first.kind,
            first.detail
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test-only registry with explicit rows (the module-private field is
    /// reachable here; production callers cannot do this).
    fn test_registry(rows: &[ObjectRelocationKind]) -> ObjectRelocationProofRegistry {
        ObjectRelocationProofRegistry {
            verified: rows.iter().map(|&k| (k, "test-lane")).collect(),
        }
    }

    #[test]
    fn relocation_inventory_reports_uncovered_aarch64_elf_relocation() {
        let registry = test_registry(&[ObjectRelocationKind::AArch64ElfCall26]);
        let report = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry_and_binding(
            "module.o",
            [
                ObjectRelocationKind::AArch64ElfCall26,
                ObjectRelocationKind::AArch64ElfAdrGotPage,
            ],
            &registry,
            ObjectProofBinding::ElfReparseEnforced,
        );

        assert!(!report.is_promotable());
        let reason = report
            .promotion_rejection_reason()
            .expect("uncovered relocation should reject promotion");
        assert!(reason.contains("object relocation inventory"));
        assert!(reason.contains("R_AARCH64_ADR_GOT_PAGE"));
    }

    #[test]
    fn relocation_inventory_accepts_fully_covered_bound_rows() {
        let registry = test_registry(&[ObjectRelocationKind::AArch64ElfJump26]);
        let report = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry_and_binding(
            "module.o",
            [ObjectRelocationKind::AArch64ElfJump26],
            &registry,
            ObjectProofBinding::ElfReparseEnforced,
        );

        assert!(report.is_promotable());
        assert!(report.promotion_rejection_reason().is_none());
    }

    #[test]
    fn relocation_inventory_rejects_cross_container_bindings() {
        // A binding only binds rows of its OWN container: an ELF reparse run
        // says nothing about a Mach-O record set and vice versa. Registered
        // rows under a mismatched binding must stay fail-closed.
        let cases = [
            (
                ObjectRelocationKind::AArch64ElfJump26,
                ObjectProofBinding::MachOReparseEnforced,
            ),
            (
                ObjectRelocationKind::X86_64ElfPlt32,
                ObjectProofBinding::MachOReparseEnforced,
            ),
            (
                ObjectRelocationKind::X86_64MachOBranch,
                ObjectProofBinding::ElfReparseEnforced,
            ),
            (
                ObjectRelocationKind::X86_64CoffRel32,
                ObjectProofBinding::ElfReparseEnforced,
            ),
        ];
        for (kind, binding) in cases {
            let registry = test_registry(&[kind]);
            let report =
                ObjectRelocationInventoryReport::from_emitted_kinds_with_registry_and_binding(
                    "module.o",
                    [kind],
                    &registry,
                    binding,
                );
            assert!(
                !report.is_promotable(),
                "cross-container binding must not bind {kind}: {report:?}"
            );
            assert!(
                report
                    .promotion_rejection_reason()
                    .is_some_and(|r| r.contains("lacks an independent reparse binding")),
                "mismatch must name the missing binding for {kind}"
            );
        }
    }

    #[test]
    fn relocation_inventory_rejects_covered_rows_without_object_binding() {
        // A registry row WITHOUT the per-object independent-check binding
        // must stay fail-closed: solver evidence alone is Trusted, not
        // Certified (the 54762bc4 doctrine).
        let registry = test_registry(&[ObjectRelocationKind::AArch64ElfJump26]);
        let report = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry(
            "module.o",
            [ObjectRelocationKind::AArch64ElfJump26],
            &registry,
        );

        assert!(!report.is_promotable());
        let reason = report
            .promotion_rejection_reason()
            .expect("unbound rows must reject promotion");
        assert!(reason.contains("lacks an independent reparse binding"));
    }

    #[test]
    fn aarch64_elf_registry_covers_non_tls_rows_but_binds_them_fail_closed() {
        let registry = ObjectRelocationProofRegistry::aarch64_elf_production();
        assert_eq!(
            ObjectRelocationKind::aarch64_elf_named_non_tls_rows().len(),
            8,
            "ordinary AArch64 ELF row inventory changed; audit its proof authority"
        );
        // Every ordinary row cites the aarch64_elf_reloc_proofs value lane…
        for kind in ObjectRelocationKind::aarch64_elf_named_non_tls_rows() {
            assert!(
                registry.contains(*kind),
                "AArch64 ELF row {kind} must cite its solver-backed value lane"
            );
        }
        // …but a registry row alone NEVER promotes: without the per-object
        // ELF reparse binding every row stays Unverified (fail-closed).
        let unbound = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry(
            "aarch64-linux-unbound.o",
            ObjectRelocationKind::aarch64_elf_named_non_tls_rows()
                .iter()
                .copied(),
            &registry,
        );
        assert!(!unbound.is_promotable());
        // With the shared ELF reparse binding, the Certified composition holds.
        let bound = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry_and_binding(
            "aarch64-linux-bound.o",
            ObjectRelocationKind::aarch64_elf_named_non_tls_rows()
                .iter()
                .copied(),
            &registry,
            ObjectProofBinding::ElfReparseEnforced,
        );
        assert!(bound.is_promotable());

        assert!(
            !registry.contains(ObjectRelocationKind::AArch64ElfOther(0xdead)),
            "unnamed/future relocation rows must stay fail-closed"
        );
        // The four EMITTED TLS kinds carry the same contract through their own
        // value lane (per-mode binding behavior pinned by
        // `relocation_inventory_certifies_tls{le,ie}_rows_only_with_reparse_binding`);
        // the never-emitted checked TPREL_LO12 has no obligation and stays out
        // (`checked_tprel_lo12_row_rejects_even_with_reparse_binding`).
        for kind in ObjectRelocationKind::aarch64_elf_named_tls_rows() {
            if *kind == ObjectRelocationKind::AArch64ElfTlsleAddTprelLo12 {
                assert!(!registry.contains(*kind));
                continue;
            }
            assert!(
                registry.contains(*kind),
                "AArch64 ELF TLS row {kind} must cite the TLS value lane"
            );
        }
    }

    #[test]
    fn relocation_inventory_rejects_named_but_unproven_aarch64_elf_rows() {
        let registry = ObjectRelocationProofRegistry::aarch64_elf_production();
        let report = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry(
            "module.o",
            ObjectRelocationKind::aarch64_elf_named_non_tls_rows()
                .iter()
                .copied(),
            &registry,
        );

        assert!(!report.is_promotable());
        assert_eq!(
            report.uncovered_relocations().len(),
            ObjectRelocationKind::aarch64_elf_named_non_tls_rows().len()
        );
        assert!(
            report
                .promotion_rejection_reason()
                .is_some_and(|reason| reason.contains("R_AARCH64_ABS64"))
        );
    }

    #[test]
    fn relocation_inventory_rejects_unknown_rows_even_with_aarch64_elf_registry() {
        let registry = ObjectRelocationProofRegistry::aarch64_elf_production();
        let report = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry(
            "module.o",
            [
                ObjectRelocationKind::AArch64ElfOther(0x539),
                ObjectRelocationKind::AArch64ElfCall26,
            ],
            &registry,
        );

        assert!(!report.is_promotable());
        let reason = report
            .promotion_rejection_reason()
            .expect("unknown relocation should remain a promotion blocker");
        assert!(reason.contains("relocation 1337"));
    }

    #[test]
    fn relocation_inventory_rejects_unbound_aarch64_elf_tls_rows() {
        // The four emitted TLS kinds cite their value lane, but a registry
        // row alone NEVER promotes: without the per-object ELF reparse
        // binding the whole TLS sweep stays fail-closed.
        let registry = ObjectRelocationProofRegistry::aarch64_elf_production();
        let registered_tls = [
            ObjectRelocationKind::AArch64ElfTlsieAdrGottprelPage21,
            ObjectRelocationKind::AArch64ElfTlsieLd64GottprelLo12Nc,
            ObjectRelocationKind::AArch64ElfTlsleAddTprelHi12,
            ObjectRelocationKind::AArch64ElfTlsleAddTprelLo12Nc,
        ];
        let report = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry(
            "module.o",
            registered_tls,
            &registry,
        );

        assert!(!report.is_promotable());
        let reason = report
            .promotion_rejection_reason()
            .expect("unbound TLS relocation rows should reject promotion");
        assert!(reason.contains("lacks an independent reparse binding"));
    }

    #[test]
    fn checked_tprel_lo12_row_rejects_even_with_reparse_binding() {
        // The checked non-NC R_AARCH64_TLSLE_ADD_TPREL_LO12 has NO obligation
        // in the TLS lane and no emitter: it must fail closed even under the
        // full Certified composition, and the report must name it.
        let registry = ObjectRelocationProofRegistry::aarch64_elf_production();
        assert!(
            !registry.contains(ObjectRelocationKind::AArch64ElfTlsleAddTprelLo12),
            "a registry row for the unproven checked TPREL_LO12 would be \
             Certified authority backed by zero proofs"
        );
        let report = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry_and_binding(
            "aarch64-linux-tls-checked-lo12.o",
            [ObjectRelocationKind::AArch64ElfTlsleAddTprelLo12],
            &registry,
            ObjectProofBinding::ElfReparseEnforced,
        );
        assert!(!report.is_promotable(), "{report:?}");
        let reason = report
            .promotion_rejection_reason()
            .expect("unproven TLS row must reject promotion");
        assert!(reason.contains("R_AARCH64_TLSLE_ADD_TPREL_LO12"));
        assert!(reason.contains("no object relocation proof is registered"));
    }

    #[test]
    fn aarch64_elf_production_registry_has_exactly_the_named_rows() {
        let registry = ObjectRelocationProofRegistry::aarch64_elf_production();
        assert_eq!(registry.verified_kinds().count(), 12);

        for kind in ObjectRelocationKind::aarch64_elf_named_non_tls_rows() {
            assert!(
                registry.contains(*kind),
                "AArch64 ELF row {kind} must cite its value lane"
            );
            assert_eq!(
                registry.lane(*kind),
                Some("trust_cg_verify::aarch64_elf_reloc_proofs"),
                "AArch64 ELF row {kind} must cite the ordinary relocation lane"
            );
        }
        // The four EMITTED TLS kinds cite their OWN lane: the ABI range
        // constraints ride the obligations as preconditions (with
        // drop-refutes controls), so the rows promote through the same
        // value-lane + reparse-enforced-binding composition as the ordinary
        // eight — never through inherited credit. The checked non-NC
        // TPREL_LO12 has NO obligation in that lane and must stay OUT
        // (`checked_tprel_lo12_row_rejects_even_with_reparse_binding`).
        for kind in ObjectRelocationKind::aarch64_elf_named_tls_rows() {
            if *kind == ObjectRelocationKind::AArch64ElfTlsleAddTprelLo12 {
                assert!(
                    !registry.contains(*kind),
                    "the unproven checked TPREL_LO12 must stay fail-closed"
                );
                continue;
            }
            assert_eq!(
                registry.lane(*kind),
                Some("trust_cg_verify::aarch64_elf_tls_reloc_proofs"),
                "AArch64 ELF TLS row {kind} must cite the TLS relocation lane"
            );
        }
    }

    #[test]
    fn relocation_inventory_certifies_tlsle_rows_only_with_reparse_binding() {
        let registry = ObjectRelocationProofRegistry::aarch64_elf_production();
        let rows = [
            ObjectRelocationKind::AArch64ElfTlsleAddTprelHi12,
            ObjectRelocationKind::AArch64ElfTlsleAddTprelLo12Nc,
        ];

        // Solver evidence WITHOUT the per-object binding: fail-closed. The
        // registry row (the TLS value lane) alone never certifies output.
        let unbound = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry(
            "aarch64-linux-tls-localexec.o",
            rows,
            &registry,
        );
        assert!(!unbound.is_promotable(), "{unbound:?}");
        assert!(
            unbound
                .promotion_rejection_reason()
                .is_some_and(|r| r.contains("lacks an independent reparse binding"))
        );

        // Value lane + the ELF reparse-enforced binding: promotable — the
        // same composition the ordinary eight rows entered under. The TPREL
        // range constraints ride the obligations as preconditions with
        // drop-refutes controls (`aarch64_elf_tls_reloc_proofs`).
        let bound = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry_and_binding(
            "aarch64-linux-tls-localexec.o",
            rows,
            &registry,
            ObjectProofBinding::ElfReparseEnforced,
        );
        assert!(bound.is_promotable(), "{bound:?}");
        assert!(bound.promotion_rejection_reason().is_none());
        for entry in &bound.entries {
            assert_eq!(entry.status, RelocationInventoryStatus::Verified);
            assert!(entry.detail.contains("ELF reparse-enforced"));
        }
    }

    #[test]
    fn relocation_inventory_certifies_tlsie_rows_only_with_reparse_binding() {
        let registry = ObjectRelocationProofRegistry::aarch64_elf_production();
        let rows = [
            ObjectRelocationKind::AArch64ElfTlsieAdrGottprelPage21,
            ObjectRelocationKind::AArch64ElfTlsieLd64GottprelLo12Nc,
        ];

        let unbound = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry(
            "aarch64-linux-tls-initialexec.o",
            rows,
            &registry,
        );
        assert!(!unbound.is_promotable(), "{unbound:?}");
        assert!(
            unbound
                .promotion_rejection_reason()
                .is_some_and(|r| r.contains("lacks an independent reparse binding"))
        );

        let bound = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry_and_binding(
            "aarch64-linux-tls-initialexec.o",
            rows,
            &registry,
            ObjectProofBinding::ElfReparseEnforced,
        );
        assert!(bound.is_promotable(), "{bound:?}");
        assert!(bound.promotion_rejection_reason().is_none());
        for entry in &bound.entries {
            assert_eq!(entry.status, RelocationInventoryStatus::Verified);
            assert!(entry.detail.contains("ELF reparse-enforced"));
        }
    }

    #[test]
    fn x86_64_inventory_names_elf_macho_and_coff_rows() {
        assert_eq!(ObjectRelocationKind::x86_64_elf_named_rows().len(), 13);
        assert_eq!(ObjectRelocationKind::x86_64_macho_named_rows().len(), 10);
        assert_eq!(ObjectRelocationKind::x86_64_coff_named_rows().len(), 2);

        let names: Vec<_> = ObjectRelocationKind::x86_64_elf_named_rows()
            .iter()
            .chain(ObjectRelocationKind::x86_64_macho_named_rows())
            .chain(ObjectRelocationKind::x86_64_coff_named_rows())
            .map(ToString::to_string)
            .collect();

        for expected in [
            "x86-64 ELF R_X86_64_PC32",
            "x86-64 ELF R_X86_64_PLT32",
            "x86-64 ELF R_X86_64_GOTPCREL",
            "x86-64 Mach-O X86_64_RELOC_BRANCH",
            "x86-64 Mach-O X86_64_RELOC_GOT_LOAD",
            "x86-64 Mach-O X86_64_RELOC_SUBTRACTOR",
            "x86-64 Mach-O X86_64_RELOC_TLV",
            "x86-64 COFF IMAGE_REL_AMD64_REL32",
            "x86-64 COFF IMAGE_REL_AMD64_ADDR32NB",
        ] {
            assert!(
                names.iter().any(|name| name == expected),
                "missing named x86-64 object relocation inventory row {expected}"
            );
        }
    }

    #[test]
    fn every_production_target_with_one_relocation_fails_closed() {
        let cases = [
            (
                "aarch64-elf.o",
                ObjectRelocationKind::AArch64ElfCall26,
                ObjectRelocationProofRegistry::aarch64_elf_production(),
            ),
            (
                "aarch64-macho.o",
                ObjectRelocationKind::AArch64MachOPage21,
                ObjectRelocationProofRegistry::aarch64_macho_production(),
            ),
            (
                "x86_64-elf.o",
                ObjectRelocationKind::X86_64ElfPlt32,
                ObjectRelocationProofRegistry::x86_64_elf_production(),
            ),
            (
                "x86_64-macho.o",
                ObjectRelocationKind::X86_64MachOBranch,
                ObjectRelocationProofRegistry::x86_64_macho_production(),
            ),
            (
                "x86_64-coff.obj",
                ObjectRelocationKind::X86_64CoffRel32,
                ObjectRelocationProofRegistry::empty(),
            ),
        ];

        for (object_name, kind, registry) in cases {
            // Registry rows may exist (x86-64 Mach-O and x86-64 ELF register
            // their proved kinds), but WITHOUT the per-object
            // independent-check binding every production report must fail
            // closed regardless.
            let expected_rows = match object_name {
                "x86_64-macho.o" => 9,
                "aarch64-macho.o" => 9,
                "x86_64-elf.o" => 4,
                "aarch64-elf.o" => 12,
                _ => 0,
            };
            assert_eq!(
                registry.verified_kinds().count(),
                expected_rows,
                "{object_name}"
            );
            let report = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry(
                object_name,
                [kind],
                &registry,
            );
            assert!(!report.is_promotable(), "{object_name}: {report:?}");
            assert_eq!(report.uncovered_relocations().len(), 1, "{object_name}");
            assert_eq!(
                report.entries[0].status,
                RelocationInventoryStatus::Unverified
            );
        }
    }

    #[test]
    fn x86_64_elf_production_registry_covers_exactly_the_proved_rows() {
        let registry = ObjectRelocationProofRegistry::x86_64_elf_production();

        // Exactly the 4 kinds the ELF emitter produces AND that carry
        // standing solver-backed value proofs, each citing its lane; every
        // other named ELF row (never emitted, no proof) stays out.
        for kind in [
            ObjectRelocationKind::X86_64ElfAbs64,
            ObjectRelocationKind::X86_64ElfPc32,
            ObjectRelocationKind::X86_64ElfGotPcRel,
        ] {
            assert_eq!(
                registry.lane(kind),
                Some("trust_cg_verify::elf_data_reloc_proofs"),
                "data row {kind} must cite the ELF data-proof lane"
            );
        }
        assert_eq!(
            registry.lane(ObjectRelocationKind::X86_64ElfPlt32),
            Some("trust_cg_verify::elf_call_reloc_proofs"),
            "PLT32 must cite the ELF call-proof lane"
        );
        assert_eq!(registry.verified_kinds().count(), 4);
        for kind in [
            ObjectRelocationKind::X86_64ElfGot32,
            ObjectRelocationKind::X86_64ElfAbs32,
            ObjectRelocationKind::X86_64ElfAbs32S,
            ObjectRelocationKind::X86_64ElfAbs16,
            ObjectRelocationKind::X86_64ElfPc16,
            ObjectRelocationKind::X86_64ElfAbs8,
            ObjectRelocationKind::X86_64ElfPc8,
            ObjectRelocationKind::X86_64ElfGotPcRelX,
            ObjectRelocationKind::X86_64ElfRexGotPcRelX,
            ObjectRelocationKind::X86_64ElfOther(0xAB),
        ] {
            assert!(
                !registry.contains(kind),
                "unproven x86-64 ELF relocation row {kind} must stay fail-closed"
            );
        }
        for kind in ObjectRelocationKind::x86_64_macho_named_rows()
            .iter()
            .chain(ObjectRelocationKind::x86_64_coff_named_rows())
            .copied()
        {
            assert!(
                !registry.contains(kind),
                "non-ELF x86-64 relocation row {kind} must stay fail-closed"
            );
        }
    }

    #[test]
    fn x86_64_elf_data_and_call_rows_promote_only_with_reparse_binding() {
        let registry = ObjectRelocationProofRegistry::x86_64_elf_production();
        let rows = [
            ObjectRelocationKind::X86_64ElfPlt32,
            ObjectRelocationKind::X86_64ElfAbs64,
            ObjectRelocationKind::X86_64ElfPc32,
            ObjectRelocationKind::X86_64ElfGotPcRel,
        ];

        // Solver evidence WITHOUT the per-object binding: fail-closed.
        let unbound = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry(
            "x86_64-elf.o",
            rows,
            &registry,
        );
        assert!(!unbound.is_promotable(), "{unbound:?}");
        assert!(
            unbound
                .promotion_rejection_reason()
                .is_some_and(|r| r.contains("lacks an independent reparse binding"))
        );

        // Solver evidence + the Mach-O binding (WRONG container): still
        // fail-closed — an ENC-9 Mach-O reparse says nothing about ELF
        // records.
        let cross = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry_and_binding(
            "x86_64-elf.o",
            rows,
            &registry,
            ObjectProofBinding::MachOReparseEnforced,
        );
        assert!(!cross.is_promotable(), "{cross:?}");

        // Solver evidence + the ELF reparse-enforced binding: promotable.
        let bound = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry_and_binding(
            "x86_64-elf.o",
            rows,
            &registry,
            ObjectProofBinding::ElfReparseEnforced,
        );
        assert!(bound.is_promotable(), "{bound:?}");
        assert!(bound.promotion_rejection_reason().is_none());
        for entry in &bound.entries {
            assert_eq!(entry.status, RelocationInventoryStatus::Verified);
            assert!(entry.detail.contains("ELF reparse-enforced"));
        }
    }

    #[test]
    fn x86_64_elf_unproven_rows_reject_even_with_reparse_binding() {
        // GOT32 (and the other never-emitted named rows) have no value
        // proof: even a reparse-bound ELF object must fail closed on them,
        // and the report names the row precisely.
        let registry = ObjectRelocationProofRegistry::x86_64_elf_production();
        let report = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry_and_binding(
            "x86_64-elf-got32.o",
            [
                ObjectRelocationKind::X86_64ElfPc32,
                ObjectRelocationKind::X86_64ElfGot32,
            ],
            &registry,
            ObjectProofBinding::ElfReparseEnforced,
        );

        assert!(!report.is_promotable());
        assert_eq!(report.uncovered_relocations().len(), 1);
        let reason = report
            .promotion_rejection_reason()
            .expect("the GOT32 row must reject promotion");
        assert!(reason.contains("R_X86_64_GOT32"));
        assert!(reason.contains("no object relocation proof is registered"));
    }

    #[test]
    fn x86_64_macho_production_registry_covers_exactly_the_proved_rows() {
        let registry = ObjectRelocationProofRegistry::x86_64_macho_production();

        // Exactly the 9 kinds with standing solver-backed value proofs, each
        // citing its lane; TLV (no proof) and unknown rows stay out.
        for kind in [
            ObjectRelocationKind::X86_64MachOUnsigned,
            ObjectRelocationKind::X86_64MachOSigned,
            ObjectRelocationKind::X86_64MachOSigned1,
            ObjectRelocationKind::X86_64MachOSigned2,
            ObjectRelocationKind::X86_64MachOSigned4,
            ObjectRelocationKind::X86_64MachOGotLoad,
            ObjectRelocationKind::X86_64MachOGot,
            ObjectRelocationKind::X86_64MachOSubtractor,
        ] {
            assert_eq!(
                registry.lane(kind),
                Some("trust_cg_verify::macho_data_reloc_proofs"),
                "data row {kind} must cite the data-proof lane"
            );
        }
        assert_eq!(
            registry.lane(ObjectRelocationKind::X86_64MachOBranch),
            Some("trust_cg_verify::macho_call_reloc_proofs"),
            "BRANCH must cite the call-proof lane"
        );
        assert_eq!(registry.verified_kinds().count(), 9);
        assert!(!registry.contains(ObjectRelocationKind::X86_64MachOTlv));
        assert!(!registry.contains(ObjectRelocationKind::X86_64MachOOther(0xAB)));
        for kind in ObjectRelocationKind::x86_64_elf_named_rows()
            .iter()
            .chain(ObjectRelocationKind::x86_64_coff_named_rows())
            .copied()
        {
            assert!(
                !registry.contains(kind),
                "non-Mach-O x86-64 relocation row {kind} must stay fail-closed"
            );
        }
    }

    #[test]
    fn x86_64_inventory_rows_all_block_production_promotion() {
        let emitted = ObjectRelocationKind::x86_64_elf_named_rows()
            .iter()
            .chain(ObjectRelocationKind::x86_64_macho_named_rows())
            .chain(ObjectRelocationKind::x86_64_coff_named_rows())
            .copied();
        let registry = ObjectRelocationProofRegistry::x86_64_elf_production();
        let report = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry(
            "x86_64-module.o",
            emitted,
            &registry,
        );

        assert!(!report.is_promotable());
        assert_eq!(
            report.uncovered_relocations().len(),
            ObjectRelocationKind::x86_64_elf_named_rows().len()
                + ObjectRelocationKind::x86_64_macho_named_rows().len()
                + ObjectRelocationKind::x86_64_coff_named_rows().len()
        );
        let reason = report
            .promotion_rejection_reason()
            .expect("x86-64 relocation rows must reject promotion");
        assert!(reason.contains("x86_64-module.o[0]"));
        assert!(reason.contains("x86-64 ELF R_X86_64_64"));
        // The first row IS registered (Abs64 has a value-proof lane), but the
        // report was built UNBOUND, so it fails closed on the missing
        // per-object binding rather than a missing proof.
        assert!(reason.contains("lacks an independent reparse binding"));
    }

    #[test]
    fn x86_64_macho_inventory_rows_all_block_production_promotion() {
        let registry = ObjectRelocationProofRegistry::x86_64_macho_production();
        let report = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry(
            "x86_64-macho.o",
            ObjectRelocationKind::x86_64_macho_named_rows()
                .iter()
                .copied(),
            &registry,
        );

        assert!(!report.is_promotable());
        assert_eq!(
            report.uncovered_relocations().len(),
            ObjectRelocationKind::x86_64_macho_named_rows().len()
        );
        assert!(
            report
                .uncovered_relocations()
                .iter()
                .any(|entry| entry.kind == ObjectRelocationKind::X86_64MachOBranch)
        );
        let reason = report
            .promotion_rejection_reason()
            .expect("every Mach-O row must reject production promotion");
        assert!(reason.contains("x86-64 Mach-O X86_64_RELOC_UNSIGNED"));
    }

    #[test]
    fn x86_64_macho_data_and_call_rows_promote_only_with_reparse_binding() {
        let registry = ObjectRelocationProofRegistry::x86_64_macho_production();
        let rows = [
            ObjectRelocationKind::X86_64MachOBranch,
            ObjectRelocationKind::X86_64MachOUnsigned,
            ObjectRelocationKind::X86_64MachOSigned,
            ObjectRelocationKind::X86_64MachOSigned1,
            ObjectRelocationKind::X86_64MachOSigned2,
            ObjectRelocationKind::X86_64MachOSigned4,
            ObjectRelocationKind::X86_64MachOGotLoad,
            ObjectRelocationKind::X86_64MachOGot,
            ObjectRelocationKind::X86_64MachOSubtractor,
        ];

        // Solver evidence WITHOUT the per-object binding: fail-closed.
        let unbound = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry(
            "x86_64-macho.o",
            rows,
            &registry,
        );
        assert!(!unbound.is_promotable(), "{unbound:?}");
        assert!(
            unbound
                .promotion_rejection_reason()
                .is_some_and(|r| r.contains("lacks an independent reparse binding"))
        );

        // Solver evidence + ENC-9 reparse-enforced object: promotable.
        let bound = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry_and_binding(
            "x86_64-macho.o",
            rows,
            &registry,
            ObjectProofBinding::MachOReparseEnforced,
        );
        assert!(bound.is_promotable(), "{bound:?}");
        assert!(bound.promotion_rejection_reason().is_none());
        for entry in &bound.entries {
            assert_eq!(entry.status, RelocationInventoryStatus::Verified);
            assert!(entry.detail.contains("ENC-9 reparse-enforced"));
        }
    }

    #[test]
    fn x86_64_macho_production_registry_rejects_full_data_reloc_surface() {
        let registry = ObjectRelocationProofRegistry::x86_64_macho_production();
        let report = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry(
            "x86_64-macho-std-main.o",
            [
                ObjectRelocationKind::X86_64MachOBranch,
                ObjectRelocationKind::X86_64MachOUnsigned,
                ObjectRelocationKind::X86_64MachOSigned,
                ObjectRelocationKind::X86_64MachOGotLoad,
                ObjectRelocationKind::X86_64MachOSubtractor,
                ObjectRelocationKind::X86_64MachOUnsigned,
                // panic=unwind EH surface: section-based compact-unwind
                // UNSIGNED rows (one per frame-covered function) + the single
                // zPLR personality GOT row.
                ObjectRelocationKind::X86_64MachOUnsigned,
                ObjectRelocationKind::X86_64MachOUnsigned,
                ObjectRelocationKind::X86_64MachOGot,
            ],
            &registry,
        );

        assert!(!report.is_promotable(), "{report:?}");
        assert_eq!(report.uncovered_relocations().len(), report.entries.len());
        assert!(
            report
                .promotion_rejection_reason()
                .is_some_and(|reason| reason.contains("X86_64_RELOC_BRANCH"))
        );
    }

    #[test]
    fn x86_64_macho_tlv_rejects_even_with_reparse_binding() {
        // TLV has no value proof: even a reparse-bound object must fail
        // closed on it, and the report names it precisely.
        let registry = ObjectRelocationProofRegistry::x86_64_macho_production();
        let report = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry_and_binding(
            "x86_64-macho-tlv.o",
            [
                ObjectRelocationKind::X86_64MachOSigned,
                ObjectRelocationKind::X86_64MachOTlv,
            ],
            &registry,
            ObjectProofBinding::MachOReparseEnforced,
        );

        assert!(!report.is_promotable());
        assert_eq!(report.uncovered_relocations().len(), 1);
        let reason = report
            .promotion_rejection_reason()
            .expect("the TLV row must reject promotion");
        assert!(reason.contains("X86_64_RELOC_TLV"));
        assert!(reason.contains("no object relocation proof is registered"));
    }

    #[test]
    fn aarch64_macho_production_registry_covers_exactly_the_proved_rows() {
        let registry = ObjectRelocationProofRegistry::aarch64_macho_production();

        // Exactly the 9 kinds with standing solver-backed value proofs, each
        // citing its lane; unknown rows stay out.
        for kind in [
            ObjectRelocationKind::AArch64MachOPage21,
            ObjectRelocationKind::AArch64MachOPageoff12,
            ObjectRelocationKind::AArch64MachOGotLoadPage21,
            ObjectRelocationKind::AArch64MachOGotLoadPageoff12,
            ObjectRelocationKind::AArch64MachOUnsigned,
            ObjectRelocationKind::AArch64MachOSubtractor,
        ] {
            assert_eq!(
                registry.lane(kind),
                Some("trust_cg_verify::aarch64_macho_data_reloc_proofs"),
                "data row {kind} must cite the aarch64 Mach-O data-proof lane"
            );
        }
        assert_eq!(
            registry.lane(ObjectRelocationKind::AArch64MachOBranch26),
            Some("trust_cg_verify::aarch64_macho_call_reloc_proofs"),
            "BRANCH26 must cite the aarch64 Mach-O call-proof lane"
        );
        for kind in [
            ObjectRelocationKind::AArch64MachOTlvpLoadPage21,
            ObjectRelocationKind::AArch64MachOTlvpLoadPageoff12,
        ] {
            assert_eq!(
                registry.lane(kind),
                Some("trust_cg_verify::aarch64_macho_tlvp_reloc_proofs"),
                "TLVP row {kind} must cite the aarch64 Mach-O TLVP-proof lane"
            );
        }
        assert_eq!(registry.verified_kinds().count(), 9);
        assert!(!registry.contains(ObjectRelocationKind::AArch64MachOOther(0x7f)));
        for kind in ObjectRelocationKind::x86_64_macho_named_rows()
            .iter()
            .chain(ObjectRelocationKind::aarch64_elf_named_non_tls_rows())
            .chain(ObjectRelocationKind::aarch64_elf_named_tls_rows())
            .copied()
        {
            assert!(
                !registry.contains(kind),
                "non-AArch64-Mach-O relocation row {kind} must stay fail-closed"
            );
        }
    }

    #[test]
    fn aarch64_macho_rows_promote_only_with_reparse_binding() {
        let registry = ObjectRelocationProofRegistry::aarch64_macho_production();
        let rows = [
            ObjectRelocationKind::AArch64MachOPage21,
            ObjectRelocationKind::AArch64MachOPageoff12,
            ObjectRelocationKind::AArch64MachOGotLoadPage21,
            ObjectRelocationKind::AArch64MachOGotLoadPageoff12,
            ObjectRelocationKind::AArch64MachOBranch26,
            ObjectRelocationKind::AArch64MachOUnsigned,
            ObjectRelocationKind::AArch64MachOSubtractor,
            ObjectRelocationKind::AArch64MachOTlvpLoadPage21,
            ObjectRelocationKind::AArch64MachOTlvpLoadPageoff12,
        ];

        // Solver evidence WITHOUT the per-object binding: fail-closed (the
        // 54762bc4 doctrine — a lane alone is Trusted, not Certified).
        let unbound = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry(
            "aarch64-macho.o",
            rows,
            &registry,
        );
        assert!(!unbound.is_promotable(), "{unbound:?}");
        assert!(
            unbound
                .promotion_rejection_reason()
                .is_some_and(|r| r.contains("lacks an independent reparse binding"))
        );

        // Solver evidence + the ELF binding (WRONG container): still
        // fail-closed — an ELF reparse says nothing about Mach-O records.
        let cross = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry_and_binding(
            "aarch64-macho.o",
            rows,
            &registry,
            ObjectProofBinding::ElfReparseEnforced,
        );
        assert!(!cross.is_promotable(), "{cross:?}");

        // Solver evidence + ENC-9 reparse-enforced object: promotable.
        let bound = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry_and_binding(
            "aarch64-macho.o",
            rows,
            &registry,
            ObjectProofBinding::MachOReparseEnforced,
        );
        assert!(bound.is_promotable(), "{bound:?}");
        assert!(bound.promotion_rejection_reason().is_none());
        for entry in &bound.entries {
            assert_eq!(entry.status, RelocationInventoryStatus::Verified);
            assert!(entry.detail.contains("ENC-9 reparse-enforced"));
        }
    }

    #[test]
    fn aarch64_macho_other_rows_reject_even_with_reparse_binding() {
        // Unknown relocation kinds have no value proof: even a reparse-bound
        // object must fail closed on them, and the report names the row.
        let registry = ObjectRelocationProofRegistry::aarch64_macho_production();
        let report = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry_and_binding(
            "aarch64-macho-other.o",
            [
                ObjectRelocationKind::AArch64MachOUnsigned,
                ObjectRelocationKind::AArch64MachOOther(0x7f),
            ],
            &registry,
            ObjectProofBinding::MachOReparseEnforced,
        );

        assert!(!report.is_promotable());
        assert_eq!(report.uncovered_relocations().len(), 1);
        let reason = report
            .promotion_rejection_reason()
            .expect("the Other(0x7f) row must reject promotion");
        assert!(reason.contains("AArch64 Mach-O relocation 127"));
        assert!(reason.contains("no object relocation proof is registered"));
    }

    #[test]
    fn aarch64_registry_does_not_cover_x86_64_rows() {
        let registry = ObjectRelocationProofRegistry::aarch64_elf_production();
        let report = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry(
            "x86_64-module.o",
            [
                ObjectRelocationKind::X86_64ElfPlt32,
                ObjectRelocationKind::X86_64MachOBranch,
                ObjectRelocationKind::X86_64CoffRel32,
            ],
            &registry,
        );

        assert!(!report.is_promotable());
        let reason = report
            .promotion_rejection_reason()
            .expect("target-mismatched registry must not cover x86-64 relocation rows");
        assert!(reason.contains("x86-64 ELF R_X86_64_PLT32"));
    }
}
