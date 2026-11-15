// trust-cg-codegen/elf/writer.rs - ELF64 object file writer
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Assembles a complete ELF64 relocatable object file (.o).
//!
//! Layout of a typical ET_REL file:
//!
//! ```text
//! ┌──────────────────────────┐  offset 0
//! │    ELF64 header          │  64 bytes
//! ├──────────────────────────┤
//! │    .text section data    │  (machine code)
//! ├──────────────────────────┤
//! │    .data section data    │  (initialized data)
//! ├──────────────────────────┤
//! │    .rela.text entries    │  24 bytes each
//! ├──────────────────────────┤
//! │    .symtab entries       │  24 bytes each
//! ├──────────────────────────┤
//! │    .strtab data          │  (symbol name strings)
//! ├──────────────────────────┤
//! │    .shstrtab data        │  (section name strings)
//! ├──────────────────────────┤
//! │    Section header table  │  64 bytes per entry
//! └──────────────────────────┘
//! ```
//!
//! Note: .bss (SHT_NOBITS) has a section header but occupies no file space,
//! and the writer never holds its zero-fill in memory either: a NOBITS
//! section is a length.
//!
//! [`ElfWriter::write_checked`] is the only serializer. It checks every
//! section, relocation and symbol and re-parses the bytes against the
//! writer's intent before returning them, so no emitter can produce an
//! object that skipped those checks.

use super::constants::*;
use super::header::{Elf64Header, ElfMachine};
use super::metadata::{NoteGnuStack, SHF_GROUP, SHT_GROUP, SHT_NOTE, SectionGroup};
use super::reloc::Elf64Rela;
use super::section::Elf64Shdr;
use super::symbol::{Elf64Sym, ElfStringTable};

/// A symbol to be emitted in the ELF object file.
#[derive(Debug, Clone)]
pub struct ElfSymbol {
    /// Symbol name.
    pub name: String,
    /// Section index (0 = undefined, matches section header table index).
    pub section: u16,
    /// Offset within the section.
    pub value: u64,
    /// Symbol size in bytes.
    pub size: u64,
    /// Whether the symbol is globally visible.
    pub is_global: bool,
    /// Symbol type (STT_NOTYPE, STT_FUNC, STT_OBJECT, etc.).
    pub sym_type: u8,
    /// Whether the symbol is WEAK (coalescable / overridable). A weak defined
    /// symbol is emitted with the `STB_WEAK` binding (the ELF equivalent of a
    /// Mach-O `N_WEAK_DEF`), so multiple objects each defining it coalesce to one
    /// instead of a duplicate-strong-definition error. A weak symbol is treated
    /// as non-local (placed in the global partition of the symbol table).
    /// Defaults to `false`.
    pub is_weak: bool,
    /// Symbol visibility (`STV_DEFAULT` / `STV_HIDDEN` / `STV_PROTECTED`),
    /// the low two bits of `st_other`. Defaults to `STV_DEFAULT`.
    pub visibility: u8,
}

impl ElfSymbol {
    /// Whether the symbol lands in the LOCAL partition of `.symtab`.
    fn is_local(&self) -> bool {
        !self.is_global && !self.is_weak
    }
}

/// Stable handle to one symbol added through [`ElfWriter::add_checked_symbol`].
///
/// The handle is the symbol's INSERTION ordinal, never its symbol-table index:
/// [`ElfWriter::write_checked`] partitions the table locals-first (gABI
/// `sh_info` rule), so a symbol's final index depends on every LOCAL symbol
/// inserted anywhere before or after it. Resolve a handle with
/// [`ElfWriter::final_symbol_index`] only after every symbol has been added;
/// that call freezes the table so an index it issued cannot be shifted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ElfSymbolId(usize);

impl ElfSymbolId {
    /// The insertion ordinal this handle names.
    pub const fn ordinal(self) -> usize {
        self.0
    }
}

/// A symbol-table operation the checked ELF symbol API refuses.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ElfSymbolError {
    /// A symbol was added after [`ElfWriter::final_symbol_index`] issued an
    /// index. A late LOCAL symbol would shift every issued global index.
    #[error(
        "ELF symbol `{symbol}` was added after final symbol indices were issued; a late symbol can shift an issued relocation index (fail-closed)"
    )]
    SymbolTableFrozen { symbol: String },
    /// The symbol names a section header index the object does not have.
    #[error(
        "ELF symbol `{symbol}` names section {section}, but the object has {section_count} user section(s) (fail-closed)"
    )]
    SectionOutOfRange {
        symbol: String,
        section: u16,
        section_count: usize,
    },
    /// A defined symbol's `[value, value + size)` exceeds its section.
    #[error(
        "ELF symbol `{symbol}` covers [{value:#x}, +{size:#x}) beyond its {section_size:#x}-byte section (fail-closed)"
    )]
    RangeOutOfSection {
        symbol: String,
        value: u64,
        size: u64,
        section_size: u64,
    },
    /// An undefined reference must be `STB_GLOBAL` or `STB_WEAK`; a local
    /// undefined symbol can never be resolved.
    #[error("ELF symbol `{symbol}` is an undefined LOCAL symbol (fail-closed)")]
    LocalUndefined { symbol: String },
    /// `st_other` visibility outside `STV_DEFAULT`/`STV_HIDDEN`/`STV_PROTECTED`.
    #[error(
        "ELF symbol `{symbol}` carries unsupported st_other visibility {visibility} (fail-closed)"
    )]
    InvalidVisibility { symbol: String, visibility: u8 },
    /// A symbol name containing NUL cannot be represented in `.strtab`.
    #[error("ELF symbol name {symbol:?} contains NUL (fail-closed)")]
    NameContainsNul { symbol: String },
    /// A handle this writer did not issue.
    #[error("ELF symbol handle {ordinal} was not issued by this writer (fail-closed)")]
    UnknownSymbol { ordinal: usize },
    /// A COMDAT group signature binding the gABI or the group refuses.
    #[error("ELF symbol `{symbol}` cannot sign a COMDAT group: {reason} (fail-closed)")]
    InvalidGroupSignature {
        symbol: String,
        reason: &'static str,
    },
    /// The final index does not fit the 32-bit `r_info` symbol field.
    #[error("ELF symbol-table index {index} does not fit a 32-bit relocation field")]
    IndexOverflow { index: usize },
}

/// The largest `sh_addralign` the writer accepts, in bytes: 2^29, the
/// largest alignment rustc's `#[repr(align)]` accepts.
///
/// The writer aligns each section's FILE offset to its `sh_addralign` (the
/// reparse gate checks it), so an alignment is also zero padding laid down
/// before the section. The cap bounds that padding below 512 MiB per section
/// and keeps the `u64` layout arithmetic far from overflow; without it one
/// `2^40`-aligned section asked the writer for a terabyte of padding.
pub const MAX_ELF_SECTION_ALIGN: u64 = 1 << 29;

/// The `sh_flags` bits a caller may request for a section it adds: each one
/// needs no header field beyond `sh_flags` itself.
///
/// `SHF_GROUP` is not among them: [`ElfWriter::add_group_member_section`]
/// sets it on the members of a group this writer registered. Every other
/// bit is refused because the writer cannot honour it: it writes
/// `sh_link = 0` and `sh_info = 0` for a caller's section (so
/// `SHF_LINK_ORDER` and `SHF_INFO_LINK` would name the null section), no
/// compression header (`SHF_COMPRESSED`), no entry-size contract for
/// mergeable sections (`SHF_MERGE`, `SHF_STRINGS`), and gives the remaining
/// OS/processor-specific bits no meaning.
const CALLER_SECTION_FLAGS: u64 =
    SHF_WRITE | SHF_ALLOC | SHF_EXECINSTR | SHF_TLS | SHF_GNU_RETAIN | SHF_EXCLUDE;

/// Entry size of the ELF64 pointer tables (`SHT_INIT_ARRAY`,
/// `SHT_FINI_ARRAY`, `SHT_PREINIT_ARRAY`).
const ELF64_POINTER_SIZE: u64 = 8;

/// A section the writer refuses to add or to serialize.
///
/// Every `add_*` method that takes a caller's type, flags, alignment, entry
/// size or zero-fill content returns it before mutating the writer, and
/// [`ElfWriter::write_checked`] re-checks every section, so an object
/// carrying one of these shapes is never produced.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ElfSectionError {
    /// A section name containing NUL: `.shstrtab` would truncate it into a
    /// different name.
    #[error("ELF section name {name:?} contains NUL (fail-closed)")]
    NameContainsNul { name: String },
    /// `sh_addralign` must be 0 or 1 (no constraint) or a power of two.
    #[error("ELF section `{name}` alignment {align} is not a power of two (fail-closed)")]
    AlignmentNotPowerOfTwo { name: String, align: u64 },
    /// `sh_addralign` above [`MAX_ELF_SECTION_ALIGN`].
    #[error(
        "ELF section `{name}` alignment {align} exceeds the writer's maximum {max} (fail-closed)"
    )]
    AlignmentTooLarge { name: String, align: u64, max: u64 },
    /// A section type a caller cannot add.
    #[error("ELF section `{name}` has type {sh_type:#x}, which {reason} (fail-closed)")]
    UnsupportedType {
        name: String,
        sh_type: u32,
        reason: &'static str,
    },
    /// Flag bits the writer cannot honour for this section.
    #[error("ELF section `{name}` carries flag bits {flags:#x}: {reason} (fail-closed)")]
    UnsupportedFlags {
        name: String,
        flags: u64,
        reason: &'static str,
    },
    /// A type and flag combination the gABI gives no meaning.
    #[error(
        "ELF section `{name}` combines type {sh_type:#x} with flags {sh_flags:#x}: {reason} (fail-closed)"
    )]
    TypeFlagMismatch {
        name: String,
        sh_type: u32,
        sh_flags: u64,
        reason: &'static str,
    },
    /// An `sh_entsize` the section's type does not admit.
    #[error(
        "ELF section `{name}` of type {sh_type:#x} has entry size {entsize}: {reason} (fail-closed)"
    )]
    InvalidEntrySize {
        name: String,
        sh_type: u32,
        entsize: u64,
        reason: &'static str,
    },
    /// A table section whose size is not a whole number of entries.
    #[error(
        "ELF section `{name}` holds {size} byte(s), not a whole number of {entsize}-byte entries (fail-closed)"
    )]
    PartialEntry {
        name: String,
        size: u64,
        entsize: u64,
    },
    /// Content for an `SHT_NOBITS` section with a nonzero byte: zero-fill
    /// has no file bytes to carry it.
    #[error(
        "ELF zero-fill section `{name}` was given a nonzero byte at offset {offset}; SHT_NOBITS has no file bytes to carry it (fail-closed)"
    )]
    NobitsWithContent { name: String, offset: usize },
    /// A group handle this writer did not issue.
    #[error("ELF section group handle {group} was not issued by this writer (fail-closed)")]
    UnknownGroup { group: usize },
    /// A section whose `SHF_GROUP` flag disagrees with the groups that list
    /// it (the gABI requires exactly the members of an `SHT_GROUP` to carry
    /// it), or an `SHT_GROUP` section no registered group owns.
    #[error("ELF section `{name}` group membership is inconsistent: {reason} (fail-closed)")]
    GroupMembership { name: String, reason: &'static str },
    /// More section headers than `e_shnum` and a 16-bit `st_shndx` can
    /// name: the writer does not emit the gABI extended section numbering
    /// (`SHN_XINDEX`, `.symtab_shndx`), so every index at or above
    /// `SHN_LORESERVE` would be truncated into a different section.
    #[error(
        "ELF object needs {count} section headers; the writer names at most {max} without extended section numbering (fail-closed)"
    )]
    TooManySections { count: usize, max: usize },
}

/// `SHN_LORESERVE`: the first section index the gABI reserves. A section
/// header index at or above it needs extended numbering.
const SHN_LORESERVE: usize = 0xff00;

/// Internal section data held by the writer.
#[derive(Debug, Clone)]
struct SectionData {
    /// Section name (e.g., ".text").
    name: String,
    /// Section content bytes. Always empty for `SHT_NOBITS`, whose size is
    /// [`Self::zero_fill`]: zero-fill is never materialised.
    data: Vec<u8>,
    /// `sh_size` of an `SHT_NOBITS` section; 0 for every other type.
    zero_fill: u64,
    /// Section type (SHT_PROGBITS, SHT_NOBITS, ...).
    sh_type: u32,
    /// Section flags.
    sh_flags: u64,
    /// `sh_addralign` in BYTES (0 or 1: no constraint).
    align: u64,
    /// `sh_entsize`: the size of one fixed-size entry (8 for an
    /// `.init_array`/`.fini_array` of pointers), or 0 when the section holds
    /// no table of fixed-size entries.
    entsize: u64,
    /// Relocations for this section.
    relocations: Vec<Elf64Rela>,
}

impl SectionData {
    /// A caller's section: `data` is its content, or for `SHT_NOBITS` the
    /// zero-fill image, which must be all zero and is kept only as a length.
    fn new(
        name: &str,
        data: &[u8],
        sh_type: u32,
        sh_flags: u64,
        align: u64,
        entsize: u64,
    ) -> Result<Self, ElfSectionError> {
        let (data, zero_fill) = if sh_type == SHT_NOBITS {
            if let Some(offset) = data.iter().position(|&byte| byte != 0) {
                return Err(ElfSectionError::NobitsWithContent {
                    name: name.to_string(),
                    offset,
                });
            }
            (Vec::new(), data.len() as u64)
        } else {
            (data.to_vec(), 0)
        };
        Ok(Self {
            name: name.to_string(),
            data,
            zero_fill,
            sh_type,
            sh_flags,
            align,
            entsize,
            relocations: Vec::new(),
        })
    }

    /// An `SHT_NOBITS` section of `size` zero bytes: a length, never bytes.
    fn nobits(name: &str, size: u64, sh_flags: u64, align: u64) -> Self {
        Self {
            name: name.to_string(),
            data: Vec::new(),
            zero_fill: size,
            sh_type: SHT_NOBITS,
            sh_flags,
            align,
            entsize: 0,
            relocations: Vec::new(),
        }
    }

    /// `sh_size`: the content length, or the zero-fill length of an
    /// `SHT_NOBITS` section.
    fn size(&self) -> u64 {
        if self.sh_type == SHT_NOBITS {
            self.zero_fill
        } else {
            self.data.len() as u64
        }
    }

    /// Check a caller's section against what the writer can serialize
    /// faithfully. `group_member` says whether a registered COMDAT group
    /// lists the section: exactly those carry `SHF_GROUP`.
    ///
    /// An `SHT_GROUP` section is checked by [`ElfWriter::check_sections`],
    /// which knows whether a registered group owns it.
    fn validate(&self, group_member: bool) -> Result<(), ElfSectionError> {
        let name = || self.name.clone();
        if self.name.as_bytes().contains(&0) {
            return Err(ElfSectionError::NameContainsNul { name: name() });
        }
        if self.align > 1 && !self.align.is_power_of_two() {
            return Err(ElfSectionError::AlignmentNotPowerOfTwo {
                name: name(),
                align: self.align,
            });
        }
        if self.align > MAX_ELF_SECTION_ALIGN {
            return Err(ElfSectionError::AlignmentTooLarge {
                name: name(),
                align: self.align,
                max: MAX_ELF_SECTION_ALIGN,
            });
        }
        match self.sh_type {
            SHT_PROGBITS | SHT_NOBITS | SHT_NOTE | SHT_INIT_ARRAY | SHT_FINI_ARRAY
            | SHT_PREINIT_ARRAY => {}
            SHT_GROUP => {
                return Err(ElfSectionError::UnsupportedType {
                    name: name(),
                    sh_type: self.sh_type,
                    reason: "is opened with `add_comdat_group`, which derives the member list and signature from the final object",
                });
            }
            _ => {
                return Err(ElfSectionError::UnsupportedType {
                    name: name(),
                    sh_type: self.sh_type,
                    reason: "the writer does not serialize for a caller: it generates the symbol, string and relocation tables itself, and writes sh_link = sh_info = 0 for a caller's section",
                });
            }
        }
        let unsupported = self.sh_flags & !(CALLER_SECTION_FLAGS | SHF_GROUP);
        if unsupported != 0 {
            return Err(ElfSectionError::UnsupportedFlags {
                name: name(),
                flags: unsupported,
                reason: "only SHF_WRITE, SHF_ALLOC, SHF_EXECINSTR, SHF_TLS, SHF_GNU_RETAIN and SHF_EXCLUDE can be requested; the writer writes no sh_link/sh_info or compression header for a caller's section",
            });
        }
        let grouped = self.sh_flags & SHF_GROUP != 0;
        if grouped && !group_member {
            return Err(ElfSectionError::UnsupportedFlags {
                name: name(),
                flags: SHF_GROUP,
                reason: "SHF_GROUP marks a member of an SHT_GROUP section; add the section with `add_group_member_section`",
            });
        }
        if group_member && !grouped {
            return Err(ElfSectionError::GroupMembership {
                name: name(),
                reason: "a COMDAT group lists the section but it lacks SHF_GROUP",
            });
        }
        self.validate_type_flags()?;
        self.validate_entries()
    }

    /// The type/flag combinations the gABI gives meaning to.
    fn validate_type_flags(&self) -> Result<(), ElfSectionError> {
        let reason = if self.sh_flags & SHF_TLS != 0 {
            if !matches!(self.sh_type, SHT_PROGBITS | SHT_NOBITS) {
                Some("a thread-local template is .tdata (SHT_PROGBITS) or .tbss (SHT_NOBITS)")
            } else if self.sh_flags & SHF_ALLOC == 0 {
                Some("a thread-local template without SHF_ALLOC never reaches PT_TLS")
            } else if self.sh_flags & SHF_EXECINSTR != 0 {
                Some("a thread-local template is data, not code")
            } else {
                None
            }
        } else if matches!(
            self.sh_type,
            SHT_INIT_ARRAY | SHT_FINI_ARRAY | SHT_PREINIT_ARRAY
        ) {
            if self.sh_flags & SHF_ALLOC == 0 {
                Some(
                    "the loader runs a constructor or destructor table only from memory (SHF_ALLOC)",
                )
            } else if self.sh_flags & SHF_EXECINSTR != 0 {
                Some("a constructor or destructor table holds pointers, not code")
            } else {
                None
            }
        } else {
            None
        };
        match reason {
            Some(reason) => Err(ElfSectionError::TypeFlagMismatch {
                name: self.name.clone(),
                sh_type: self.sh_type,
                sh_flags: self.sh_flags,
                reason,
            }),
            None => Ok(()),
        }
    }

    /// `sh_entsize` against the type, and the size against the entry size.
    fn validate_entries(&self) -> Result<(), ElfSectionError> {
        let pointer_table = matches!(
            self.sh_type,
            SHT_INIT_ARRAY | SHT_FINI_ARRAY | SHT_PREINIT_ARRAY
        );
        if pointer_table && !matches!(self.entsize, 0 | ELF64_POINTER_SIZE) {
            return Err(ElfSectionError::InvalidEntrySize {
                name: self.name.clone(),
                sh_type: self.sh_type,
                entsize: self.entsize,
                reason: "an ELF64 constructor or destructor table holds 8-byte pointers",
            });
        }
        // A pointer table is a whole number of pointers whatever its
        // `sh_entsize` says; any other table follows its own entry size.
        let entsize = if pointer_table {
            ELF64_POINTER_SIZE
        } else {
            self.entsize
        };
        if entsize != 0 && !self.size().is_multiple_of(entsize) {
            return Err(ElfSectionError::PartialEntry {
                name: self.name.clone(),
                size: self.size(),
                entsize,
            });
        }
        Ok(())
    }
}

/// A COMDAT section group registered with [`ElfWriter::add_comdat_group`].
#[derive(Debug, Clone)]
struct GroupData {
    /// 0-based user-section index of the group's own `SHT_GROUP` section.
    section: usize,
    /// The group's signature symbol, bound through
    /// [`ElfWriter::bind_comdat_group_signature`] once that symbol exists
    /// (`sh_info` of the group section names it by its FINAL symbol-table
    /// index, resolved at serialization). An unbound group names no symbol
    /// and fails the reparse gate.
    signature: Option<ElfSymbolId>,
    /// 0-based user-section indices of the member sections, in insertion order.
    members: Vec<usize>,
}

/// Handle to a COMDAT section group created by [`ElfWriter::add_comdat_group`].
///
/// Member sections are added through
/// [`ElfWriter::add_group_member_section`]; because a group handle exists only
/// after its `SHT_GROUP` section was pushed, every member necessarily FOLLOWS
/// the group in the section header table, as the gABI requires.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ElfSectionGroupId(usize);

/// Assembles a complete ELF64 relocatable object file.
///
/// # Example
///
/// ```
/// use trust_cg_codegen::elf::{ElfWriter, ElfMachine};
///
/// let mut writer = ElfWriter::new(ElfMachine::AArch64);
/// // ARM64 NOP = 0xD503201F
/// writer.add_text_section(&[0x1F, 0x20, 0x03, 0xD5]);
/// writer.add_symbol("main", 1, 0, 4, true, 2); // STT_FUNC = 2
/// let bytes = writer.write_checked().expect("a well-formed object");
/// // bytes now contains a valid ELF .o file
/// ```
pub struct ElfWriter {
    /// Target architecture.
    machine: ElfMachine,
    /// Processor-specific `Elf64_Ehdr::e_flags` value.
    ///
    /// This defaults to zero and is changed only through
    /// [`set_e_flags`](Self::set_e_flags), keeping target-specific policy at the
    /// caller while avoiding post-serialization byte patching.
    e_flags: u32,
    /// User-defined sections (.text, .data, .bss).
    sections: Vec<SectionData>,
    /// Symbols to emit.
    symbols: Vec<ElfSymbol>,
    /// Set by [`Self::final_symbol_index`]: an index has been issued, so no
    /// further symbol may be added.
    symbols_frozen: bool,
    /// The first symbol an unchecked `add_*symbol` call appended AFTER the
    /// table froze. [`Self::write_checked`] refuses such an object.
    late_symbol: Option<String>,
    /// Final `.symtab` index per insertion ordinal, built in one pass by
    /// [`Self::final_symbol_index`] (rebuilt only if a late unchecked append
    /// grew the table, which [`Self::write_checked`] refuses anyway).
    final_indices: Vec<usize>,
    /// COMDAT section groups, in creation order.
    groups: Vec<GroupData>,
}

impl ElfWriter {
    /// Create a new empty ELF writer for the specified architecture.
    pub fn new(machine: ElfMachine) -> Self {
        Self {
            machine,
            e_flags: 0,
            sections: Vec::new(),
            symbols: Vec::new(),
            symbols_frozen: false,
            late_symbol: None,
            final_indices: Vec::new(),
            groups: Vec::new(),
        }
    }

    /// Set the processor-specific ELF header flags (`Elf64_Ehdr::e_flags`).
    ///
    /// The writer deliberately defaults this field to zero because the meaning
    /// of every bit is target-specific. Architecture pipelines should opt in
    /// with their ABI-defined constants before calling
    /// [`write_checked`](Self::write_checked).
    pub fn set_e_flags(&mut self, e_flags: u32) {
        self.e_flags = e_flags;
    }

    /// Append a section and return its 1-based section header table index
    /// (section 0 is always the null section).
    fn push_section(&mut self, section: SectionData) -> u16 {
        let idx = self.sections.len();
        self.sections.push(section);
        (idx + 1) as u16
    }

    /// Validate a caller's section (not a group member), then append it.
    fn push_checked_section(&mut self, section: SectionData) -> Result<u16, ElfSectionError> {
        section.validate(false)?;
        Ok(self.push_section(section))
    }

    /// Add a `.text` section (executable code) with the given machine code bytes.
    ///
    /// Returns the 1-based section index in the section header table.
    /// (Section 0 is always the null section.) Infallible: the type, flags
    /// and per-machine alignment are fixed and valid, and
    /// [`Self::write_checked`] re-checks every section anyway.
    pub fn add_text_section(&mut self, code: &[u8]) -> u16 {
        let align = match self.machine {
            ElfMachine::AArch64 => 4, // ARM64 instructions are 4-byte aligned
            ElfMachine::X86_64 => 16, // x86-64 typically 16-byte aligned
            ElfMachine::Riscv64 => 4, // RISC-V instructions are 4-byte aligned
        };
        self.push_section(Self::text_section(code, align))
    }

    /// The `.text` section record for `code` at `align` bytes.
    fn text_section(code: &[u8], align: u64) -> SectionData {
        SectionData {
            name: ".text".to_string(),
            data: code.to_vec(),
            zero_fill: 0,
            sh_type: SHT_PROGBITS,
            sh_flags: SHF_ALLOC | SHF_EXECINSTR,
            align,
            entsize: 0,
            relocations: Vec::new(),
        }
    }

    /// Like [`add_text_section`](Self::add_text_section) with an explicit
    /// `sh_addralign` in BYTES. Used when the code carries function-relative
    /// alignment padding (loop-head alignment) that must stay on-boundary in
    /// the linked image. Refuses an alignment that is not a power of two or
    /// exceeds [`MAX_ELF_SECTION_ALIGN`].
    pub fn add_text_section_with_align(
        &mut self,
        code: &[u8],
        align: u64,
    ) -> Result<u16, ElfSectionError> {
        self.push_checked_section(Self::text_section(code, align))
    }

    /// Add a `.data` section (initialized data) with the given data bytes.
    ///
    /// Returns the 1-based section index. Infallible for the same reason as
    /// [`Self::add_text_section`].
    pub fn add_data_section(&mut self, data: &[u8]) -> u16 {
        self.push_section(SectionData {
            name: ".data".to_string(),
            data: data.to_vec(),
            zero_fill: 0,
            sh_type: SHT_PROGBITS,
            sh_flags: SHF_ALLOC | SHF_WRITE,
            align: 8,
            entsize: 0,
            relocations: Vec::new(),
        })
    }

    /// Add a `.bss` section (uninitialized data) with the given size.
    ///
    /// BSS sections occupy no space in the file; only the section header
    /// records the size for runtime allocation. Infallible: any `u64` size is
    /// a representable `sh_size`, and nothing is allocated for it.
    ///
    /// Returns the 1-based section index.
    pub fn add_bss_section(&mut self, size: u64) -> u16 {
        self.push_section(SectionData::nobits(".bss", size, SHF_ALLOC | SHF_WRITE, 8))
    }

    /// Add a zero-fill (`SHT_NOBITS`) section such as `.bss` or `.tbss`.
    ///
    /// The section occupies no file bytes: its header records `size`, the
    /// caller's flags (for example `SHF_TLS` on `.tbss`) and `align` (in
    /// BYTES), and the loader or TLS runtime supplies zeroed memory. The
    /// writer keeps only the length — the zero-fill is never materialised,
    /// here or in the reparse intent — so a huge `.bss` costs no memory.
    ///
    /// Returns the 1-based section header table index, or the
    /// [`ElfSectionError`] for flags or an alignment the writer refuses.
    pub fn add_nobits_section(
        &mut self,
        name: &str,
        size: u64,
        sh_flags: u64,
        align: u64,
    ) -> Result<u16, ElfSectionError> {
        self.push_checked_section(SectionData::nobits(name, size, sh_flags, align))
    }

    /// Add a symbol to the object file.
    ///
    /// - `name`: Symbol name.
    /// - `section`: 1-based section index (0 = undefined/external).
    /// - `offset`: Byte offset within the section.
    /// - `size`: Symbol size in bytes.
    /// - `is_global`: Whether the symbol is globally visible.
    /// - `sym_type`: Symbol type (STT_NOTYPE=0, STT_OBJECT=1, STT_FUNC=2).
    pub fn add_symbol(
        &mut self,
        name: &str,
        section: u16,
        offset: u64,
        size: u64,
        is_global: bool,
        sym_type: u8,
    ) {
        self.push_unchecked_symbol(ElfSymbol {
            name: name.to_string(),
            section,
            value: offset,
            size,
            is_global,
            sym_type,
            is_weak: false,
            visibility: STV_DEFAULT,
        });
    }

    /// Add a symbol carrying the full trust-ir v41 symbol residue: binding
    /// (`is_global` / `is_weak`, exactly as [`Self::add_symbol`] and
    /// [`Self::add_weak_symbol`]) plus an explicit `STV_*` visibility in
    /// `st_other`. A weak symbol is placed in the global partition.
    #[allow(clippy::too_many_arguments)]
    pub fn add_symbol_with_attrs(
        &mut self,
        name: &str,
        section: u16,
        offset: u64,
        size: u64,
        is_global: bool,
        is_weak: bool,
        sym_type: u8,
        visibility: u8,
    ) {
        self.push_unchecked_symbol(ElfSymbol {
            name: name.to_string(),
            section,
            value: offset,
            size,
            is_global: is_global || is_weak,
            sym_type,
            is_weak,
            visibility,
        });
    }

    /// Add a WEAK symbol to the object file.
    ///
    /// A weak defined symbol is emitted with the `STB_WEAK` binding (a
    /// coalescable / overridable definition — the ELF equivalent of a Mach-O
    /// `N_WEAK_DEF`); it is placed in the global partition of the symbol table.
    /// Arguments mirror [`add_symbol`](Self::add_symbol).
    pub fn add_weak_symbol(
        &mut self,
        name: &str,
        section: u16,
        offset: u64,
        size: u64,
        sym_type: u8,
    ) {
        self.push_unchecked_symbol(ElfSymbol {
            name: name.to_string(),
            section,
            value: offset,
            size,
            // A weak symbol lives in the global partition (STB_WEAK, not local).
            is_global: true,
            sym_type,
            is_weak: true,
            visibility: STV_DEFAULT,
        });
    }

    /// Unchecked append shared by the legacy `add_*symbol` methods. They
    /// predate symbol handles and return nothing, so a late append is
    /// recorded here and refused by [`Self::write_checked`].
    fn push_unchecked_symbol(&mut self, symbol: ElfSymbol) {
        if self.symbols_frozen && self.late_symbol.is_none() {
            self.late_symbol = Some(symbol.name.clone());
        }
        self.symbols.push(symbol);
    }

    /// Add a symbol through the CHECKED symbol API and return its handle.
    ///
    /// The binding is exactly the symbol's fields: `is_weak` selects
    /// `STB_WEAK` (and implies the global partition), otherwise `is_global`
    /// selects `STB_GLOBAL` over `STB_LOCAL`. Before mutating the table the
    /// call refuses a table frozen by [`Self::final_symbol_index`], a section
    /// index the object does not have, a defined `[value, value + size)`
    /// range outside its section (a zero-fill section's range is its
    /// `sh_size`), an undefined LOCAL symbol, a visibility outside
    /// `STV_DEFAULT`/`STV_HIDDEN`/`STV_PROTECTED`, and a NUL in the name. An
    /// undefined `STB_GLOBAL`/`STB_WEAK` symbol may carry `STV_HIDDEN` or
    /// `STV_PROTECTED`: the gABI then requires its definition in the output
    /// being linked (or, for a weak one, resolves it to 0).
    pub fn add_checked_symbol(&mut self, symbol: ElfSymbol) -> Result<ElfSymbolId, ElfSymbolError> {
        if self.symbols_frozen {
            return Err(ElfSymbolError::SymbolTableFrozen {
                symbol: symbol.name,
            });
        }
        if symbol.name.as_bytes().contains(&0) {
            return Err(ElfSymbolError::NameContainsNul {
                symbol: symbol.name,
            });
        }
        if !matches!(symbol.visibility, STV_DEFAULT | STV_HIDDEN | STV_PROTECTED) {
            return Err(ElfSymbolError::InvalidVisibility {
                symbol: symbol.name,
                visibility: symbol.visibility,
            });
        }
        let is_global = symbol.is_global || symbol.is_weak;
        if symbol.section == 0 {
            if !is_global {
                return Err(ElfSymbolError::LocalUndefined {
                    symbol: symbol.name,
                });
            }
        } else {
            let Some(section) = self.sections.get(usize::from(symbol.section) - 1) else {
                return Err(ElfSymbolError::SectionOutOfRange {
                    symbol: symbol.name,
                    section: symbol.section,
                    section_count: self.sections.len(),
                });
            };
            let section_size = section.size();
            if symbol
                .value
                .checked_add(symbol.size)
                .is_none_or(|end| end > section_size)
            {
                return Err(ElfSymbolError::RangeOutOfSection {
                    symbol: symbol.name,
                    value: symbol.value,
                    size: symbol.size,
                    section_size,
                });
            }
        }
        let id = ElfSymbolId(self.symbols.len());
        self.symbols.push(ElfSymbol {
            is_global,
            ..symbol
        });
        Ok(id)
    }

    /// The FINAL `.symtab` index of `id`: the null symbol is 0, then locals in
    /// insertion order, then globals/weak in insertion order — exactly the
    /// order [`Self::write_checked`] serializes and the reparse gate
    /// reconstructs.
    ///
    /// The first call FREEZES the table: the checked API refuses any later
    /// symbol, and a later unchecked append makes [`Self::write_checked`]
    /// fail, because a late local would shift an index already written into
    /// a relocation.
    pub fn final_symbol_index(&mut self, id: ElfSymbolId) -> Result<u32, ElfSymbolError> {
        if id.0 >= self.symbols.len() {
            return Err(ElfSymbolError::UnknownSymbol { ordinal: id.0 });
        }
        // One linear pass per table size, not one scan per handle: a module
        // resolves every symbol's index, so a per-handle scan is quadratic.
        if self.final_indices.len() != self.symbols.len() {
            self.final_indices = self.locals_first_indices();
        }
        self.symbols_frozen = true;
        let index = self.final_indices[id.0];
        u32::try_from(index).map_err(|_| ElfSymbolError::IndexOverflow { index })
    }

    /// Every symbol in FINAL `.symtab` order, without the null symbol: entry
    /// `k` is the symbol serialized at index `k + 1`.
    ///
    /// Read-only (it does not freeze the table). An emitter that assigns
    /// symbol indices by its own arithmetic instead of
    /// [`Self::final_symbol_index`] checks each index it wrote into a
    /// relocation against this order before serializing: a LOCAL symbol it
    /// did not account for shifts every global behind it.
    pub fn symbols_in_final_order(&self) -> Vec<&ElfSymbol> {
        let locals = self.symbols.iter().filter(|symbol| symbol.is_local());
        let globals = self.symbols.iter().filter(|symbol| !symbol.is_local());
        locals.chain(globals).collect()
    }

    /// Every symbol's locals-first `.symtab` index, by insertion ordinal: the
    /// null symbol is 0, locals follow in insertion order, then every
    /// global/weak symbol in insertion order (the serialized partition).
    fn locals_first_indices(&self) -> Vec<usize> {
        let locals = self
            .symbols
            .iter()
            .filter(|candidate| candidate.is_local())
            .count();
        let mut next_local = 1;
        let mut next_global = 1 + locals;
        self.symbols
            .iter()
            .map(|symbol| {
                let next = if symbol.is_local() {
                    &mut next_local
                } else {
                    &mut next_global
                };
                let index = *next;
                *next += 1;
                index
            })
            .collect()
    }

    /// Add a relocation entry to the specified section.
    ///
    /// - `section_idx`: 0-based index into the user sections (NOT the section
    ///   header table index). For example, if .text was the first section added,
    ///   use 0.
    /// - `rela`: The relocation entry.
    pub fn add_relocation(&mut self, section_idx: usize, rela: Elf64Rela) {
        assert!(
            section_idx < self.sections.len(),
            "ELF relocation section index {section_idx} out of range for {} section(s)",
            self.sections.len()
        );
        self.sections[section_idx].relocations.push(rela);
    }

    /// Add a generic named section with explicit type, flags, and data.
    ///
    /// Returns the 1-based section header table index, or the
    /// [`ElfSectionError`] for a name, type, flag combination or alignment
    /// the writer cannot serialize faithfully. For `SHT_NOBITS` `data` is the
    /// zero-fill image: it must be all zero, and only its length is kept.
    pub fn add_section(
        &mut self,
        name: &str,
        data: &[u8],
        sh_type: u32,
        sh_flags: u64,
        align: u64,
    ) -> Result<u16, ElfSectionError> {
        self.add_section_with_entsize(name, data, sh_type, sh_flags, align, 0)
    }

    /// Add a `.note.GNU-stack` section to mark the stack as non-executable.
    ///
    /// GNU-convention marker: an empty `SHT_PROGBITS` section with flags 0.
    /// When every input object carries it, the static linker emits
    /// `PT_GNU_STACK` without `PF_X`; an input lacking it makes GNU ld assume
    /// that object needs an executable stack. Emitters add it after every
    /// other user section so earlier section indices are unchanged.
    ///
    /// Returns the 1-based section header table index.
    pub fn add_note_gnu_stack(&mut self) -> u16 {
        let note = NoteGnuStack::new();
        self.push_section(SectionData {
            name: NoteGnuStack::NAME.to_string(),
            data: note.section_bytes(),
            zero_fill: 0,
            sh_type: note.section_type(),
            sh_flags: note.section_flags(),
            align: note.section_align(),
            entsize: 0,
            relocations: Vec::new(),
        })
    }

    /// Add a generic named section with an explicit `sh_entsize`.
    ///
    /// Identical to [`Self::add_section`] except for the entry size, which a
    /// table section of fixed-size entries carries (8 for the pointer tables
    /// `.init_array`, `.fini_array` and `.preinit_array`); the section must
    /// hold a whole number of entries.
    ///
    /// Returns the 1-based section header table index.
    pub fn add_section_with_entsize(
        &mut self,
        name: &str,
        data: &[u8],
        sh_type: u32,
        sh_flags: u64,
        align: u64,
        entsize: u64,
    ) -> Result<u16, ElfSectionError> {
        let section = SectionData::new(name, data, sh_type, sh_flags, align, entsize)?;
        self.push_checked_section(section)
    }

    /// Open a COMDAT section group (`SHT_GROUP`, flag word `GRP_COMDAT`).
    ///
    /// The group's `SHT_GROUP` section is pushed NOW, so every member added
    /// afterwards through [`Self::add_group_member_section`] follows it in the
    /// section header table (the gABI placement rule). Its signature is a
    /// checked symbol handle bound later with
    /// [`Self::bind_comdat_group_signature`] (the signature symbol is defined
    /// IN a member, so it can only be added after the member section exists).
    /// Serialization fills in the rest from the final object: `sh_link` =
    /// `.symtab`, `sh_info` = the FINAL symbol-table index of the signature
    /// (the same locals-first index [`Self::final_symbol_index`] issues),
    /// `sh_entsize` = 4, and the member list = every member section followed
    /// by the `.rela.*` section of every member that has relocations (those
    /// carry `SHF_GROUP` too, so a linker that discards the group discards its
    /// relocations with it).
    pub fn add_comdat_group(&mut self) -> ElfSectionGroupId {
        let section = self.sections.len();
        self.push_section(SectionData {
            name: SectionGroup::NAME.to_string(),
            // Filled from the final section/symbol indices at serialization.
            data: Vec::new(),
            zero_fill: 0,
            sh_type: SHT_GROUP,
            sh_flags: 0,
            align: SectionGroup::ALIGN,
            entsize: SectionGroup::ENTRY_SIZE,
            relocations: Vec::new(),
        });
        let id = self.groups.len();
        self.groups.push(GroupData {
            section,
            signature: None,
            members: Vec::new(),
        });
        ElfSectionGroupId(id)
    }

    /// Bind COMDAT `group`'s signature to the checked symbol `signature`.
    ///
    /// Refuses a handle this writer did not issue, a second binding, a LOCAL
    /// symbol (a COMDAT signature must be visible to the linker to identify
    /// the group across objects) and a symbol not defined in one of the
    /// group's member sections (the group would name a definition it cannot
    /// discard).
    pub fn bind_comdat_group_signature(
        &mut self,
        group: ElfSectionGroupId,
        signature: ElfSymbolId,
    ) -> Result<(), ElfSymbolError> {
        let Some(symbol) = self.symbols.get(signature.0) else {
            return Err(ElfSymbolError::UnknownSymbol {
                ordinal: signature.0,
            });
        };
        let refuse = |reason: &'static str| ElfSymbolError::InvalidGroupSignature {
            symbol: symbol.name.clone(),
            reason,
        };
        let Some(data) = self.groups.get(group.0) else {
            return Err(refuse("the group handle was not issued by this writer"));
        };
        if data.signature.is_some() {
            return Err(refuse("the group's signature is already bound"));
        }
        if symbol.is_local() {
            return Err(refuse("a COMDAT signature must be a non-local symbol"));
        }
        if !data
            .members
            .iter()
            .any(|&member| usize::from(symbol.section) == member + 1)
        {
            return Err(refuse(
                "the signature symbol is not defined in a member section of the group",
            ));
        }
        self.groups[group.0].signature = Some(signature);
        Ok(())
    }

    /// Add a section that belongs to COMDAT `group` (it gets `SHF_GROUP`).
    ///
    /// Arguments mirror [`Self::add_section_with_entsize`], and the section is
    /// checked the same way. Returns the 1-based section header table index,
    /// or the [`ElfSectionError`] for a group handle this writer did not
    /// issue or a section it refuses.
    #[allow(clippy::too_many_arguments)]
    pub fn add_group_member_section(
        &mut self,
        group: ElfSectionGroupId,
        name: &str,
        data: &[u8],
        sh_type: u32,
        sh_flags: u64,
        align: u64,
        entsize: u64,
    ) -> Result<u16, ElfSectionError> {
        if group.0 >= self.groups.len() {
            return Err(ElfSectionError::UnknownGroup { group: group.0 });
        }
        let section = SectionData::new(name, data, sh_type, sh_flags | SHF_GROUP, align, entsize)?;
        section.validate(true)?;
        let index = self.push_section(section);
        self.groups[group.0].members.push(usize::from(index) - 1);
        Ok(index)
    }

    /// The `SHT_GROUP` section payload for every group, keyed by user-section
    /// index: `GRP_COMDAT`, then each member's section header index, then the
    /// header index of each member's `.rela.*` section (in member order).
    fn group_payloads(
        &self,
        rela_shndx: &[Option<u32>],
        symtab_shdr_idx: u32,
        final_symbol_index: impl Fn(ElfSymbolId) -> u32,
    ) -> Vec<Option<(Vec<u8>, u32)>> {
        let mut payloads = vec![None; self.sections.len()];
        for group in &self.groups {
            let mut members: Vec<u32> = group
                .members
                .iter()
                .map(|&member| (member + 1) as u32)
                .collect();
            members.extend(
                group
                    .members
                    .iter()
                    .filter_map(|&member| rela_shndx[member]),
            );
            // An unbound signature is index 0: the reparse gate refuses the
            // unnamed group.
            let signature_index = group.signature.map_or(0, &final_symbol_index);
            let bytes =
                SectionGroup::new(symtab_shdr_idx, signature_index, members).section_bytes();
            payloads[group.section] = Some((bytes, signature_index));
        }
        payloads
    }

    /// Build the intended-object description for the ELF reparse gate.
    ///
    /// Derived from the writer's HIGH-LEVEL input model (sections, symbols,
    /// relocation records as supplied), never from the computed file layout —
    /// the gate ([`crate::elf::reparse`]) derives offsets from the reparsed
    /// bytes and cross-checks them, so a layout bug in the serializer cannot
    /// hide. A zero-fill section is described by its size alone.
    pub fn reparse_object_intent(&self) -> crate::elf::reparse::ElfObjectIntent {
        use crate::elf::reparse::{
            ElfGroupIntent, ElfObjectIntent, ElfRelocIntent, ElfSectionIntent, ElfSymbolIntent,
        };
        ElfObjectIntent {
            machine: self.machine.to_e_machine(),
            sections: self
                .sections
                .iter()
                .map(|sec| ElfSectionIntent {
                    name: sec.name.clone(),
                    sh_type: sec.sh_type,
                    sh_flags: sec.sh_flags,
                    align: sec.align,
                    entsize: sec.entsize,
                    size: sec.size(),
                    // A group's payload is derived from final indices; the
                    // gate recomputes it independently from `groups` below.
                    // A NOBITS section's `data` is empty.
                    data: sec.data.clone(),
                })
                .collect(),
            groups: self
                .groups
                .iter()
                .map(|group| ElfGroupIntent {
                    section: group.section,
                    signature: group
                        .signature
                        .and_then(|id| self.symbols.get(id.0))
                        .map(|symbol| symbol.name.clone())
                        .unwrap_or_default(),
                    members: group.members.clone(),
                })
                .collect(),
            section_relocs: self
                .sections
                .iter()
                .map(|sec| {
                    sec.relocations
                        .iter()
                        .map(|rela| ElfRelocIntent {
                            r_offset: rela.r_offset,
                            symbol_index: rela.symbol_index,
                            reloc_type: rela.reloc_type,
                            r_addend: rela.r_addend,
                        })
                        .collect()
                })
                .collect(),
            symbols: self
                .symbols
                .iter()
                .map(|sym| ElfSymbolIntent {
                    name: sym.name.clone(),
                    section: sym.section,
                    value: sym.value,
                    size: sym.size,
                    is_global: sym.is_global,
                    is_weak: sym.is_weak,
                    sym_type: sym.sym_type,
                    visibility: sym.visibility,
                })
                .collect(),
        }
    }

    /// Check every section the writer holds before serialization: each
    /// caller-shaped section against [`SectionData::validate`] (with its
    /// group membership), and each `SHT_GROUP` section against the group
    /// that owns it.
    ///
    /// The `add_*` methods already refuse every shape checked here, so this
    /// pass is the serializer's own guarantee rather than the first line of
    /// defence: an object that reaches the bytes has passed it whatever path
    /// built the section list.
    fn check_sections(&self) -> Result<(), ElfSectionError> {
        // null + user sections + one `.rela.*` per relocated section +
        // `.symtab`, `.strtab`, `.shstrtab`.
        let relocated = self
            .sections
            .iter()
            .filter(|section| !section.relocations.is_empty())
            .count();
        let count = 1 + self.sections.len() + relocated + 3;
        if count > SHN_LORESERVE {
            return Err(ElfSectionError::TooManySections {
                count,
                max: SHN_LORESERVE,
            });
        }
        let mut member = vec![false; self.sections.len()];
        let mut group_section = vec![false; self.sections.len()];
        for group in &self.groups {
            group_section[group.section] = true;
            for &index in &group.members {
                member[index] = true;
            }
        }
        for (index, section) in self.sections.iter().enumerate() {
            if section.sh_type == SHT_GROUP {
                if !group_section[index] {
                    return Err(ElfSectionError::GroupMembership {
                        name: section.name.clone(),
                        reason: "an SHT_GROUP section that no registered group owns",
                    });
                }
                continue;
            }
            section.validate(member[index])?;
        }
        Ok(())
    }

    /// Check every relocation record against the target machine's psABI
    /// before serialization.
    ///
    /// Three ways a relocation silently corrupts the linked image:
    ///
    /// * an `r_type` this machine does not define — the linker's own table
    ///   decides what to patch and how wide, and nothing here can check it,
    ///   so the record is refused instead of guessed at (an x86-64 type
    ///   number reaching an AArch64 object is exactly this case);
    /// * a field running past the end of its section — the linker writes
    ///   bytes belonging to whatever the layout put next;
    /// * any relocation against a zero-fill (`SHT_NOBITS`) section, which has
    ///   no file bytes to patch.
    ///
    /// `R_RISCV_RELAX` is checked additionally: it is a MARKER on the
    /// relocation it shares an `r_offset` with, and standing alone it names
    /// nothing to relax.
    fn check_relocation_fields(&self) -> Result<(), crate::elf::reparse::ElfReparseError> {
        let err = |message: String| crate::elf::reparse::ElfReparseError { message };
        for section in &self.sections {
            if section.sh_type == SHT_NOBITS && !section.relocations.is_empty() {
                return Err(err(format!(
                    "zero-fill section `{}` carries {} relocation(s); SHT_NOBITS has no file bytes to patch (fail-closed)",
                    section.name,
                    section.relocations.len()
                )));
            }
            let section_size = section.size();
            for rela in &section.relocations {
                let Some(width) =
                    crate::elf::reloc::elf_relocation_field_width(self.machine, rela.reloc_type)
                else {
                    return Err(err(format!(
                        "section `{}` carries unknown relocation type {} for e_machine {} (fail-closed)",
                        section.name,
                        rela.reloc_type,
                        self.machine.to_e_machine()
                    )));
                };
                let end = rela.r_offset.checked_add(width).ok_or_else(|| {
                    err(format!(
                        "section `{}` relocation R_TYPE {} at {:#x} overflows its field end (fail-closed)",
                        section.name, rela.reloc_type, rela.r_offset
                    ))
                })?;
                if end > section_size {
                    return Err(err(format!(
                        "section `{}` relocation R_TYPE {} patches [{:#x}, {:#x}) beyond its {:#x}-byte section (fail-closed)",
                        section.name, rela.reloc_type, rela.r_offset, end, section_size
                    )));
                }
                if self.machine == ElfMachine::Riscv64
                    && rela.reloc_type == crate::elf::constants::R_RISCV_RELAX
                    && !section.relocations.iter().any(|other| {
                        other.r_offset == rela.r_offset
                            && other.reloc_type != crate::elf::constants::R_RISCV_RELAX
                            && other.reloc_type != crate::elf::constants::R_RISCV_NONE
                    })
                {
                    return Err(err(format!(
                        "section `{}` carries an R_RISCV_RELAX marker at {:#x} with no relocation to relax (fail-closed)",
                        section.name, rela.r_offset
                    )));
                }
            }
        }
        Ok(())
    }

    /// Serialize the object AND run the ELF reparse gate over the produced
    /// bytes (the ENC-9 sibling; see [`crate::elf::reparse`]). This is the
    /// writer's ONLY serializer.
    ///
    /// Before a byte is laid down it checks every section
    /// ([`ElfSectionError`]: name, type, flags, alignment, entry size, group
    /// membership), every relocation (psABI type, field bounds, RISC-V
    /// `RELAX` pairing, none into zero-fill) and the symbol table (no symbol
    /// appended after [`Self::final_symbol_index`] froze it). In the default
    /// `enforce` mode a structural disagreement between the reparsed bytes
    /// and the writer's intent then FAILS the write closed — a
    /// promoted-but-unreparsed object cannot exist. This is the per-object
    /// binding half that the object-relocation inventory's
    /// `ObjectProofBinding::ElfReparseEnforced` claims.
    pub fn write_checked(&self) -> Result<Vec<u8>, crate::elf::reparse::ElfReparseError> {
        self.check_sections()
            .map_err(|error| crate::elf::reparse::ElfReparseError {
                message: error.to_string(),
            })?;
        self.check_relocation_fields()?;
        if let Some(symbol) = &self.late_symbol {
            return Err(crate::elf::reparse::ElfReparseError {
                message: format!(
                    "symbol `{symbol}` was appended after final symbol indices were issued; relocation symbol indices may have shifted (fail-closed)"
                ),
            });
        }
        let bytes = self.serialize()?;
        let intent = self.reparse_object_intent();
        crate::elf::reparse::run_elf_reparse_gate(
            &intent,
            &bytes,
            crate::elf::reparse::elf_reparse_mode(),
        )?;
        Ok(bytes)
    }

    /// Lay the complete ELF .o file out as a byte vector: header, section
    /// data, relocations, symbol table, string tables, and the section
    /// header table (at the end).
    ///
    /// Private: it checks nothing, so [`Self::write_checked`] is its only
    /// caller.
    fn serialize(&self) -> Result<Vec<u8>, crate::elf::reparse::ElfReparseError> {
        // --- Build section header string table (.shstrtab) ---
        let mut shstrtab = ElfStringTable::new();

        // Pre-register all section names we'll need.
        // Collect name indices for each user section.
        let mut user_section_name_indices: Vec<u32> = Vec::new();
        for sec in &self.sections {
            let idx = shstrtab.add(&sec.name);
            user_section_name_indices.push(idx);
        }

        // Also register names for generated sections.
        // We need: .rela.X for each section with relocations, .symtab, .strtab, .shstrtab
        let mut rela_name_indices: Vec<Option<u32>> = Vec::new();
        for sec in &self.sections {
            if sec.relocations.is_empty() {
                rela_name_indices.push(None);
            } else {
                let rela_name = format!(".rela{}", sec.name);
                let idx = shstrtab.add(&rela_name);
                rela_name_indices.push(Some(idx));
            }
        }

        let symtab_name_idx = shstrtab.add(".symtab");
        let strtab_name_idx = shstrtab.add(".strtab");
        let shstrtab_name_idx = shstrtab.add(".shstrtab");

        // --- Build symbol string table (.strtab) ---
        let mut strtab = ElfStringTable::new();

        // Partition symbols: locals first, then globals (ELF requirement).
        let mut local_syms: Vec<&ElfSymbol> = Vec::new();
        let mut global_syms: Vec<&ElfSymbol> = Vec::new();
        for sym in &self.symbols {
            // Weak symbols, like globals, must live in the global partition of
            // the symbol table (after the local/global boundary `sh_info`).
            if sym.is_global || sym.is_weak {
                global_syms.push(sym);
            } else {
                local_syms.push(sym);
            }
        }

        // Build Elf64_Sym entries: null symbol + locals + globals.
        let mut sym_entries: Vec<Elf64Sym> = Vec::new();
        sym_entries.push(Elf64Sym::null()); // Index 0 is always the null symbol.

        // Map from original symbol index to final symbol table index.
        // (We need this for relocations, but since the user provides symbol
        //  indices directly in Elf64Rela, we assume they account for the
        //  null symbol at index 0.)

        for sym in local_syms.iter().chain(global_syms.iter()) {
            let name_idx = strtab.add(&sym.name);
            let binding = if sym.is_weak {
                STB_WEAK
            } else if sym.is_global {
                STB_GLOBAL
            } else {
                STB_LOCAL
            };
            sym_entries.push(Elf64Sym::new(
                name_idx,
                binding,
                sym.sym_type,
                sym.visibility,
                sym.section,
                sym.value,
                sym.size,
            ));
        }

        // Number of local symbols (including null symbol): for .symtab sh_info.
        let num_local_plus_null = 1 + local_syms.len() as u32;

        // --- Compute section header table layout ---
        //
        // Section header table indices:
        //   0: null
        //   1..N: user sections (.text, .data, .bss, ...)
        //   N+1..M: .rela.X sections (one per user section with relocs)
        //   M+1: .symtab
        //   M+2: .strtab
        //   M+3: .shstrtab
        //
        // Total: 1 + num_user_sections + num_rela_sections + 3

        let num_user_sections = self.sections.len();
        let num_rela_sections = self
            .sections
            .iter()
            .filter(|s| !s.relocations.is_empty())
            .count();
        let total_sections = 1 + num_user_sections + num_rela_sections + 3;

        // Compute .symtab and .strtab section header indices.
        let symtab_shdr_idx = (1 + num_user_sections + num_rela_sections) as u32;
        let strtab_shdr_idx = symtab_shdr_idx + 1;
        let shstrtab_shdr_idx = strtab_shdr_idx + 1;

        // Header index of each user section's `.rela.*` section (they follow
        // the user sections in user-section order).
        let mut rela_shndx: Vec<Option<u32>> = Vec::with_capacity(num_user_sections);
        let mut next_rela_shndx = (1 + num_user_sections) as u32;
        for sec in &self.sections {
            if sec.relocations.is_empty() {
                rela_shndx.push(None);
            } else {
                rela_shndx.push(Some(next_rela_shndx));
                next_rela_shndx += 1;
            }
        }
        // User sections that belong to a COMDAT group: their `.rela.*`
        // sections join the group too (and carry `SHF_GROUP`).
        let mut in_group = vec![false; num_user_sections];
        for group in &self.groups {
            for &member in &group.members {
                in_group[member] = true;
            }
        }
        // COMDAT group payloads. `sh_info` is the signature's FINAL symbol
        // index: the same locals-first index `final_symbol_index` issues for
        // its checked handle. An unbound signature yields 0, which the reparse
        // gate rejects (the group would be unnamed).
        let final_indices = self.locals_first_indices();
        let group_payloads = self.group_payloads(&rela_shndx, symtab_shdr_idx, |signature| {
            final_indices
                .get(signature.0)
                .and_then(|&index| u32::try_from(index).ok())
                .unwrap_or(0)
        });
        let section_bytes = |i: usize| -> &[u8] {
            match &group_payloads[i] {
                Some((bytes, _)) => bytes.as_slice(),
                None => self.sections[i].data.as_slice(),
            }
        };

        // --- Compute file offsets ---
        let mut offset: u64 = ELF64_EHDR_SIZE as u64;

        // User section data offsets. A NOBITS section records the aligned
        // current file position (the GNU `as` convention) but consumes no
        // file bytes.
        let mut section_offsets: Vec<u64> = Vec::new();
        for (i, sec) in self.sections.iter().enumerate() {
            let align = sec.align.max(1);
            let misalign = offset % align;
            let aligned = if misalign == 0 {
                offset
            } else {
                offset + (align - misalign)
            };
            section_offsets.push(aligned);
            if sec.sh_type != SHT_NOBITS {
                offset = aligned + section_bytes(i).len() as u64;
            }
        }

        // .rela.X section offsets.
        // Align to 8 bytes.
        let align8 = |off: &mut u64| {
            let m = *off % 8;
            if m != 0 {
                *off += 8 - m;
            }
        };
        align8(&mut offset);

        let mut rela_offsets: Vec<Option<u64>> = Vec::new();
        for sec in &self.sections {
            if sec.relocations.is_empty() {
                rela_offsets.push(None);
            } else {
                rela_offsets.push(Some(offset));
                offset += (sec.relocations.len() * ELF64_RELA_SIZE) as u64;
            }
        }

        // .symtab offset.
        align8(&mut offset);
        let symtab_offset = offset;
        let symtab_size = (sym_entries.len() * ELF64_SYM_SIZE) as u64;
        offset += symtab_size;

        // .strtab offset.
        let strtab_offset = offset;
        let strtab_size = strtab.size() as u64;
        offset += strtab_size;

        // .shstrtab offset.
        let shstrtab_offset = offset;
        let shstrtab_size = shstrtab.size() as u64;
        offset += shstrtab_size;

        // Section header table offset (aligned to 8 bytes).
        align8(&mut offset);
        let sh_offset = offset;

        // --- Write the file ---
        let total_size = (sh_offset + (total_sections * ELF64_SHDR_SIZE) as u64) as usize;
        let mut buf = Vec::with_capacity(total_size);

        // 1. ELF header.
        let mut header = Elf64Header::new(
            self.machine,
            sh_offset,
            total_sections as u16,
            shstrtab_shdr_idx as u16,
        );
        // `SHF_GNU_RETAIN` is a GNU extension linkers only honor under the GNU
        // OSABI (LLVM's ELF writer makes the same flip when it sees one).
        if self
            .sections
            .iter()
            .any(|sec| sec.sh_flags & SHF_GNU_RETAIN != 0)
        {
            header.osabi = ELFOSABI_GNU;
        }
        header.flags = self.e_flags;
        header.write(&mut buf);

        // 2. User section data.
        for (i, sec) in self.sections.iter().enumerate() {
            if sec.sh_type == SHT_NOBITS {
                continue; // BSS has no file data
            }
            // Pad to section offset.
            let target = section_offsets[i] as usize;
            while buf.len() < target {
                buf.push(0);
            }
            buf.extend_from_slice(section_bytes(i));
        }

        // 3. .rela.X entries.
        for (i, sec) in self.sections.iter().enumerate() {
            if sec.relocations.is_empty() {
                continue;
            }
            if let Some(rela_off) = rela_offsets[i] {
                let target = rela_off as usize;
                while buf.len() < target {
                    buf.push(0);
                }
                for rela in &sec.relocations {
                    buf.extend_from_slice(&rela.encode());
                }
            }
        }

        // 4. .symtab entries.
        while buf.len() < symtab_offset as usize {
            buf.push(0);
        }
        for sym in &sym_entries {
            buf.extend_from_slice(&sym.encode());
        }

        // 5. .strtab data, then 6. .shstrtab data, each exactly where its
        // section header will say it starts: the headers are written from the
        // precomputed offsets, so a drifted cursor would point both tables at
        // the wrong bytes.
        for (table, offset, bytes) in [
            (".strtab", strtab_offset, strtab.as_bytes()),
            (".shstrtab", shstrtab_offset, shstrtab.as_bytes()),
        ] {
            if buf.len() as u64 != offset {
                return Err(crate::elf::reparse::ElfReparseError {
                    message: format!(
                        "ELF {table} would be written at file offset {:#x} but its header records {offset:#x} (fail-closed)",
                        buf.len()
                    ),
                });
            }
            buf.extend_from_slice(bytes);
        }

        // 7. Section header table.
        while buf.len() < sh_offset as usize {
            buf.push(0);
        }

        // Section 0: null.
        Elf64Shdr::null().write(&mut buf);

        // User sections.
        for (i, sec) in self.sections.iter().enumerate() {
            let shdr = match sec.sh_type {
                SHT_NOBITS => {
                    let mut shdr =
                        Elf64Shdr::bss(user_section_name_indices[i], sec.zero_fill, sec.align);
                    // Honor the caller's flags (`.tbss` carries SHF_TLS and
                    // retained zero-fill carries SHF_GNU_RETAIN). The offset
                    // is the aligned file position; NOBITS has no file bytes.
                    shdr.sh_flags = sec.sh_flags;
                    shdr.sh_offset = section_offsets[i];
                    shdr
                }
                _ => {
                    // A COMDAT group links the symbol table and names its
                    // signature symbol by final index.
                    let (sh_link, sh_info) = match &group_payloads[i] {
                        Some((_, signature_index)) => (symtab_shdr_idx, *signature_index),
                        None => (0, 0),
                    };
                    Elf64Shdr {
                        sh_name: user_section_name_indices[i],
                        sh_type: sec.sh_type,
                        sh_flags: sec.sh_flags,
                        sh_addr: 0,
                        sh_offset: section_offsets[i],
                        sh_size: section_bytes(i).len() as u64,
                        sh_link,
                        sh_info,
                        sh_addralign: sec.align,
                        sh_entsize: sec.entsize,
                    }
                }
            };
            shdr.write(&mut buf);
        }

        // .rela.X sections.
        // We need to track the section header index for each user section
        // to fill in sh_info on the .rela sections.
        for (i, sec) in self.sections.iter().enumerate() {
            if sec.relocations.is_empty() {
                continue;
            }
            if let (Some(name_idx), Some(rela_off)) = (rela_name_indices[i], rela_offsets[i]) {
                let mut rela_shdr = Elf64Shdr::rela(
                    name_idx,
                    rela_off,
                    (sec.relocations.len() * ELF64_RELA_SIZE) as u64,
                    symtab_shdr_idx, // sh_link → .symtab
                    (i + 1) as u32,  // sh_info → user section index (1-based)
                );
                if in_group[i] {
                    rela_shdr.sh_flags |= SHF_GROUP;
                }
                rela_shdr.write(&mut buf);
            }
        }

        // .symtab section.
        Elf64Shdr::symtab(
            symtab_name_idx,
            symtab_offset,
            symtab_size,
            strtab_shdr_idx,     // sh_link → .strtab
            num_local_plus_null, // sh_info → one past last local
        )
        .write(&mut buf);

        // .strtab section.
        Elf64Shdr::strtab(strtab_name_idx, strtab_offset, strtab_size).write(&mut buf);

        // .shstrtab section.
        Elf64Shdr::strtab(shstrtab_name_idx, shstrtab_offset, shstrtab_size).write(&mut buf);

        Ok(buf)
    }
}

impl Default for ElfWriter {
    fn default() -> Self {
        Self::new(ElfMachine::AArch64)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elf::metadata::GRP_COMDAT;
    use crate::elf::reloc::{AArch64RelocType, X86_64RelocType};

    /// Helper: read a little-endian u16 from a byte slice.
    fn read_u16(bytes: &[u8], offset: usize) -> u16 {
        u16::from_le_bytes([bytes[offset], bytes[offset + 1]])
    }

    /// Helper: read a little-endian u32 from a byte slice.
    fn read_u32(bytes: &[u8], offset: usize) -> u32 {
        u32::from_le_bytes([
            bytes[offset],
            bytes[offset + 1],
            bytes[offset + 2],
            bytes[offset + 3],
        ])
    }

    /// Helper: read a little-endian u64 from a byte slice.
    fn read_u64(bytes: &[u8], offset: usize) -> u64 {
        u64::from_le_bytes([
            bytes[offset],
            bytes[offset + 1],
            bytes[offset + 2],
            bytes[offset + 3],
            bytes[offset + 4],
            bytes[offset + 5],
            bytes[offset + 6],
            bytes[offset + 7],
        ])
    }

    #[test]
    fn test_elf_magic_bytes() {
        let writer = ElfWriter::new(ElfMachine::AArch64);
        let bytes = writer.write_checked().unwrap();
        assert_eq!(
            &bytes[0..4],
            &[0x7f, b'E', b'L', b'F'],
            "ELF magic must be 7f 45 4c 46"
        );
    }

    #[test]
    fn test_elf_header_class_and_endian() {
        let writer = ElfWriter::new(ElfMachine::AArch64);
        let bytes = writer.write_checked().unwrap();
        assert_eq!(bytes[4], ELFCLASS64, "must be 64-bit");
        assert_eq!(bytes[5], ELFDATA2LSB, "must be little-endian");
        assert_eq!(bytes[6], EV_CURRENT, "ELF version 1");
    }

    #[test]
    fn test_elf_type_is_rel() {
        let writer = ElfWriter::new(ElfMachine::AArch64);
        let bytes = writer.write_checked().unwrap();
        let e_type = read_u16(&bytes, 16);
        assert_eq!(e_type, ET_REL, "must be relocatable object");
    }

    #[test]
    fn test_elf_machine_aarch64() {
        let writer = ElfWriter::new(ElfMachine::AArch64);
        let bytes = writer.write_checked().unwrap();
        let e_machine = read_u16(&bytes, 18);
        assert_eq!(e_machine, EM_AARCH64);
    }

    #[test]
    fn test_elf_machine_x86_64() {
        let writer = ElfWriter::new(ElfMachine::X86_64);
        let bytes = writer.write_checked().unwrap();
        let e_machine = read_u16(&bytes, 18);
        assert_eq!(e_machine, EM_X86_64);
    }

    #[test]
    fn test_elf_e_flags_default_to_zero() {
        let writer = ElfWriter::new(ElfMachine::Riscv64);
        let bytes = writer.write_checked().unwrap();
        assert_eq!(read_u32(&bytes, 48), 0);
    }

    #[test]
    fn test_elf_e_flags_are_written_explicitly() {
        let mut writer = ElfWriter::new(ElfMachine::Riscv64);
        writer.set_e_flags(EF_RISCV_FLOAT_ABI_DOUBLE);
        let bytes = writer.write_checked().unwrap();
        assert_eq!(read_u32(&bytes, 48), EF_RISCV_FLOAT_ABI_DOUBLE);
        assert_eq!(&bytes[48..52], &[0x04, 0x00, 0x00, 0x00]);
    }

    #[test]
    fn test_empty_writer_section_count() {
        // Empty writer should have: null + .symtab + .strtab + .shstrtab = 4 sections
        let writer = ElfWriter::new(ElfMachine::AArch64);
        let bytes = writer.write_checked().unwrap();
        let e_shnum = read_u16(&bytes, 60);
        assert_eq!(
            e_shnum, 4,
            "empty writer: null + symtab + strtab + shstrtab"
        );
    }

    #[test]
    fn test_text_section_count() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&[0x1F, 0x20, 0x03, 0xD5]); // NOP
        let bytes = writer.write_checked().unwrap();
        let e_shnum = read_u16(&bytes, 60);
        // null + .text + .symtab + .strtab + .shstrtab = 5
        assert_eq!(e_shnum, 5);
    }

    #[test]
    fn test_text_and_data_section_count() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&[0x1F, 0x20, 0x03, 0xD5]);
        writer.add_data_section(&[1, 2, 3, 4, 5, 6, 7, 8]);
        let bytes = writer.write_checked().unwrap();
        let e_shnum = read_u16(&bytes, 60);
        // null + .text + .data + .symtab + .strtab + .shstrtab = 6
        assert_eq!(e_shnum, 6);
    }

    #[test]
    fn test_text_with_relocs_section_count() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        let nop = 0xD503201Fu32;
        let code: Vec<u8> = (0..4).flat_map(|_| nop.to_le_bytes()).collect();
        writer.add_text_section(&code);
        writer.add_symbol("callee", 0, 0, 0, true, STT_NOTYPE);
        writer.add_relocation(0, Elf64Rela::aarch64(0x04, 1, AArch64RelocType::Call26, 0));
        let bytes = writer.write_checked().unwrap();
        let e_shnum = read_u16(&bytes, 60);
        // null + .text + .rela.text + .symtab + .strtab + .shstrtab = 6
        assert_eq!(e_shnum, 6);
    }

    #[test]
    fn test_bss_section() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&[0; 16]);
        let bss_idx = writer.add_bss_section(1024);
        assert_eq!(bss_idx, 2); // .text=1, .bss=2

        let bytes = writer.write_checked().unwrap();
        let e_shnum = read_u16(&bytes, 60);
        // null + .text + .bss + .symtab + .strtab + .shstrtab = 6
        assert_eq!(e_shnum, 6);

        // Find the BSS section header and verify it's SHT_NOBITS.
        let sh_offset = read_u64(&bytes, 40) as usize;
        // Section 2 (index 2) is .bss — at sh_offset + 2*64
        let bss_shdr_off = sh_offset + 2 * ELF64_SHDR_SIZE;
        let bss_type = read_u32(&bytes, bss_shdr_off + 4);
        assert_eq!(bss_type, SHT_NOBITS, ".bss must be SHT_NOBITS");
        let bss_size = read_u64(&bytes, bss_shdr_off + 32);
        assert_eq!(bss_size, 1024, ".bss size must be 1024");
    }

    #[test]
    fn nobits_sections_keep_flags_alignment_and_occupy_no_file_bytes() {
        let build = |bss_size: u64, tbss_size: u64| {
            let mut writer = ElfWriter::new(ElfMachine::AArch64);
            writer.add_text_section(&[0; 8]);
            let data = writer.add_data_section(&[7; 3]);
            let bss = writer
                .add_nobits_section(".bss", bss_size, SHF_ALLOC | SHF_WRITE | SHF_GNU_RETAIN, 64)
                .unwrap();
            let tbss = writer
                .add_nobits_section(".tbss", tbss_size, SHF_ALLOC | SHF_WRITE | SHF_TLS, 32)
                .unwrap();
            let rodata = writer
                .add_section(".rodata", &[9; 5], SHT_PROGBITS, SHF_ALLOC, 16)
                .unwrap();
            assert_eq!((data, bss, tbss, rodata), (2, 3, 4, 5));
            writer.add_symbol("zero", bss, 0, bss_size, true, STT_OBJECT);
            writer.add_symbol("tls_zero", tbss, 0, tbss_size, true, STT_TLS);
            writer
                .write_checked()
                .expect("NOBITS object must pass the reparse gate")
        };
        let small = build(16, 8);
        let large = build(1 << 20, 1 << 16);
        assert_eq!(
            small.len(),
            large.len(),
            "zero-fill size must not change the object's file size"
        );
        let sh_offset = read_u64(&large, 40) as usize;
        let header = |index: usize| sh_offset + index * ELF64_SHDR_SIZE;
        let data_end = read_u64(&large, header(2) + 24) + read_u64(&large, header(2) + 32);
        for (index, flags, size, align) in [
            (3, SHF_ALLOC | SHF_WRITE | SHF_GNU_RETAIN, 1u64 << 20, 64u64),
            (4, SHF_ALLOC | SHF_WRITE | SHF_TLS, 1 << 16, 32),
        ] {
            let off = header(index);
            assert_eq!(read_u32(&large, off + 4), SHT_NOBITS);
            assert_eq!(read_u64(&large, off + 8), flags);
            assert_eq!(read_u64(&large, off + 32), size);
            assert_eq!(read_u64(&large, off + 48), align);
            let file_offset = read_u64(&large, off + 24);
            assert_eq!(file_offset % align, 0, "NOBITS offset is aligned");
            assert!(file_offset >= data_end && file_offset < large.len() as u64);
        }
        // The next PROGBITS section starts at the first 16-aligned offset
        // after `.data`: the NOBITS sections consumed no file bytes.
        let rodata_offset = read_u64(&large, header(5) + 24);
        assert_eq!(rodata_offset, data_end.next_multiple_of(16));
        assert_eq!(
            &large[rodata_offset as usize..rodata_offset as usize + 5],
            &[9; 5]
        );
    }

    #[test]
    fn test_symbol_table_entries() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&[0; 16]);
        writer.add_symbol("main", 1, 0, 16, true, STT_FUNC);
        writer.add_symbol("local_var", 1, 0, 4, false, STT_OBJECT);

        let bytes = writer.write_checked().unwrap();

        // Find .symtab section header.
        let sh_offset = read_u64(&bytes, 40) as usize;
        let e_shnum = read_u16(&bytes, 60) as usize;

        // Search for the .symtab section (sh_type == SHT_SYMTAB).
        let mut symtab_off = 0u64;
        let mut symtab_size = 0u64;
        let mut symtab_info = 0u32;
        for i in 0..e_shnum {
            let shdr_off = sh_offset + i * ELF64_SHDR_SIZE;
            let sh_type = read_u32(&bytes, shdr_off + 4);
            if sh_type == SHT_SYMTAB {
                symtab_off = read_u64(&bytes, shdr_off + 24);
                symtab_size = read_u64(&bytes, shdr_off + 32);
                symtab_info = read_u32(&bytes, shdr_off + 44);
                break;
            }
        }

        // We have: null symbol + local_var + main = 3 entries.
        let num_syms = symtab_size / ELF64_SYM_SIZE as u64;
        assert_eq!(num_syms, 3, "null + local_var + main = 3 symbols");

        // sh_info = one past last local = 2 (null + local_var).
        assert_eq!(symtab_info, 2, "sh_info should be 2 (null + 1 local)");

        // Verify null symbol at index 0.
        let sym0_off = symtab_off as usize;
        let sym0_info = bytes[sym0_off + 4];
        assert_eq!(sym0_info, 0, "null symbol st_info must be 0");

        // Verify local symbol at index 1 (local_var comes before main).
        let sym1_off = symtab_off as usize + ELF64_SYM_SIZE;
        let sym1_info = bytes[sym1_off + 4];
        assert_eq!(
            elf64_st_bind(sym1_info),
            STB_LOCAL,
            "symbol 1 should be local"
        );

        // Verify global symbol at index 2.
        let sym2_off = symtab_off as usize + 2 * ELF64_SYM_SIZE;
        let sym2_info = bytes[sym2_off + 4];
        assert_eq!(
            elf64_st_bind(sym2_info),
            STB_GLOBAL,
            "symbol 2 should be global"
        );
    }

    #[test]
    fn test_relocation_entries() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        // 16 bytes of ARM64 code (4 instructions).
        let nop = 0xD503201Fu32;
        let code: Vec<u8> = (0..4).flat_map(|_| nop.to_le_bytes()).collect();
        writer.add_text_section(&code);

        writer.add_symbol("callee", 0, 0, 0, true, STT_FUNC);

        // Add a CALL26 relocation at offset 4 (second instruction).
        writer.add_relocation(0, Elf64Rela::aarch64(4, 1, AArch64RelocType::Call26, 0));

        // Add an ADRP + ADD pair.
        writer.add_relocation(
            0,
            Elf64Rela::aarch64(8, 1, AArch64RelocType::AdrPrelPgHi21, 0),
        );
        writer.add_relocation(
            0,
            Elf64Rela::aarch64(12, 1, AArch64RelocType::AddAbsLo12Nc, 0),
        );

        let bytes = writer.write_checked().unwrap();

        // Find .rela.text section.
        let sh_offset = read_u64(&bytes, 40) as usize;
        let e_shnum = read_u16(&bytes, 60) as usize;

        let mut rela_off = 0u64;
        let mut rela_size = 0u64;
        for i in 0..e_shnum {
            let shdr_off = sh_offset + i * ELF64_SHDR_SIZE;
            let sh_type = read_u32(&bytes, shdr_off + 4);
            if sh_type == SHT_RELA {
                rela_off = read_u64(&bytes, shdr_off + 24);
                rela_size = read_u64(&bytes, shdr_off + 32);
                break;
            }
        }

        let num_relas = rela_size / ELF64_RELA_SIZE as u64;
        assert_eq!(num_relas, 3, "should have 3 relocation entries");

        // Verify first relocation (CALL26 at offset 4).
        let rela0_off = rela_off as usize;
        let r_offset = read_u64(&bytes, rela0_off);
        assert_eq!(r_offset, 4, "first reloc at offset 4");
        let r_info = read_u64(&bytes, rela0_off + 8);
        assert_eq!(elf64_r_type(r_info), R_AARCH64_CALL26);
        assert_eq!(elf64_r_sym(r_info), 1, "symbol index 1");
    }

    #[test]
    fn test_x86_64_relocation_entries() {
        let mut writer = ElfWriter::new(ElfMachine::X86_64);
        // 16 bytes of x86-64 NOPs.
        writer.add_text_section(&[0x90; 16]);

        writer.add_symbol("puts", 0, 0, 0, true, STT_FUNC);

        // PLT32 relocation (typical for function calls).
        writer.add_relocation(0, Elf64Rela::x86_64(5, 1, X86_64RelocType::Plt32, -4));

        // GOTPCREL relocation.
        writer.add_relocation(0, Elf64Rela::x86_64(10, 1, X86_64RelocType::GotPcRel, -4));

        let bytes = writer.write_checked().unwrap();

        // Verify machine type.
        let e_machine = read_u16(&bytes, 18);
        assert_eq!(e_machine, EM_X86_64);

        // Find .rela.text.
        let sh_offset = read_u64(&bytes, 40) as usize;
        let e_shnum = read_u16(&bytes, 60) as usize;

        let mut rela_off = 0u64;
        let mut rela_size = 0u64;
        for i in 0..e_shnum {
            let shdr_off = sh_offset + i * ELF64_SHDR_SIZE;
            let sh_type = read_u32(&bytes, shdr_off + 4);
            if sh_type == SHT_RELA {
                rela_off = read_u64(&bytes, shdr_off + 24);
                rela_size = read_u64(&bytes, shdr_off + 32);
                break;
            }
        }

        let num_relas = rela_size / ELF64_RELA_SIZE as u64;
        assert_eq!(num_relas, 2, "should have 2 relocation entries");

        // Verify PLT32 relocation.
        let r_info = read_u64(&bytes, rela_off as usize + 8);
        assert_eq!(elf64_r_type(r_info), R_X86_64_PLT32);

        // Verify addend = -4.
        let r_addend_bytes = &bytes[(rela_off as usize + 16)..(rela_off as usize + 24)];
        let r_addend = i64::from_le_bytes(r_addend_bytes.try_into().unwrap());
        assert_eq!(r_addend, -4);
    }

    /// Drive the new x86-64 TLS / modern relocations through the ELF writer and
    /// verify the emitted `.rela.text` entries carry the correct ABI codes,
    /// packed `r_info`, and addends at the byte level.
    #[test]
    fn test_x86_64_tls_relocation_entries_in_rela_section() {
        let mut writer = ElfWriter::new(ElfMachine::X86_64);
        writer.add_text_section(&[0x90; 64]);
        // Symbol index 1 is the first user symbol (index 0 is the null symbol).
        writer.add_symbol("tls_var", 0, 0, 0, true, STT_OBJECT);

        // One entry for each newly added relocation kind. (offset, kind, addend).
        let specs: [(u64, X86_64RelocType, i64); 12] = [
            (0, X86_64RelocType::TlsGd, -4),
            (4, X86_64RelocType::TlsLd, -4),
            (8, X86_64RelocType::DtpMod64, 0),
            (12, X86_64RelocType::DtpOff64, 0),
            (16, X86_64RelocType::DtpOff32, 0),
            (20, X86_64RelocType::TpOff64, 0),
            (24, X86_64RelocType::TpOff32, 0),
            (28, X86_64RelocType::GotTpOff, -4),
            (32, X86_64RelocType::Pc64, 0),
            (40, X86_64RelocType::GotPcRelX, -4),
            (44, X86_64RelocType::RexGotPcRelX, -4),
            (48, X86_64RelocType::IRelative, 0),
        ];
        for (off, kind, addend) in &specs {
            writer.add_relocation(0, Elf64Rela::x86_64(*off, 1, *kind, *addend));
        }

        let bytes = writer.write_checked().unwrap();
        assert_eq!(read_u16(&bytes, 18), EM_X86_64);

        // Locate the .rela.text section.
        let sh_offset = read_u64(&bytes, 40) as usize;
        let e_shnum = read_u16(&bytes, 60) as usize;
        let mut rela_off = 0u64;
        let mut rela_size = 0u64;
        for i in 0..e_shnum {
            let shdr_off = sh_offset + i * ELF64_SHDR_SIZE;
            if read_u32(&bytes, shdr_off + 4) == SHT_RELA {
                rela_off = read_u64(&bytes, shdr_off + 24);
                rela_size = read_u64(&bytes, shdr_off + 32);
                break;
            }
        }
        assert_eq!(rela_size / ELF64_RELA_SIZE as u64, specs.len() as u64);

        // Each entry must decode to exactly what we asked for, with the symbol
        // index packed into the upper 32 bits of r_info.
        for (i, (off, kind, addend)) in specs.iter().enumerate() {
            let entry_off = rela_off as usize + i * ELF64_RELA_SIZE;
            let r_offset = read_u64(&bytes, entry_off);
            let r_info = read_u64(&bytes, entry_off + 8);
            let r_addend =
                i64::from_le_bytes(bytes[entry_off + 16..entry_off + 24].try_into().unwrap());

            assert_eq!(r_offset, *off, "r_offset for {kind:?}");
            assert_eq!(elf64_r_sym(r_info), 1, "r_info sym for {kind:?}");
            assert_eq!(
                elf64_r_type(r_info),
                kind.to_type_val(),
                "r_info type for {kind:?}"
            );
            assert_eq!(r_info, (1u64 << 32) | kind.to_type_val() as u64);
            assert_eq!(r_addend, *addend, "addend for {kind:?}");
        }
    }

    #[test]
    fn test_shstrtab_index() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&[0; 4]);
        let bytes = writer.write_checked().unwrap();

        let e_shstrndx = read_u16(&bytes, 62);
        let e_shnum = read_u16(&bytes, 60);
        // .shstrtab is the last section.
        assert_eq!(e_shstrndx, e_shnum - 1);
    }

    #[test]
    fn test_null_section_is_all_zeros() {
        let writer = ElfWriter::new(ElfMachine::AArch64);
        let bytes = writer.write_checked().unwrap();

        let sh_offset = read_u64(&bytes, 40) as usize;
        // First section header (64 bytes) should be all zeros.
        let null_section = &bytes[sh_offset..sh_offset + ELF64_SHDR_SIZE];
        assert!(
            null_section.iter().all(|&b| b == 0),
            "null section must be all zeros"
        );
    }

    #[test]
    fn test_text_section_data_present() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        let nop = 0xD503201Fu32;
        let code: Vec<u8> = nop.to_le_bytes().to_vec();
        writer.add_text_section(&code);

        let bytes = writer.write_checked().unwrap();

        // The NOP bytes should appear in the output.
        let nop_bytes = &[0x1F, 0x20, 0x03, 0xD5];
        let found = bytes.windows(4).any(|w| w == nop_bytes);
        assert!(found, "text section NOP data should be in the output");
    }

    #[test]
    fn test_default_impl() {
        let writer = ElfWriter::default();
        let bytes = writer.write_checked().unwrap();
        assert_eq!(&bytes[0..4], &[0x7f, b'E', b'L', b'F']);
        // Default is AArch64.
        let e_machine = read_u16(&bytes, 18);
        assert_eq!(e_machine, EM_AARCH64);
    }

    #[test]
    fn test_multiple_sections_with_symbols() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        let text_idx = writer.add_text_section(&[0; 32]);
        let data_idx = writer.add_data_section(&[0xDE, 0xAD, 0xBE, 0xEF]);
        let bss_idx = writer.add_bss_section(256);

        writer.add_symbol("main", text_idx, 0, 32, true, STT_FUNC);
        writer.add_symbol("global_data", data_idx, 0, 4, true, STT_OBJECT);
        writer.add_symbol("bss_var", bss_idx, 0, 256, true, STT_OBJECT);
        writer.add_symbol("local_helper", text_idx, 16, 16, false, STT_FUNC);

        let bytes = writer.write_checked().unwrap();

        // Verify valid ELF header.
        assert_eq!(&bytes[0..4], &[0x7f, b'E', b'L', b'F']);

        // Should have: null + .text + .data + .bss + .symtab + .strtab + .shstrtab = 7.
        let e_shnum = read_u16(&bytes, 60);
        assert_eq!(e_shnum, 7);

        // Find .symtab and check symbol count.
        let sh_offset = read_u64(&bytes, 40) as usize;
        for i in 0..e_shnum as usize {
            let shdr_off = sh_offset + i * ELF64_SHDR_SIZE;
            let sh_type = read_u32(&bytes, shdr_off + 4);
            if sh_type == SHT_SYMTAB {
                let size = read_u64(&bytes, shdr_off + 32);
                let num_syms = size / ELF64_SYM_SIZE as u64;
                // null + local_helper + main + global_data + bss_var = 5
                assert_eq!(num_syms, 5);
                break;
            }
        }
    }

    #[test]
    fn test_aarch64_got_relocations() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&[0; 8]);
        writer.add_symbol("extern_sym", 0, 0, 0, true, STT_NOTYPE);

        writer.add_relocation(0, Elf64Rela::aarch64(0, 1, AArch64RelocType::AdrGotPage, 0));
        writer.add_relocation(
            0,
            Elf64Rela::aarch64(4, 1, AArch64RelocType::Ld64GotLo12Nc, 0),
        );

        let bytes = writer.write_checked().unwrap();
        assert_eq!(&bytes[0..4], &[0x7f, b'E', b'L', b'F']);

        // Find .rela.text and verify types.
        let sh_offset = read_u64(&bytes, 40) as usize;
        let e_shnum = read_u16(&bytes, 60) as usize;

        let mut found_rela = false;
        for i in 0..e_shnum {
            let shdr_off = sh_offset + i * ELF64_SHDR_SIZE;
            let sh_type = read_u32(&bytes, shdr_off + 4);
            if sh_type == SHT_RELA {
                found_rela = true;
                let rela_off = read_u64(&bytes, shdr_off + 24) as usize;

                let r_info0 = read_u64(&bytes, rela_off + 8);
                assert_eq!(elf64_r_type(r_info0), R_AARCH64_ADR_GOT_PAGE);

                let r_info1 = read_u64(&bytes, rela_off + ELF64_RELA_SIZE + 8);
                assert_eq!(elf64_r_type(r_info1), R_AARCH64_LD64_GOT_LO12_NC);
                break;
            }
        }
        assert!(found_rela, "expected .rela.text section");
    }

    #[test]
    fn test_aarch64_tls_relocations() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&[0; 8]);
        writer.add_symbol("tls_var", 0, 0, 0, true, STT_NOTYPE);

        writer.add_relocation(
            0,
            Elf64Rela::aarch64(0, 1, AArch64RelocType::TlsieAdrGottprelPage21, 0),
        );
        writer.add_relocation(
            0,
            Elf64Rela::aarch64(4, 1, AArch64RelocType::TlsieLd64GottprelLo12Nc, 0),
        );

        let bytes = writer.write_checked().unwrap();
        assert_eq!(&bytes[0..4], &[0x7f, b'E', b'L', b'F']);

        let sh_offset = read_u64(&bytes, 40) as usize;
        let e_shnum = read_u16(&bytes, 60) as usize;

        let mut found_rela = false;
        for i in 0..e_shnum {
            let shdr_off = sh_offset + i * ELF64_SHDR_SIZE;
            let sh_type = read_u32(&bytes, shdr_off + 4);
            if sh_type == SHT_RELA {
                found_rela = true;
                let rela_off = read_u64(&bytes, shdr_off + 24) as usize;

                let r_info0 = read_u64(&bytes, rela_off + 8);
                assert_eq!(elf64_r_type(r_info0), R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21);

                let r_info1 = read_u64(&bytes, rela_off + ELF64_RELA_SIZE + 8);
                assert_eq!(elf64_r_type(r_info1), R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC);
                break;
            }
        }
        assert!(found_rela, "expected .rela.text section");
    }

    #[test]
    fn test_aarch64_tlsle_relocations() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&[0; 8]);
        writer.add_symbol("tls_var", 0, 0, 0, true, STT_NOTYPE);

        writer.add_relocation(
            0,
            Elf64Rela::aarch64(0, 1, AArch64RelocType::TlsleAddTprelHi12, 0),
        );
        writer.add_relocation(
            0,
            Elf64Rela::aarch64(4, 1, AArch64RelocType::TlsleAddTprelLo12Nc, 0),
        );

        let bytes = writer.write_checked().unwrap();
        assert_eq!(&bytes[0..4], &[0x7f, b'E', b'L', b'F']);

        let sh_offset = read_u64(&bytes, 40) as usize;
        let e_shnum = read_u16(&bytes, 60) as usize;

        let mut found_rela = false;
        for i in 0..e_shnum {
            let shdr_off = sh_offset + i * ELF64_SHDR_SIZE;
            let sh_type = read_u32(&bytes, shdr_off + 4);
            if sh_type == SHT_RELA {
                found_rela = true;
                let rela_off = read_u64(&bytes, shdr_off + 24) as usize;

                let r_info0 = read_u64(&bytes, rela_off + 8);
                assert_eq!(elf64_r_type(r_info0), R_AARCH64_TLSLE_ADD_TPREL_HI12);

                let r_info1 = read_u64(&bytes, rela_off + ELF64_RELA_SIZE + 8);
                assert_eq!(elf64_r_type(r_info1), R_AARCH64_TLSLE_ADD_TPREL_LO12_NC);
                break;
            }
        }
        assert!(found_rela, "expected .rela.text section");
    }

    #[test]
    #[should_panic(expected = "ELF relocation section index 99 out of range")]
    fn test_relocation_to_out_of_range_section_panics() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&[0; 4]);
        writer.add_relocation(99, Elf64Rela::aarch64(0, 0, AArch64RelocType::Call26, 0));
    }

    #[test]
    fn test_ehsize_field() {
        let writer = ElfWriter::new(ElfMachine::X86_64);
        let bytes = writer.write_checked().unwrap();
        let e_ehsize = read_u16(&bytes, 52);
        assert_eq!(e_ehsize, 64, "ELF64 header size must be 64");
    }

    #[test]
    fn test_shentsize_field() {
        let writer = ElfWriter::new(ElfMachine::X86_64);
        let bytes = writer.write_checked().unwrap();
        let e_shentsize = read_u16(&bytes, 58);
        assert_eq!(e_shentsize, 64, "section header entry size must be 64");
    }

    // --- Tests for metadata section writer methods ---

    #[test]
    fn test_add_note_gnu_stack() {
        let mut writer = ElfWriter::new(ElfMachine::X86_64);
        writer.add_text_section(&[0x90; 16]);
        let stack_idx = writer.add_note_gnu_stack();
        assert_eq!(stack_idx, 2); // .text=1, .note.GNU-stack=2

        let bytes = writer.write_checked().unwrap();
        // null + .text + .note.GNU-stack + .symtab + .strtab + .shstrtab = 6
        let e_shnum = read_u16(&bytes, 60);
        assert_eq!(e_shnum, 6);

        // Find the .note.GNU-stack section header and verify its type.
        let sh_offset = read_u64(&bytes, 40) as usize;
        // Section 2 is .note.GNU-stack
        let note_shdr_off = sh_offset + 2 * ELF64_SHDR_SIZE;
        let note_type = read_u32(&bytes, note_shdr_off + 4);
        assert_eq!(
            note_type, SHT_PROGBITS,
            ".note.GNU-stack must be SHT_PROGBITS"
        );
        // Flags must be 0 (no SHF_EXECINSTR)
        let note_flags = read_u64(&bytes, note_shdr_off + 8);
        assert_eq!(
            note_flags, 0,
            ".note.GNU-stack must have no executable flag"
        );
        // Size must be 0 (empty marker section)
        let note_size = read_u64(&bytes, note_shdr_off + 32);
        assert_eq!(note_size, 0, ".note.GNU-stack must be empty");
    }

    /// Section-header field reader for the COMDAT tests: (type, flags, offset,
    /// size, link, info, entsize) of header `index`.
    fn shdr_fields(bytes: &[u8], index: usize) -> (u32, u64, u64, u64, u32, u32, u64) {
        let sh = read_u64(bytes, 40) as usize + index * ELF64_SHDR_SIZE;
        (
            read_u32(bytes, sh + 4),
            read_u64(bytes, sh + 8),
            read_u64(bytes, sh + 24),
            read_u64(bytes, sh + 32),
            read_u32(bytes, sh + 40),
            read_u32(bytes, sh + 44),
            read_u64(bytes, sh + 56),
        )
    }

    /// A COMDAT group of two text members, one with relocations: the group
    /// precedes its members, links `.symtab`, names its signature by FINAL
    /// symbol index (after the locals-first partition moved it), lists both
    /// members and the member's `.rela.*` section, and `SHF_GROUP` is set on
    /// exactly the members and that relocation section.
    #[test]
    fn comdat_group_links_final_signature_and_member_relocations() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&[0; 8]); // shndx 1, not grouped
        let group = writer.add_comdat_group(); // shndx 2
        let member = writer
            .add_group_member_section(
                group,
                ".text.inline_fn",
                &[0; 8],
                SHT_PROGBITS,
                SHF_ALLOC | SHF_EXECINSTR,
                4,
                0,
            )
            .unwrap(); // shndx 3
        let second = writer
            .add_group_member_section(
                group,
                ".rodata.inline_fn",
                &[1; 4],
                SHT_PROGBITS,
                SHF_ALLOC,
                4,
                0,
            )
            .unwrap(); // shndx 4
        assert_eq!((member, second), (3, 4));
        // A local symbol inserted AFTER the global signature: the writer's
        // locals-first partition moves the signature to final index 2.
        let signature = writer
            .add_checked_symbol(ElfSymbol {
                name: "inline_fn".to_string(),
                section: member,
                value: 0,
                size: 8,
                is_global: true,
                sym_type: STT_FUNC,
                is_weak: true,
                visibility: STV_DEFAULT,
            })
            .expect("checked signature symbol");
        writer
            .bind_comdat_group_signature(group, signature)
            .expect("weak member symbol signs the group");
        writer.add_symbol("local_anchor", 1, 0, 0, false, STT_FUNC);
        writer.add_symbol("callee", 0, 0, 0, true, 0);
        writer.add_relocation(
            usize::from(member) - 1,
            Elf64Rela::aarch64(0, 3, AArch64RelocType::Call26, 0),
        );
        let bytes = writer.write_checked().expect("COMDAT object must reparse");

        let (ty, flags, offset, size, link, info, entsize) = shdr_fields(&bytes, 2);
        assert_eq!(ty, SHT_GROUP);
        assert_eq!(flags, 0);
        assert_eq!(entsize, 4);
        // null, .text, .group, 2 members, .rela.text.inline_fn, .symtab, ...
        assert_eq!(link, 6, "group links .symtab");
        assert_eq!(info, 2, "signature is the first global after one local");
        assert_eq!(size, 16);
        let words: Vec<u32> = (0..4)
            .map(|w| read_u32(&bytes, offset as usize + 4 * w))
            .collect();
        assert_eq!(words, vec![GRP_COMDAT, 3, 4, 5]);
        assert_eq!(shdr_fields(&bytes, 1).1 & SHF_GROUP, 0);
        assert_ne!(shdr_fields(&bytes, 3).1 & SHF_GROUP, 0);
        assert_ne!(shdr_fields(&bytes, 4).1 & SHF_GROUP, 0);
        let rela = shdr_fields(&bytes, 5);
        assert_eq!(rela.1, SHF_INFO_LINK | SHF_GROUP);
        assert_eq!(rela.5, 3, ".rela targets the grouped text member");
    }

    /// The reparse gate recomputes every group field independently: a
    /// dropped member word, a wrong signature index, a cleared `SHF_GROUP`
    /// on a member or on its relocation section, and a group that no longer
    /// links the symbol table each fail closed.
    #[test]
    fn comdat_group_mutations_fail_the_reparse_gate() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        let group = writer.add_comdat_group();
        let member = writer
            .add_group_member_section(
                group,
                ".text.f",
                &[0; 4],
                SHT_PROGBITS,
                SHF_ALLOC | SHF_EXECINSTR,
                4,
                0,
            )
            .unwrap();
        let signature = writer
            .add_checked_symbol(ElfSymbol {
                name: "f".to_string(),
                section: member,
                value: 0,
                size: 4,
                is_global: true,
                sym_type: STT_FUNC,
                is_weak: true,
                visibility: STV_DEFAULT,
            })
            .expect("checked signature symbol");
        writer
            .bind_comdat_group_signature(group, signature)
            .expect("weak member symbol signs the group");
        writer.add_symbol("g", 0, 0, 0, true, 0);
        writer.add_relocation(
            usize::from(member) - 1,
            Elf64Rela::aarch64(0, 2, AArch64RelocType::Call26, 0),
        );
        let bytes = writer.write_checked().expect("faithful object");
        let intent = writer.reparse_object_intent();
        let sh = |index: usize| read_u64(&bytes, 40) as usize + index * ELF64_SHDR_SIZE;
        let group_data = read_u64(&bytes, sh(1) + 24) as usize;
        let mutations: Vec<(&str, Box<dyn Fn(&mut Vec<u8>)>)> = vec![
            (
                "member word",
                Box::new(move |b: &mut Vec<u8>| b[group_data + 4] ^= 1),
            ),
            (
                "rela member word",
                Box::new(move |b: &mut Vec<u8>| b[group_data + 8] ^= 1),
            ),
            (
                "signature index",
                Box::new(move |b: &mut Vec<u8>| b[sh(1) + 44] = 2),
            ),
            (
                "member SHF_GROUP",
                Box::new(move |b: &mut Vec<u8>| b[sh(2) + 9] &= !0x02),
            ),
            (
                "rela SHF_GROUP",
                Box::new(move |b: &mut Vec<u8>| b[sh(3) + 9] &= !0x02),
            ),
            (
                "symtab link",
                Box::new(move |b: &mut Vec<u8>| b[sh(1) + 40] = 0),
            ),
        ];
        for (what, mutate) in mutations {
            let mut mutated = bytes.clone();
            mutate(&mut mutated);
            assert!(
                crate::elf::reparse::check_object(&intent, &mutated).is_err(),
                "{what} mutation must fail the gate"
            );
        }
    }

    /// A group whose signature was never bound cannot name one: the gate
    /// refuses the unnamed group rather than ship it.
    #[test]
    fn comdat_group_without_signature_symbol_fails_closed() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        let group = writer.add_comdat_group();
        writer
            .add_group_member_section(group, ".text.missing", &[0; 4], SHT_PROGBITS, 6, 4, 0)
            .unwrap();
        writer.add_symbol("other", 0, 0, 0, true, 0);
        let error = writer
            .write_checked()
            .expect_err("unnamed group must fail closed");
        assert!(error.message.contains("names no symbol"), "{error}");
    }

    /// The checked signature binding refuses a local symbol, a symbol defined
    /// outside the group's members, an unknown handle and a second binding.
    #[test]
    fn comdat_group_signature_binding_is_checked() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        let text = writer.add_text_section(&[0; 8]);
        let group = writer.add_comdat_group();
        let member = writer
            .add_group_member_section(group, ".text.g", &[0; 4], SHT_PROGBITS, 6, 4, 0)
            .unwrap();
        let symbol = |name: &str, section: u16, is_global: bool, is_weak: bool| ElfSymbol {
            name: name.to_string(),
            section,
            value: 0,
            size: 4,
            is_global,
            sym_type: STT_FUNC,
            is_weak,
            visibility: STV_DEFAULT,
        };
        let local = writer
            .add_checked_symbol(symbol("local_g", member, false, false))
            .unwrap();
        let outside = writer
            .add_checked_symbol(symbol("outside", text, true, false))
            .unwrap();
        let weak = writer
            .add_checked_symbol(symbol("g", member, true, true))
            .unwrap();
        for (id, reason) in [(local, "non-local"), (outside, "member section")] {
            let error = writer
                .bind_comdat_group_signature(group, id)
                .expect_err("refused signature");
            assert!(error.to_string().contains(reason), "{error}");
        }
        assert!(matches!(
            writer.bind_comdat_group_signature(group, ElfSymbolId(99)),
            Err(ElfSymbolError::UnknownSymbol { ordinal: 99 })
        ));
        writer.bind_comdat_group_signature(group, weak).unwrap();
        let error = writer
            .bind_comdat_group_signature(group, weak)
            .expect_err("second binding");
        assert!(error.to_string().contains("already bound"), "{error}");
        writer.write_checked().expect("bound group reparses");
    }

    #[test]
    fn section_entsize_is_emitted_and_checked() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        let init = writer
            .add_section_with_entsize(
                ".init_array",
                &[0; 8],
                SHT_INIT_ARRAY,
                SHF_ALLOC | SHF_WRITE,
                8,
                8,
            )
            .unwrap();
        let bytes = writer.write_checked().expect("init_array object");
        let (ty, flags, _, size, _, _, entsize) = shdr_fields(&bytes, usize::from(init));
        assert_eq!((ty, flags, size, entsize), (SHT_INIT_ARRAY, 3, 8, 8));
        let intent = writer.reparse_object_intent();
        let mut mutated = bytes.clone();
        let sh = read_u64(&bytes, 40) as usize + usize::from(init) * ELF64_SHDR_SIZE;
        mutated[sh + 56] = 0;
        assert!(crate::elf::reparse::check_object(&intent, &mutated).is_err());
    }

    #[test]
    fn test_add_generic_section() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        let rodata = b"Hello, Trust Codegen!";
        let idx = writer
            .add_section(".rodata", rodata, SHT_PROGBITS, SHF_ALLOC, 4)
            .unwrap();
        assert_eq!(idx, 1);

        let bytes = writer.write_checked().unwrap();
        // The rodata string should appear in the output.
        let found = bytes.windows(rodata.len()).any(|w| w == rodata);
        assert!(found, ".rodata data should be in the output");
    }

    #[test]
    fn test_full_object_with_data_and_stack() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        // ARM64 NOP = 0xD503201F
        let nop: Vec<u8> = (0..4).flat_map(|_| 0xD503201Fu32.to_le_bytes()).collect();
        writer.add_text_section(&nop);
        writer.add_data_section(&[0xCA, 0xFE]);
        writer.add_note_gnu_stack();
        writer.add_symbol("main", 1, 0, 16, true, STT_FUNC);

        let bytes = writer.write_checked().unwrap();
        assert_eq!(&bytes[0..4], &[0x7f, b'E', b'L', b'F']);
        // null + .text + .data + .note.GNU-stack + .symtab + .strtab
        //   + .shstrtab = 7
        let e_shnum = read_u16(&bytes, 60);
        assert_eq!(e_shnum, 7);
    }

    /// Independent `.symtab` walk: (name, st_info, st_other, st_shndx) per
    /// entry in final index order, plus the symtab `sh_info`.
    fn symtab_rows(bytes: &[u8]) -> (Vec<(String, u8, u8, u16)>, u32) {
        let shoff = read_u64(bytes, 0x28) as usize;
        let shnum = read_u16(bytes, 0x3C) as usize;
        let header = |index: usize| shoff + index * 64;
        let symtab = (0..shnum)
            .find(|&index| read_u32(bytes, header(index) + 4) == SHT_SYMTAB)
            .expect("symtab section");
        let offset = read_u64(bytes, header(symtab) + 0x18) as usize;
        let size = read_u64(bytes, header(symtab) + 0x20) as usize;
        let link = read_u32(bytes, header(symtab) + 0x28) as usize;
        let info = read_u32(bytes, header(symtab) + 0x2C);
        let strtab = read_u64(bytes, header(link) + 0x18) as usize;
        let rows = (offset..offset + size)
            .step_by(24)
            .map(|entry| {
                let name_start = strtab + read_u32(bytes, entry) as usize;
                let name_end = bytes[name_start..]
                    .iter()
                    .position(|&byte| byte == 0)
                    .map(|length| name_start + length)
                    .expect("NUL-terminated symbol name");
                (
                    String::from_utf8_lossy(&bytes[name_start..name_end]).into_owned(),
                    bytes[entry + 4],
                    bytes[entry + 5],
                    read_u16(bytes, entry + 6),
                )
            })
            .collect();
        (rows, info)
    }

    fn checked(name: &str, section: u16, global: bool, weak: bool, visibility: u8) -> ElfSymbol {
        ElfSymbol {
            name: name.to_string(),
            section,
            value: 0,
            size: if section == 0 { 0 } else { 4 },
            is_global: global,
            sym_type: if section == 0 { STT_NOTYPE } else { STT_FUNC },
            is_weak: weak,
            visibility,
        }
    }

    #[test]
    fn checked_symbol_ids_resolve_to_the_serialized_locals_first_order() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&0xD503201Fu32.to_le_bytes());
        // Interleave every binding class; the handles must not care.
        let global = writer
            .add_checked_symbol(checked("global_fn", 1, true, false, STV_PROTECTED))
            .unwrap();
        let local = writer
            .add_checked_symbol(checked("local_fn", 1, false, false, STV_DEFAULT))
            .unwrap();
        let weak_def = writer
            .add_checked_symbol(checked("weak_fn", 1, false, true, STV_HIDDEN))
            .unwrap();
        let weak_undef = writer
            .add_checked_symbol(checked("maybe_absent", 0, false, true, STV_DEFAULT))
            .unwrap();
        let late_local = writer
            .add_checked_symbol(checked("late_local", 1, false, false, STV_DEFAULT))
            .unwrap();
        // Undefined references may carry STV_HIDDEN/STV_PROTECTED (gABI: the
        // definition must then be in the output being linked, or a weak one
        // resolves to 0).
        let hidden_undef = writer
            .add_checked_symbol(checked("hidden_import", 0, true, false, STV_HIDDEN))
            .unwrap();
        let protected_weak_undef = writer
            .add_checked_symbol(checked("protected_maybe", 0, false, true, STV_PROTECTED))
            .unwrap();
        let indices: Vec<(ElfSymbolId, u32)> = [
            global,
            local,
            weak_def,
            weak_undef,
            late_local,
            hidden_undef,
            protected_weak_undef,
        ]
        .into_iter()
        .map(|id| (id, writer.final_symbol_index(id).unwrap()))
        .collect();
        // One relocation per handle so the reparse gate replays every index.
        // `Prel32` (a 4-byte field) fits the one-instruction `.text`.
        for (offset, (_, index)) in indices.iter().enumerate() {
            writer.add_relocation(
                0,
                Elf64Rela::aarch64(0, *index, AArch64RelocType::Prel32, offset as i64),
            );
        }
        let bytes = writer.write_checked().expect("reparse gate agrees");
        let (rows, sh_info) = symtab_rows(&bytes);
        assert_eq!(sh_info, 3, "null + two locals");
        let expect = [
            ("global_fn", STB_GLOBAL, STV_PROTECTED, 1),
            ("local_fn", STB_LOCAL, STV_DEFAULT, 1),
            ("weak_fn", STB_WEAK, STV_HIDDEN, 1),
            ("maybe_absent", STB_WEAK, STV_DEFAULT, 0),
            ("late_local", STB_LOCAL, STV_DEFAULT, 1),
            ("hidden_import", STB_GLOBAL, STV_HIDDEN, 0),
            ("protected_maybe", STB_WEAK, STV_PROTECTED, 0),
        ];
        for ((_, index), (name, binding, visibility, section)) in indices.iter().zip(expect) {
            let row = &rows[*index as usize];
            assert_eq!(row.0, name, "index {index}");
            assert_eq!(row.1 >> 4, binding, "{name} binding");
            assert_eq!(row.2 & 3, visibility, "{name} visibility");
            assert_eq!(row.3, section, "{name} section");
        }
        assert_eq!(
            indices.iter().map(|(_, index)| *index).collect::<Vec<_>>(),
            [3, 1, 4, 5, 2, 6, 7]
        );
    }

    #[test]
    fn checked_symbol_indices_match_the_serialized_symtab_for_a_large_interleaved_table() {
        // Every handle of a long, irregularly interleaved local/global/weak
        // table must name its own row in the independently walked `.symtab`.
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&[0; 8]);
        let mut state = 0x2545_f491_u32;
        let mut ids = Vec::new();
        for ordinal in 0..300 {
            state ^= state << 13;
            state ^= state >> 17;
            state ^= state << 5;
            let (global, weak) = match state % 3 {
                0 => (false, false),
                1 => (true, false),
                _ => (false, true),
            };
            let name = format!("sym_{ordinal}");
            let id = writer
                .add_checked_symbol(checked(&name, 1, global, weak, STV_DEFAULT))
                .unwrap();
            ids.push((name, id));
        }
        let mut indices = Vec::new();
        for (offset, (name, id)) in ids.iter().enumerate() {
            let index = writer.final_symbol_index(*id).unwrap();
            writer.add_relocation(
                0,
                Elf64Rela::aarch64(0, index, AArch64RelocType::Abs64, offset as i64),
            );
            indices.push((name.clone(), index));
        }
        let bytes = writer.write_checked().expect("reparse gate agrees");
        let (rows, _) = symtab_rows(&bytes);
        assert_eq!(rows.len(), 301, "null + every symbol");
        for (name, index) in indices {
            assert_eq!(rows[index as usize].0, name, "index {index}");
        }
    }

    #[test]
    fn checked_symbol_api_refuses_malformed_and_late_symbols() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&[0; 8]);
        let refusals = [
            (
                checked("local_undef", 0, false, false, STV_DEFAULT),
                "undefined LOCAL",
            ),
            (
                checked("internal", 1, true, false, 1),
                "unsupported st_other",
            ),
            (
                checked("no_section", 2, true, false, STV_DEFAULT),
                "names section 2",
            ),
            (
                checked("nul\0name", 1, true, false, STV_DEFAULT),
                "contains NUL",
            ),
        ];
        for (symbol, reason) in refusals {
            let error = writer.add_checked_symbol(symbol).unwrap_err().to_string();
            assert!(error.contains(reason), "{error}");
        }
        let mut past_end = checked("past_end", 1, true, false, STV_DEFAULT);
        past_end.value = 6;
        let error = writer.add_checked_symbol(past_end).unwrap_err().to_string();
        assert!(error.contains("beyond its 0x8-byte section"), "{error}");
        assert!(
            writer.symbols.is_empty(),
            "refusals must not mutate the table"
        );

        let id = writer
            .add_checked_symbol(checked("f", 1, true, false, STV_DEFAULT))
            .unwrap();
        assert_eq!(writer.final_symbol_index(id), Ok(1));
        assert_eq!(
            writer.final_symbol_index(ElfSymbolId(7)),
            Err(ElfSymbolError::UnknownSymbol { ordinal: 7 })
        );
        assert!(matches!(
            writer.add_checked_symbol(checked("g", 1, true, false, STV_DEFAULT)),
            Err(ElfSymbolError::SymbolTableFrozen { .. })
        ));
        writer.write_checked().expect("frozen table still writes");
        // A legacy append after freezing would shift issued indices.
        writer.add_symbol("late", 1, 0, 0, false, STT_FUNC);
        let error = writer.write_checked().unwrap_err().to_string();
        assert!(error.contains("`late` was appended after"), "{error}");
    }

    /// A relocation whose patched field would run past the end of its
    /// section is refused by `write_checked`: the linker would write bytes
    /// belonging to whatever follows the section.
    #[test]
    fn write_checked_rejects_relocation_field_crossing_target_section_end() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_data_section(&[0; 8]);
        writer.add_symbol("target", 1, 0, 8, true, STT_OBJECT);
        writer.add_relocation(0, Elf64Rela::aarch64(1, 1, AArch64RelocType::Abs64, 0));
        let error = writer.write_checked().unwrap_err().to_string();
        assert!(
            error.contains("R_TYPE 257") && error.contains("[0x1, 0x9)") && error.contains("0x8"),
            "{error}"
        );

        // Control: the same field ending exactly at the section end is fine.
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_data_section(&[0; 8]);
        writer.add_symbol("target", 1, 0, 8, true, STT_OBJECT);
        writer.add_relocation(0, Elf64Rela::aarch64(0, 1, AArch64RelocType::Abs64, 0));
        writer
            .write_checked()
            .expect("an in-bounds relocation field is accepted");
    }

    /// An `r_type` the target machine's psABI table does not know has no
    /// defined field width: refuse it instead of guessing.
    #[test]
    fn write_checked_rejects_unknown_relocation_instead_of_guessing_field_width() {
        for (machine, reloc_type) in [
            (ElfMachine::AArch64, u32::MAX),
            // An x86-64 type number is not an AArch64 relocation.
            (ElfMachine::AArch64, R_X86_64_PLT32),
            (ElfMachine::X86_64, R_AARCH64_CALL26),
            (ElfMachine::Riscv64, R_X86_64_64),
        ] {
            let mut writer = ElfWriter::new(machine);
            writer.add_data_section(&[0; 8]);
            writer.add_symbol("target", 1, 0, 8, true, STT_OBJECT);
            writer.add_relocation(0, Elf64Rela::new(0, 1, reloc_type, 0));
            let error = writer.write_checked().unwrap_err().to_string();
            assert!(
                error.contains(&format!("unknown relocation type {reloc_type}")),
                "{machine:?}/{reloc_type}: {error}"
            );
        }
    }

    /// The per-machine field-width table covers every relocation the typed
    /// enums can spell, with the psABI widths (`R_RISCV_CALL*` patches the
    /// AUIPC+JALR pair; markers patch nothing).
    #[test]
    fn relocation_field_widths_follow_the_psabi_tables() {
        use crate::elf::reloc::{RiscvRelocType, elf_relocation_field_width};
        assert_eq!(
            elf_relocation_field_width(ElfMachine::AArch64, R_AARCH64_ABS64),
            Some(8)
        );
        assert_eq!(
            elf_relocation_field_width(ElfMachine::AArch64, R_AARCH64_CALL26),
            Some(4)
        );
        assert_eq!(
            elf_relocation_field_width(ElfMachine::X86_64, R_X86_64_PC8),
            Some(1)
        );
        assert_eq!(
            elf_relocation_field_width(ElfMachine::X86_64, R_X86_64_16),
            Some(2)
        );
        assert_eq!(
            elf_relocation_field_width(ElfMachine::Riscv64, RiscvRelocType::Call.to_type_val()),
            Some(8)
        );
        assert_eq!(
            elf_relocation_field_width(ElfMachine::Riscv64, R_RISCV_RELAX),
            Some(0)
        );
        assert_eq!(
            elf_relocation_field_width(ElfMachine::Riscv64, 0xFFFF),
            None
        );
    }

    /// `R_RISCV_RELAX` is a marker on the relocation it shares an offset
    /// with; standing alone it relaxes nothing and is refused. The paired
    /// form is accepted, even at a zero-width field.
    #[test]
    fn write_checked_pairs_riscv_relax_with_a_same_offset_relocation() {
        let mut writer = ElfWriter::new(ElfMachine::Riscv64);
        writer.add_text_section(&[0; 8]);
        writer.add_symbol("target", 1, 0, 8, true, STT_FUNC);
        writer.add_relocation(0, Elf64Rela::new(8, 0, R_RISCV_RELAX, 0));
        let error = writer.write_checked().unwrap_err().to_string();
        assert!(error.contains("R_RISCV_RELAX"), "{error}");

        let mut writer = ElfWriter::new(ElfMachine::Riscv64);
        writer.add_text_section(&[0; 8]);
        writer.add_symbol("target", 1, 0, 8, true, STT_FUNC);
        writer.add_relocation(0, Elf64Rela::new(0, 1, R_RISCV_CALL_PLT, 0));
        writer.add_relocation(0, Elf64Rela::new(0, 0, R_RISCV_RELAX, 0));
        let object = writer.write_checked().expect("valid CALL_PLT+RELAX pair");
        assert_eq!(&object[..4], b"\x7fELF");
    }

    /// Number of user sections the writer holds (the reparse intent lists
    /// exactly those): a refused `add_*` call must leave it unchanged.
    fn user_sections(writer: &ElfWriter) -> usize {
        writer.reparse_object_intent().sections.len()
    }

    /// `sh_addralign` is 0/1 or a power of two no larger than
    /// [`MAX_ELF_SECTION_ALIGN`] on every path that takes a caller's
    /// alignment; each refusal comes before the writer changes. Before the
    /// checks an alignment of 3 serialized unchallenged and 2^30 made the
    /// writer lay down a gigabyte of padding.
    #[test]
    fn section_alignment_is_a_power_of_two_within_the_cap() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&[0; 4]);
        // Group members are checked on a writer of their own: a group with no
        // member cannot be signed, so it is never serialized.
        let mut grouped = ElfWriter::new(ElfMachine::AArch64);
        let group = grouped.add_comdat_group();
        let flags = SHF_ALLOC | SHF_WRITE;
        let not_pow2 = |align| ElfSectionError::AlignmentNotPowerOfTwo {
            name: ".data".to_string(),
            align,
        };
        let too_large = |align| ElfSectionError::AlignmentTooLarge {
            name: ".data".to_string(),
            align,
            max: MAX_ELF_SECTION_ALIGN,
        };
        for (align, expected) in [
            (3, not_pow2(3)),
            (24, not_pow2(24)),
            (
                MAX_ELF_SECTION_ALIGN * 2,
                too_large(MAX_ELF_SECTION_ALIGN * 2),
            ),
            (1 << 40, too_large(1 << 40)),
        ] {
            let before = user_sections(&writer);
            assert_eq!(
                writer.add_section(".data", &[0; 8], SHT_PROGBITS, flags, align),
                Err(expected.clone())
            );
            assert_eq!(
                writer.add_section_with_entsize(".data", &[0; 8], SHT_PROGBITS, flags, align, 0),
                Err(expected.clone())
            );
            assert_eq!(
                grouped.add_group_member_section(
                    group,
                    ".data",
                    &[0; 8],
                    SHT_PROGBITS,
                    flags,
                    align,
                    0
                ),
                Err(expected.clone())
            );
            assert_eq!(user_sections(&grouped), 1, "align {align}: group changed");
            let rename = |error: ElfSectionError, name: &str| match error {
                ElfSectionError::AlignmentNotPowerOfTwo { align, .. } => {
                    ElfSectionError::AlignmentNotPowerOfTwo {
                        name: name.to_string(),
                        align,
                    }
                }
                ElfSectionError::AlignmentTooLarge { align, max, .. } => {
                    ElfSectionError::AlignmentTooLarge {
                        name: name.to_string(),
                        align,
                        max,
                    }
                }
                other => other,
            };
            assert_eq!(
                writer.add_nobits_section(".bss", 8, flags, align),
                Err(rename(expected.clone(), ".bss"))
            );
            assert_eq!(
                writer.add_text_section_with_align(&[0; 4], align),
                Err(rename(expected, ".text"))
            );
            assert_eq!(
                user_sections(&writer),
                before,
                "align {align}: writer changed"
            );
        }
        // Every power of two up to the cap is accepted, and 0 and 1 mean "no
        // constraint".
        for align in [0, 1, 2, 64, 4096, MAX_ELF_SECTION_ALIGN] {
            writer
                .add_nobits_section(".bss", 8, flags, align)
                .expect("a valid alignment");
        }
        writer
            .add_section(".data", &[1; 8], SHT_PROGBITS, flags, 16)
            .expect("a valid alignment");
        writer.write_checked().expect("a well-formed object");
    }

    /// A caller may add only the section types the writer serializes for it,
    /// with only the flags it can honour, in combinations the gABI gives a
    /// meaning. Each refusal comes before the writer changes.
    #[test]
    fn section_types_and_flags_the_writer_cannot_honour_are_refused() {
        use crate::elf::metadata::SHT_NOTE;
        const SHF_MERGE: u64 = 0x10;
        const SHF_STRINGS: u64 = 0x20;
        const SHF_LINK_ORDER: u64 = 0x80;
        const SHF_OS_NONCONFORMING: u64 = 0x100;
        const SHF_COMPRESSED: u64 = 0x800;
        const SHF_X86_64_LARGE: u64 = 0x1000_0000;

        let mut writer = ElfWriter::new(ElfMachine::X86_64);
        writer.add_text_section(&[0x90; 16]);
        let before = user_sections(&writer);
        for sh_type in [
            SHT_NULL,
            SHT_SYMTAB,
            SHT_STRTAB,
            SHT_RELA,
            SHT_GROUP,
            5,
            6,
            11,
            0x6fff_fff6,
        ] {
            let error = writer
                .add_section(".x", &[0; 16], sh_type, SHF_ALLOC, 8)
                .expect_err("a type the writer does not serialize for a caller");
            assert!(
                matches!(error, ElfSectionError::UnsupportedType { sh_type: refused, .. } if refused == sh_type),
                "{sh_type:#x}: {error}"
            );
        }
        for bits in [
            SHF_INFO_LINK,
            SHF_MERGE,
            SHF_STRINGS,
            SHF_LINK_ORDER,
            SHF_OS_NONCONFORMING,
            SHF_COMPRESSED,
            SHF_X86_64_LARGE,
            SHF_GROUP,
        ] {
            let error = writer
                .add_section(".x", &[0; 16], SHT_PROGBITS, SHF_ALLOC | bits, 8)
                .expect_err("a flag the writer cannot honour");
            assert!(
                matches!(error, ElfSectionError::UnsupportedFlags { flags, .. } if flags == bits),
                "{bits:#x}: {error}"
            );
        }
        for (sh_type, flags) in [
            (SHT_NOTE, SHF_ALLOC | SHF_WRITE | SHF_TLS),
            (SHT_INIT_ARRAY, SHF_ALLOC | SHF_WRITE | SHF_TLS),
            (SHT_PROGBITS, SHF_WRITE | SHF_TLS),
            (SHT_NOBITS, SHF_WRITE | SHF_TLS),
            (SHT_PROGBITS, SHF_ALLOC | SHF_EXECINSTR | SHF_TLS),
            (SHT_INIT_ARRAY, SHF_WRITE),
            (SHT_FINI_ARRAY, SHF_ALLOC | SHF_EXECINSTR),
            (SHT_PREINIT_ARRAY, 0),
        ] {
            let error = writer
                .add_section(".x", &[0; 16], sh_type, flags, 8)
                .expect_err("a type/flag combination with no meaning");
            assert!(
                matches!(error, ElfSectionError::TypeFlagMismatch { .. }),
                "{sh_type:#x}/{flags:#x}: {error}"
            );
        }
        let error = writer
            .add_section("bad\0name", &[0; 16], SHT_PROGBITS, SHF_ALLOC, 8)
            .expect_err("a NUL would truncate the name in .shstrtab");
        assert!(
            matches!(error, ElfSectionError::NameContainsNul { .. }),
            "{error}"
        );
        assert_eq!(
            user_sections(&writer),
            before,
            "a refused section changed the writer"
        );

        // The shapes the emitters produce are accepted and serialize.
        writer
            .add_section(
                ".tdata",
                &[1; 8],
                SHT_PROGBITS,
                SHF_ALLOC | SHF_WRITE | SHF_TLS,
                8,
            )
            .unwrap();
        writer
            .add_nobits_section(".tbss", 8, SHF_ALLOC | SHF_WRITE | SHF_TLS, 8)
            .unwrap();
        writer
            .add_section_with_entsize(
                ".init_array",
                &[0; 16],
                SHT_INIT_ARRAY,
                SHF_ALLOC | SHF_WRITE,
                8,
                8,
            )
            .unwrap();
        writer
            .add_section(
                ".rodata.keep",
                &[2; 4],
                SHT_PROGBITS,
                SHF_ALLOC | SHF_GNU_RETAIN,
                4,
            )
            .unwrap();
        writer
            .add_section(".gnu.lto_.opts", &[1], SHT_PROGBITS, SHF_EXCLUDE, 1)
            .unwrap();
        writer
            .add_section(".note.ABI-tag", &[0; 16], SHT_NOTE, SHF_ALLOC, 4)
            .unwrap();
        writer
            .add_section(".debug_str", b"a\0", SHT_PROGBITS, 0, 1)
            .unwrap();
        writer.add_note_gnu_stack();
        writer.write_checked().expect("a well-formed object");
    }

    /// A table section holds a whole number of entries, and an ELF64 pointer
    /// table's entries are 8-byte pointers whatever `sh_entsize` it states.
    #[test]
    fn table_sections_hold_whole_entries() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&[0; 4]);
        let flags = SHF_ALLOC | SHF_WRITE;
        let partial = |size, entsize| ElfSectionError::PartialEntry {
            name: ".init_array".to_string(),
            size,
            entsize,
        };
        assert_eq!(
            writer.add_section_with_entsize(".init_array", &[0; 12], SHT_INIT_ARRAY, flags, 8, 8),
            Err(partial(12, 8))
        );
        assert_eq!(
            writer.add_section(".init_array", &[0; 12], SHT_INIT_ARRAY, flags, 8),
            Err(partial(12, 8))
        );
        assert_eq!(
            writer.add_section_with_entsize(".init_array", &[0; 16], SHT_INIT_ARRAY, flags, 8, 4),
            Err(ElfSectionError::InvalidEntrySize {
                name: ".init_array".to_string(),
                sh_type: SHT_INIT_ARRAY,
                entsize: 4,
                reason: "an ELF64 constructor or destructor table holds 8-byte pointers",
            })
        );
        assert_eq!(
            writer.add_section_with_entsize(".tab", &[0; 6], SHT_PROGBITS, SHF_ALLOC, 4, 4),
            Err(ElfSectionError::PartialEntry {
                name: ".tab".to_string(),
                size: 6,
                entsize: 4,
            })
        );
        assert_eq!(user_sections(&writer), 1);
        writer
            .add_section(".init_array", &[0; 16], SHT_INIT_ARRAY, flags, 8)
            .expect("two pointers");
        writer
            .add_section_with_entsize(".tab", &[0; 8], SHT_PROGBITS, SHF_ALLOC, 4, 4)
            .expect("two entries");
        writer.write_checked().expect("a well-formed object");
    }

    /// Zero-fill is a length: a terabyte `.bss` costs the writer nothing,
    /// its intent carries no bytes, and the object records the full size.
    /// Before, the writer allocated `size` zero bytes for every NOBITS
    /// section (and the reparse intent cloned them).
    #[test]
    fn nobits_zero_fill_is_never_materialised() {
        const TIB: u64 = 1 << 40;
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&[0; 4]);
        let bss = writer
            .add_nobits_section(".bss.huge", TIB, SHF_ALLOC | SHF_WRITE, 4096)
            .expect("any u64 zero-fill size");
        let tbss = writer.add_bss_section(TIB / 2);
        // A zero image through the generic API is kept as a length too.
        let zeroes = writer
            .add_section(
                ".bss.small",
                &[0; 4096],
                SHT_NOBITS,
                SHF_ALLOC | SHF_WRITE,
                8,
            )
            .expect("an all-zero NOBITS image");
        let id = writer
            .add_checked_symbol(ElfSymbol {
                name: "huge".to_string(),
                section: bss,
                value: TIB - 8,
                size: 8,
                is_global: true,
                sym_type: STT_OBJECT,
                is_weak: false,
                visibility: STV_DEFAULT,
            })
            .expect("a symbol inside the zero-fill");
        assert_eq!(
            writer.add_checked_symbol(ElfSymbol {
                name: "past".to_string(),
                section: bss,
                value: TIB,
                size: 1,
                is_global: true,
                sym_type: STT_OBJECT,
                is_weak: false,
                visibility: STV_DEFAULT,
            }),
            Err(ElfSymbolError::RangeOutOfSection {
                symbol: "past".to_string(),
                value: TIB,
                size: 1,
                section_size: TIB,
            })
        );
        writer.final_symbol_index(id).unwrap();

        let intent = writer.reparse_object_intent();
        for (index, size) in [(bss, TIB), (tbss, TIB / 2), (zeroes, 4096)] {
            let section = &intent.sections[usize::from(index) - 1];
            assert_eq!(section.size, size, "{}", section.name);
            assert!(section.data.is_empty(), "{} materialised", section.name);
        }
        let bytes = writer.write_checked().expect("a well-formed object");
        assert!(
            bytes.len() < 4096,
            "zero fill took {} file bytes",
            bytes.len()
        );
        let sh_offset = read_u64(&bytes, 40) as usize;
        let size_of = |index: u16| {
            read_u64(
                &bytes,
                sh_offset + usize::from(index) * ELF64_SHDR_SIZE + 32,
            )
        };
        assert_eq!(
            (size_of(bss), size_of(tbss), size_of(zeroes)),
            (TIB, TIB / 2, 4096)
        );
    }

    /// A group handle another writer issued is refused before anything
    /// changes (the unchecked path indexed this writer's groups with it).
    #[test]
    fn group_member_with_a_foreign_group_handle_is_refused() {
        let mut other = ElfWriter::new(ElfMachine::AArch64);
        other.add_comdat_group();
        let foreign = other.add_comdat_group();
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&[0; 4]);
        assert_eq!(
            writer.add_group_member_section(
                foreign,
                ".text.f",
                &[0; 4],
                SHT_PROGBITS,
                SHF_ALLOC | SHF_EXECINSTR,
                4,
                0
            ),
            Err(ElfSectionError::UnknownGroup { group: 1 })
        );
        assert_eq!(user_sections(&writer), 1);
    }

    /// More section headers than the 16-bit header fields can name are
    /// refused instead of being truncated into other sections' indices.
    #[test]
    fn a_section_count_past_shn_loreserve_is_refused() {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        // null + N user sections + .symtab/.strtab/.shstrtab.
        for _ in 0..SHN_LORESERVE - 4 {
            writer.add_data_section(&[]);
        }
        writer
            .write_checked()
            .expect("exactly SHN_LORESERVE headers fit");
        writer.add_data_section(&[]);
        let error = writer
            .write_checked()
            .expect_err("one more header needs extended numbering");
        assert!(
            error
                .message
                .contains(&format!("needs {} section headers", SHN_LORESERVE + 1)),
            "{error}"
        );
    }
}
