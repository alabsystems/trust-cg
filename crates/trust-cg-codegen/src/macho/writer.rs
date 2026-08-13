// trust-cg-codegen/macho/writer.rs - Mach-O object file writer
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Assembles a complete Mach-O 64-bit relocatable object file (.o).
//!
//! Layout of a typical MH_OBJECT file:
//!
//! ```text
//! ┌──────────────────────────┐  offset 0
//! │    mach_header_64        │  32 bytes
//! ├──────────────────────────┤
//! │    Load commands:        │
//! │      LC_SEGMENT_64       │  72 + 80*nsects bytes
//! │      LC_BUILD_VERSION    │  24 bytes
//! │      LC_SYMTAB           │  24 bytes
//! │      LC_DYSYMTAB         │  80 bytes
//! ├──────────────────────────┤
//! │    Section data          │  (text, data, etc.)
//! ├──────────────────────────┤
//! │    Relocation entries    │  8 bytes each
//! ├──────────────────────────┤
//! │    Symbol table (nlist)  │  16 bytes each
//! ├──────────────────────────┤
//! │    String table          │  variable
//! └──────────────────────────┘
//! ```

use thiserror::Error;

use super::constants::*;
use super::header::MachHeader;
use super::reloc::{MachORelocationError, Relocation, encode_relocation_validated};
use super::section::{Section64, SegmentCommand64};
use super::x86_64_reloc::{X86_64Relocation, encode_x86_64_relocation_validated};

/// `n_desc` flag: weak reference (an undefined symbol that may stay unresolved).
///
/// Reference: `<mach-o/nlist.h>`.
pub const N_WEAK_REF: u16 = 0x0040;

/// `n_desc` flag: weak definition (a defined symbol the linker may coalesce or
/// override). This is the Mach-O equivalent of an ELF `STB_WEAK` definition and
/// is what tooling refers to as the "weak external"/`N_WEAK_EXT` flag.
///
/// Reference: `<mach-o/nlist.h>`.
pub const N_WEAK_DEF: u16 = 0x0080;

/// Target CPU for the Mach-O object file.
///
/// Determines the CPU type in the Mach-O header and which relocation
/// encoding is used.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MachOTarget {
    /// AArch64 (Apple Silicon).
    AArch64,
    /// x86-64 (Intel).
    X86_64,
}

/// A symbol to be emitted in the object file.
#[derive(Debug, Clone)]
pub struct Symbol {
    /// Symbol name (will be prefixed with '_' per Mach-O convention).
    pub name: String,
    /// Section index (1-based; 0 = N_UNDF).
    pub section: usize,
    /// Offset within the section.
    pub value: u64,
    /// Whether the symbol is externally visible.
    pub is_global: bool,
    /// Whether the symbol is weak.
    ///
    /// For a defined symbol this emits `N_WEAK_DEF` in `n_desc` (coalescable /
    /// overridable definition); for an undefined symbol it emits `N_WEAK_REF`
    /// (the reference may stay unresolved). Defaults to `false`.
    pub is_weak: bool,
}

impl Symbol {
    /// Compute the `n_desc` value for this symbol, encoding the weak flags.
    fn n_desc(&self) -> u16 {
        if !self.is_weak {
            return 0;
        }
        if self.section == 0 {
            // Undefined weak reference.
            N_WEAK_REF
        } else {
            // Defined weak ("weak external") definition.
            N_WEAK_DEF
        }
    }
}

/// Stable insertion-time symbol id used to query final Mach-O symbol order.
pub type SymbolId = usize;

/// A target-independent relocation that holds either AArch64 or x86-64 data.
#[derive(Debug, Clone)]
pub enum MachORelocation {
    /// AArch64 relocation.
    AArch64(Relocation),
    /// x86-64 relocation.
    X86_64(X86_64Relocation),
}

/// Internal section data held by the writer.
#[derive(Debug, Clone)]
struct SectionData {
    /// Section name (e.g., b"__text").
    sectname: Vec<u8>,
    /// Segment name (e.g., b"__TEXT").
    segname: Vec<u8>,
    /// Section content bytes.
    data: Vec<u8>,
    /// Alignment as power of 2.
    align: u32,
    /// Section flags.
    flags: u32,
    /// AArch64 relocations for this section.
    relocations: Vec<Relocation>,
    /// x86-64 relocations for this section.
    x86_64_relocations: Vec<X86_64Relocation>,
}

/// Fail-closed errors from Mach-O layout planning and serialization.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum MachOWriteError {
    #[error("Mach-O relocation validation failed: {0}")]
    Relocation(#[from] MachORelocationError),
    #[error("Mach-O field `{field}` value {value} exceeds maximum {max}")]
    FieldOutOfRange {
        field: &'static str,
        value: u128,
        max: u128,
    },
    #[error(
        "Mach-O {owner} alignment exponent {align_log2} exceeds the checked u64 shift maximum {max_align_log2}"
    )]
    InvalidAlignment {
        owner: String,
        align_log2: u32,
        max_align_log2: u32,
    },
    #[error(
        "Mach-O symbol `{symbol}` section ordinal {section} is invalid for {section_count} section(s) (maximum encodable ordinal {max_supported_ordinal})"
    )]
    SymbolSectionOutOfRange {
        symbol: String,
        section: usize,
        section_count: usize,
        max_supported_ordinal: u8,
    },
    #[error(
        "Mach-O symbol `{symbol}` offset {offset} exceeds section {section} size {section_size}"
    )]
    SymbolOffsetOutOfRange {
        symbol: String,
        section: usize,
        offset: u64,
        section_size: u64,
    },
    #[error("Mach-O {kind} name exceeds 16 bytes ({len} bytes)")]
    SectionNameTooLong { kind: &'static str, len: usize },
    #[error("Mach-O {kind} name contains an interior NUL byte")]
    NameContainsNul { kind: &'static str },
    #[error(
        "Mach-O {architecture} relocation {relocation_index} in section {section} references {reference_kind} {reference} but only {available} exist"
    )]
    RelocationReferenceOutOfRange {
        architecture: &'static str,
        section: usize,
        relocation_index: usize,
        reference_kind: &'static str,
        reference: u32,
        available: usize,
    },
    #[error(
        "Mach-O {architecture} relocation {relocation_index} in section {section} spans bytes {offset}..{end}, outside the section size {section_size}"
    )]
    RelocationFieldOutOfRange {
        architecture: &'static str,
        section: usize,
        relocation_index: usize,
        offset: u32,
        end: u64,
        section_size: u64,
    },
    #[error("Mach-O {operation} allocation for {requested_capacity} elements failed")]
    AllocationFailed {
        operation: &'static str,
        requested_capacity: usize,
    },
    #[error("Mach-O {kind} index {index} is out of range for {count} entries")]
    IndexOutOfRange {
        kind: &'static str,
        index: usize,
        count: usize,
    },
    #[error(
        "Mach-O serializer layout drift at {stage}: planned offset {expected}, actual offset {actual}"
    )]
    LayoutMismatch {
        stage: &'static str,
        expected: usize,
        actual: usize,
    },
    #[error("Mach-O enforce-mode reparse gate rejected serialization: {0}")]
    ReparseGate(String),
    #[error(
        "Mach-O symbol table is frozen because final indices or external relocations were already exposed"
    )]
    SymbolTableFrozen,
}

#[derive(Debug)]
struct MachOLayoutPlan {
    nsects: u32,
    segment_cmd_size: u32,
    total_lc_size: u32,
    header_plus_lc: usize,
    section_offsets: Vec<u32>,
    section_vmaddrs: Vec<u64>,
    section_sizes: Vec<u64>,
    relocation_offsets: Vec<u32>,
    relocation_counts: Vec<u32>,
    section_data_end: usize,
    symtab_off: u32,
    nsyms: u32,
    strtab_off: u32,
    strtab_size: u32,
    strtab: Vec<u8>,
    str_offsets: Vec<u32>,
    ordered_symbol_indices: Vec<usize>,
    symbol_sections: Vec<u8>,
    symbol_values: Vec<u64>,
    nlocalsym: u32,
    nextdefsym: u32,
    iundefsym: u32,
    nundefsym: u32,
    vmsize: u64,
    fileoff: u64,
    filesize: u64,
    file_len: usize,
}

fn macho_field_u32(field: &'static str, value: u128) -> Result<u32, MachOWriteError> {
    u32::try_from(value).map_err(|_| MachOWriteError::FieldOutOfRange {
        field,
        value,
        max: u128::from(u32::MAX),
    })
}

fn macho_field_u64(field: &'static str, value: u128) -> Result<u64, MachOWriteError> {
    u64::try_from(value).map_err(|_| MachOWriteError::FieldOutOfRange {
        field,
        value,
        max: u128::from(u64::MAX),
    })
}

fn macho_field_usize(field: &'static str, value: u128) -> Result<usize, MachOWriteError> {
    usize::try_from(value).map_err(|_| MachOWriteError::FieldOutOfRange {
        field,
        value,
        max: usize::MAX as u128,
    })
}

fn checked_macho_align_u64(
    owner: impl Into<String>,
    value: u64,
    align_log2: u32,
) -> Result<u64, MachOWriteError> {
    let owner = owner.into();
    let alignment =
        1u64.checked_shl(align_log2)
            .ok_or_else(|| MachOWriteError::InvalidAlignment {
                owner: owner.clone(),
                align_log2,
                max_align_log2: 63,
            })?;
    let padding = (alignment - (value % alignment)) % alignment;
    macho_field_u64("aligned offset", u128::from(value) + u128::from(padding))
}

fn reserve_macho_exact<T>(
    vec: &mut Vec<T>,
    additional: usize,
    operation: &'static str,
) -> Result<(), MachOWriteError> {
    vec.try_reserve_exact(additional)
        .map_err(|_| MachOWriteError::AllocationFailed {
            operation,
            requested_capacity: additional,
        })
}

fn clone_macho_bytes(bytes: &[u8], operation: &'static str) -> Result<Vec<u8>, MachOWriteError> {
    let mut copy = Vec::new();
    reserve_macho_exact(&mut copy, bytes.len(), operation)?;
    copy.extend_from_slice(bytes);
    Ok(copy)
}

fn clone_macho_string(string: &str, operation: &'static str) -> Result<String, MachOWriteError> {
    let mut copy = String::new();
    copy.try_reserve_exact(string.len())
        .map_err(|_| MachOWriteError::AllocationFailed {
            operation,
            requested_capacity: string.len(),
        })?;
    copy.push_str(string);
    Ok(copy)
}

/// Assembles a complete Mach-O 64-bit relocatable object file.
///
/// Supports both AArch64 and x86-64 targets. The target is selected at
/// construction time and determines the CPU type in the header, the text
/// section alignment, and which relocation encoding is used.
///
/// # Example
///
/// ```
/// use trust_cg_codegen::macho::{MachOWriter, MachOTarget};
///
/// // AArch64 (default)
/// let mut writer = MachOWriter::new();
/// writer.add_text_section(&[0x1F, 0x20, 0x03, 0xD5]);
/// writer.add_symbol("_main", 1, 0, true).unwrap();
/// let bytes = writer.write().unwrap();
///
/// // x86-64
/// let mut writer = MachOWriter::for_target(MachOTarget::X86_64);
/// writer.add_text_section(&[0xC3]);
// RET
/// writer.add_symbol("_main", 1, 0, true).unwrap();
/// let bytes = writer.write().unwrap();
/// ```
pub struct MachOWriter {
    /// Target CPU for this object file.
    target: MachOTarget,
    sections: Vec<SectionData>,
    symbols: Vec<Symbol>,
    /// Once a final symbol index is observed or an external relocation is
    /// stored, later insertion could invalidate that index. Freeze instead.
    symbols_frozen: bool,
    /// Cache of the final (link-editor-ordered) symtab index for each symbol,
    /// indexed by `SymbolId`. The mapping is a pure function of the frozen
    /// symbol table — locals first, then defined globals, then undefined
    /// globals, each in insertion order — so it is computed once in O(n) and
    /// reused, replacing the previous O(n)-per-lookup / O(n^2)-per-object scan.
    /// `None` until the first `final_symbol_index` call freezes the table.
    final_symbol_indices: Option<Vec<u32>>,
}

impl MachOWriter {
    /// Create a new empty Mach-O writer for AArch64 (default target).
    pub fn new() -> Self {
        Self {
            target: MachOTarget::AArch64,
            sections: Vec::new(),
            symbols: Vec::new(),
            symbols_frozen: false,
            final_symbol_indices: None,
        }
    }

    /// Create a new empty Mach-O writer for the specified target.
    pub fn for_target(target: MachOTarget) -> Self {
        Self {
            target,
            sections: Vec::new(),
            symbols: Vec::new(),
            symbols_frozen: false,
            final_symbol_indices: None,
        }
    }

    /// Returns the target CPU for this writer.
    pub fn target(&self) -> MachOTarget {
        self.target
    }

    /// Add a text section (__text in __TEXT) with the given machine code bytes.
    ///
    /// Alignment is chosen based on the target:
    /// - AArch64: 4-byte aligned (2^2) for fixed-width instructions
    /// - x86-64: 16-byte aligned (2^4) per System V ABI convention
    pub fn add_text_section(&mut self, code: &[u8]) {
        let align = match self.target {
            MachOTarget::AArch64 => 2, // 2^2 = 4-byte
            MachOTarget::X86_64 => 4,  // 2^4 = 16-byte
        };
        self.add_text_section_with_align(code, align);
    }

    /// Like [`add_text_section`](Self::add_text_section) with an explicit
    /// alignment exponent (log2 bytes). Used when the emitted code carries
    /// function-relative alignment padding (loop-head alignment): the section
    /// must be at least as aligned as the strongest per-function request, or
    /// the linker may place it so the padded boundaries land off-boundary in
    /// the final image.
    pub fn add_text_section_with_align(&mut self, code: &[u8], align: u32) {
        self.sections.push(SectionData {
            sectname: b"__text".to_vec(),
            segname: b"__TEXT".to_vec(),
            data: code.to_vec(),
            align,
            flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS,
            relocations: Vec::new(),
            x86_64_relocations: Vec::new(),
        });
    }

    /// Add a data section (__data in __DATA) with the given data bytes.
    pub fn add_data_section(&mut self, data: &[u8]) {
        self.sections.push(SectionData {
            sectname: b"__data".to_vec(),
            segname: b"__DATA".to_vec(),
            data: data.to_vec(),
            align: 3, // 2^3 = 8-byte alignment
            flags: S_REGULAR,
            relocations: Vec::new(),
            x86_64_relocations: Vec::new(),
        });
    }

    /// Add a custom section with the given name, segment, data, alignment, and flags.
    ///
    /// This is used for sections like `__LD,__compact_unwind` that don't fit
    /// the standard `__TEXT/__text` or `__DATA/__data` patterns.
    ///
    /// - `sectname`: Section name (e.g., b"__compact_unwind"), max 16 bytes.
    /// - `segname`: Segment name (e.g., b"__LD"), max 16 bytes.
    /// - `data`: Section content bytes.
    /// - `align`: Alignment as power of 2 (e.g., 3 means 8-byte aligned).
    /// - `flags`: Section flags (e.g., S_ATTR_DEBUG).
    ///
    /// Returns the 0-based section index.
    pub fn add_custom_section(
        &mut self,
        sectname: &[u8],
        segname: &[u8],
        data: &[u8],
        align: u32,
        flags: u32,
    ) -> usize {
        let index = self.sections.len();
        self.sections.push(SectionData {
            sectname: sectname.to_vec(),
            segname: segname.to_vec(),
            data: data.to_vec(),
            align,
            flags,
            relocations: Vec::new(),
            x86_64_relocations: Vec::new(),
        });
        index
    }

    /// Add a symbol to the object file.
    ///
    /// - `name`: Symbol name (Mach-O convention adds '_' prefix; caller should
    ///   include it if desired, e.g., "_main").
    /// - `section`: 1-based section index (order of add_text_section / add_data_section calls).
    /// - `offset`: Byte offset within the section.
    /// - `is_global`: Whether the symbol is externally visible.
    pub fn add_symbol(
        &mut self,
        name: &str,
        section: usize,
        offset: u64,
        is_global: bool,
    ) -> Result<SymbolId, MachOWriteError> {
        self.add_symbol_impl(name, section, offset, is_global, false)
    }

    /// Add a weak symbol to the object file.
    ///
    /// A defined weak symbol (`section != 0`) is emitted with the `N_WEAK_DEF`
    /// flag in `n_desc` (a coalescable / overridable definition); a weak
    /// undefined symbol (`section == 0`) is emitted with `N_WEAK_REF` (the
    /// reference may stay unresolved at link time).
    ///
    /// Arguments mirror [`add_symbol`](Self::add_symbol).
    pub fn add_weak_symbol(
        &mut self,
        name: &str,
        section: usize,
        offset: u64,
        is_global: bool,
    ) -> Result<SymbolId, MachOWriteError> {
        self.add_symbol_impl(name, section, offset, is_global, true)
    }

    fn add_symbol_impl(
        &mut self,
        name: &str,
        section: usize,
        offset: u64,
        is_global: bool,
        is_weak: bool,
    ) -> Result<SymbolId, MachOWriteError> {
        if self.symbols_frozen {
            return Err(MachOWriteError::SymbolTableFrozen);
        }
        if name.as_bytes().contains(&0) {
            return Err(MachOWriteError::NameContainsNul { kind: "symbol" });
        }
        if section > self.sections.len() || section > usize::from(u8::MAX) {
            return Err(MachOWriteError::SymbolSectionOutOfRange {
                symbol: name.to_string(),
                section,
                section_count: self.sections.len(),
                max_supported_ordinal: u8::MAX,
            });
        }
        if section != 0 {
            let section_size = macho_field_u64(
                "section byte length",
                self.sections[section - 1].data.len() as u128,
            )?;
            if offset > section_size {
                return Err(MachOWriteError::SymbolOffsetOutOfRange {
                    symbol: name.to_string(),
                    section,
                    offset,
                    section_size,
                });
            }
        }
        let mut owned_name = String::new();
        owned_name.try_reserve_exact(name.len()).map_err(|_| {
            MachOWriteError::AllocationFailed {
                operation: "symbol name",
                requested_capacity: name.len(),
            }
        })?;
        owned_name.push_str(name);
        self.symbols
            .try_reserve(1)
            .map_err(|_| MachOWriteError::AllocationFailed {
                operation: "symbol table growth",
                requested_capacity: self.symbols.len().saturating_add(1),
            })?;
        let id = self.symbols.len();
        self.symbols.push(Symbol {
            name: owned_name,
            section,
            value: offset,
            is_global,
            is_weak,
        });
        Ok(id)
    }

    /// Add an AArch64 relocation entry to the specified section.
    ///
    /// - `section`: 0-based section index.
    /// - `reloc`: The AArch64 relocation entry.
    pub fn add_relocation(
        &mut self,
        section: usize,
        reloc: Relocation,
    ) -> Result<(), MachORelocationError> {
        if self.target != MachOTarget::AArch64 {
            return Err(MachORelocationError::TargetMismatch {
                writer_target: "x86-64",
                relocation_target: "AArch64",
            });
        }
        if section >= self.sections.len() {
            return Err(MachORelocationError::SectionIndexOutOfRange {
                section,
                section_count: self.sections.len(),
            });
        }
        reloc.validate()?;
        self.sections[section]
            .relocations
            .try_reserve(1)
            .map_err(|_| MachORelocationError::StorageAllocationFailed)?;
        let freezes_symbols = reloc.is_extern;
        self.sections[section].relocations.push(reloc);
        self.symbols_frozen |= freezes_symbols;
        Ok(())
    }

    /// Add an x86-64 relocation entry to the specified section.
    ///
    /// - `section`: 0-based section index.
    /// - `reloc`: The x86-64 relocation entry.
    pub fn add_x86_64_relocation(
        &mut self,
        section: usize,
        reloc: X86_64Relocation,
    ) -> Result<(), MachORelocationError> {
        if self.target != MachOTarget::X86_64 {
            return Err(MachORelocationError::TargetMismatch {
                writer_target: "AArch64",
                relocation_target: "x86-64",
            });
        }
        if section >= self.sections.len() {
            return Err(MachORelocationError::SectionIndexOutOfRange {
                section,
                section_count: self.sections.len(),
            });
        }
        reloc.validate()?;
        self.sections[section]
            .x86_64_relocations
            .try_reserve(1)
            .map_err(|_| MachORelocationError::StorageAllocationFailed)?;
        let freezes_symbols = reloc.is_extern;
        self.sections[section].x86_64_relocations.push(reloc);
        self.symbols_frozen |= freezes_symbols;
        Ok(())
    }

    /// Returns the total number of relocations for a section (across both targets).
    fn section_reloc_count(&self, sec: &SectionData) -> Result<u32, MachOWriteError> {
        macho_field_u32(
            "section relocation count",
            (sec.relocations.len() as u128) + (sec.x86_64_relocations.len() as u128),
        )
    }

    fn validate_relocation_record(
        &self,
        architecture: &'static str,
        section: usize,
        relocation_index: usize,
        offset: u32,
        length: u8,
        is_extern: bool,
        reference: u32,
        is_addend: bool,
        section_size: u64,
    ) -> Result<(), MachOWriteError> {
        let width =
            1u64.checked_shl(u32::from(length))
                .ok_or(MachOWriteError::FieldOutOfRange {
                    field: "relocation field width",
                    value: u128::from(length),
                    max: 3,
                })?;
        let end = macho_field_u64(
            "relocation field end",
            u128::from(offset) + u128::from(width),
        )?;
        if end > section_size {
            return Err(MachOWriteError::RelocationFieldOutOfRange {
                architecture,
                section,
                relocation_index,
                offset,
                end,
                section_size,
            });
        }

        if is_extern {
            if (reference as usize) >= self.symbols.len() {
                return Err(MachOWriteError::RelocationReferenceOutOfRange {
                    architecture,
                    section,
                    relocation_index,
                    reference_kind: "symbol index",
                    reference,
                    available: self.symbols.len(),
                });
            }
        } else if !is_addend && (reference == 0 || (reference as usize) > self.sections.len()) {
            return Err(MachOWriteError::RelocationReferenceOutOfRange {
                architecture,
                section,
                relocation_index,
                reference_kind: "section ordinal",
                reference,
                available: self.sections.len(),
            });
        }
        Ok(())
    }

    fn layout_plan(&self) -> Result<MachOLayoutPlan, MachOWriteError> {
        let nsects = macho_field_u32("section count", self.sections.len() as u128)?;
        let segment_cmd_size = macho_field_u32(
            "segment command size",
            u128::from(SEGMENT_COMMAND_64_SIZE) + u128::from(nsects) * u128::from(SECTION_64_SIZE),
        )?;
        let total_lc_size = macho_field_u32(
            "load command byte length",
            u128::from(segment_cmd_size)
                + u128::from(BUILD_VERSION_COMMAND_SIZE)
                + u128::from(SYMTAB_COMMAND_SIZE)
                + u128::from(DYSYMTAB_COMMAND_SIZE),
        )?;
        let header_plus_lc_u64 = macho_field_u64(
            "header and load command byte length",
            u128::from(MACH_HEADER_64_SIZE) + u128::from(total_lc_size),
        )?;
        let header_plus_lc = macho_field_usize(
            "header and load command host byte length",
            u128::from(header_plus_lc_u64),
        )?;

        let mut section_offsets = Vec::new();
        let mut section_vmaddrs = Vec::new();
        let mut section_sizes = Vec::new();
        reserve_macho_exact(
            &mut section_offsets,
            self.sections.len(),
            "section file-offset plan",
        )?;
        reserve_macho_exact(
            &mut section_vmaddrs,
            self.sections.len(),
            "section virtual-address plan",
        )?;
        reserve_macho_exact(&mut section_sizes, self.sections.len(), "section size plan")?;

        let mut file_cursor = header_plus_lc_u64;
        let mut vm_cursor = 0u64;
        for (i, sec) in self.sections.iter().enumerate() {
            for (kind, name) in [("section", &sec.sectname), ("segment", &sec.segname)] {
                if name.len() > 16 {
                    return Err(MachOWriteError::SectionNameTooLong {
                        kind,
                        len: name.len(),
                    });
                }
                if name.contains(&0) {
                    return Err(MachOWriteError::NameContainsNul { kind });
                }
            }
            file_cursor = checked_macho_align_u64(
                format!("section {i} file offset"),
                file_cursor,
                sec.align,
            )?;
            vm_cursor = checked_macho_align_u64(
                format!("section {i} virtual address"),
                vm_cursor,
                sec.align,
            )?;
            section_offsets.push(macho_field_u32(
                "section file offset",
                u128::from(file_cursor),
            )?);
            section_vmaddrs.push(vm_cursor);
            let section_size = macho_field_u64("section byte length", sec.data.len() as u128)?;
            section_sizes.push(section_size);
            file_cursor = macho_field_u64(
                "section data end",
                u128::from(file_cursor) + u128::from(section_size),
            )?;
            // Every later table offset is u32 in Mach-O. Fail at the section
            // that crosses the boundary, before allocating the output buffer.
            macho_field_u32("section data end", u128::from(file_cursor))?;
            vm_cursor = macho_field_u64(
                "section virtual end",
                u128::from(vm_cursor) + u128::from(section_size),
            )?;
        }
        let section_data_end = macho_field_usize("section data host end", u128::from(file_cursor))?;

        let mut relocation_offsets = Vec::new();
        let mut relocation_counts = Vec::new();
        reserve_macho_exact(
            &mut relocation_offsets,
            self.sections.len(),
            "section relocation-offset plan",
        )?;
        reserve_macho_exact(
            &mut relocation_counts,
            self.sections.len(),
            "section relocation-count plan",
        )?;
        let mut relocation_cursor = file_cursor;
        for (section_index, sec) in self.sections.iter().enumerate() {
            if self.target == MachOTarget::AArch64 && !sec.x86_64_relocations.is_empty() {
                return Err(MachORelocationError::TargetMismatch {
                    writer_target: "AArch64",
                    relocation_target: "x86-64",
                }
                .into());
            }
            if self.target == MachOTarget::X86_64 && !sec.relocations.is_empty() {
                return Err(MachORelocationError::TargetMismatch {
                    writer_target: "x86-64",
                    relocation_target: "AArch64",
                }
                .into());
            }
            for (relocation_index, reloc) in sec.relocations.iter().enumerate() {
                reloc.validate()?;
                self.validate_relocation_record(
                    "AArch64",
                    section_index,
                    relocation_index,
                    reloc.offset,
                    reloc.length,
                    reloc.is_extern,
                    reloc.symbol_index,
                    reloc.kind == super::reloc::AArch64RelocKind::Addend,
                    section_sizes[section_index],
                )?;
            }
            for (relocation_index, reloc) in sec.x86_64_relocations.iter().enumerate() {
                reloc.validate()?;
                self.validate_relocation_record(
                    "x86-64",
                    section_index,
                    relocation_index,
                    reloc.offset,
                    reloc.length,
                    reloc.is_extern,
                    reloc.symbol_index,
                    false,
                    section_sizes[section_index],
                )?;
            }
            let count = self.section_reloc_count(sec)?;
            relocation_counts.push(count);
            relocation_offsets.push(if count == 0 {
                0
            } else {
                macho_field_u32("section relocation offset", u128::from(relocation_cursor))?
            });
            relocation_cursor = macho_field_u64(
                "relocation table end",
                u128::from(relocation_cursor)
                    + u128::from(count) * u128::from(RELOCATION_INFO_SIZE),
            )?;
            macho_field_u32("relocation table end", u128::from(relocation_cursor))?;
        }
        let symtab_off = macho_field_u32("symbol table offset", u128::from(relocation_cursor))?;

        let nsyms = macho_field_u32("symbol count", self.symbols.len() as u128)?;
        let nlocals_usize = self.symbols.iter().filter(|sym| !sym.is_global).count();
        let nextdef_usize = self
            .symbols
            .iter()
            .filter(|sym| sym.is_global && sym.section != 0)
            .count();
        let nundef_usize = self
            .symbols
            .iter()
            .filter(|sym| sym.is_global && sym.section == 0)
            .count();
        let nlocalsym = macho_field_u32("local symbol count", nlocals_usize as u128)?;
        let nextdefsym = macho_field_u32("defined external symbol count", nextdef_usize as u128)?;
        let nundefsym = macho_field_u32("undefined symbol count", nundef_usize as u128)?;
        let iundefsym = macho_field_u32(
            "undefined symbol start index",
            u128::from(nlocalsym) + u128::from(nextdefsym),
        )?;

        let mut ordered_symbol_indices = Vec::new();
        reserve_macho_exact(
            &mut ordered_symbol_indices,
            self.symbols.len(),
            "ordered symbol-index plan",
        )?;
        for wanted_class in 0..3 {
            for (index, sym) in self.symbols.iter().enumerate() {
                let class = if !sym.is_global {
                    0
                } else if sym.section != 0 {
                    1
                } else {
                    2
                };
                if class == wanted_class {
                    ordered_symbol_indices.push(index);
                }
            }
        }

        let mut strtab = Vec::new();
        reserve_macho_exact(&mut strtab, 1, "string table")?;
        strtab.push(0);
        let mut str_offsets = Vec::new();
        reserve_macho_exact(
            &mut str_offsets,
            self.symbols.len(),
            "symbol string-offset plan",
        )?;
        for sym in &self.symbols {
            if sym.name.as_bytes().contains(&0) {
                return Err(MachOWriteError::NameContainsNul { kind: "symbol" });
            }
            str_offsets.push(macho_field_u32(
                "symbol string-table offset",
                strtab.len() as u128,
            )?);
            let additional =
                macho_field_usize("symbol string-table growth", (sym.name.len() as u128) + 1)?;
            strtab
                .try_reserve(additional)
                .map_err(|_| MachOWriteError::AllocationFailed {
                    operation: "string table growth",
                    requested_capacity: additional,
                })?;
            strtab.extend_from_slice(sym.name.as_bytes());
            strtab.push(0);
        }
        let strtab_size = macho_field_u32("string table byte length", strtab.len() as u128)?;
        let strtab_off = macho_field_u32(
            "string table offset",
            u128::from(symtab_off) + u128::from(nsyms) * u128::from(NLIST_64_SIZE),
        )?;

        let mut symbol_sections = Vec::new();
        let mut symbol_values = Vec::new();
        reserve_macho_exact(
            &mut symbol_sections,
            self.symbols.len(),
            "symbol section-ordinal plan",
        )?;
        reserve_macho_exact(
            &mut symbol_values,
            self.symbols.len(),
            "symbol n_value plan",
        )?;
        for sym in &self.symbols {
            if sym.section == 0 {
                symbol_sections.push(0);
                symbol_values.push(0);
                continue;
            }
            if sym.section > self.sections.len() || sym.section > usize::from(u8::MAX) {
                return Err(MachOWriteError::SymbolSectionOutOfRange {
                    symbol: sym.name.clone(),
                    section: sym.section,
                    section_count: self.sections.len(),
                    max_supported_ordinal: u8::MAX,
                });
            }
            let section_index = sym.section - 1;
            if sym.value > section_sizes[section_index] {
                return Err(MachOWriteError::SymbolOffsetOutOfRange {
                    symbol: sym.name.clone(),
                    section: sym.section,
                    offset: sym.value,
                    section_size: section_sizes[section_index],
                });
            }
            let ordinal = u8::try_from(sym.section).map_err(|_| {
                MachOWriteError::SymbolSectionOutOfRange {
                    symbol: sym.name.clone(),
                    section: sym.section,
                    section_count: self.sections.len(),
                    max_supported_ordinal: u8::MAX,
                }
            })?;
            symbol_sections.push(ordinal);
            symbol_values.push(macho_field_u64(
                "symbol n_value",
                u128::from(section_vmaddrs[section_index]) + u128::from(sym.value),
            )?);
        }

        let file_len = macho_field_usize(
            "Mach-O output byte length",
            u128::from(strtab_off) + u128::from(strtab_size),
        )?;
        let fileoff = section_offsets.first().copied().map(u64::from).unwrap_or(0);
        let filesize = if self.sections.is_empty() {
            0
        } else {
            macho_field_u64(
                "segment file size",
                (section_data_end as u128) - u128::from(fileoff),
            )?
        };

        Ok(MachOLayoutPlan {
            nsects,
            segment_cmd_size,
            total_lc_size,
            header_plus_lc,
            section_offsets,
            section_vmaddrs,
            section_sizes,
            relocation_offsets,
            relocation_counts,
            section_data_end,
            symtab_off,
            nsyms,
            strtab_off,
            strtab_size,
            strtab,
            str_offsets,
            ordered_symbol_indices,
            symbol_sections,
            symbol_values,
            nlocalsym,
            nextdefsym,
            iundefsym,
            nundefsym,
            vmsize: vm_cursor,
            fileoff,
            filesize,
            file_len,
        })
    }

    /// Return the final `nlist_64` index for an insertion-time symbol id.
    pub fn final_symbol_index(
        &mut self,
        symbol_id: SymbolId,
    ) -> Result<Option<u32>, MachOWriteError> {
        if symbol_id >= self.symbols.len() {
            return Ok(None);
        }
        self.symbols_frozen = true;
        if self.final_symbol_indices.is_none() {
            self.final_symbol_indices = Some(self.compute_final_symbol_indices()?);
        }
        // Safe: just populated above if it was None.
        Ok(Some(
            self.final_symbol_indices.as_ref().expect("cache populated")[symbol_id],
        ))
    }

    /// Compute the final (link-editor-ordered) symtab index for every symbol in
    /// one O(n) pass. The symbol table is frozen before this runs, so the result
    /// is stable for the lifetime of the writer.
    ///
    /// The ordering — and therefore the per-symbol formulas — are exactly the
    /// ones the previous per-call scan produced:
    /// - a local's index = number of preceding locals;
    /// - a defined global's index = (total locals) + preceding defined globals;
    /// - an undefined global's index =
    ///   (total locals) + (total defined globals) + preceding undefined globals.
    /// Maintaining the three running ranks in insertion order reproduces those
    /// counts without the per-symbol re-scan. The same `macho_field_u32` range
    /// checks (symbol count and each final index fitting `u32`) are preserved.
    fn compute_final_symbol_indices(&self) -> Result<Vec<u32>, MachOWriteError> {
        macho_field_u32("symbol count", self.symbols.len() as u128)?;
        let total_locals = self.symbols.iter().filter(|sym| !sym.is_global).count();
        let total_definitions = self
            .symbols
            .iter()
            .filter(|sym| sym.is_global && sym.section != 0)
            .count();

        let mut indices = Vec::with_capacity(self.symbols.len());
        let mut local_rank: usize = 0;
        let mut defined_global_rank: usize = 0;
        let mut undefined_global_rank: usize = 0;
        for sym in &self.symbols {
            let preceding = if !sym.is_global {
                let v = local_rank;
                local_rank += 1;
                v
            } else if sym.section != 0 {
                let v = total_locals + defined_global_rank;
                defined_global_rank += 1;
                v
            } else {
                let v = total_locals + total_definitions + undefined_global_rank;
                undefined_global_rank += 1;
                v
            };
            indices.push(macho_field_u32("final symbol index", preceding as u128)?);
        }
        Ok(indices)
    }

    /// Provisional in-object vmaddr of section `index` (0-based).
    pub fn section_vmaddr(&self, index: usize) -> Result<u64, MachOWriteError> {
        if index >= self.sections.len() {
            return Err(MachOWriteError::IndexOutOfRange {
                kind: "section",
                index,
                count: self.sections.len(),
            });
        }
        let mut addr = 0u64;
        for (i, sec) in self.sections.iter().enumerate() {
            addr =
                checked_macho_align_u64(format!("section {i} virtual address"), addr, sec.align)?;
            if i == index {
                return Ok(addr);
            }
            addr = macho_field_u64(
                "section virtual end",
                u128::from(addr) + (sec.data.len() as u128),
            )?;
        }
        Err(MachOWriteError::IndexOutOfRange {
            kind: "section",
            index,
            count: self.sections.len(),
        })
    }

    /// Provisional vmaddr for a not-yet-added section.
    pub fn next_section_vmaddr(&self, align_log2: u32) -> Result<u64, MachOWriteError> {
        let mut addr = 0u64;
        for (i, sec) in self.sections.iter().enumerate() {
            addr =
                checked_macho_align_u64(format!("section {i} virtual address"), addr, sec.align)?;
            addr = macho_field_u64(
                "section virtual end",
                u128::from(addr) + (sec.data.len() as u128),
            )?;
        }
        checked_macho_align_u64("next section virtual address", addr, align_log2)
    }

    /// Provisional in-object vmaddr of a defined symbol; undefined symbols map
    /// to zero. Invalid symbol ids and section ordinals fail closed.
    pub fn symbol_vmaddr(&self, symbol_id: SymbolId) -> Result<u64, MachOWriteError> {
        let sym = self
            .symbols
            .get(symbol_id)
            .ok_or(MachOWriteError::IndexOutOfRange {
                kind: "symbol",
                index: symbol_id,
                count: self.symbols.len(),
            })?;
        if sym.section == 0 {
            return Ok(0);
        }
        if sym.section > self.sections.len() || sym.section > usize::from(u8::MAX) {
            return Err(MachOWriteError::SymbolSectionOutOfRange {
                symbol: sym.name.clone(),
                section: sym.section,
                section_count: self.sections.len(),
                max_supported_ordinal: u8::MAX,
            });
        }
        let section_index = sym.section - 1;
        let section_size = macho_field_u64(
            "section byte length",
            self.sections[section_index].data.len() as u128,
        )?;
        if sym.value > section_size {
            return Err(MachOWriteError::SymbolOffsetOutOfRange {
                symbol: sym.name.clone(),
                section: sym.section,
                offset: sym.value,
                section_size,
            });
        }
        macho_field_u64(
            "symbol virtual address",
            u128::from(self.section_vmaddr(section_index)?) + u128::from(sym.value),
        )
    }

    /// Produce the complete `.o` file using one prevalidated layout plan.
    pub fn write(&self) -> Result<Vec<u8>, MachOWriteError> {
        let plan = self.layout_plan()?;
        let mut buf = Vec::new();
        reserve_macho_exact(&mut buf, plan.file_len, "Mach-O output buffer")?;

        let ncmds = 4u32;
        let header = match self.target {
            MachOTarget::AArch64 => MachHeader::new_arm64_object(ncmds, plan.total_lc_size),
            MachOTarget::X86_64 => MachHeader::new_x86_64_object(ncmds, plan.total_lc_size),
        };
        header.write(&mut buf);

        let segment = SegmentCommand64::new_object_with_cmdsize(
            plan.segment_cmd_size,
            plan.nsects,
            plan.vmsize,
            plan.fileoff,
            plan.filesize,
        );
        segment.write(&mut buf);
        for (i, sec) in self.sections.iter().enumerate() {
            Section64::new(
                &sec.sectname,
                &sec.segname,
                plan.section_vmaddrs[i],
                plan.section_sizes[i],
                plan.section_offsets[i],
                sec.align,
                plan.relocation_offsets[i],
                plan.relocation_counts[i],
                sec.flags,
            )
            .write(&mut buf);
        }
        self.write_build_version(&mut buf);
        self.write_symtab_command(
            &mut buf,
            plan.symtab_off,
            plan.nsyms,
            plan.strtab_off,
            plan.strtab_size,
        );
        self.write_dysymtab_command(
            &mut buf,
            plan.nlocalsym,
            plan.nextdefsym,
            plan.iundefsym,
            plan.nundefsym,
        );
        Self::check_layout_position(&buf, plan.header_plus_lc, "header/load commands")?;

        for (i, sec) in self.sections.iter().enumerate() {
            let target = plan.section_offsets[i] as usize;
            if buf.len() > target {
                return Err(MachOWriteError::LayoutMismatch {
                    stage: "section padding",
                    expected: target,
                    actual: buf.len(),
                });
            }
            buf.resize(target, 0);
            buf.extend_from_slice(&sec.data);
        }
        Self::check_layout_position(&buf, plan.section_data_end, "section data")?;

        for sec in &self.sections {
            for reloc in &sec.relocations {
                buf.extend_from_slice(&encode_relocation_validated(reloc));
            }
            for reloc in &sec.x86_64_relocations {
                buf.extend_from_slice(&encode_x86_64_relocation_validated(reloc));
            }
        }
        Self::check_layout_position(&buf, plan.symtab_off as usize, "relocation tables")?;

        for &idx in &plan.ordered_symbol_indices {
            self.write_nlist64(&mut buf, &plan, idx);
        }
        Self::check_layout_position(&buf, plan.strtab_off as usize, "symbol table")?;
        buf.extend_from_slice(&plan.strtab);
        Self::check_layout_position(&buf, plan.file_len, "string table")?;

        self.reparse_gate(&buf, &plan)?;
        Ok(buf)
    }

    fn check_layout_position(
        buf: &[u8],
        expected: usize,
        stage: &'static str,
    ) -> Result<(), MachOWriteError> {
        if buf.len() != expected {
            return Err(MachOWriteError::LayoutMismatch {
                stage,
                expected,
                actual: buf.len(),
            });
        }
        Ok(())
    }

    /// Build the intended-object description this writer was asked to emit,
    /// consumed by the ENC-9 reparse gate ([`crate::macho::reparse`]). This
    /// snapshots the high-level INPUT model (section names/sizes/align/flags/
    /// content, symbols, relocation fields) — NOT the computed file layout; the
    /// gate derives offsets/addresses from the reparsed bytes and cross-checks
    /// them, so a layout bug in `write()` cannot hide.
    pub fn reparse_object_intent(
        &self,
    ) -> Result<crate::macho::reparse::MachoObjectIntent, MachOWriteError> {
        let plan = self.layout_plan()?;
        self.reparse_object_intent_with_plan(&plan)
    }

    fn reparse_object_intent_with_plan(
        &self,
        plan: &MachOLayoutPlan,
    ) -> Result<crate::macho::reparse::MachoObjectIntent, MachOWriteError> {
        use crate::macho::reparse::{MachoObjectIntent, RelocIntent, SectionIntent, SymbolIntent};

        let mut sections = Vec::new();
        reserve_macho_exact(
            &mut sections,
            self.sections.len(),
            "reparse-intent section table",
        )?;
        for sec in &self.sections {
            sections.push(SectionIntent {
                sectname: clone_macho_bytes(&sec.sectname, "reparse-intent section name")?,
                segname: clone_macho_bytes(&sec.segname, "reparse-intent segment name")?,
                align: sec.align,
                flags: sec.flags,
                data: clone_macho_bytes(&sec.data, "reparse-intent section data")?,
            });
        }

        // Per-section relocation records in the writer's emission order:
        // AArch64 records first, then x86-64 records (matches `write()`).
        let mut section_relocs = Vec::new();
        reserve_macho_exact(
            &mut section_relocs,
            self.sections.len(),
            "reparse-intent per-section relocation tables",
        )?;
        for sec in &self.sections {
            let relocation_count = macho_field_usize(
                "reparse-intent relocation count",
                (sec.relocations.len() as u128) + (sec.x86_64_relocations.len() as u128),
            )?;
            let mut recs: Vec<RelocIntent> = Vec::new();
            reserve_macho_exact(
                &mut recs,
                relocation_count,
                "reparse-intent relocation table",
            )?;
            for r in &sec.relocations {
                recs.push(RelocIntent {
                    r_address: r.offset,
                    r_symbolnum: r.symbol_index,
                    r_pcrel: r.pc_relative,
                    r_length: r.length,
                    r_extern: r.is_extern,
                    r_type: r.kind as u8,
                });
            }
            for r in &sec.x86_64_relocations {
                recs.push(RelocIntent {
                    r_address: r.offset,
                    r_symbolnum: r.symbol_index,
                    r_pcrel: r.pc_relative,
                    r_length: r.length,
                    r_extern: r.is_extern,
                    r_type: r.kind as u8,
                });
            }
            section_relocs.push(recs);
        }

        let mut symbols = Vec::new();
        reserve_macho_exact(
            &mut symbols,
            self.symbols.len(),
            "reparse-intent symbol table",
        )?;
        for (i, s) in self.symbols.iter().enumerate() {
            symbols.push(SymbolIntent {
                name: clone_macho_string(&s.name, "reparse-intent symbol name")?,
                section: plan.symbol_sections[i],
                value: s.value,
                is_global: s.is_global,
                is_weak: s.is_weak,
            });
        }

        Ok(MachoObjectIntent {
            target: self.target,
            sections,
            section_relocs,
            symbols,
        })
    }

    /// Run the ENC-9 reparse gate over the emitted bytes. In enforce mode a
    /// structural disagreement is returned as an error in enforce mode.
    fn reparse_gate(&self, bytes: &[u8], plan: &MachOLayoutPlan) -> Result<(), MachOWriteError> {
        use crate::macho::reparse::{MachoReparseMode, macho_reparse_mode, run_macho_reparse_gate};
        let mode = macho_reparse_mode();
        if mode == MachoReparseMode::Off {
            return Ok(());
        }
        let intent = self.reparse_object_intent_with_plan(plan)?;
        run_macho_reparse_gate(&intent, bytes, mode)
            .map_err(|error| MachOWriteError::ReparseGate(error.to_string()))
    }

    /// Write the LC_BUILD_VERSION load command.
    ///
    /// Specifies macOS 14.0 as the minimum deployment target with no tool entries.
    fn write_build_version(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&LC_BUILD_VERSION.to_le_bytes());
        // cmd
        buf.extend_from_slice(&BUILD_VERSION_COMMAND_SIZE.to_le_bytes());
        // cmdsize
        buf.extend_from_slice(&PLATFORM_MACOS.to_le_bytes());
        // platform
        // minos: 14.0.0 encoded as 0x000E0000
        buf.extend_from_slice(&0x000E_0000u32.to_le_bytes());
        // sdk: 14.0.0
        buf.extend_from_slice(&0x000E_0000u32.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());
        // ntools = 0
    }

    /// Write the LC_SYMTAB load command.
    fn write_symtab_command(
        &self,
        buf: &mut Vec<u8>,
        symoff: u32,
        nsyms: u32,
        stroff: u32,
        strsize: u32,
    ) {
        buf.extend_from_slice(&LC_SYMTAB.to_le_bytes());
        // cmd
        buf.extend_from_slice(&SYMTAB_COMMAND_SIZE.to_le_bytes());
        // cmdsize
        buf.extend_from_slice(&symoff.to_le_bytes());
        buf.extend_from_slice(&nsyms.to_le_bytes());
        buf.extend_from_slice(&stroff.to_le_bytes());
        buf.extend_from_slice(&strsize.to_le_bytes());
    }

    /// Write the LC_DYSYMTAB load command.
    fn write_dysymtab_command(
        &self,
        buf: &mut Vec<u8>,
        nlocalsym: u32,
        nextdefsym: u32,
        iundefsym: u32,
        nundefsym: u32,
    ) {
        buf.extend_from_slice(&LC_DYSYMTAB.to_le_bytes());
        // cmd
        buf.extend_from_slice(&DYSYMTAB_COMMAND_SIZE.to_le_bytes());
        // cmdsize
        buf.extend_from_slice(&0u32.to_le_bytes());
        // ilocalsym = 0
        buf.extend_from_slice(&nlocalsym.to_le_bytes());
        // nlocalsym
        buf.extend_from_slice(&nlocalsym.to_le_bytes());
        // iextdefsym = nlocalsym
        buf.extend_from_slice(&nextdefsym.to_le_bytes());
        // nextdefsym
        buf.extend_from_slice(&iundefsym.to_le_bytes());
        // iundefsym
        buf.extend_from_slice(&nundefsym.to_le_bytes());
        // nundefsym

        // Remaining fields are all zero for simple object files:
        // tocoff, ntoc, modtaboff, nmodtab, extrefsymoff, nextrefsyms,
        // indirectsymoff, nindirectsyms, extreloff, nextrel, locreloff, nlocrel
        for _ in 0..12 {
            buf.extend_from_slice(&0u32.to_le_bytes());
        }
    }

    /// Write a single nlist_64 entry.
    fn write_nlist64(&self, buf: &mut Vec<u8>, plan: &MachOLayoutPlan, idx: usize) {
        let sym = &self.symbols[idx];
        // n_strx: offset into string table (4 bytes)
        buf.extend_from_slice(&plan.str_offsets[idx].to_le_bytes());

        // n_type: 1 byte
        let n_type = if sym.section == 0 {
            if sym.is_global {
                N_UNDF | N_EXT
            } else {
                N_UNDF
            }
        } else if sym.is_global {
            N_SECT | N_EXT
        } else {
            N_SECT
        };
        buf.push(n_type);

        // n_sect: 1 byte (1-based section ordinal, or 0 for N_UNDF)
        buf.push(plan.symbol_sections[idx]);

        // n_desc: 2 bytes (0 for simple symbols; weak flags for weak symbols)
        buf.extend_from_slice(&sym.n_desc().to_le_bytes());

        // n_value: 8 bytes, precomputed by the checked layout plan.
        buf.extend_from_slice(&plan.symbol_values[idx].to_le_bytes());
    }
}

impl Default for MachOWriter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_writer() {
        let writer = MachOWriter::new();
        let bytes = writer.write().unwrap();
        // Should at least have a header
        assert!(bytes.len() >= 32);
        // Check magic
        assert_eq!(&bytes[0..4], &[0xCF, 0xFA, 0xED, 0xFE]);
    }

    #[test]
    fn test_writer_with_text() {
        let mut writer = MachOWriter::new();
        // 4 ARM64 NOPs
        let nop = 0xD503201Fu32;
        let mut code = Vec::new();
        for _ in 0..4 {
            code.extend_from_slice(&nop.to_le_bytes());
        }
        writer.add_text_section(&code);
        writer.add_symbol("_main", 1, 0, true).unwrap();
        let bytes = writer.write().unwrap();
        // Check magic
        assert_eq!(&bytes[0..4], &[0xCF, 0xFA, 0xED, 0xFE]);
        // Check file type = MH_OBJECT
        let filetype = u32::from_le_bytes([bytes[12], bytes[13], bytes[14], bytes[15]]);
        assert_eq!(filetype, MH_OBJECT);
    }

    #[test]
    fn test_relocation_encoding() {
        use super::super::reloc::encode_relocation;

        let reloc = Relocation::branch26(0x10, 1);
        let encoded = encode_relocation(&reloc).unwrap();
        // r_address = 0x10
        assert_eq!(&encoded[0..4], &0x10u32.to_le_bytes());
        // Packed: symbolnum=1, pcrel=1, length=2, extern=1, type=2
        // = 1 | (1<<24) | (2<<25) | (1<<27) | (2<<28)
        let expected: u32 = 1 | (1 << 24) | (2 << 25) | (1 << 27) | (2 << 28);
        assert_eq!(&encoded[4..8], &expected.to_le_bytes());
    }

    #[test]
    fn test_writer_with_both_sections() {
        let mut writer = MachOWriter::new();
        let nop = 0xD503201Fu32;
        let mut code = Vec::new();
        code.extend_from_slice(&nop.to_le_bytes());
        writer.add_text_section(&code);
        writer.add_data_section(&[1, 2, 3, 4, 5, 6, 7, 8]);
        writer.add_symbol("_main", 1, 0, true).unwrap();
        writer.add_symbol("_data", 2, 0, true).unwrap();
        let bytes = writer.write().unwrap();
        // Check ncmds = 4
        let ncmds = u32::from_le_bytes([bytes[16], bytes[17], bytes[18], bytes[19]]);
        assert_eq!(ncmds, 4);
    }

    #[test]
    fn test_symbol_ordering() {
        let mut writer = MachOWriter::new();
        writer.add_text_section(&[0x1F, 0x20, 0x03, 0xD5]);
        // Add a local then a global — dysymtab should sort locals before globals
        writer.add_symbol("_local_func", 1, 0, false).unwrap();
        writer.add_symbol("_main", 1, 0, true).unwrap();
        let bytes = writer.write().unwrap();
        // Just verify it produces a valid-looking file
        assert_eq!(&bytes[0..4], &[0xCF, 0xFA, 0xED, 0xFE]);
    }

    #[test]
    fn test_final_symbol_index_matches_macho_ordering() {
        let mut writer = MachOWriter::new();
        writer.add_text_section(&[0x1F, 0x20, 0x03, 0xD5]);
        let main = writer.add_symbol("_main", 1, 0, true).unwrap();
        let extern_undef = writer.add_symbol("_extern_undef", 0, 0, true).unwrap();
        let local = writer.add_symbol("_local", 1, 0, false).unwrap();
        let helper = writer.add_symbol("_helper", 1, 4, true).unwrap();
        assert_eq!(writer.final_symbol_index(local).unwrap(), Some(0));
        assert_eq!(writer.final_symbol_index(main).unwrap(), Some(1));
        assert_eq!(writer.final_symbol_index(helper).unwrap(), Some(2));
        assert_eq!(writer.final_symbol_index(extern_undef).unwrap(), Some(3));
        assert_eq!(writer.final_symbol_index(usize::MAX).unwrap(), None);
    }

    #[test]
    fn test_final_symbol_index_disambiguates_duplicate_names_by_id() {
        let mut writer = MachOWriter::new();
        writer.add_text_section(&[0x1F, 0x20, 0x03, 0xD5]);
        let global_dup = writer.add_symbol("_dup", 1, 0, true).unwrap();
        let local_dup = writer.add_symbol("_dup", 1, 0, false).unwrap();
        assert_eq!(writer.final_symbol_index(local_dup).unwrap(), Some(0));
        assert_eq!(writer.final_symbol_index(global_dup).unwrap(), Some(1));
    }

    #[test]
    fn final_index_freezes_symbol_table_without_failed_insertion_mutation() {
        let mut writer = MachOWriter::new();
        writer.add_text_section(&[0; 8]);
        let first = writer.add_symbol("_first", 1, 0, true).unwrap();
        assert_eq!(writer.final_symbol_index(first).unwrap(), Some(0));

        let before = writer.symbols.len();
        assert_eq!(
            writer.add_symbol("_too_late", 1, 4, false),
            Err(MachOWriteError::SymbolTableFrozen)
        );
        assert_eq!(writer.symbols.len(), before);
        assert_eq!(writer.symbols[0].name, "_first");
    }

    #[test]
    fn external_relocation_freezes_symbol_table_without_failed_insertion_mutation() {
        let mut writer = MachOWriter::new();
        writer.add_text_section(&[0; 8]);
        writer.add_symbol("_callee", 0, 0, true).unwrap();
        writer
            .add_relocation(0, Relocation::branch26(0, 0))
            .unwrap();

        let before = writer.symbols.len();
        assert_eq!(
            writer.add_symbol("_too_late", 1, 0, false),
            Err(MachOWriteError::SymbolTableFrozen)
        );
        assert_eq!(writer.symbols.len(), before);
        assert_eq!(writer.symbols[0].name, "_callee");
    }

    #[test]
    fn invalid_symbol_and_layout_boundaries_fail_before_serialization() {
        let mut writer = MachOWriter::new();
        writer.add_text_section(&[0; 4]);
        let before = writer.symbols.len();
        assert!(matches!(
            writer.add_symbol("_bad_section", 256, 0, true),
            Err(MachOWriteError::SymbolSectionOutOfRange { .. })
        ));
        assert_eq!(writer.symbols.len(), before);

        writer.add_custom_section(b"__bad_align", b"__TEXT", &[0], 64, S_REGULAR);
        assert!(matches!(
            writer.write(),
            Err(MachOWriteError::InvalidAlignment { align_log2: 64, .. })
        ));

        assert!(matches!(
            macho_field_u32("test field", u128::from(u32::MAX) + 1),
            Err(MachOWriteError::FieldOutOfRange {
                field: "test field",
                ..
            })
        ));
    }

    #[test]
    fn overlong_section_names_fail_closed_in_layout_plan() {
        let mut writer = MachOWriter::new();
        writer.add_custom_section(b"12345678901234567", b"__TEXT", &[], 0, S_REGULAR);
        assert!(matches!(
            writer.write(),
            Err(MachOWriteError::SectionNameTooLong {
                kind: "section",
                len: 17
            })
        ));
    }

    #[test]
    fn test_got_relocations_in_object() {
        use super::super::reloc::{Relocation, encode_relocation};

        let mut writer = MachOWriter::new();
        // Two ARM64 instructions: ADRP + LDR (GOT-indirect pattern)
        let adrp = 0x9000_0000u32;
        // ADRP X0, #0
        let ldr = 0xF940_0000u32;
        // LDR X0, [X0, #0]
        let mut code = Vec::new();
        code.extend_from_slice(&adrp.to_le_bytes());
        code.extend_from_slice(&ldr.to_le_bytes());
        writer.add_text_section(&code);

        // External symbol for GOT access
        writer.add_symbol("_printf", 0, 0, true).unwrap();
        // undefined external

        // GOT relocations
        writer
            .add_relocation(0, Relocation::got_load_page21(0x00, 0))
            .unwrap();
        writer
            .add_relocation(0, Relocation::got_load_pageoff12(0x04, 0))
            .unwrap();

        let bytes = writer.write().unwrap();
        // Verify valid Mach-O
        assert_eq!(&bytes[0..4], &[0xCF, 0xFA, 0xED, 0xFE]);

        // Verify the GOT relocations encode correctly
        let got_page_encoded = encode_relocation(&Relocation::got_load_page21(0x00, 0)).unwrap();
        let r_word1 = u32::from_le_bytes([
            got_page_encoded[4],
            got_page_encoded[5],
            got_page_encoded[6],
            got_page_encoded[7],
        ]);
        assert_eq!((r_word1 >> 28) & 0xF, 5, "GOT_LOAD_PAGE21 type = 5");
        assert_eq!((r_word1 >> 24) & 1, 1, "GOT_LOAD_PAGE21 is PC-relative");

        let got_off_encoded = encode_relocation(&Relocation::got_load_pageoff12(0x04, 0)).unwrap();
        let r_word1 = u32::from_le_bytes([
            got_off_encoded[4],
            got_off_encoded[5],
            got_off_encoded[6],
            got_off_encoded[7],
        ]);
        assert_eq!((r_word1 >> 28) & 0xF, 6, "GOT_LOAD_PAGEOFF12 type = 6");
        assert_eq!(
            (r_word1 >> 24) & 1,
            0,
            "GOT_LOAD_PAGEOFF12 is not PC-relative"
        );
    }

    #[test]
    fn test_tlvp_relocations_in_object() {
        use super::super::reloc::{Relocation, encode_relocation};

        let mut writer = MachOWriter::new();
        // Two ARM64 instructions: ADRP + LDR (TLV pattern)
        let adrp = 0x9000_0000u32;
        let ldr = 0xF940_0000u32;
        let mut code = Vec::new();
        code.extend_from_slice(&adrp.to_le_bytes());
        code.extend_from_slice(&ldr.to_le_bytes());
        writer.add_text_section(&code);

        // TLV symbol
        writer.add_symbol("_thread_var", 0, 0, true).unwrap();
        // TLV relocations
        writer
            .add_relocation(0, Relocation::tlvp_load_page21(0x00, 0))
            .unwrap();
        writer
            .add_relocation(0, Relocation::tlvp_load_pageoff12(0x04, 0))
            .unwrap();

        let bytes = writer.write().unwrap();
        assert_eq!(&bytes[0..4], &[0xCF, 0xFA, 0xED, 0xFE]);

        // Verify TLV relocation types
        let tlvp_page_encoded = encode_relocation(&Relocation::tlvp_load_page21(0x00, 0)).unwrap();
        let r_word1 = u32::from_le_bytes([
            tlvp_page_encoded[4],
            tlvp_page_encoded[5],
            tlvp_page_encoded[6],
            tlvp_page_encoded[7],
        ]);
        assert_eq!((r_word1 >> 28) & 0xF, 8, "TLVP_LOAD_PAGE21 type = 8");
        assert_eq!((r_word1 >> 24) & 1, 1, "TLVP_LOAD_PAGE21 is PC-relative");

        let tlvp_off_encoded =
            encode_relocation(&Relocation::tlvp_load_pageoff12(0x04, 0)).unwrap();
        let r_word1 = u32::from_le_bytes([
            tlvp_off_encoded[4],
            tlvp_off_encoded[5],
            tlvp_off_encoded[6],
            tlvp_off_encoded[7],
        ]);
        assert_eq!((r_word1 >> 28) & 0xF, 9, "TLVP_LOAD_PAGEOFF12 type = 9");
        assert_eq!(
            (r_word1 >> 24) & 1,
            0,
            "TLVP_LOAD_PAGEOFF12 is not PC-relative"
        );
    }

    // =====================================================================
    // Additional coverage tests
    // =====================================================================

    // -- Helper to read a little-endian u32 from a byte slice --
    fn read_u32(bytes: &[u8], offset: usize) -> u32 {
        u32::from_le_bytes([
            bytes[offset],
            bytes[offset + 1],
            bytes[offset + 2],
            bytes[offset + 3],
        ])
    }

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
    fn test_empty_function_valid_macho_header() {
        // An empty writer (no sections, no symbols) should still produce a
        // structurally valid Mach-O header.
        let writer = MachOWriter::new();
        let bytes = writer.write().unwrap();

        // Mach-O magic
        assert_eq!(read_u32(&bytes, 0), MH_MAGIC_64);
        // CPU type = ARM64
        assert_eq!(read_u32(&bytes, 4), CPU_TYPE_ARM64);
        // CPU subtype = ALL
        assert_eq!(read_u32(&bytes, 8), CPU_SUBTYPE_ARM64_ALL);
        // File type = MH_OBJECT
        assert_eq!(read_u32(&bytes, 12), MH_OBJECT);
        // ncmds = 4 (segment, build_version, symtab, dysymtab)
        assert_eq!(read_u32(&bytes, 16), 4);
        // sizeofcmds should be non-zero
        let sizeofcmds = read_u32(&bytes, 20);
        assert!(sizeofcmds > 0);
        // flags
        let flags = read_u32(&bytes, 24);
        assert_eq!(
            flags & MH_SUBSECTIONS_VIA_SYMBOLS,
            MH_SUBSECTIONS_VIA_SYMBOLS
        );
    }

    #[test]
    fn test_single_text_section_alignment() {
        let mut writer = MachOWriter::new();
        // 16 bytes of ARM64 code (4 NOPs)
        let nop = 0xD503201Fu32;
        let code: Vec<u8> = (0..4).flat_map(|_| nop.to_le_bytes()).collect();
        writer.add_text_section(&code);

        let bytes = writer.write().unwrap();
        let header_plus_lc = MACH_HEADER_64_SIZE
            + SEGMENT_COMMAND_64_SIZE
            + SECTION_64_SIZE
            + BUILD_VERSION_COMMAND_SIZE
            + SYMTAB_COMMAND_SIZE
            + DYSYMTAB_COMMAND_SIZE;

        // Section data should be aligned to 4 bytes (2^2).
        // Since header+lc is already a multiple of 4, offset = header_plus_lc.
        assert_eq!(header_plus_lc % 4, 0, "header+lc should be 4-byte aligned");

        // Verify the section data is present at the expected offset.
        let offset = header_plus_lc as usize;
        assert_eq!(
            read_u32(&bytes, offset),
            nop,
            "first instruction at section offset should be NOP"
        );
    }

    #[test]
    fn test_symbol_table_local_vs_external() {
        let mut writer = MachOWriter::new();
        writer.add_text_section(&[0x1F, 0x20, 0x03, 0xD5]);
        // 1 NOP

        // Add symbols: 2 locals, 1 global defined, 1 global undefined
        writer.add_symbol("_local1", 1, 0, false).unwrap();
        writer.add_symbol("_local2", 1, 4, false).unwrap();
        writer.add_symbol("_main", 1, 0, true).unwrap();
        writer.add_symbol("_extern_undef", 0, 0, true).unwrap();
        let bytes = writer.write().unwrap();

        // Find the LC_SYMTAB command to locate the symbol table.
        // It comes after LC_SEGMENT_64 + sections + LC_BUILD_VERSION.
        let seg_cmd_size = SEGMENT_COMMAND_64_SIZE + SECTION_64_SIZE;
        let symtab_cmd_offset =
            (MACH_HEADER_64_SIZE + seg_cmd_size + BUILD_VERSION_COMMAND_SIZE) as usize;
        let symtab_cmd = read_u32(&bytes, symtab_cmd_offset);
        assert_eq!(symtab_cmd, LC_SYMTAB, "expected LC_SYMTAB command");

        let symoff = read_u32(&bytes, symtab_cmd_offset + 8) as usize;
        let nsyms = read_u32(&bytes, symtab_cmd_offset + 12);
        assert_eq!(nsyms, 4, "should have 4 symbols");

        let stroff = read_u32(&bytes, symtab_cmd_offset + 16) as usize;

        // Read the 4 nlist_64 entries (16 bytes each).
        // Mach-O requires locals first, then extdef, then undef.
        // Expected ordering: _local1, _local2, _main, _extern_undef.

        // Symbol 0: should be local (n_type = N_SECT, no N_EXT)
        let n_type_0 = bytes[symoff + 4];
        // offset 4 in nlist_64
        assert_eq!(
            n_type_0, N_SECT,
            "symbol 0 should be local (N_SECT, no N_EXT)"
        );

        // Symbol 1: should also be local
        let n_type_1 = bytes[symoff + 16 + 4];
        assert_eq!(n_type_1, N_SECT, "symbol 1 should be local");

        // Symbol 2: should be external defined (N_SECT | N_EXT)
        let n_type_2 = bytes[symoff + 32 + 4];
        assert_eq!(
            n_type_2,
            N_SECT | N_EXT,
            "symbol 2 should be global defined"
        );

        // Symbol 3: should be undefined external (N_UNDF | N_EXT)
        let n_type_3 = bytes[symoff + 48 + 4];
        assert_eq!(
            n_type_3,
            N_UNDF | N_EXT,
            "symbol 3 should be undefined external"
        );

        // Verify string table offsets point to valid strings.
        let str_offset_0 = read_u32(&bytes, symoff) as usize;
        assert!(stroff + str_offset_0 < bytes.len());
    }

    #[test]
    fn test_string_table_correctness() {
        let mut writer = MachOWriter::new();
        writer.add_text_section(&[0x1F, 0x20, 0x03, 0xD5]);
        writer.add_symbol("_foo", 1, 0, true).unwrap();
        writer.add_symbol("_bar", 1, 0, false).unwrap();
        let bytes = writer.write().unwrap();

        // Find string table via LC_SYMTAB.
        let seg_cmd_size = SEGMENT_COMMAND_64_SIZE + SECTION_64_SIZE;
        let symtab_cmd_offset =
            (MACH_HEADER_64_SIZE + seg_cmd_size + BUILD_VERSION_COMMAND_SIZE) as usize;
        let stroff = read_u32(&bytes, symtab_cmd_offset + 16) as usize;
        let strsize = read_u32(&bytes, symtab_cmd_offset + 20) as usize;

        // String table starts with a null byte.
        assert_eq!(bytes[stroff], 0, "string table must start with null byte");

        // Verify both symbol names appear in the string table.
        let strtab = &bytes[stroff..stroff + strsize];
        let strtab_str = String::from_utf8_lossy(strtab);
        assert!(
            strtab_str.contains("_foo"),
            "string table should contain _foo"
        );
        assert!(
            strtab_str.contains("_bar"),
            "string table should contain _bar"
        );
    }

    #[test]
    fn test_relocation_emission_in_section() {
        use super::super::reloc::Relocation;

        let mut writer = MachOWriter::new();
        // 3 ARM64 instructions
        let nop = 0xD503201Fu32;
        let code: Vec<u8> = (0..3).flat_map(|_| nop.to_le_bytes()).collect();
        writer.add_text_section(&code);
        writer.add_symbol("_callee", 0, 0, true).unwrap();
        // undefined external

        // Add a BRANCH26 relocation at offset 4 (second instruction).
        writer
            .add_relocation(0, Relocation::branch26(0x04, 0))
            .unwrap();

        let bytes = writer.write().unwrap();

        // The section header should record 1 relocation.
        // Section header is at: header(32) + segment_cmd(72) = offset 104.
        // section_64 layout: sectname(16) + segname(16) + addr(8) + size(8)
        //   + offset(4) + align(4) + reloff(4) + nreloc(4) + flags(4) + reserved(12) = 80
        let section_hdr_offset = (MACH_HEADER_64_SIZE + SEGMENT_COMMAND_64_SIZE) as usize;

        // reloff at offset 56 in section_64 (16+16+8+8+4+4=56)
        let reloff = read_u32(&bytes, section_hdr_offset + 56) as usize;
        assert!(reloff > 0, "relocation offset should be non-zero");

        // nreloc at offset 60 in section_64 (56+4=60)
        let nreloc = read_u32(&bytes, section_hdr_offset + 60);
        assert_eq!(nreloc, 1, "section should have 1 relocation");

        // Verify relocation address field (first 4 bytes of relocation_info).
        let r_address = read_u32(&bytes, reloff);
        assert_eq!(r_address, 0x04, "relocation should be at offset 0x04");
    }

    #[test]
    fn test_multi_section_output() {
        let mut writer = MachOWriter::new();
        writer.add_text_section(&[0x1F, 0x20, 0x03, 0xD5]);
        // 4 bytes text
        writer.add_data_section(&[0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE, 0xBA, 0xBE]);
        // 8 bytes data

        // Add a custom section (e.g., compact unwind)
        writer.add_custom_section(
            b"__compact_unwind",
            b"__LD",
            &[0; 32], // 32 bytes of zero (compact unwind entry)
            3,        // 8-byte aligned
            S_REGULAR,
        );

        writer.add_symbol("_main", 1, 0, true).unwrap();
        writer.add_symbol("_data_sym", 2, 0, true).unwrap();
        let bytes = writer.write().unwrap();

        // Header should show nsects = 3 in the segment command.
        let seg_cmd_offset = MACH_HEADER_64_SIZE as usize;
        // nsects is at offset 64 of segment_command_64:
        // cmd(4) + cmdsize(4) + segname(16) + vmaddr(8) + vmsize(8) +
        // fileoff(8) + filesize(8) + maxprot(4) + initprot(4) + nsects(4)
        let nsects = read_u32(&bytes, seg_cmd_offset + 64);
        assert_eq!(nsects, 3, "should have 3 sections");

        // Verify all section data is present in the file.
        // The text section data (NOP) should be somewhere in the file.
        let nop_bytes = &[0x1F, 0x20, 0x03, 0xD5];
        let found_nop = bytes.windows(4).any(|w| w == nop_bytes);
        assert!(found_nop, "text section NOP should be in the output");

        // The data section bytes should be somewhere in the file.
        let data_bytes = &[0xDE, 0xAD, 0xBE, 0xEF];
        let found_data = bytes.windows(4).any(|w| w == data_bytes);
        assert!(found_data, "data section content should be in the output");
    }

    #[test]
    fn test_dysymtab_partition_counts() {
        let mut writer = MachOWriter::new();
        writer.add_text_section(&[0x1F, 0x20, 0x03, 0xD5, 0, 0, 0, 0, 0, 0, 0, 0]);

        // 2 locals, 3 globals defined, 1 undefined
        writer.add_symbol("_local_a", 1, 0, false).unwrap();
        writer.add_symbol("_local_b", 1, 4, false).unwrap();
        writer.add_symbol("_global_a", 1, 0, true).unwrap();
        writer.add_symbol("_global_b", 1, 4, true).unwrap();
        writer.add_symbol("_global_c", 1, 8, true).unwrap();
        writer.add_symbol("_undef", 0, 0, true).unwrap();
        let bytes = writer.write().unwrap();

        // Find LC_DYSYMTAB command.
        let seg_cmd_size = SEGMENT_COMMAND_64_SIZE + SECTION_64_SIZE;
        let dysymtab_offset =
            (MACH_HEADER_64_SIZE + seg_cmd_size + BUILD_VERSION_COMMAND_SIZE + SYMTAB_COMMAND_SIZE)
                as usize;
        let cmd = read_u32(&bytes, dysymtab_offset);
        assert_eq!(cmd, LC_DYSYMTAB, "should be LC_DYSYMTAB");

        // ilocalsym = 0
        let ilocalsym = read_u32(&bytes, dysymtab_offset + 8);
        assert_eq!(ilocalsym, 0);

        // nlocalsym = 2
        let nlocalsym = read_u32(&bytes, dysymtab_offset + 12);
        assert_eq!(nlocalsym, 2);

        // iextdefsym = nlocalsym = 2
        let iextdefsym = read_u32(&bytes, dysymtab_offset + 16);
        assert_eq!(iextdefsym, 2);

        // nextdefsym = 3
        let nextdefsym = read_u32(&bytes, dysymtab_offset + 20);
        assert_eq!(nextdefsym, 3);

        // iundefsym = nlocalsym + nextdefsym = 5
        let iundefsym = read_u32(&bytes, dysymtab_offset + 24);
        assert_eq!(iundefsym, 5);

        // nundefsym = 1
        let nundefsym = read_u32(&bytes, dysymtab_offset + 28);
        assert_eq!(nundefsym, 1);
    }

    #[test]
    fn test_symbol_value_computation() {
        // Symbol value should be the section base VM address + offset.
        let mut writer = MachOWriter::new();
        writer.add_text_section(&[0u8; 16]);
        // 16 bytes of code
        writer.add_symbol("_func_at_8", 1, 8, true).unwrap();
        let bytes = writer.write().unwrap();

        // Find symbol table.
        let seg_cmd_size = SEGMENT_COMMAND_64_SIZE + SECTION_64_SIZE;
        let symtab_cmd_offset =
            (MACH_HEADER_64_SIZE + seg_cmd_size + BUILD_VERSION_COMMAND_SIZE) as usize;
        let symoff = read_u32(&bytes, symtab_cmd_offset + 8) as usize;

        // n_value is at offset 8 in nlist_64 (8 bytes).
        let n_value = read_u64(&bytes, symoff + 8);
        // Section 1 starts at vmaddr=0, so symbol value = 0 + 8.
        assert_eq!(n_value, 8, "symbol value should be section base + offset");
    }

    #[test]
    fn test_build_version_command() {
        let writer = MachOWriter::new();
        let bytes = writer.write().unwrap();

        // LC_BUILD_VERSION is the second load command (after LC_SEGMENT_64).
        let seg_cmd_size = SEGMENT_COMMAND_64_SIZE;
        // no sections for empty writer
        let bv_offset = (MACH_HEADER_64_SIZE + seg_cmd_size) as usize;

        let cmd = read_u32(&bytes, bv_offset);
        assert_eq!(cmd, LC_BUILD_VERSION, "expected LC_BUILD_VERSION");

        let cmdsize = read_u32(&bytes, bv_offset + 4);
        assert_eq!(cmdsize, BUILD_VERSION_COMMAND_SIZE);

        let platform = read_u32(&bytes, bv_offset + 8);
        assert_eq!(platform, PLATFORM_MACOS, "platform should be macOS");

        // minos: 14.0.0 = 0x000E0000
        let minos = read_u32(&bytes, bv_offset + 12);
        assert_eq!(minos, 0x000E_0000, "minimum OS should be macOS 14.0");

        // ntools = 0
        let ntools = read_u32(&bytes, bv_offset + 20);
        assert_eq!(ntools, 0, "no tool entries");
    }

    #[test]
    fn test_default_impl() {
        // Verify the Default implementation works.
        let writer: MachOWriter = MachOWriter::default();
        let bytes = writer.write().unwrap();
        assert_eq!(read_u32(&bytes, 0), MH_MAGIC_64);
    }

    #[test]
    fn test_custom_section_index_returned() {
        let mut writer = MachOWriter::new();
        writer.add_text_section(&[0; 4]);
        let idx =
            writer.add_custom_section(b"__cstring", b"__TEXT", b"hello\0", 0, S_CSTRING_LITERALS);
        assert_eq!(
            idx, 1,
            "custom section should be at index 1 (after text at index 0)"
        );
    }

    #[test]
    fn test_relocation_to_out_of_range_section_fails_without_mutation() {
        let mut writer = MachOWriter::new();
        writer.add_text_section(&[0; 4]);

        use super::super::reloc::Relocation;
        assert_eq!(
            writer.add_relocation(99, Relocation::branch26(0, 0)),
            Err(MachORelocationError::SectionIndexOutOfRange {
                section: 99,
                section_count: 1,
            })
        );
        assert_eq!(writer.section_reloc_count(&writer.sections[0]).unwrap(), 0);
    }

    #[test]
    fn test_segment_vmsize_and_filesize() {
        let mut writer = MachOWriter::new();
        // 8 bytes text + 16 bytes data
        writer.add_text_section(&[0u8; 8]);
        writer.add_data_section(&[0u8; 16]);

        let bytes = writer.write().unwrap();

        // Segment command layout: cmd(4) + cmdsize(4) + segname(16) +
        // vmaddr(8, offset 24) + vmsize(8, offset 32) +
        // fileoff(8, offset 40) + filesize(8, offset 48)
        let seg_offset = MACH_HEADER_64_SIZE as usize;
        let vmsize = read_u64(&bytes, seg_offset + 32);
        let filesize = read_u64(&bytes, seg_offset + 48);

        // vmsize: text(8) aligned to data alignment (8-byte, so 8 is ok) + data(16) = 24
        assert!(
            vmsize >= 24,
            "vmsize should cover all sections: got {}",
            vmsize
        );
        // filesize should also cover all section data.
        assert!(
            filesize >= 24,
            "filesize should cover all sections: got {}",
            filesize
        );
    }

    // =====================================================================
    // x86-64 Mach-O writer tests
    // =====================================================================

    #[test]
    fn test_x86_64_empty_writer() {
        let writer = MachOWriter::for_target(MachOTarget::X86_64);
        let bytes = writer.write().unwrap();
        // Should at least have a header
        assert!(bytes.len() >= 32);
        // Check magic
        assert_eq!(&bytes[0..4], &[0xCF, 0xFA, 0xED, 0xFE]);
        // CPU type = x86-64
        assert_eq!(read_u32(&bytes, 4), CPU_TYPE_X86_64);
        // CPU subtype = ALL
        assert_eq!(read_u32(&bytes, 8), CPU_SUBTYPE_X86_64_ALL);
    }

    #[test]
    fn test_x86_64_writer_with_text() {
        let mut writer = MachOWriter::for_target(MachOTarget::X86_64);
        // x86-64: push rbp; mov rbp, rsp; pop rbp; ret
        let code = vec![
            0x55, // push rbp
            0x48, 0x89, 0xE5, // mov rbp, rsp
            0x5D, // pop rbp
            0xC3, // ret
        ];
        writer.add_text_section(&code);
        writer.add_symbol("_main", 1, 0, true).unwrap();
        let bytes = writer.write().unwrap();
        // Check magic
        assert_eq!(&bytes[0..4], &[0xCF, 0xFA, 0xED, 0xFE]);
        // CPU type = x86-64
        assert_eq!(read_u32(&bytes, 4), CPU_TYPE_X86_64);
        // File type = MH_OBJECT
        assert_eq!(read_u32(&bytes, 12), MH_OBJECT);
    }

    #[test]
    fn test_x86_64_writer_with_relocation() {
        use super::super::x86_64_reloc::X86_64Relocation;

        let mut writer = MachOWriter::for_target(MachOTarget::X86_64);
        // CALL rel32 (E8 + 4 bytes displacement)
        let code = vec![0xE8, 0x00, 0x00, 0x00, 0x00];
        // call +0 (placeholder)
        writer.add_text_section(&code);
        writer.add_symbol("_callee", 0, 0, true).unwrap();
        // undefined external

        // Add a BRANCH relocation at offset 1 (the displacement field)
        writer
            .add_x86_64_relocation(0, X86_64Relocation::branch(0x01, 0))
            .unwrap();

        let bytes = writer.write().unwrap();
        assert_eq!(&bytes[0..4], &[0xCF, 0xFA, 0xED, 0xFE]);
        assert_eq!(read_u32(&bytes, 4), CPU_TYPE_X86_64);

        // Find section header to verify nreloc = 1
        let section_hdr_offset = (MACH_HEADER_64_SIZE + SEGMENT_COMMAND_64_SIZE) as usize;
        // nreloc at offset 60 in section_64
        let nreloc = read_u32(&bytes, section_hdr_offset + 60);
        assert_eq!(nreloc, 1, "section should have 1 relocation");
    }

    #[test]
    fn test_x86_64_writer_with_data_section() {
        let mut writer = MachOWriter::for_target(MachOTarget::X86_64);
        writer.add_text_section(&[0xC3]);
        // ret
        writer.add_data_section(&[0xDE, 0xAD, 0xBE, 0xEF]);
        writer.add_symbol("_main", 1, 0, true).unwrap();
        writer.add_symbol("_data", 2, 0, true).unwrap();
        let bytes = writer.write().unwrap();
        assert_eq!(read_u32(&bytes, 4), CPU_TYPE_X86_64);

        // Verify ncmds
        let ncmds = read_u32(&bytes, 16);
        assert_eq!(ncmds, 4);

        // Verify data appears in the output
        let found = bytes.windows(4).any(|w| w == [0xDE, 0xAD, 0xBE, 0xEF]);
        assert!(found, "data section content should be in the output");
    }

    #[test]
    fn test_x86_64_target_accessor() {
        let writer_arm = MachOWriter::new();
        assert_eq!(writer_arm.target(), MachOTarget::AArch64);

        let writer_x86 = MachOWriter::for_target(MachOTarget::X86_64);
        assert_eq!(writer_x86.target(), MachOTarget::X86_64);
    }

    #[test]
    fn test_x86_64_got_relocation() {
        use super::super::x86_64_reloc::X86_64Relocation;

        let mut writer = MachOWriter::for_target(MachOTarget::X86_64);
        // mov rax, [rip + disp32] (GOT load pattern)
        let code = vec![0x48, 0x8B, 0x05, 0x00, 0x00, 0x00, 0x00];
        writer.add_text_section(&code);
        writer.add_symbol("_extern_sym", 0, 0, true).unwrap();
        writer
            .add_x86_64_relocation(0, X86_64Relocation::got_load(0x03, 0))
            .unwrap();

        let bytes = writer.write().unwrap();
        assert_eq!(read_u32(&bytes, 4), CPU_TYPE_X86_64);

        // Verify relocation was emitted
        let section_hdr_offset = (MACH_HEADER_64_SIZE + SEGMENT_COMMAND_64_SIZE) as usize;
        let nreloc = read_u32(&bytes, section_hdr_offset + 60);
        assert_eq!(nreloc, 1);
    }

    #[test]
    fn test_x86_64_multiple_relocations() {
        use super::super::x86_64_reloc::X86_64Relocation;

        let mut writer = MachOWriter::for_target(MachOTarget::X86_64);
        // Two calls + RIP-relative load
        let code = vec![0u8; 20];
        writer.add_text_section(&code);
        writer.add_symbol("_func1", 0, 0, true).unwrap();
        writer.add_symbol("_func2", 0, 0, true).unwrap();
        writer.add_symbol("_data", 0, 0, true).unwrap();
        writer
            .add_x86_64_relocation(0, X86_64Relocation::branch(0x01, 0))
            .unwrap();
        writer
            .add_x86_64_relocation(0, X86_64Relocation::branch(0x06, 1))
            .unwrap();
        writer
            .add_x86_64_relocation(0, X86_64Relocation::signed(0x0C, 2))
            .unwrap();

        let bytes = writer.write().unwrap();
        let section_hdr_offset = (MACH_HEADER_64_SIZE + SEGMENT_COMMAND_64_SIZE) as usize;
        let nreloc = read_u32(&bytes, section_hdr_offset + 60);
        assert_eq!(nreloc, 3, "section should have 3 relocations");
    }

    /// The X86_64_RELOC_TLV emission path must be reachable through the writer:
    /// a TLV relocation added to a section is written into the file's relocation
    /// area and decodes back to `X86_64RelocKind::Tlv` (type 9, PC-relative).
    #[test]
    fn test_x86_64_tlv_relocation_emission_path() {
        use super::super::x86_64_reloc::{X86_64RelocKind, decode_x86_64_relocation};

        let mut writer = MachOWriter::for_target(MachOTarget::X86_64);
        // mov rax, [rip + tlv_descriptor] then call *(%rax) pattern placeholder.
        let code = vec![0x48, 0x8B, 0x05, 0x00, 0x00, 0x00, 0x00];
        writer.add_text_section(&code);
        writer.add_symbol("_tls_var", 0, 0, true).unwrap();
        // undefined external TLV symbol

        // TLV relocation at the disp32 field (offset 3).
        writer
            .add_x86_64_relocation(0, X86_64Relocation::tlv(0x03, 0))
            .unwrap();

        let bytes = writer.write().unwrap();
        let section_hdr_offset = (MACH_HEADER_64_SIZE + SEGMENT_COMMAND_64_SIZE) as usize;
        let nreloc = read_u32(&bytes, section_hdr_offset + 60);
        assert_eq!(nreloc, 1, "section should carry the TLV relocation");

        // reloff is at section header offset + 56; the 8-byte relocation_info
        // entry sits there.
        let reloff = read_u32(&bytes, section_hdr_offset + 56) as usize;
        let entry: [u8; 8] = bytes[reloff..reloff + 8].try_into().unwrap();
        let decoded = decode_x86_64_relocation(&entry).unwrap();

        assert_eq!(decoded.kind, X86_64RelocKind::Tlv);
        assert_eq!(decoded.offset, 0x03);
        assert!(decoded.pc_relative, "TLV is PC-relative");
        assert_eq!(decoded.length, 2, "TLV operates on a 4-byte field");
        assert!(decoded.is_extern);
        // The packed r_type nibble (bits 28-31) must be 9 (X86_64_RELOC_TLV).
        let r_word1 = read_u32(&bytes, reloff + 4);
        assert_eq!((r_word1 >> 28) & 0xF, X86_64_RELOC_TLV);
    }

    /// Weak symbols must encode the appropriate `n_desc` flags: a defined weak
    /// symbol gets `N_WEAK_DEF`, a weak undefined reference gets `N_WEAK_REF`,
    /// and ordinary symbols keep `n_desc == 0`.
    #[test]
    fn test_weak_symbol_nlist_encoding() {
        let mut writer = MachOWriter::for_target(MachOTarget::X86_64);
        writer.add_text_section(&[0xC3]);
        // ret

        // Defined weak global -> N_WEAK_DEF, defined external symbol.
        let weak_def = writer.add_weak_symbol("_weak_def", 1, 0, true).unwrap();
        // Weak undefined reference -> N_WEAK_REF.
        let weak_ref = writer.add_weak_symbol("_weak_ref", 0, 0, true).unwrap();
        // Ordinary defined symbol -> n_desc == 0.
        let strong = writer.add_symbol("_strong", 1, 0, true).unwrap();
        let bytes = writer.write().unwrap();

        // Locate the symbol table via LC_SYMTAB (symoff is the 3rd u32 of the
        // command). Walk load commands to find it.
        let ncmds = read_u32(&bytes, 16);
        let mut cmd_off = (MACH_HEADER_64_SIZE) as usize;
        let mut symoff = 0usize;
        let mut nsyms = 0u32;
        for _ in 0..ncmds {
            let cmd = read_u32(&bytes, cmd_off);
            let cmdsize = read_u32(&bytes, cmd_off + 4) as usize;
            if cmd == LC_SYMTAB {
                symoff = read_u32(&bytes, cmd_off + 8) as usize;
                nsyms = read_u32(&bytes, cmd_off + 12);
                break;
            }
            cmd_off += cmdsize;
        }
        assert_eq!(nsyms, 3, "three symbols expected");

        // n_desc lives at byte 6 of each 16-byte nlist_64 entry. Map insertion
        // ids to their final emitted index.
        let mut read_desc = |sym_id: SymbolId| -> u16 {
            let idx = writer.final_symbol_index(sym_id).unwrap().unwrap() as usize;
            let entry = symoff + idx * NLIST_64_SIZE as usize;
            u16::from_le_bytes([bytes[entry + 6], bytes[entry + 7]])
        };

        assert_eq!(
            read_desc(weak_def) & N_WEAK_DEF,
            N_WEAK_DEF,
            "defined weak -> N_WEAK_DEF"
        );
        assert_eq!(read_desc(weak_def) & N_WEAK_REF, 0);
        assert_eq!(
            read_desc(weak_ref) & N_WEAK_REF,
            N_WEAK_REF,
            "undef weak -> N_WEAK_REF"
        );
        assert_eq!(read_desc(weak_ref) & N_WEAK_DEF, 0);
        assert_eq!(read_desc(strong), 0, "non-weak symbol keeps n_desc == 0");

        // Spot-check the published flag values.
        assert_eq!(N_WEAK_REF, 0x0040);
        assert_eq!(N_WEAK_DEF, 0x0080);
    }
}
