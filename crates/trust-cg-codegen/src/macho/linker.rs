// trust-cg-codegen/macho/linker.rs - Mach-O linker: read .o files, resolve symbols, emit executables
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Minimal Mach-O linker for Trust Codegen-generated object files.
//!
//! Reads Mach-O MH_OBJECT (.o) files, resolves symbols across objects, applies
//! relocations (BRANCH26, PAGE21, PAGEOFF12), and emits a Mach-O MH_EXECUTE
//! binary.
//!
//! This is an MVP linker for the Trust Codegen pipeline. It handles the common case of
//! linking a small number of .o files into a static executable for AArch64 macOS.
//!
//! # Layout of emitted MH_EXECUTE
//!
//! ```text
//! __PAGEZERO  vmaddr=0x0            vmsize=0x1_0000_0000  (no file data)
//! __TEXT      vmaddr=0x1_0000_0000  (rx) contains __text
//! __DATA      vmaddr=aligned after __TEXT  (rw) contains __data
//! ```

use std::collections::{HashMap, HashSet};

use super::constants::*;
use super::reloc::{AArch64RelocKind, Relocation, decode_relocation};
use super::section::padded_name;
use super::symbol::NList64;

use thiserror::Error;

// ---------------------------------------------------------------------------
// Constants for executable emission
// ---------------------------------------------------------------------------

/// Mach-O executable file type.
const MH_EXECUTE: u32 = 0x2;

/// Executable has no undefined references after static link.
const MH_NOUNDEFS: u32 = 0x0000_0001;

/// Input is for the dynamic linker.
const MH_DYLDLINK: u32 = 0x0000_0004;

/// Image uses two-level namespace bindings.
const MH_TWOLEVEL: u32 = 0x0000_0080;

/// Position-independent executable flag.
const MH_PIE: u32 = 0x0020_0000;

/// Standard flags for modern Darwin MH_EXECUTE output.
const MH_EXECUTE_FLAGS: u32 = MH_NOUNDEFS | MH_DYLDLINK | MH_TWOLEVEL | MH_PIE;

/// LC_MAIN load command type (entry point for executables).
const LC_MAIN: u32 = 0x8000_0028;

/// Size of the LC_MAIN (entry_point_command) load command in bytes.
const LC_MAIN_SIZE: u32 = 24;

/// Default base virtual address for macOS AArch64 executables.
const DEFAULT_BASE_ADDR: u64 = 0x1_0000_0000;

/// Page size for AArch64 macOS (16 KiB).
const PAGE_SIZE: u64 = 0x4000;

/// LC_LOAD_DYLIB load command type.
const LC_LOAD_DYLIB: u32 = 0x0C;

/// Size of the dylib_command header (without the name string).
/// cmd(4) + cmdsize(4) + name_offset(4) + timestamp(4) + current_version(4) + compat_version(4)
const LC_LOAD_DYLIB_HEADER_SIZE: u32 = 24;

/// LC_LOAD_DYLINKER load command type (modern macOS requires this for dyld invocation).
const LC_LOAD_DYLINKER: u32 = 0x0E;

/// Size of the dylinker_command header (without the name string).
/// cmd(4) + cmdsize(4) + name_offset(4)
const LC_LOAD_DYLINKER_HEADER_SIZE: u32 = 12;

/// Standard path to macOS dynamic linker.
const DYLD_PATH: &str = "/usr/lib/dyld";

/// macOS 14.0.0 encoded as (major << 16) | (minor << 8) | patch.
const MACOS_14_0_0: u32 = 0x000E_0000;

/// Section type for lazy symbol pointers (__la_symbol_ptr).
/// Used for lazy-binding stubs (future: dyld_stub_binder integration).
#[allow(dead_code)]
const S_LAZY_SYMBOL_POINTERS: u32 = 0x7;

/// Section type for non-lazy symbol pointers (__got / __nl_symbol_ptr).
const S_NON_LAZY_SYMBOL_POINTERS: u32 = 0x6;

/// Section type for symbol stubs (__stubs).
const S_SYMBOL_STUBS: u32 = 0x8;

/// Size of a single AArch64 stub entry (3 instructions: ADRP + LDR + BR = 12 bytes).
const STUB_SIZE: u32 = 12;

/// Weak definition flag in n_desc field.
const N_WEAK_DEF: u16 = 0x0080;

/// Weak reference flag in n_desc field.
const N_WEAK_REF: u16 = 0x0040;

/// No dead strip flag in n_desc field.
const N_NO_DEAD_STRIP: u16 = 0x0020;

/// Section type mask (lower 8 bits of section flags).
const SECTION_TYPE_MASK: u32 = 0x0000_00FF;

/// dyld_chained_fixups_header size before 8-byte payload alignment.
const DYLD_CHAINED_FIXUPS_HEADER_SIZE: u32 = 28;

/// dyld_chained_import format identifier.
const DYLD_CHAINED_IMPORT: u32 = 1;

/// Uncompressed symbol strings in the chained-fixups payload.
const DYLD_CHAINED_SYMBOLS_UNCOMPRESSED: u32 = 0;

/// 64-bit chained pointer format.
const DYLD_CHAINED_PTR_64: u16 = 2;

/// No chained fixups start on this page.
const DYLD_CHAINED_PTR_START_NONE: u16 = 0xFFFF;

/// An empty exports trie: root node with no terminal payload and no children.
const EMPTY_EXPORTS_TRIE: &[u8] = &[0, 0];

/// Code signature payload alignment required by libstuff and followed by lld.
const CODE_SIGNATURE_ALIGNMENT: u64 = 16;

/// Code signing hashes cover 4 KiB blocks even though arm64 segment pages are 16 KiB.
const CODE_SIGNATURE_BLOCK_SIZE_SHIFT: u8 = 12;
const CODE_SIGNATURE_BLOCK_SIZE: u64 = 1 << CODE_SIGNATURE_BLOCK_SIZE_SHIFT;
const CODE_SIGNATURE_HASH_SIZE: usize = 32;
const CODE_SIGNATURE_IDENTIFIER: &[u8] = b"trust-cg";

const CSMAGIC_CODEDIRECTORY: u32 = 0xFADE_0C02;
const CSMAGIC_EMBEDDED_SIGNATURE: u32 = 0xFADE_0CC0;
const CS_SUPPORTSEXECSEG: u32 = 0x0002_0400;
const CS_ADHOC: u32 = 0x0000_0002;
const CS_LINKER_SIGNED: u32 = 0x0002_0000;
const CS_EXECSEG_MAIN_BINARY: u64 = 0x1;
const CSSLOT_CODEDIRECTORY: u32 = 0;
const CS_HASHTYPE_SHA256: u8 = 2;
const CS_BLOB_HEADERS_SIZE: usize = 24;
const CS_CODE_DIRECTORY_SIZE: usize = 88;
const CS_FIXED_HEADERS_SIZE: usize = CS_BLOB_HEADERS_SIZE + CS_CODE_DIRECTORY_SIZE;

#[derive(Debug, Clone)]
struct ChainedFixupSegmentInfo {
    segment_index: usize,
    segment_offset: u64,
    page_starts: Vec<(u16, u16)>,
}

#[derive(Debug, Clone)]
struct LinkeditPayload {
    data: Vec<u8>,
    fixups_offset: u64,
    fixups_size: u32,
    exports_offset: u64,
    exports_size: u32,
    code_signature_offset: u64,
    code_signature_size: u32,
}

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors that can occur during linking.
#[derive(Debug, Error)]
pub enum LinkerError {
    /// The input data is too short to contain a valid Mach-O header.
    #[error("data too short: need at least {expected} bytes, got {actual}")]
    TooShort { expected: usize, actual: usize },

    /// The Mach-O magic number is incorrect.
    #[error("bad magic: expected 0xFEEDFACF, got 0x{0:08X}")]
    BadMagic(u32),

    /// The file type is not MH_OBJECT.
    #[error("expected MH_OBJECT (0x1), got 0x{0:X}")]
    NotObject(u32),

    /// The CPU type is not CPU_TYPE_ARM64.
    #[error("expected CPU_TYPE_ARM64 (0x0100000C), got 0x{0:08X}")]
    UnsupportedCpuType(u32),

    /// A load command extends beyond the declared sizeofcmds.
    #[error("load command at offset {offset} extends beyond load command area")]
    LoadCommandOverflow { offset: usize },

    /// Failed to decode a relocation entry.
    #[error("relocation decode error in section {section}: {detail}")]
    RelocDecode { section: String, detail: String },

    /// An undefined symbol could not be resolved.
    #[error("undefined symbol: {0}")]
    UndefinedSymbol(String),

    /// Duplicate symbol definition.
    #[error("duplicate symbol: {0}")]
    DuplicateSymbol(String),

    /// A relocation type is not yet supported by the linker.
    #[error("unsupported relocation type: {0:?}")]
    UnsupportedRelocation(AArch64RelocKind),

    /// A relocation sequence is malformed.
    #[error("malformed relocation sequence: {0}")]
    MalformedRelocation(String),

    /// A relocation target is out of range for the instruction encoding.
    #[error("relocation overflow: {detail}")]
    RelocationOverflow { detail: String },

    /// No _main entry point found.
    #[error("no _main entry point found")]
    NoEntryPoint,

    /// Input file is malformed (general parsing error with context).
    #[error("malformed input '{file}': {detail}")]
    MalformedInput { file: String, detail: String },

    /// Section data extends beyond file bounds.
    #[error(
        "section '{section}' data at offset {offset:#x} extends beyond file (size {file_size:#x})"
    )]
    SectionDataOverflow {
        section: String,
        offset: usize,
        file_size: usize,
    },

    /// Multiple strong definitions of the same symbol (detailed variant).
    #[error(
        "duplicate symbol '{name}' (first defined in object {first_obj}, also in object {second_obj})"
    )]
    DuplicateSymbolDetailed {
        name: String,
        first_obj: usize,
        second_obj: usize,
    },
}

// ---------------------------------------------------------------------------
// Parsed object file structures
// ---------------------------------------------------------------------------

/// A parsed Mach-O section from an object file.
#[derive(Debug, Clone)]
pub struct ParsedSection {
    /// Section name (e.g., "__text").
    pub name: String,
    /// Segment name (e.g., "__TEXT").
    pub segment: String,
    /// Raw section data bytes.
    pub data: Vec<u8>,
    /// Virtual address in the object file (usually 0-based for .o files).
    pub addr: u64,
    /// Alignment as power of 2.
    pub align: u32,
    /// Section flags.
    pub flags: u32,
    /// Relocations that apply to this section.
    pub relocations: Vec<Relocation>,
    /// Virtual size (for zerofill sections, may exceed data.len()).
    pub vmsize: u64,
}

impl ParsedSection {
    /// Returns the section type (lower 8 bits of flags).
    pub fn section_type(&self) -> u32 {
        self.flags & SECTION_TYPE_MASK
    }

    /// Returns true if this is a zerofill section (__bss).
    pub fn is_zerofill(&self) -> bool {
        self.section_type() == S_ZEROFILL
    }

    /// Returns the effective size of this section in virtual memory.
    /// For zerofill sections, this is vmsize; for regular sections, data length.
    pub fn effective_size(&self) -> u64 {
        if self.is_zerofill() {
            self.vmsize
        } else {
            self.data.len() as u64
        }
    }
}

/// A parsed symbol from a Mach-O object file.
#[derive(Debug, Clone)]
pub struct ParsedSymbol {
    /// Symbol name from the string table.
    pub name: String,
    /// n_type field from nlist_64.
    pub n_type: u8,
    /// Section number (1-based, 0 = undefined).
    pub section: u8,
    /// n_desc field.
    pub desc: u16,
    /// Symbol value (address/offset).
    pub value: u64,
}

impl ParsedSymbol {
    /// Returns true if this symbol is defined (in a section).
    pub fn is_defined(&self) -> bool {
        (self.n_type & N_TYPE) == N_SECT
    }

    /// Returns true if this symbol is undefined.
    pub fn is_undefined(&self) -> bool {
        (self.n_type & N_TYPE) == N_UNDF && self.section == 0
    }

    /// Returns true if this symbol is external.
    pub fn is_external(&self) -> bool {
        (self.n_type & N_EXT) != 0
    }

    /// Returns true if this symbol is a weak definition.
    pub fn is_weak_def(&self) -> bool {
        self.desc & N_WEAK_DEF != 0
    }

    /// Returns true if this symbol is a weak reference (undefined weak).
    pub fn is_weak_ref(&self) -> bool {
        self.desc & N_WEAK_REF != 0
    }

    /// Returns true if this symbol should not be dead-stripped.
    pub fn is_no_dead_strip(&self) -> bool {
        self.desc & N_NO_DEAD_STRIP != 0
    }
}

/// A fully parsed Mach-O object file.
#[derive(Debug, Clone)]
pub struct ParsedObject {
    /// CPU type from the header.
    pub cputype: u32,
    /// CPU subtype from the header.
    pub cpusubtype: u32,
    /// Header flags.
    pub flags: u32,
    /// Parsed sections.
    pub sections: Vec<ParsedSection>,
    /// Parsed symbols.
    pub symbols: Vec<ParsedSymbol>,
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

/// Read a little-endian u32 from a byte slice at the given offset.
fn read_u32(data: &[u8], off: usize) -> u32 {
    u32::from_le_bytes([data[off], data[off + 1], data[off + 2], data[off + 3]])
}

/// Read a little-endian u64 from a byte slice at the given offset.
fn read_u64(data: &[u8], off: usize) -> u64 {
    u64::from_le_bytes([
        data[off],
        data[off + 1],
        data[off + 2],
        data[off + 3],
        data[off + 4],
        data[off + 5],
        data[off + 6],
        data[off + 7],
    ])
}

/// Read a NUL-terminated string from a byte slice starting at `off`.
fn read_cstring(data: &[u8], off: usize) -> String {
    let mut end = off;
    while end < data.len() && data[end] != 0 {
        end += 1;
    }
    String::from_utf8_lossy(&data[off..end]).into_owned()
}

/// Read a fixed-size name field (16 bytes, NUL-padded) and return a trimmed string.
fn read_name16(data: &[u8], off: usize) -> String {
    let raw = &data[off..off + 16];
    let end = raw.iter().position(|&b| b == 0).unwrap_or(16);
    String::from_utf8_lossy(&raw[..end]).into_owned()
}

/// Parser for Mach-O MH_OBJECT files.
pub struct MachOParser;

impl MachOParser {
    /// Parse a Mach-O .o file from raw bytes.
    pub fn parse(data: &[u8]) -> Result<ParsedObject, LinkerError> {
        // --- Validate header ---
        let hdr_size = MACH_HEADER_64_SIZE as usize;
        if data.len() < hdr_size {
            return Err(LinkerError::TooShort {
                expected: hdr_size,
                actual: data.len(),
            });
        }

        let magic = read_u32(data, 0);
        if magic != MH_MAGIC_64 {
            return Err(LinkerError::BadMagic(magic));
        }

        let cputype = read_u32(data, 4);
        if cputype != CPU_TYPE_ARM64 {
            // This linker only decodes AArch64 objects: section relocations are
            // decoded with the AArch64-only decode_relocation and the output
            // emitter hardcodes CPU_TYPE_ARM64. Fail closed on any other CPU
            // type (e.g. an x86-64 .o) rather than misparsing it as ARM64.
            return Err(LinkerError::UnsupportedCpuType(cputype));
        }
        let cpusubtype = read_u32(data, 8);
        let filetype = read_u32(data, 12);
        if filetype != MH_OBJECT {
            return Err(LinkerError::NotObject(filetype));
        }

        let ncmds = read_u32(data, 16);
        let sizeofcmds = read_u32(data, 20);
        let flags = read_u32(data, 24);

        // --- Walk load commands ---
        let mut sections = Vec::new();
        let mut symbols = Vec::new();

        let lc_start = hdr_size;
        let lc_end = lc_start + sizeofcmds as usize;
        let mut offset = lc_start;

        for _ in 0..ncmds {
            if offset + 8 > lc_end || offset + 8 > data.len() {
                return Err(LinkerError::LoadCommandOverflow { offset });
            }

            let cmd = read_u32(data, offset);
            let cmdsize = read_u32(data, offset + 4) as usize;

            if cmdsize < 8 || offset + cmdsize > data.len() {
                return Err(LinkerError::LoadCommandOverflow { offset });
            }

            match cmd {
                LC_SEGMENT_64 => {
                    // Parse segment command header to find nsects.
                    // segment_command_64 layout:
                    //   cmd(4) + cmdsize(4) + segname(16) + vmaddr(8) + vmsize(8) +
                    //   fileoff(8) + filesize(8) + maxprot(4) + initprot(4) + nsects(4) + flags(4)
                    //
                    // FINDING #4: the per-command bounds check above only enforces
                    // `cmdsize >= 8 && offset + cmdsize <= len`. The fixed header
                    // fields read below (nsects at offset+64) extend past a small
                    // cmdsize. A crafted object with cmdsize=8 would index `data`
                    // out of bounds in `read_u32`, PANICking instead of returning
                    // the advertised Result. Require the command actually covers
                    // the fixed segment_command_64 fields first.
                    if cmdsize < SEGMENT_COMMAND_64_SIZE as usize
                        || offset + SEGMENT_COMMAND_64_SIZE as usize > data.len()
                    {
                        return Err(LinkerError::LoadCommandOverflow { offset });
                    }
                    let nsects = read_u32(data, offset + 64);

                    // Parse each section_64 header.
                    let mut sec_offset = offset + SEGMENT_COMMAND_64_SIZE as usize;
                    for _ in 0..nsects {
                        let sec_size = SECTION_64_SIZE as usize;
                        if sec_offset + sec_size > data.len() {
                            return Err(LinkerError::LoadCommandOverflow { offset: sec_offset });
                        }

                        let sec_name = read_name16(data, sec_offset);
                        let seg_name = read_name16(data, sec_offset + 16);
                        let sec_addr = read_u64(data, sec_offset + 32);
                        let sec_data_size = read_u64(data, sec_offset + 40) as usize;
                        let sec_file_offset = read_u32(data, sec_offset + 48) as usize;
                        let sec_align = read_u32(data, sec_offset + 52);
                        let sec_reloff = read_u32(data, sec_offset + 56) as usize;
                        let sec_nreloc = read_u32(data, sec_offset + 60);
                        let sec_flags = read_u32(data, sec_offset + 64);

                        // Read section data. FINDING #4 (section-data arm): both
                        // `sec_data_size` and `sec_file_offset` are attacker-controlled
                        // (u64/u32 read from the object), so `sec_file_offset +
                        // sec_data_size` can overflow usize (panic in debug / wrap in
                        // release, defeating the `<= len` guard), and the zero-fill else
                        // branch `vec![0u8; sec_data_size]` can be an allocation bomb
                        // (~18 EB for sec_data_size = u64::MAX). Use checked arithmetic
                        // and reject a section whose size exceeds the whole object,
                        // returning the advertised typed error rather than panicking.
                        let sec_data = match sec_file_offset.checked_add(sec_data_size) {
                            Some(end) if sec_data_size > 0 && end <= data.len() => {
                                data[sec_file_offset..end].to_vec()
                            }
                            _ => {
                                // Zero-fill (BSS-style) or out-of-file section. Cap the
                                // allocation: a section claiming more bytes than the
                                // entire object is malformed -> fail closed.
                                if sec_data_size > data.len() {
                                    return Err(LinkerError::LoadCommandOverflow {
                                        offset: sec_offset,
                                    });
                                }
                                vec![0u8; sec_data_size]
                            }
                        };

                        // Read relocations for this section.
                        let mut relocations = Vec::new();
                        let reloc_size = RELOCATION_INFO_SIZE as usize;
                        for r in 0..sec_nreloc as usize {
                            let roff = sec_reloff + r * reloc_size;
                            if roff + reloc_size <= data.len() {
                                let reloc_bytes: [u8; 8] = [
                                    data[roff],
                                    data[roff + 1],
                                    data[roff + 2],
                                    data[roff + 3],
                                    data[roff + 4],
                                    data[roff + 5],
                                    data[roff + 6],
                                    data[roff + 7],
                                ];
                                match decode_relocation(&reloc_bytes) {
                                    Ok(reloc) => relocations.push(reloc),
                                    Err(e) => {
                                        return Err(LinkerError::RelocDecode {
                                            section: sec_name.clone(),
                                            detail: e.to_string(),
                                        });
                                    }
                                }
                            }
                        }

                        // For zerofill sections (BSS), vmsize is the declared
                        // size but data is empty (no file backing).
                        let vmsize = sec_data_size as u64;

                        sections.push(ParsedSection {
                            name: sec_name,
                            segment: seg_name,
                            data: sec_data,
                            addr: sec_addr,
                            align: sec_align,
                            flags: sec_flags,
                            relocations,
                            vmsize,
                        });

                        sec_offset += sec_size;
                    }
                }
                LC_SYMTAB => {
                    // symtab_command layout:
                    //   cmd(4) + cmdsize(4) + symoff(4) + nsyms(4) + stroff(4) + strsize(4)
                    //
                    // FINDING #4: same fail-closed guard as LC_SEGMENT_64 — the
                    // fixed fields read below (offset+8..+24) require the command
                    // to cover the full 24-byte symtab_command, else a small
                    // cmdsize would make `read_u32` index out of bounds and panic.
                    if cmdsize < SYMTAB_COMMAND_SIZE as usize
                        || offset + SYMTAB_COMMAND_SIZE as usize > data.len()
                    {
                        return Err(LinkerError::LoadCommandOverflow { offset });
                    }
                    let symoff = read_u32(data, offset + 8) as usize;
                    let nsyms = read_u32(data, offset + 12) as usize;
                    let stroff = read_u32(data, offset + 16) as usize;
                    let _strsize = read_u32(data, offset + 20) as usize;

                    let nlist_size = NLIST_64_SIZE as usize;
                    for i in 0..nsyms {
                        let sym_off = symoff + i * nlist_size;
                        if sym_off + nlist_size <= data.len() {
                            let nlist_bytes: [u8; 16] = data[sym_off..sym_off + 16]
                                .try_into()
                                .expect("nlist_64 slice");
                            let nlist = NList64::decode(&nlist_bytes);

                            // Read the symbol name from the string table.
                            let name = if (stroff + nlist.strx as usize) < data.len() {
                                read_cstring(data, stroff + nlist.strx as usize)
                            } else {
                                String::new()
                            };

                            symbols.push(ParsedSymbol {
                                name,
                                n_type: nlist.typ,
                                section: nlist.sect,
                                desc: nlist.desc,
                                value: nlist.value,
                            });
                        }
                    }
                }
                _ => {
                    // Skip unknown load commands (LC_BUILD_VERSION, LC_DYSYMTAB, etc.)
                }
            }

            offset += cmdsize;
        }

        Ok(ParsedObject {
            cputype,
            cpusubtype,
            flags,
            sections,
            symbols,
        })
    }
}

// ---------------------------------------------------------------------------
// Symbol resolution
// ---------------------------------------------------------------------------

/// A resolved symbol with its final virtual address.
#[derive(Debug, Clone)]
pub struct ResolvedSymbol {
    /// Final virtual address of the symbol.
    pub address: u64,
    /// Object index the symbol was defined in.
    pub object_index: usize,
    /// Section index within that object.
    pub section_index: usize,
    /// Whether this is a weak definition (can be overridden).
    pub is_weak: bool,
}

/// Resolves symbols across multiple parsed object files.
pub struct SymbolResolver {
    /// Map from symbol name to its definition.
    defined: HashMap<String, ResolvedSymbol>,
    /// Map from (object index, symbol table index) to defined symbol address.
    ///
    /// Mach-O `r_extern=1` relocations name a symbol table index. That symbol
    /// may be local, so local defined symbols must remain object-scoped instead
    /// of being published through the global name map.
    defined_by_index: HashMap<(usize, usize), u64>,
    /// List of (object_index, symbol_index, name) for undefined references.
    undefined: Vec<(usize, usize, String)>,
    /// Set of symbol names that are weak references (can remain unresolved).
    weak_refs: HashSet<String>,
}

impl SymbolResolver {
    /// Create a new empty resolver.
    pub fn new() -> Self {
        Self {
            defined: HashMap::new(),
            defined_by_index: HashMap::new(),
            undefined: Vec::new(),
            weak_refs: HashSet::new(),
        }
    }

    /// Register all symbols from a parsed object. The `layout` provides the
    /// section base addresses for computing final symbol addresses.
    ///
    /// Weak symbol semantics:
    /// - Strong definition overrides any existing weak definition
    /// - Weak definition is silently skipped if a strong definition exists
    /// - Duplicate strong definitions produce an error
    pub fn add_object(
        &mut self,
        obj_index: usize,
        obj: &ParsedObject,
        section_addrs: &[u64],
    ) -> Result<(), LinkerError> {
        for (sym_idx, sym) in obj.symbols.iter().enumerate() {
            if sym.is_defined() {
                let sec_idx = (sym.section as usize).saturating_sub(1);
                let base = if sec_idx < section_addrs.len() {
                    section_addrs[sec_idx]
                } else {
                    0
                };
                let address = base + sym.value;
                self.defined_by_index.insert((obj_index, sym_idx), address);

                if !sym.is_external() {
                    continue;
                }

                let new_is_weak = sym.is_weak_def();

                if let Some(existing) = self.defined.get(&sym.name) {
                    if existing.is_weak && !new_is_weak {
                        // Strong definition overrides existing weak - replace.
                        self.defined.insert(
                            sym.name.clone(),
                            ResolvedSymbol {
                                address,
                                object_index: obj_index,
                                section_index: sec_idx,
                                is_weak: false,
                            },
                        );
                    } else if new_is_weak {
                        // New is weak, existing is strong (or also weak) - skip.
                        continue;
                    } else {
                        // Both strong - duplicate symbol error.
                        return Err(LinkerError::DuplicateSymbolDetailed {
                            name: sym.name.clone(),
                            first_obj: existing.object_index,
                            second_obj: obj_index,
                        });
                    }
                } else {
                    self.defined.insert(
                        sym.name.clone(),
                        ResolvedSymbol {
                            address,
                            object_index: obj_index,
                            section_index: sec_idx,
                            is_weak: new_is_weak,
                        },
                    );
                }
            } else if sym.is_undefined() && sym.is_external() {
                // Track weak references separately.
                if sym.is_weak_ref() {
                    self.weak_refs.insert(sym.name.clone());
                }
                self.undefined.push((obj_index, sym_idx, sym.name.clone()));
            }
        }
        Ok(())
    }

    /// Return the object-local symbol address map for one source object.
    pub fn object_symbol_addrs(&self, obj_index: usize) -> HashMap<usize, u64> {
        self.defined_by_index
            .iter()
            .filter_map(|(&(object_index, symbol_index), &address)| {
                (object_index == obj_index).then_some((symbol_index, address))
            })
            .collect()
    }

    /// Resolve all undefined symbols. Returns a map from symbol name to address.
    ///
    /// Weak references that remain unresolved are bound to address 0 (null).
    /// Strong undefined references that have no definition produce an error.
    pub fn resolve(&self) -> Result<HashMap<String, u64>, LinkerError> {
        let mut result: HashMap<String, u64> = HashMap::new();

        // Copy all defined symbols.
        for (name, sym) in &self.defined {
            result.insert(name.clone(), sym.address);
        }

        // Verify all undefined symbols have definitions.
        for (_obj_idx, _sym_idx, name) in &self.undefined {
            if !result.contains_key(name) {
                if self.weak_refs.contains(name) {
                    // Weak references resolve to 0 if not defined.
                    result.insert(name.clone(), 0);
                } else {
                    return Err(LinkerError::UndefinedSymbol(name.clone()));
                }
            }
        }

        Ok(result)
    }

    /// Look up a symbol's resolved address by name.
    pub fn lookup(&self, name: &str) -> Option<u64> {
        self.defined.get(name).map(|s| s.address)
    }
}

impl Default for SymbolResolver {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Section layout
// ---------------------------------------------------------------------------

/// Result of laying out sections across multiple objects.
#[derive(Debug, Clone)]
pub struct LayoutResult {
    /// Base addresses for each section, in order: all sections from obj 0,
    /// then all sections from obj 1, etc.
    pub section_addrs: Vec<Vec<u64>>,
    /// Total size of the __TEXT segment content.
    pub text_size: u64,
    /// Total size of the __DATA segment content.
    pub data_size: u64,
    /// File offset where __TEXT segment data starts.
    pub text_file_offset: u64,
    /// File offset where __DATA segment data starts.
    pub data_file_offset: u64,
    /// Virtual address of __TEXT segment.
    pub text_vmaddr: u64,
    /// Virtual address of __DATA segment.
    pub data_vmaddr: u64,
}

/// Assign final virtual addresses to sections from multiple objects.
///
/// Handles zerofill (BSS) sections: they occupy virtual address space but not
/// file space. BSS sections are placed after regular data sections in the
/// __DATA segment's virtual address space.
pub fn lay_out_sections(objects: &[ParsedObject], base_addr: u64) -> LayoutResult {
    let mut text_offset: u64 = 0;
    let mut data_offset: u64 = 0;
    let mut bss_offset: u64 = 0;

    let mut section_addrs: Vec<Vec<u64>> = Vec::new();

    // First pass: compute sizes and assign addresses for regular sections.
    // BSS sections are deferred to a second pass (they go after regular data).
    for obj in objects {
        let mut addrs = Vec::new();
        for sec in &obj.sections {
            let is_text = sec.segment == "__TEXT";
            let alignment = 1u64 << sec.align;

            if is_text {
                // Align text_offset.
                let misalign = text_offset % alignment;
                if misalign != 0 {
                    text_offset += alignment - misalign;
                }
                addrs.push(base_addr + text_offset);
                text_offset += sec.data.len() as u64;
            } else if sec.is_zerofill() {
                // Zerofill (BSS) - placeholder, will be fixed up in second pass.
                addrs.push(bss_offset);
                let misalign = bss_offset % alignment;
                if misalign != 0 {
                    bss_offset += alignment - misalign;
                    // Re-store with aligned offset.
                    *addrs.last_mut().unwrap() = bss_offset;
                }
                bss_offset += sec.effective_size();
            } else {
                // Regular __DATA section.
                let misalign = data_offset % alignment;
                if misalign != 0 {
                    data_offset += alignment - misalign;
                }
                // Data address will be computed after we know total text size.
                // Store as a relative offset for now.
                addrs.push(data_offset);
                data_offset += sec.data.len() as u64;
            }
        }
        section_addrs.push(addrs);
    }

    // Align text_size to page boundary.
    let text_size = text_offset;
    let text_size_aligned = align_to(text_size, PAGE_SIZE);

    let data_vmaddr = base_addr + text_size_aligned;

    // Fix up data and BSS section addresses.
    // BSS sections are placed after regular data sections in virtual space.
    let bss_base = data_vmaddr + data_offset;
    for (obj_idx, obj) in objects.iter().enumerate() {
        for (sec_idx, sec) in obj.sections.iter().enumerate() {
            if sec.segment == "__TEXT" {
                // Already has absolute addresses from the first pass.
            } else if sec.is_zerofill() {
                // BSS sections: relative offset was stored; add bss_base.
                section_addrs[obj_idx][sec_idx] += bss_base;
            } else {
                // Regular data sections: add data_vmaddr.
                section_addrs[obj_idx][sec_idx] += data_vmaddr;
            }
        }
    }

    // Total data segment VM size includes both regular data and BSS.
    let total_data_vmsize = data_offset + bss_offset;

    // Compute file offsets. For the MVP, we'll compute these during emission.
    // The text file offset comes after all load commands.
    LayoutResult {
        section_addrs,
        text_size,
        data_size: total_data_vmsize,
        text_file_offset: 0, // Will be set during emission.
        data_file_offset: 0, // Will be set during emission.
        text_vmaddr: base_addr,
        data_vmaddr,
    }
}

/// Align `value` up to the next multiple of `alignment`.
fn align_to(value: u64, alignment: u64) -> u64 {
    if alignment == 0 {
        return value;
    }
    let remainder = value % alignment;
    if remainder == 0 {
        value
    } else {
        value + alignment - remainder
    }
}

fn pad_vec_to_alignment(buf: &mut Vec<u8>, alignment: u64) {
    let aligned = align_to(buf.len() as u64, alignment) as usize;
    buf.resize(aligned, 0);
}

fn patch_u32(buf: &mut [u8], offset: usize, value: u32) {
    buf[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
}

fn write_be_u32(buf: &mut Vec<u8>, value: u32) {
    buf.extend_from_slice(&value.to_be_bytes());
}

fn write_be_u64(buf: &mut Vec<u8>, value: u64) {
    buf.extend_from_slice(&value.to_be_bytes());
}

fn code_signature_block_count(code_limit: u64) -> u32 {
    let count = if code_limit == 0 {
        0
    } else {
        code_limit.div_ceil(CODE_SIGNATURE_BLOCK_SIZE)
    };
    assert!(
        count <= u32::MAX as u64,
        "code signature block count exceeds CodeDirectory range"
    );
    count as u32
}

fn code_signature_headers_size() -> usize {
    align_to(
        (CS_FIXED_HEADERS_SIZE + CODE_SIGNATURE_IDENTIFIER.len() + 1) as u64,
        CODE_SIGNATURE_ALIGNMENT,
    ) as usize
}

fn code_signature_size(code_limit: u64) -> u32 {
    let size = code_signature_headers_size()
        + code_signature_block_count(code_limit) as usize * CODE_SIGNATURE_HASH_SIZE;
    assert!(
        size <= u32::MAX as usize,
        "code signature size exceeds linkedit_data_command range"
    );
    size as u32
}

fn build_ad_hoc_code_signature(
    file_prefix: &[u8],
    text_file_offset: u64,
    text_file_size: u64,
) -> Vec<u8> {
    let code_limit = file_prefix.len() as u64;
    assert!(
        code_limit <= u32::MAX as u64,
        "CodeDirectory codeLimit64 is not wired for large executables yet"
    );

    let block_count = code_signature_block_count(code_limit);
    let all_headers_size = code_signature_headers_size();
    let hash_offset = all_headers_size - CS_BLOB_HEADERS_SIZE;
    let code_directory_length = hash_offset + block_count as usize * CODE_SIGNATURE_HASH_SIZE;
    let signature_size = CS_BLOB_HEADERS_SIZE + code_directory_length;
    assert_eq!(signature_size, code_signature_size(code_limit) as usize);

    let mut buf = Vec::with_capacity(signature_size);

    // SuperBlob and BlobIndex fields are big-endian on disk.
    write_be_u32(&mut buf, CSMAGIC_EMBEDDED_SIGNATURE);
    write_be_u32(&mut buf, signature_size as u32);
    write_be_u32(&mut buf, 1);
    write_be_u32(&mut buf, CSSLOT_CODEDIRECTORY);
    write_be_u32(&mut buf, CS_BLOB_HEADERS_SIZE as u32);
    buf.resize(CS_BLOB_HEADERS_SIZE, 0);

    write_be_u32(&mut buf, CSMAGIC_CODEDIRECTORY);
    write_be_u32(&mut buf, code_directory_length as u32);
    write_be_u32(&mut buf, CS_SUPPORTSEXECSEG);
    write_be_u32(&mut buf, CS_ADHOC | CS_LINKER_SIGNED);
    write_be_u32(&mut buf, hash_offset as u32);
    write_be_u32(&mut buf, CS_CODE_DIRECTORY_SIZE as u32);
    write_be_u32(&mut buf, 0); // nSpecialSlots
    write_be_u32(&mut buf, block_count);
    write_be_u32(&mut buf, code_limit as u32);
    buf.push(CODE_SIGNATURE_HASH_SIZE as u8);
    buf.push(CS_HASHTYPE_SHA256);
    buf.push(0); // platform
    buf.push(CODE_SIGNATURE_BLOCK_SIZE_SHIFT);
    write_be_u32(&mut buf, 0); // spare2
    write_be_u32(&mut buf, 0); // scatterOffset
    write_be_u32(&mut buf, 0); // teamOffset
    write_be_u32(&mut buf, 0); // spare3
    write_be_u64(&mut buf, 0); // codeLimit64
    write_be_u64(&mut buf, text_file_offset);
    write_be_u64(&mut buf, text_file_size);
    write_be_u64(&mut buf, CS_EXECSEG_MAIN_BINARY);
    debug_assert_eq!(buf.len(), CS_FIXED_HEADERS_SIZE);

    buf.extend_from_slice(CODE_SIGNATURE_IDENTIFIER);
    buf.resize(all_headers_size, 0);

    for block_idx in 0..block_count as usize {
        let start = block_idx * CODE_SIGNATURE_BLOCK_SIZE as usize;
        let end = ((block_idx as u64 + 1) * CODE_SIGNATURE_BLOCK_SIZE).min(code_limit) as usize;
        buf.extend_from_slice(&sha256_digest(&file_prefix[start..end]));
    }

    debug_assert_eq!(buf.len(), signature_size);
    buf
}

fn sha256_digest(data: &[u8]) -> [u8; 32] {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];

    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];

    let bit_len = (data.len() as u64).wrapping_mul(8);
    let mut padded = Vec::with_capacity(data.len() + 72);
    padded.extend_from_slice(data);
    padded.push(0x80);
    while padded.len() % 64 != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    for chunk in padded.chunks_exact(64) {
        let mut w = [0u32; 64];
        for (i, word) in w.iter_mut().take(16).enumerate() {
            let base = i * 4;
            *word = u32::from_be_bytes([
                chunk[base],
                chunk[base + 1],
                chunk[base + 2],
                chunk[base + 3],
            ]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }

        let mut a = h[0];
        let mut b = h[1];
        let mut c = h[2];
        let mut d = h[3];
        let mut e = h[4];
        let mut f = h[5];
        let mut g = h[6];
        let mut hh = h[7];

        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);

            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }

        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
        h[5] = h[5].wrapping_add(f);
        h[6] = h[6].wrapping_add(g);
        h[7] = h[7].wrapping_add(hh);
    }

    let mut out = [0u8; 32];
    for (i, word) in h.iter().enumerate() {
        out[i * 4..i * 4 + 4].copy_from_slice(&word.to_be_bytes());
    }
    out
}

fn write_lc_linkedit_data(buf: &mut Vec<u8>, cmd: u32, dataoff: u64, datasize: u32) {
    assert!(
        dataoff <= u32::MAX as u64,
        "linkedit data offset exceeds Mach-O command range"
    );
    buf.extend_from_slice(&cmd.to_le_bytes());
    buf.extend_from_slice(&LINKEDIT_DATA_COMMAND_SIZE.to_le_bytes());
    buf.extend_from_slice(&(dataoff as u32).to_le_bytes());
    buf.extend_from_slice(&datasize.to_le_bytes());
}

fn write_import_entry(buf: &mut Vec<u8>, lib_ordinal: u32, name_offset: u32) {
    assert!(
        lib_ordinal <= 0xF0,
        "dylib ordinal exceeds compact import format"
    );
    assert!(
        name_offset < (1 << 23),
        "chained import symbol-name table offset exceeds compact import format"
    );
    let raw = (lib_ordinal & 0xFF) | (name_offset << 9);
    buf.extend_from_slice(&raw.to_le_bytes());
}

fn write_chained_fixup_segment_info(buf: &mut Vec<u8>, segment: &ChainedFixupSegmentInfo) {
    let first = buf.len();
    let page_count = segment
        .page_starts
        .iter()
        .map(|(page, _)| *page as usize)
        .max()
        .map_or(0, |max_page| max_page + 1);
    assert!(
        page_count <= u16::MAX as usize,
        "too many chained-fixup pages"
    );

    let raw_size = 22 + page_count * 2;
    let size = align_to(raw_size as u64, 8) as u32;

    buf.extend_from_slice(&size.to_le_bytes());
    buf.extend_from_slice(&(PAGE_SIZE as u16).to_le_bytes());
    buf.extend_from_slice(&DYLD_CHAINED_PTR_64.to_le_bytes());
    buf.extend_from_slice(&segment.segment_offset.to_le_bytes());
    buf.extend_from_slice(&0u32.to_le_bytes()); // max_valid_pointer is unused for 64-bit.
    buf.extend_from_slice(&(page_count as u16).to_le_bytes());

    let mut starts = vec![DYLD_CHAINED_PTR_START_NONE; page_count];
    for &(page, start) in &segment.page_starts {
        starts[page as usize] = start;
    }
    for start in starts {
        buf.extend_from_slice(&start.to_le_bytes());
    }

    buf.resize(first + size as usize, 0);
}

fn build_chained_fixups_payload(
    segment_count: usize,
    fixup_segment: Option<&ChainedFixupSegmentInfo>,
    import_symbols: &[String],
    import_ordinals: &[u32],
) -> Vec<u8> {
    assert_eq!(
        import_symbols.len(),
        import_ordinals.len(),
        "chained-fixups import symbols and ordinals must match"
    );

    let mut buf = Vec::new();
    buf.extend_from_slice(&0u32.to_le_bytes()); // fixups_version
    buf.extend_from_slice(&0u32.to_le_bytes()); // starts_offset, patched below
    buf.extend_from_slice(&0u32.to_le_bytes()); // imports_offset, patched below
    buf.extend_from_slice(&0u32.to_le_bytes()); // symbols_offset, patched below
    buf.extend_from_slice(&(import_symbols.len() as u32).to_le_bytes());
    buf.extend_from_slice(&DYLD_CHAINED_IMPORT.to_le_bytes());
    buf.extend_from_slice(&DYLD_CHAINED_SYMBOLS_UNCOMPRESSED.to_le_bytes());
    debug_assert_eq!(buf.len(), DYLD_CHAINED_FIXUPS_HEADER_SIZE as usize);
    pad_vec_to_alignment(&mut buf, 8);

    let starts_offset = buf.len();
    patch_u32(&mut buf, 4, starts_offset as u32);
    buf.extend_from_slice(&(segment_count as u32).to_le_bytes());
    let seg_info_offsets_start = buf.len();
    for _ in 0..segment_count {
        buf.extend_from_slice(&0u32.to_le_bytes());
    }
    pad_vec_to_alignment(&mut buf, 8);

    if let Some(segment) = fixup_segment {
        assert!(
            segment.segment_index < segment_count,
            "chained-fixups segment index out of range"
        );
        let segment_offset_from_starts = (buf.len() - starts_offset) as u32;
        patch_u32(
            &mut buf,
            seg_info_offsets_start + segment.segment_index * 4,
            segment_offset_from_starts,
        );
        write_chained_fixup_segment_info(&mut buf, segment);
    }

    let imports_offset = buf.len();
    patch_u32(&mut buf, 8, imports_offset as u32);
    let mut name_offset = 0u32;
    for (&lib_ordinal, symbol) in import_ordinals.iter().zip(import_symbols) {
        write_import_entry(&mut buf, lib_ordinal, name_offset);
        name_offset += symbol.len() as u32 + 1;
    }

    let symbols_offset = buf.len();
    patch_u32(&mut buf, 12, symbols_offset as u32);
    for symbol in import_symbols {
        buf.extend_from_slice(symbol.as_bytes());
        buf.push(0);
    }

    buf
}

fn build_linkedit_payload(
    linkedit_file_offset: u64,
    segment_count: usize,
    fixup_segment: Option<&ChainedFixupSegmentInfo>,
    import_symbols: &[String],
    import_ordinals: &[u32],
) -> LinkeditPayload {
    let fixups = build_chained_fixups_payload(
        segment_count,
        fixup_segment,
        import_symbols,
        import_ordinals,
    );
    let fixups_size = fixups.len() as u32;
    let mut data = fixups;
    pad_vec_to_alignment(&mut data, 8);

    let exports_offset = linkedit_file_offset + data.len() as u64;
    let exports_size = EMPTY_EXPORTS_TRIE.len() as u32;
    data.extend_from_slice(EMPTY_EXPORTS_TRIE);
    pad_vec_to_alignment(&mut data, 8);

    let code_signature_offset = align_to(
        linkedit_file_offset + data.len() as u64,
        CODE_SIGNATURE_ALIGNMENT,
    );
    let code_signature_padding =
        (code_signature_offset - (linkedit_file_offset + data.len() as u64)) as usize;
    data.resize(data.len() + code_signature_padding, 0);
    let code_signature_size = code_signature_size(code_signature_offset);

    LinkeditPayload {
        data,
        fixups_offset: linkedit_file_offset,
        fixups_size,
        exports_offset,
        exports_size,
        code_signature_offset,
        code_signature_size,
    }
}

fn has_file_backed_data_sections(objects: &[ParsedObject]) -> bool {
    objects.iter().any(|obj| {
        obj.sections
            .iter()
            .any(|sec| sec.segment != "__TEXT" && !sec.data.is_empty())
    })
}

fn dylib_command_size(dylib: &DylibEntry) -> u32 {
    let name_len = dylib.install_name.len() as u32 + 1;
    let raw_size = LC_LOAD_DYLIB_HEADER_SIZE + name_len;
    align_to(raw_size as u64, 8) as u32
}

fn executable_load_command_size(
    has_data: bool,
    text_nsects: u32,
    data_nsects: u32,
    dylib_cmd_sizes: &[u32],
) -> u32 {
    let pagezero_seg_size = SEGMENT_COMMAND_64_SIZE;
    let text_seg_size = SEGMENT_COMMAND_64_SIZE + text_nsects * SECTION_64_SIZE;
    let data_seg_size = if has_data {
        SEGMENT_COMMAND_64_SIZE + data_nsects * SECTION_64_SIZE
    } else {
        0
    };
    let linkedit_seg_size = SEGMENT_COMMAND_64_SIZE;
    let total_dylib_size: u32 = dylib_cmd_sizes.iter().sum();

    pagezero_seg_size
        + text_seg_size
        + data_seg_size
        + linkedit_seg_size
        + BUILD_VERSION_COMMAND_SIZE
        + UUID_COMMAND_SIZE
        + LC_MAIN_SIZE
        + LINKEDIT_DATA_COMMAND_SIZE
        + LINKEDIT_DATA_COMMAND_SIZE
        + LINKEDIT_DATA_COMMAND_SIZE
        + SYMTAB_COMMAND_SIZE
        + DYSYMTAB_COMMAND_SIZE
        + dylinker_command_size()
        + total_dylib_size
}

fn executable_text_file_offset_from_lc_size(total_lc_size: u32) -> u64 {
    align_to(MACH_HEADER_64_SIZE as u64 + total_lc_size as u64, PAGE_SIZE)
}

fn plain_executable_text_file_offset(has_data: bool) -> u64 {
    executable_text_file_offset_from_lc_size(executable_load_command_size(
        has_data,
        1,
        if has_data { 1 } else { 0 },
        &[],
    ))
}

fn dylib_executable_text_file_offset(
    has_data: bool,
    has_stubs: bool,
    needed_dylibs: &[&DylibEntry],
) -> u64 {
    let text_nsects = if has_stubs { 2 } else { 1 };
    let data_nsects = if has_stubs { 2 } else { 1 };
    let dylib_cmd_sizes: Vec<u32> = needed_dylibs
        .iter()
        .map(|dylib| dylib_command_size(dylib))
        .collect();

    executable_text_file_offset_from_lc_size(executable_load_command_size(
        has_data,
        text_nsects,
        data_nsects,
        &dylib_cmd_sizes,
    ))
}

fn dylib_ordinal_for_symbol(needed_dylibs: &[&DylibEntry], symbol: &str) -> u32 {
    needed_dylibs
        .iter()
        .position(|dylib| dylib.symbols.contains(symbol))
        .map(|idx| idx as u32 + 1)
        .expect("dylib symbol must be provided by a loaded dylib")
}

fn encode_chained_ptr_64_bind(import_ordinal: u32, next: u16) -> u64 {
    assert!(
        import_ordinal < (1 << 24),
        "chained bind import ordinal exceeds DYLD_CHAINED_PTR_64 range"
    );
    (import_ordinal as u64) | ((next as u64) << 51) | (1u64 << 63)
}

fn encode_got_chained_binds(
    data: &mut [u8],
    got_offset: u64,
    import_count: usize,
) -> Vec<(u16, u16)> {
    let mut page_starts = Vec::new();

    for index in 0..import_count {
        let slot_offset = got_offset + index as u64 * 8;
        let slot_end = slot_offset as usize + 8;
        assert!(
            slot_end <= data.len(),
            "GOT chained bind slot exceeds __DATA bounds"
        );

        let page_index = slot_offset / PAGE_SIZE;
        assert!(
            page_index <= u16::MAX as u64,
            "GOT chained bind page index exceeds dyld format range"
        );
        if index == 0 || (slot_offset - 8) / PAGE_SIZE != page_index {
            page_starts.push((page_index as u16, (slot_offset % PAGE_SIZE) as u16));
        }

        let next_slot_offset = slot_offset + 8;
        let next = if index + 1 < import_count && next_slot_offset / PAGE_SIZE == page_index {
            2
        } else {
            0
        };
        let encoded = encode_chained_ptr_64_bind(index as u32, next);
        data[slot_offset as usize..slot_end].copy_from_slice(&encoded.to_le_bytes());
    }

    page_starts
}

/// Compute the size of the LC_LOAD_DYLINKER load command (8-byte aligned).
fn dylinker_command_size() -> u32 {
    let name_len = DYLD_PATH.len() as u32 + 1; // +1 for NUL
    let raw = LC_LOAD_DYLINKER_HEADER_SIZE + name_len;
    align_to(raw as u64, 8) as u32
}

/// Append an LC_LOAD_DYLINKER load command pointing at `/usr/lib/dyld`.
///
/// Format:
///   cmd       u32 = LC_LOAD_DYLINKER
///   cmdsize   u32 (8-byte aligned)
///   name.offset u32 = 12 (immediately after header)
///   name      NUL-terminated string
///   padding   0..7 bytes to reach cmdsize
fn write_lc_load_dylinker(buf: &mut Vec<u8>) {
    let cmd_size = dylinker_command_size();
    buf.extend_from_slice(&LC_LOAD_DYLINKER.to_le_bytes());
    buf.extend_from_slice(&cmd_size.to_le_bytes());
    buf.extend_from_slice(&LC_LOAD_DYLINKER_HEADER_SIZE.to_le_bytes()); // name.offset
    let name_bytes = DYLD_PATH.as_bytes();
    buf.extend_from_slice(name_bytes);
    buf.push(0); // NUL terminator
    let written = LC_LOAD_DYLINKER_HEADER_SIZE as usize + name_bytes.len() + 1;
    let padding = cmd_size as usize - written;
    for _ in 0..padding {
        buf.push(0);
    }
}

fn write_lc_build_version(buf: &mut Vec<u8>) {
    buf.extend_from_slice(&LC_BUILD_VERSION.to_le_bytes());
    buf.extend_from_slice(&BUILD_VERSION_COMMAND_SIZE.to_le_bytes());
    buf.extend_from_slice(&PLATFORM_MACOS.to_le_bytes());
    buf.extend_from_slice(&MACOS_14_0_0.to_le_bytes());
    buf.extend_from_slice(&MACOS_14_0_0.to_le_bytes());
    buf.extend_from_slice(&0u32.to_le_bytes()); // ntools
}

fn update_uuid_hashes(lo: &mut u64, hi: &mut u64, bytes: &[u8]) {
    const FNV_PRIME: u64 = 0x0000_0100_0000_01B3;

    for &byte in bytes {
        *lo ^= byte as u64;
        *lo = lo.wrapping_mul(FNV_PRIME);

        *hi ^= (byte as u64).wrapping_add(0x9E37_79B9_7F4A_7C15);
        *hi = hi.rotate_left(5).wrapping_mul(FNV_PRIME);
    }
}

fn update_uuid_u64(lo: &mut u64, hi: &mut u64, value: u64) {
    update_uuid_hashes(lo, hi, &value.to_le_bytes());
}

fn update_uuid_bytes(lo: &mut u64, hi: &mut u64, bytes: &[u8]) {
    update_uuid_u64(lo, hi, bytes.len() as u64);
    update_uuid_hashes(lo, hi, bytes);
}

fn deterministic_executable_uuid(
    text_data: &[u8],
    data_data: &[u8],
    text_vmaddr: u64,
    data_vmaddr: u64,
    entry_offset: u64,
    stubs_offset: u64,
    needed_dylibs: &[&DylibEntry],
    dylib_symbols: &[String],
) -> [u8; 16] {
    let mut lo = 0xCBF2_9CE4_8422_2325u64;
    let mut hi = 0x8422_2325_CBF2_9CE4u64;

    update_uuid_bytes(&mut lo, &mut hi, b"trust-cg-macho-executable-v1");
    update_uuid_u64(&mut lo, &mut hi, text_vmaddr);
    update_uuid_u64(&mut lo, &mut hi, data_vmaddr);
    update_uuid_u64(&mut lo, &mut hi, entry_offset);
    update_uuid_u64(&mut lo, &mut hi, stubs_offset);
    update_uuid_bytes(&mut lo, &mut hi, text_data);
    update_uuid_bytes(&mut lo, &mut hi, data_data);

    update_uuid_u64(&mut lo, &mut hi, needed_dylibs.len() as u64);
    for dylib in needed_dylibs {
        update_uuid_bytes(&mut lo, &mut hi, dylib.install_name.as_bytes());
    }

    update_uuid_u64(&mut lo, &mut hi, dylib_symbols.len() as u64);
    for symbol in dylib_symbols {
        update_uuid_bytes(&mut lo, &mut hi, symbol.as_bytes());
    }

    let mut uuid = [0u8; 16];
    uuid[..8].copy_from_slice(&lo.to_le_bytes());
    uuid[8..].copy_from_slice(&hi.to_le_bytes());
    uuid
}

fn write_lc_uuid(buf: &mut Vec<u8>, uuid: [u8; 16]) {
    buf.extend_from_slice(&LC_UUID.to_le_bytes());
    buf.extend_from_slice(&UUID_COMMAND_SIZE.to_le_bytes());
    buf.extend_from_slice(&uuid);
}

fn write_empty_lc_dysymtab(buf: &mut Vec<u8>) {
    buf.extend_from_slice(&LC_DYSYMTAB.to_le_bytes());
    buf.extend_from_slice(&DYSYMTAB_COMMAND_SIZE.to_le_bytes());
    for _ in 0..18 {
        buf.extend_from_slice(&0u32.to_le_bytes());
    }
}

// ---------------------------------------------------------------------------
// Relocation application
// ---------------------------------------------------------------------------

const RELOC32_PATCH_OOB_DETAIL: &str = "32-bit relocation patch offset out of bounds";
const RELOC64_PATCH_OOB_DETAIL: &str = "64-bit relocation patch offset out of bounds";

/// Apply relocations to mutable section data.
pub struct RelocationApplicator;

impl RelocationApplicator {
    /// Apply all relocations for a section, patching the section data in place.
    ///
    /// - `section_data`: mutable section bytes to patch.
    /// - `section_addr`: virtual address of this section.
    /// - `relocations`: relocations for this section.
    /// - `symbols`: symbol table from the source object.
    /// - `symbol_addrs`: map from symbol name to resolved address.
    ///
    /// Local defined `N_SECT` targets require object-scoped symbol-index
    /// addresses and are only supported by [`Self::apply_with_local_symbols`].
    ///
    /// `section_addrs` is the per-object mapped-base table (0-based section
    /// index -> virtual base address) used to resolve section-relative
    /// (`is_extern == false`) relocations to the referenced section's mapped
    /// base, not the raw section ordinal.
    pub fn apply(
        section_data: &mut [u8],
        section_addr: u64,
        relocations: &[Relocation],
        symbols: &[ParsedSymbol],
        symbol_addrs: &HashMap<String, u64>,
        section_addrs: &[u64],
    ) -> Result<(), LinkerError> {
        let local_symbol_addrs = HashMap::new();
        Self::apply_with_local_symbols(
            section_data,
            section_addr,
            relocations,
            symbols,
            symbol_addrs,
            &local_symbol_addrs,
            section_addrs,
        )
    }

    /// Apply relocations with an object-local symbol-index address map.
    ///
    /// `section_addrs` is the per-object mapped-base table (0-based section
    /// index -> virtual base address) used to resolve section-relative
    /// (`is_extern == false`) relocations to the referenced section's mapped
    /// base, not the raw section ordinal.
    pub fn apply_with_local_symbols(
        section_data: &mut [u8],
        section_addr: u64,
        relocations: &[Relocation],
        symbols: &[ParsedSymbol],
        symbol_addrs: &HashMap<String, u64>,
        local_symbol_addrs: &HashMap<usize, u64>,
        section_addrs: &[u64],
    ) -> Result<(), LinkerError> {
        let mut idx = 0usize;
        while idx < relocations.len() {
            let reloc = &relocations[idx];
            if reloc.kind == AArch64RelocKind::Subtractor {
                let Some(unsigned) = relocations.get(idx + 1) else {
                    return Err(LinkerError::MalformedRelocation(
                        "ARM64_RELOC_SUBTRACTOR must be followed by ARM64_RELOC_UNSIGNED".into(),
                    ));
                };
                if unsigned.kind != AArch64RelocKind::Unsigned
                    || unsigned.offset != reloc.offset
                    || unsigned.length != reloc.length
                {
                    return Err(LinkerError::MalformedRelocation(
                        "ARM64_RELOC_SUBTRACTOR must be followed by matching ARM64_RELOC_UNSIGNED"
                            .into(),
                    ));
                }

                let subtrahend = Self::target_addr(
                    reloc,
                    symbols,
                    symbol_addrs,
                    local_symbol_addrs,
                    section_addrs,
                )?;
                let target_addr = Self::target_addr(
                    unsigned,
                    symbols,
                    symbol_addrs,
                    local_symbol_addrs,
                    section_addrs,
                )?;
                let patch_offset = reloc.offset as usize;
                Self::apply_subtractor_pair(
                    section_data,
                    patch_offset,
                    target_addr,
                    subtrahend,
                    reloc.length,
                )?;
                idx += 2;
                continue;
            }

            let target_addr = Self::target_addr(
                reloc,
                symbols,
                symbol_addrs,
                local_symbol_addrs,
                section_addrs,
            )?;

            let pc = section_addr + reloc.offset as u64;
            let patch_offset = reloc.offset as usize;

            match reloc.kind {
                AArch64RelocKind::Branch26 => {
                    Self::apply_branch26(section_data, patch_offset, pc, target_addr)?;
                }
                AArch64RelocKind::Page21 => {
                    Self::apply_page21(section_data, patch_offset, pc, target_addr)?;
                }
                AArch64RelocKind::Pageoff12 => {
                    Self::apply_pageoff12(section_data, patch_offset, target_addr)?;
                }
                AArch64RelocKind::Unsigned => {
                    Self::apply_unsigned(section_data, patch_offset, pc, target_addr, reloc)?;
                }
                AArch64RelocKind::PointerToGot => {
                    Self::apply_pointer_to_got(section_data, patch_offset, pc, target_addr, reloc)?;
                }
                other => {
                    return Err(LinkerError::UnsupportedRelocation(other));
                }
            }
            idx += 1;
        }
        Ok(())
    }

    fn target_addr(
        reloc: &Relocation,
        symbols: &[ParsedSymbol],
        symbol_addrs: &HashMap<String, u64>,
        local_symbol_addrs: &HashMap<usize, u64>,
        section_addrs: &[u64],
    ) -> Result<u64, LinkerError> {
        if !reloc.is_extern {
            // Section-relative relocation: r_symbolnum is a 1-based SECTION
            // ORDINAL (per the Mach-O ABI), NOT an address. Resolve it to the
            // referenced section's mapped base address. The inline / preceding
            // ARM64_RELOC_ADDEND addend is applied by the per-kind handlers
            // (apply_unsigned/apply_branch26/...), so return ONLY the base here.
            let ordinal = reloc.symbol_index;
            if ordinal == 0 || (ordinal as usize) > section_addrs.len() {
                return Err(LinkerError::MalformedRelocation(format!(
                    "section ordinal {ordinal} out of range (have {} sections)",
                    section_addrs.len()
                )));
            }
            return Ok(section_addrs[(ordinal - 1) as usize]);
        }

        let sym_idx = reloc.symbol_index as usize;
        if sym_idx >= symbols.len() {
            return Err(LinkerError::MalformedRelocation(format!(
                "symbol index {} out of range",
                reloc.symbol_index
            )));
        }
        let sym = &symbols[sym_idx];
        if sym.is_defined() && !sym.is_external() {
            if let Some(address) = local_symbol_addrs.get(&sym_idx).copied() {
                return Ok(address);
            }
            return Err(LinkerError::MalformedRelocation(format!(
                "local defined symbol '{}' at index {} has no object-local resolved address",
                sym.name, sym_idx
            )));
        }
        symbol_addrs
            .get(&sym.name)
            .copied()
            .ok_or_else(|| LinkerError::UndefinedSymbol(sym.name.clone()))
    }

    /// Apply ARM64_RELOC_BRANCH26.
    ///
    /// B/BL instructions encode a signed 26-bit word offset in bits [25:0].
    /// The actual byte displacement is imm26 << 2.
    fn apply_branch26(
        data: &mut [u8],
        offset: usize,
        pc: u64,
        target: u64,
    ) -> Result<(), LinkerError> {
        if offset + 4 > data.len() {
            return Err(LinkerError::RelocationOverflow {
                detail: "BRANCH26 patch offset out of bounds".into(),
            });
        }

        let displacement = target as i64 - pc as i64;
        let imm26 = displacement >> 2;

        // Check range: signed 26-bit = +/- 128 MiB.
        if !(-(1 << 25)..(1 << 25)).contains(&imm26) {
            return Err(LinkerError::RelocationOverflow {
                detail: format!(
                    "BRANCH26 displacement {:#x} out of +/-128MiB range",
                    displacement
                ),
            });
        }

        let mut inst = u32::from_le_bytes([
            data[offset],
            data[offset + 1],
            data[offset + 2],
            data[offset + 3],
        ]);

        // Clear existing imm26 field and set new value.
        inst = (inst & !0x03FF_FFFF) | ((imm26 as u32) & 0x03FF_FFFF);

        let bytes = inst.to_le_bytes();
        data[offset..offset + 4].copy_from_slice(&bytes);

        Ok(())
    }

    /// Apply ARM64_RELOC_PAGE21.
    ///
    /// ADRP encodes a signed 21-bit page offset. The page delta is:
    ///   (target_page - pc_page) >> 12
    /// where page = addr & ~0xFFF.
    ///
    /// ADRP encoding: immhi[23:5] in bits [23:5], immlo[1:0] in bits [30:29].
    fn apply_page21(
        data: &mut [u8],
        offset: usize,
        pc: u64,
        target: u64,
    ) -> Result<(), LinkerError> {
        if offset + 4 > data.len() {
            return Err(LinkerError::RelocationOverflow {
                detail: "PAGE21 patch offset out of bounds".into(),
            });
        }

        let pc_page = pc & !0xFFF;
        let target_page = target & !0xFFF;
        let page_delta = (target_page as i64 - pc_page as i64) >> 12;

        // Check range: signed 21-bit = +/- 4 GiB.
        if !(-(1 << 20)..(1 << 20)).contains(&page_delta) {
            return Err(LinkerError::RelocationOverflow {
                detail: format!("PAGE21 page delta {:#x} out of +/-4GiB range", page_delta),
            });
        }

        let imm21 = (page_delta as u32) & 0x001F_FFFF;
        let immlo = imm21 & 0x3;
        let immhi = (imm21 >> 2) & 0x7FFFF;

        let mut inst = u32::from_le_bytes([
            data[offset],
            data[offset + 1],
            data[offset + 2],
            data[offset + 3],
        ]);

        // Clear immhi (bits 23:5) and immlo (bits 30:29), then set.
        inst &= !(0x7FFFF << 5); // Clear immhi
        inst &= !(0x3 << 29); // Clear immlo
        inst |= immhi << 5;
        inst |= immlo << 29;

        let bytes = inst.to_le_bytes();
        data[offset..offset + 4].copy_from_slice(&bytes);

        Ok(())
    }

    /// Apply ARM64_RELOC_PAGEOFF12.
    ///
    /// ADD/LDR instructions encode a 12-bit page offset in bits [21:10].
    /// The offset is target & 0xFFF.
    fn apply_pageoff12(data: &mut [u8], offset: usize, target: u64) -> Result<(), LinkerError> {
        if offset + 4 > data.len() {
            return Err(LinkerError::RelocationOverflow {
                detail: "PAGEOFF12 patch offset out of bounds".into(),
            });
        }

        let page_offset = (target & 0xFFF) as u32;

        let mut inst = u32::from_le_bytes([
            data[offset],
            data[offset + 1],
            data[offset + 2],
            data[offset + 3],
        ]);

        // Determine if this is a load/store (needs scaling) or ADD (no scaling).
        // LDR/STR instructions have bit 27 = 1 and bit 26 = 0 (load/store class).
        // ADD has opc = 0b00x at bits [30:29] and op=0 at bit [30].
        let is_load_store = (inst >> 27) & 0x1 == 1 && (inst >> 24) & 0x3 == 0x1;

        let imm12 = if is_load_store {
            // For load/store, the offset is scaled by the access size.
            // size field is bits [31:30]: 00=1B, 01=2B, 10=4B, 11=8B
            let size = (inst >> 30) & 0x3;
            let scale = 1u32 << size;
            page_offset / scale
        } else {
            // For ADD, the immediate is unscaled.
            page_offset
        };

        // Clear imm12 field (bits 21:10) and set new value.
        inst = (inst & !(0xFFF << 10)) | ((imm12 & 0xFFF) << 10);

        let bytes = inst.to_le_bytes();
        data[offset..offset + 4].copy_from_slice(&bytes);

        Ok(())
    }

    /// Apply ARM64_RELOC_UNSIGNED.
    ///
    /// Supports absolute pointer relocations. Darwin AArch64 PC-relative
    /// `__eh_frame` values are emitted as SUBTRACTOR+UNSIGNED pairs.
    fn apply_unsigned(
        data: &mut [u8],
        offset: usize,
        _pc: u64,
        target: u64,
        reloc: &Relocation,
    ) -> Result<(), LinkerError> {
        if reloc.pc_relative {
            return Err(LinkerError::UnsupportedRelocation(
                AArch64RelocKind::Unsigned,
            ));
        }

        let value = Self::read_signed_addend(data, offset, reloc.length)?
            .checked_add(target as i128)
            .ok_or_else(|| LinkerError::RelocationOverflow {
                detail: format!("UNSIGNED target {target:#x} plus addend overflowed"),
            })?;
        Self::write_sized_value(data, offset, reloc.length, value)
    }

    fn apply_pointer_to_got(
        data: &mut [u8],
        offset: usize,
        pc: u64,
        target: u64,
        reloc: &Relocation,
    ) -> Result<(), LinkerError> {
        if !reloc.pc_relative || reloc.length != 2 {
            return Err(LinkerError::UnsupportedRelocation(
                AArch64RelocKind::PointerToGot,
            ));
        }

        let addend = Self::read_signed_addend(data, offset, reloc.length)?;
        let value = target as i128 + addend - pc as i128;
        Self::write_sized_value(data, offset, reloc.length, value)
    }

    fn apply_subtractor_pair(
        data: &mut [u8],
        offset: usize,
        target: u64,
        subtrahend: u64,
        length: u8,
    ) -> Result<(), LinkerError> {
        let addend = Self::read_signed_addend(data, offset, length)?;
        let value = target as i128 + addend - subtrahend as i128;
        Self::write_sized_value(data, offset, length, value)
    }

    fn read_signed_addend(data: &[u8], offset: usize, length: u8) -> Result<i128, LinkerError> {
        match length {
            2 => {
                let end = offset
                    .checked_add(4)
                    .ok_or_else(|| LinkerError::RelocationOverflow {
                        detail: RELOC32_PATCH_OOB_DETAIL.into(),
                    })?;
                let bytes =
                    data.get(offset..end)
                        .ok_or_else(|| LinkerError::RelocationOverflow {
                            detail: RELOC32_PATCH_OOB_DETAIL.into(),
                        })?;
                let mut addend = [0u8; 4];
                addend.copy_from_slice(bytes);
                Ok(i32::from_le_bytes(addend) as i128)
            }
            3 => {
                let end = offset
                    .checked_add(8)
                    .ok_or_else(|| LinkerError::RelocationOverflow {
                        detail: RELOC64_PATCH_OOB_DETAIL.into(),
                    })?;
                let bytes =
                    data.get(offset..end)
                        .ok_or_else(|| LinkerError::RelocationOverflow {
                            detail: RELOC64_PATCH_OOB_DETAIL.into(),
                        })?;
                let mut addend = [0u8; 8];
                addend.copy_from_slice(bytes);
                Ok(i64::from_le_bytes(addend) as i128)
            }
            _ => Err(LinkerError::UnsupportedRelocation(
                AArch64RelocKind::Unsigned,
            )),
        }
    }

    fn write_sized_value(
        data: &mut [u8],
        offset: usize,
        length: u8,
        value: i128,
    ) -> Result<(), LinkerError> {
        match length {
            2 => {
                if value < i32::MIN as i128 || value > i32::MAX as i128 {
                    return Err(LinkerError::RelocationOverflow {
                        detail: format!("32-bit relocation value {value:#x} out of range"),
                    });
                }
                data[offset..offset + 4].copy_from_slice(&(value as i32).to_le_bytes());
                Ok(())
            }
            3 => {
                if value < i64::MIN as i128 || value > i64::MAX as i128 {
                    return Err(LinkerError::RelocationOverflow {
                        detail: format!("64-bit relocation value {value:#x} out of range"),
                    });
                }
                data[offset..offset + 8].copy_from_slice(&(value as i64).to_le_bytes());
                Ok(())
            }
            _ => Err(LinkerError::UnsupportedRelocation(
                AArch64RelocKind::Unsigned,
            )),
        }
    }
}

// ---------------------------------------------------------------------------
// Executable emission
// ---------------------------------------------------------------------------

/// Emits a Mach-O MH_EXECUTE binary from linked sections.
pub struct ExecutableEmitter;

impl ExecutableEmitter {
    /// Emit a complete MH_EXECUTE Mach-O file.
    ///
    /// - `text_sections`: concatenated, relocated __TEXT section data.
    /// - `data_sections`: concatenated, relocated __DATA section data.
    /// - `text_vmaddr`: virtual address of the __TEXT segment.
    /// - `data_vmaddr`: virtual address of the __DATA segment.
    /// - `entry_offset`: offset of _main within the __TEXT segment (from text_vmaddr).
    pub fn emit(
        text_data: &[u8],
        data_data: &[u8],
        text_vmaddr: u64,
        data_vmaddr: u64,
        entry_offset: u64,
    ) -> Vec<u8> {
        // Compute sizes.
        let text_size = text_data.len() as u64;
        let data_size = data_data.len() as u64;
        let text_size_aligned = align_to(text_size, PAGE_SIZE);
        let data_size_aligned = if data_size > 0 {
            align_to(data_size, PAGE_SIZE)
        } else {
            0
        };

        let has_data = !data_data.is_empty();
        let segment_count = if has_data { 4 } else { 3 };
        // __PAGEZERO + __TEXT [+ __DATA] + __LINKEDIT + LC_BUILD_VERSION +
        // LC_UUID + LC_MAIN + LC_DYLD_CHAINED_FIXUPS + LC_DYLD_EXPORTS_TRIE +
        // LC_CODE_SIGNATURE + LC_SYMTAB + LC_DYSYMTAB + LC_LOAD_DYLINKER.
        let ncmds: u32 = if has_data { 13 } else { 12 };

        let total_lc_size =
            executable_load_command_size(has_data, 1, if has_data { 1 } else { 0 }, &[]);

        // __TEXT is file-backed from offset 0 so the Mach-O header and load
        // commands are mapped. The __text section stays page-aligned inside it.
        let text_file_offset = executable_text_file_offset_from_lc_size(total_lc_size);
        let text_segment_filesize = text_file_offset + text_size_aligned;
        let text_segment_vmsize = align_to(text_segment_filesize, PAGE_SIZE);
        let text_section_vmaddr = text_vmaddr + text_file_offset;
        let data_file_offset = text_segment_filesize;
        let linkedit_file_offset = if has_data {
            data_file_offset + data_size_aligned
        } else {
            text_segment_filesize
        };
        let linkedit_vmaddr = if has_data {
            data_vmaddr + data_size_aligned
        } else {
            text_vmaddr + text_segment_vmsize
        };
        let linkedit_payload =
            build_linkedit_payload(linkedit_file_offset, segment_count, None, &[], &[]);
        let linkedit_filesize =
            linkedit_payload.data.len() as u64 + linkedit_payload.code_signature_size as u64;
        let linkedit_vmsize = align_to(linkedit_filesize, PAGE_SIZE);

        let total_file_size = linkedit_file_offset + linkedit_filesize;

        let mut buf = Vec::with_capacity(total_file_size as usize);

        // --- Header ---
        buf.extend_from_slice(&MH_MAGIC_64.to_le_bytes()); // magic
        buf.extend_from_slice(&CPU_TYPE_ARM64.to_le_bytes()); // cputype
        buf.extend_from_slice(&CPU_SUBTYPE_ARM64_ALL.to_le_bytes()); // cpusubtype
        buf.extend_from_slice(&MH_EXECUTE.to_le_bytes()); // filetype
        buf.extend_from_slice(&ncmds.to_le_bytes()); // ncmds
        buf.extend_from_slice(&total_lc_size.to_le_bytes()); // sizeofcmds
        buf.extend_from_slice(&(MH_EXECUTE_FLAGS).to_le_bytes()); // flags
        buf.extend_from_slice(&0u32.to_le_bytes()); // reserved

        // --- __PAGEZERO segment ---
        Self::write_segment(
            &mut buf,
            b"__PAGEZERO",
            0,                 // vmaddr
            DEFAULT_BASE_ADDR, // vmsize = 4GB
            0,                 // fileoff
            0,                 // filesize
            0,                 // maxprot
            0,                 // initprot
            0,                 // nsects
            0,                 // flags
        );

        // --- __TEXT segment ---
        Self::write_segment(
            &mut buf,
            b"__TEXT",
            text_vmaddr,
            text_segment_vmsize,
            0,
            text_segment_filesize,
            VM_PROT_READ | VM_PROT_EXECUTE,
            VM_PROT_READ | VM_PROT_EXECUTE,
            1, // 1 section
            0,
        );

        // __text section header
        Self::write_section_header(
            &mut buf,
            b"__text",
            b"__TEXT",
            text_section_vmaddr,
            text_size,
            text_file_offset as u32,
            2, // align = 2^2 = 4
            0, // reloff
            0, // nreloc
            S_REGULAR | S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS,
        );

        // --- __DATA segment (if needed) ---
        if has_data {
            let data_seg_vmsize = data_size_aligned;
            Self::write_segment(
                &mut buf,
                b"__DATA",
                data_vmaddr,
                data_seg_vmsize,
                data_file_offset,
                data_size_aligned,
                VM_PROT_READ | VM_PROT_WRITE,
                VM_PROT_READ | VM_PROT_WRITE,
                1,
                0,
            );

            // __data section header
            Self::write_section_header(
                &mut buf,
                b"__data",
                b"__DATA",
                data_vmaddr,
                data_size,
                data_file_offset as u32,
                3, // align = 2^3 = 8
                0,
                0,
                S_REGULAR,
            );
        }

        // --- __LINKEDIT segment ---
        Self::write_segment(
            &mut buf,
            b"__LINKEDIT",
            linkedit_vmaddr,
            linkedit_vmsize,
            linkedit_file_offset,
            linkedit_filesize,
            VM_PROT_READ,
            VM_PROT_READ,
            0,
            0,
        );

        // --- LC_BUILD_VERSION ---
        write_lc_build_version(&mut buf);

        // --- LC_UUID ---
        let uuid = deterministic_executable_uuid(
            text_data,
            data_data,
            text_vmaddr,
            data_vmaddr,
            entry_offset,
            0,
            &[],
            &[],
        );
        write_lc_uuid(&mut buf, uuid);

        // --- LC_MAIN ---
        buf.extend_from_slice(&LC_MAIN.to_le_bytes()); // cmd
        buf.extend_from_slice(&LC_MAIN_SIZE.to_le_bytes()); // cmdsize
        buf.extend_from_slice(&entry_offset.to_le_bytes()); // entryoff
        buf.extend_from_slice(&0u64.to_le_bytes()); // stacksize (0 = default)

        // --- LC_DYLD_CHAINED_FIXUPS / LC_DYLD_EXPORTS_TRIE ---
        write_lc_linkedit_data(
            &mut buf,
            LC_DYLD_CHAINED_FIXUPS,
            linkedit_payload.fixups_offset,
            linkedit_payload.fixups_size,
        );
        write_lc_linkedit_data(
            &mut buf,
            LC_DYLD_EXPORTS_TRIE,
            linkedit_payload.exports_offset,
            linkedit_payload.exports_size,
        );
        write_lc_linkedit_data(
            &mut buf,
            LC_CODE_SIGNATURE,
            linkedit_payload.code_signature_offset,
            linkedit_payload.code_signature_size,
        );

        // --- LC_SYMTAB (empty, for format compliance) ---
        buf.extend_from_slice(&LC_SYMTAB.to_le_bytes());
        buf.extend_from_slice(&SYMTAB_COMMAND_SIZE.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes()); // symoff
        buf.extend_from_slice(&0u32.to_le_bytes()); // nsyms
        buf.extend_from_slice(&0u32.to_le_bytes()); // stroff
        buf.extend_from_slice(&0u32.to_le_bytes()); // strsize

        // --- LC_DYSYMTAB (empty, matching the empty LC_SYMTAB) ---
        write_empty_lc_dysymtab(&mut buf);

        // --- LC_LOAD_DYLINKER (tells macOS kernel to use /usr/lib/dyld) ---
        write_lc_load_dylinker(&mut buf);

        // --- Pad to text_file_offset ---
        while (buf.len() as u64) < text_file_offset {
            buf.push(0);
        }

        // --- Write text data ---
        buf.extend_from_slice(text_data);
        while (buf.len() as u64) < text_file_offset + text_size_aligned {
            buf.push(0);
        }

        // --- Write data data ---
        if has_data {
            buf.extend_from_slice(data_data);
            while (buf.len() as u64) < linkedit_file_offset {
                buf.push(0);
            }
        }

        // --- Write __LINKEDIT payloads ---
        while (buf.len() as u64) < linkedit_file_offset {
            buf.push(0);
        }
        buf.extend_from_slice(&linkedit_payload.data);
        debug_assert_eq!(buf.len() as u64, linkedit_payload.code_signature_offset);
        let code_signature = build_ad_hoc_code_signature(&buf, 0, text_segment_filesize);
        debug_assert_eq!(
            code_signature.len() as u32,
            linkedit_payload.code_signature_size
        );
        buf.extend_from_slice(&code_signature);
        while (buf.len() as u64) < total_file_size {
            buf.push(0);
        }

        buf
    }

    /// Write a segment_command_64 to the buffer.
    #[allow(clippy::too_many_arguments)]
    fn write_segment(
        buf: &mut Vec<u8>,
        name: &[u8],
        vmaddr: u64,
        vmsize: u64,
        fileoff: u64,
        filesize: u64,
        maxprot: i32,
        initprot: i32,
        nsects: u32,
        flags: u32,
    ) {
        let cmdsize = SEGMENT_COMMAND_64_SIZE + nsects * SECTION_64_SIZE;
        buf.extend_from_slice(&LC_SEGMENT_64.to_le_bytes());
        buf.extend_from_slice(&cmdsize.to_le_bytes());
        buf.extend_from_slice(&padded_name(name));
        buf.extend_from_slice(&vmaddr.to_le_bytes());
        buf.extend_from_slice(&vmsize.to_le_bytes());
        buf.extend_from_slice(&fileoff.to_le_bytes());
        buf.extend_from_slice(&filesize.to_le_bytes());
        buf.extend_from_slice(&maxprot.to_le_bytes());
        buf.extend_from_slice(&initprot.to_le_bytes());
        buf.extend_from_slice(&nsects.to_le_bytes());
        buf.extend_from_slice(&flags.to_le_bytes());
    }

    /// Write a section_64 header to the buffer.
    #[allow(clippy::too_many_arguments)]
    fn write_section_header(
        buf: &mut Vec<u8>,
        sectname: &[u8],
        segname: &[u8],
        addr: u64,
        size: u64,
        offset: u32,
        align: u32,
        reloff: u32,
        nreloc: u32,
        flags: u32,
    ) {
        buf.extend_from_slice(&padded_name(sectname));
        buf.extend_from_slice(&padded_name(segname));
        buf.extend_from_slice(&addr.to_le_bytes());
        buf.extend_from_slice(&size.to_le_bytes());
        buf.extend_from_slice(&offset.to_le_bytes());
        buf.extend_from_slice(&align.to_le_bytes());
        buf.extend_from_slice(&reloff.to_le_bytes());
        buf.extend_from_slice(&nreloc.to_le_bytes());
        buf.extend_from_slice(&flags.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes()); // reserved1
        buf.extend_from_slice(&0u32.to_le_bytes()); // reserved2
        buf.extend_from_slice(&0u32.to_le_bytes()); // reserved3
    }
}

// ---------------------------------------------------------------------------
// Dead code stripping
// ---------------------------------------------------------------------------

/// Perform basic dead code stripping by removing unreferenced sections.
///
/// This is a conservative implementation: a section is kept if it contains a
/// symbol that is transitively referenced from the entry point. Sections in
/// __DATA segments are always kept (conservative: data may be referenced by
/// address without a relocation). Symbols with N_NO_DEAD_STRIP are also kept.
///
/// Returns a filtered set of objects with unreferenced __TEXT sections removed.
pub fn dead_strip_sections(objects: &[ParsedObject], entry_symbol: &str) -> Vec<ParsedObject> {
    // Phase 1: Collect all initially referenced symbols.
    let mut referenced_symbols: HashSet<String> = HashSet::new();
    referenced_symbols.insert(entry_symbol.to_string());

    // Walk all sections and collect extern relocation targets from ALL sections
    // (initial seed: everything that is referenced from anywhere, then we prune).
    for obj in objects {
        for sec in &obj.sections {
            for reloc in &sec.relocations {
                if reloc.is_extern {
                    let sym_idx = reloc.symbol_index as usize;
                    if sym_idx < obj.symbols.len() {
                        referenced_symbols.insert(obj.symbols[sym_idx].name.clone());
                    }
                }
            }
        }
    }

    // Phase 2: Iteratively compute transitive closure of referenced symbols.
    // A section is live if it defines a referenced symbol. If live, all symbols
    // referenced by its relocations are also referenced.
    let mut changed = true;
    while changed {
        changed = false;
        for obj in objects {
            for (sec_idx, sec) in obj.sections.iter().enumerate() {
                let sec_ordinal = (sec_idx + 1) as u8;
                let section_referenced = obj.symbols.iter().any(|sym| {
                    sym.section == sec_ordinal && referenced_symbols.contains(&sym.name)
                });

                if section_referenced {
                    for reloc in &sec.relocations {
                        if reloc.is_extern {
                            let sym_idx = reloc.symbol_index as usize;
                            if sym_idx < obj.symbols.len() {
                                let name = &obj.symbols[sym_idx].name;
                                if !referenced_symbols.contains(name) {
                                    referenced_symbols.insert(name.clone());
                                    changed = true;
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // Phase 3: Filter out unreferenced __TEXT sections.
    objects
        .iter()
        .map(|obj| {
            // While filtering, build an old 1-based ordinal -> new 1-based
            // ordinal map. Kept sections are renumbered sequentially; stripped
            // sections map to None. This keeps each surviving symbol's `section`
            // (n_sect) field pointing at the right section after re-indexing.
            let mut sections: Vec<ParsedSection> = Vec::new();
            let mut ordinal_map: Vec<Option<u8>> = Vec::with_capacity(obj.sections.len());
            for (sec_idx, sec) in obj.sections.iter().enumerate() {
                let sec_ordinal = (sec_idx + 1) as u8;

                // Keep if any symbol in it is referenced.
                let has_referenced_sym = obj.symbols.iter().any(|sym| {
                    sym.section == sec_ordinal && referenced_symbols.contains(&sym.name)
                });

                // Keep if any symbol has N_NO_DEAD_STRIP.
                let has_no_dead_strip = obj
                    .symbols
                    .iter()
                    .any(|sym| sym.section == sec_ordinal && sym.is_no_dead_strip());

                // Always keep non-TEXT sections (conservative: data may be
                // referenced by address).
                let is_data = sec.segment != "__TEXT";

                if has_referenced_sym || has_no_dead_strip || is_data {
                    sections.push(sec.clone());
                    ordinal_map.push(Some(sections.len() as u8));
                } else {
                    ordinal_map.push(None);
                }
            }

            // Remap each kept symbol's section ordinal to its new index. Drop a
            // symbol whose defining section was stripped (it can no longer be
            // located); undefined symbols (section == 0) pass through unchanged.
            let symbols: Vec<ParsedSymbol> = obj
                .symbols
                .iter()
                .filter_map(|sym| {
                    if sym.section == 0 {
                        // Undefined symbol: no section ordinal to remap.
                        return Some(sym.clone());
                    }
                    match ordinal_map
                        .get((sym.section - 1) as usize)
                        .copied()
                        .flatten()
                    {
                        Some(new_ordinal) => {
                            let mut s = sym.clone();
                            s.section = new_ordinal;
                            Some(s)
                        }
                        // Defining section was stripped: drop the symbol so no
                        // surviving symbol carries a stale ordinal.
                        None => None,
                    }
                })
                .collect();

            ParsedObject {
                cputype: obj.cputype,
                cpusubtype: obj.cpusubtype,
                flags: obj.flags,
                sections,
                symbols,
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// High-level link API
// ---------------------------------------------------------------------------

/// Link multiple parsed object files into an executable.
///
/// Returns the raw bytes of a Mach-O MH_EXECUTE file.
pub fn link(objects: &[ParsedObject]) -> Result<Vec<u8>, LinkerError> {
    // 1. Lay out sections.
    let text_file_offset =
        plain_executable_text_file_offset(has_file_backed_data_sections(objects));
    let layout = lay_out_sections(objects, DEFAULT_BASE_ADDR + text_file_offset);

    // 2. Resolve symbols.
    let mut resolver = SymbolResolver::new();
    for (obj_idx, obj) in objects.iter().enumerate() {
        resolver.add_object(obj_idx, obj, &layout.section_addrs[obj_idx])?;
    }
    let symbol_addrs = resolver.resolve()?;

    // 3. Build concatenated section data and apply relocations.
    let mut text_data = Vec::new();
    let mut data_data = Vec::new();

    for (obj_idx, obj) in objects.iter().enumerate() {
        let local_symbol_addrs = resolver.object_symbol_addrs(obj_idx);
        for (sec_idx, sec) in obj.sections.iter().enumerate() {
            let sec_addr = layout.section_addrs[obj_idx][sec_idx];
            let mut sec_data = sec.data.clone();

            // Apply relocations.
            if !sec.relocations.is_empty() {
                RelocationApplicator::apply_with_local_symbols(
                    &mut sec_data,
                    sec_addr,
                    &sec.relocations,
                    &obj.symbols,
                    &symbol_addrs,
                    &local_symbol_addrs,
                    &layout.section_addrs[obj_idx],
                )?;
            }

            if sec.segment == "__TEXT" {
                // Pad to alignment.
                let alignment = 1usize << sec.align;
                let misalign = text_data.len() % alignment;
                if misalign != 0 {
                    text_data.resize(text_data.len() + alignment - misalign, 0);
                }
                text_data.extend_from_slice(&sec_data);
            } else {
                let alignment = 1usize << sec.align;
                let misalign = data_data.len() % alignment;
                if misalign != 0 {
                    data_data.resize(data_data.len() + alignment - misalign, 0);
                }
                data_data.extend_from_slice(&sec_data);
            }
        }
    }

    // 4. Find _main entry point.
    let entry_addr = symbol_addrs.get("_main").ok_or(LinkerError::NoEntryPoint)?;
    let entry_offset = entry_addr - DEFAULT_BASE_ADDR;

    // 5. Emit executable.
    let text_size_aligned = align_to(text_data.len() as u64, PAGE_SIZE);
    let data_vmaddr = DEFAULT_BASE_ADDR + text_file_offset + text_size_aligned;

    Ok(ExecutableEmitter::emit(
        &text_data,
        &data_data,
        DEFAULT_BASE_ADDR,
        data_vmaddr,
        entry_offset,
    ))
}

// ---------------------------------------------------------------------------
// Dylib linking support
// ---------------------------------------------------------------------------

/// Configuration for dynamic library linking.
///
/// Specifies which dylibs to link against and which symbols they provide.
/// The linker uses this to:
/// 1. Allow undefined symbols that will be resolved at load time
/// 2. Emit LC_LOAD_DYLIB commands for each required dylib
/// 3. Generate stub/GOT entries so code can call dylib functions
#[derive(Debug, Clone)]
pub struct DylibConfig {
    /// Dylib entries: (install_name, set of provided symbols).
    pub dylibs: Vec<DylibEntry>,
}

/// A single dynamic library entry with its symbols.
#[derive(Debug, Clone)]
pub struct DylibEntry {
    /// The install name path (e.g., "/usr/lib/libSystem.B.dylib").
    pub install_name: String,
    /// Symbols exported by this dylib.
    pub symbols: HashSet<String>,
}

impl DylibConfig {
    /// Create a new empty dylib config.
    pub fn new() -> Self {
        Self { dylibs: Vec::new() }
    }

    /// Create a config with libSystem.dylib providing common symbols.
    pub fn with_libsystem() -> Self {
        let mut symbols = HashSet::new();
        // Common libSystem symbols needed by most executables.
        for sym in &[
            "_exit",
            "_printf",
            "_puts",
            "_malloc",
            "_free",
            "_write",
            "_read",
            "_open",
            "_close",
            "_mmap",
            "_munmap",
            "_memcpy",
            "_memset",
            "_strlen",
            "_abort",
            "___stack_chk_fail",
            "___stack_chk_guard",
            "_atexit",
        ] {
            symbols.insert(sym.to_string());
        }

        Self {
            dylibs: vec![DylibEntry {
                install_name: "/usr/lib/libSystem.B.dylib".to_string(),
                symbols,
            }],
        }
    }

    /// Add a dylib entry.
    pub fn add_dylib(&mut self, install_name: &str, symbols: HashSet<String>) {
        self.dylibs.push(DylibEntry {
            install_name: install_name.to_string(),
            symbols,
        });
    }

    /// Check if a symbol name is provided by any configured dylib.
    pub fn is_dylib_symbol(&self, name: &str) -> bool {
        self.dylibs.iter().any(|d| d.symbols.contains(name))
    }

    /// Get the indices of dylibs that are actually needed (have symbols referenced).
    pub fn needed_dylibs(&self, undefined_symbols: &[String]) -> Vec<usize> {
        let mut needed = Vec::new();
        for (idx, dylib) in self.dylibs.iter().enumerate() {
            if undefined_symbols.iter().any(|s| dylib.symbols.contains(s)) {
                needed.push(idx);
            }
        }
        needed
    }
}

impl Default for DylibConfig {
    fn default() -> Self {
        Self::new()
    }
}

/// Resolve all undefined symbols, allowing dylib symbols to remain unresolved
/// in the object graph (they will be resolved via stubs at runtime).
impl SymbolResolver {
    /// Resolve symbols with dylib support. Symbols in the dylib config
    /// are assigned addresses in the stub region rather than requiring
    /// a definition in the object files.
    pub fn resolve_with_dylibs(
        &self,
        dylib_config: &DylibConfig,
        stub_base_addr: u64,
    ) -> Result<(HashMap<String, u64>, Vec<String>), LinkerError> {
        let mut result: HashMap<String, u64> = HashMap::new();
        let mut dylib_symbols: Vec<String> = Vec::new();

        // Copy all defined symbols.
        for (name, sym) in &self.defined {
            result.insert(name.clone(), sym.address);
        }

        // Process undefined symbols.
        let mut stub_offset = 0u64;
        for (_obj_idx, _sym_idx, name) in &self.undefined {
            if result.contains_key(name) {
                continue;
            }
            if dylib_config.is_dylib_symbol(name) {
                // Assign a stub address for this dylib symbol.
                let stub_addr = stub_base_addr + stub_offset;
                result.insert(name.clone(), stub_addr);
                if !dylib_symbols.contains(name) {
                    dylib_symbols.push(name.clone());
                    stub_offset += STUB_SIZE as u64;
                }
            } else if self.weak_refs.contains(name) {
                // Weak references resolve to 0 if not in any dylib.
                result.insert(name.clone(), 0);
            } else {
                return Err(LinkerError::UndefinedSymbol(name.clone()));
            }
        }

        Ok((result, dylib_symbols))
    }
}

/// Link multiple parsed object files into an executable with dylib support.
///
/// This is the dylib-aware version of `link()`. It handles:
/// - Multi-file linking (any number of .o files)
/// - External dylib symbol resolution via stubs
/// - LC_LOAD_DYLIB emission for required dylibs
/// - GOT entries for indirect symbol access
///
/// Returns the raw bytes of a Mach-O MH_EXECUTE file.
pub fn link_with_dylibs(
    objects: &[ParsedObject],
    dylib_config: &DylibConfig,
) -> Result<Vec<u8>, LinkerError> {
    // 1. Do a name-only dylib resolution prepass to compute the final load
    // command size. The mapped __TEXT code base depends on that size.
    let prepass_layout = lay_out_sections(objects, DEFAULT_BASE_ADDR);
    let mut prepass_resolver = SymbolResolver::new();
    for (obj_idx, obj) in objects.iter().enumerate() {
        prepass_resolver.add_object(obj_idx, obj, &prepass_layout.section_addrs[obj_idx])?;
    }
    let (_prepass_symbol_addrs, prepass_dylib_symbols) =
        prepass_resolver.resolve_with_dylibs(dylib_config, DEFAULT_BASE_ADDR)?;
    let prepass_has_stubs = !prepass_dylib_symbols.is_empty();
    let prepass_needed_dylib_indices = dylib_config.needed_dylibs(&prepass_dylib_symbols);
    let prepass_needed_dylibs: Vec<&DylibEntry> = prepass_needed_dylib_indices
        .iter()
        .map(|&i| &dylib_config.dylibs[i])
        .collect();
    let text_file_offset = dylib_executable_text_file_offset(
        has_file_backed_data_sections(objects) || prepass_has_stubs,
        prepass_has_stubs,
        &prepass_needed_dylibs,
    );

    // 2. Lay out sections at their mapped __TEXT addresses.
    let layout = lay_out_sections(objects, DEFAULT_BASE_ADDR + text_file_offset);

    // 3. Resolve symbols with final mapped addresses.
    let mut resolver = SymbolResolver::new();
    for (obj_idx, obj) in objects.iter().enumerate() {
        resolver.add_object(obj_idx, obj, &layout.section_addrs[obj_idx])?;
    }

    // Compute text data size to figure out where stubs go.
    let mut text_size_estimate: u64 = 0;
    for obj in objects {
        for sec in &obj.sections {
            if sec.segment == "__TEXT" {
                let alignment = 1u64 << sec.align;
                let misalign = text_size_estimate % alignment;
                if misalign != 0 {
                    text_size_estimate += alignment - misalign;
                }
                text_size_estimate += sec.data.len() as u64;
            }
        }
    }

    // Stubs go at the end of the __TEXT segment content, 4-byte aligned.
    let stubs_offset_in_text = align_to(text_size_estimate, 4);
    let stub_base_addr = DEFAULT_BASE_ADDR + text_file_offset + stubs_offset_in_text;

    // Resolve with dylib support.
    let (symbol_addrs, dylib_symbols) =
        resolver.resolve_with_dylibs(dylib_config, stub_base_addr)?;
    debug_assert_eq!(prepass_dylib_symbols, dylib_symbols);

    let has_dylib_symbols = !dylib_symbols.is_empty();

    // 4. Build concatenated section data and apply relocations.
    let mut text_data = Vec::new();
    let mut data_data = Vec::new();

    for (obj_idx, obj) in objects.iter().enumerate() {
        let local_symbol_addrs = resolver.object_symbol_addrs(obj_idx);
        for (sec_idx, sec) in obj.sections.iter().enumerate() {
            let sec_addr = layout.section_addrs[obj_idx][sec_idx];
            let mut sec_data = sec.data.clone();

            if !sec.relocations.is_empty() {
                RelocationApplicator::apply_with_local_symbols(
                    &mut sec_data,
                    sec_addr,
                    &sec.relocations,
                    &obj.symbols,
                    &symbol_addrs,
                    &local_symbol_addrs,
                    &layout.section_addrs[obj_idx],
                )?;
            }

            if sec.segment == "__TEXT" {
                let alignment = 1usize << sec.align;
                let misalign = text_data.len() % alignment;
                if misalign != 0 {
                    text_data.resize(text_data.len() + alignment - misalign, 0);
                }
                text_data.extend_from_slice(&sec_data);
            } else {
                let alignment = 1usize << sec.align;
                let misalign = data_data.len() % alignment;
                if misalign != 0 {
                    data_data.resize(data_data.len() + alignment - misalign, 0);
                }
                data_data.extend_from_slice(&sec_data);
            }
        }
    }

    // 5. Generate stub code for dylib symbols.
    // Each stub is: ADRP Xip0, _got_slot@PAGE; LDR Xip0, [Xip0, _got_slot@PAGEOFF]; BR Xip0
    // We use placeholder stubs that the dynamic linker patches via the GOT.
    let stubs_data = generate_stubs(&dylib_symbols, stub_base_addr, &layout, &text_data);

    // Pad text_data to stub alignment, then append stubs.
    let stubs_padding = stubs_offset_in_text as usize - text_data.len();
    text_data.resize(text_data.len() + stubs_padding, 0);
    text_data.extend_from_slice(&stubs_data);

    // 6. Generate GOT entries (8 bytes each, in __DATA segment).
    // Each GOT entry will hold the runtime address of a dylib symbol.
    let got_data: Vec<u8> = vec![0u8; dylib_symbols.len() * 8];

    // Append GOT to data section.
    if has_dylib_symbols {
        let alignment = 8usize;
        let misalign = data_data.len() % alignment;
        if misalign != 0 {
            data_data.resize(data_data.len() + alignment - misalign, 0);
        }
        data_data.extend_from_slice(&got_data);
    }

    // 7. Find _main entry point.
    let entry_addr = symbol_addrs.get("_main").ok_or(LinkerError::NoEntryPoint)?;
    let entry_offset = entry_addr - DEFAULT_BASE_ADDR;

    // 8. Emit executable with dylib support.
    let text_size_aligned = align_to(text_data.len() as u64, PAGE_SIZE);
    let data_vmaddr = DEFAULT_BASE_ADDR + text_file_offset + text_size_aligned;

    // Determine which dylibs are needed.
    let needed_dylib_indices = dylib_config.needed_dylibs(&dylib_symbols);
    let needed_dylibs: Vec<&DylibEntry> = needed_dylib_indices
        .iter()
        .map(|&i| &dylib_config.dylibs[i])
        .collect();

    Ok(emit_executable_with_dylibs(
        &text_data,
        &data_data,
        DEFAULT_BASE_ADDR,
        data_vmaddr,
        entry_offset,
        &needed_dylibs,
        &dylib_symbols,
        stubs_offset_in_text,
    ))
}

/// Generate stub instructions for dylib symbols.
///
/// Each stub is a sequence of AArch64 instructions that loads the target
/// address from the GOT and branches to it:
/// ```text
///   ADRP  X16, _got_entry@PAGE
///   LDR   X16, [X16, _got_entry@PAGEOFF]
///   BR    X16
/// ```
fn generate_stubs(
    _dylib_symbols: &[String],
    _stub_base_addr: u64,
    _layout: &LayoutResult,
    _text_data: &[u8],
) -> Vec<u8> {
    let num_stubs = _dylib_symbols.len();
    let mut stubs = Vec::with_capacity(num_stubs * STUB_SIZE as usize);

    for _i in 0..num_stubs {
        // Generate: ADRP X16, #0; LDR X16, [X16]; BR X16
        // These are placeholder encodings. The GOT address will be patched
        // by the dynamic linker at load time.
        let adrp_x16 = 0x9000_0010u32; // ADRP X16, #0
        let ldr_x16 = 0xF940_0210u32; // LDR X16, [X16, #0]
        let br_x16 = 0xD61F_0200u32; // BR X16

        stubs.extend_from_slice(&adrp_x16.to_le_bytes());
        stubs.extend_from_slice(&ldr_x16.to_le_bytes());
        stubs.extend_from_slice(&br_x16.to_le_bytes());
    }

    stubs
}

/// Emit a Mach-O executable with LC_LOAD_DYLIB commands.
#[allow(clippy::too_many_arguments)]
fn emit_executable_with_dylibs(
    text_data: &[u8],
    data_data: &[u8],
    text_vmaddr: u64,
    data_vmaddr: u64,
    entry_offset: u64,
    needed_dylibs: &[&DylibEntry],
    dylib_symbols: &[String],
    stubs_offset: u64,
) -> Vec<u8> {
    let text_size = text_data.len() as u64;
    let mut data_bytes = data_data.to_vec();
    let data_size = data_bytes.len() as u64;
    let text_size_aligned = align_to(text_size, PAGE_SIZE);
    let data_size_aligned = if data_size > 0 {
        align_to(data_size, PAGE_SIZE)
    } else {
        0
    };

    let has_data = !data_data.is_empty();
    let has_stubs = !dylib_symbols.is_empty();

    let num_dylib_cmds = needed_dylibs.len() as u32;
    let segment_count = if has_data { 4 } else { 3 };
    // __PAGEZERO + __TEXT + [__DATA] + __LINKEDIT + LC_BUILD_VERSION +
    // LC_UUID + LC_MAIN + LC_DYLD_CHAINED_FIXUPS + LC_DYLD_EXPORTS_TRIE +
    // LC_CODE_SIGNATURE + LC_SYMTAB + LC_DYSYMTAB + LC_LOAD_DYLINKER +
    // N * LC_LOAD_DYLIB.
    let base_cmds: u32 = if has_data { 13 } else { 12 };
    let ncmds = base_cmds + num_dylib_cmds;

    let got_size = (dylib_symbols.len() as u64) * 8;
    let got_offset_in_data = has_stubs.then_some(data_size - got_size);
    let import_ordinals: Vec<u32> = dylib_symbols
        .iter()
        .map(|symbol| dylib_ordinal_for_symbol(needed_dylibs, symbol))
        .collect();
    let got_page_starts = got_offset_in_data
        .map(|offset| encode_got_chained_binds(&mut data_bytes, offset, dylib_symbols.len()));
    let fixup_segment = got_page_starts.map(|page_starts| ChainedFixupSegmentInfo {
        segment_index: 2,
        segment_offset: data_vmaddr - text_vmaddr,
        page_starts,
    });

    // Compute load command sizes.
    // __TEXT segment: __text section + optional __stubs section
    let text_nsects: u32 = if has_stubs { 2 } else { 1 };
    let data_nsects: u32 = if has_stubs { 2 } else { 1 };

    // Compute each LC_LOAD_DYLIB size (must be 8-byte aligned).
    let dylib_cmd_sizes: Vec<u32> = needed_dylibs
        .iter()
        .map(|dylib| dylib_command_size(dylib))
        .collect();
    let total_lc_size =
        executable_load_command_size(has_data, text_nsects, data_nsects, &dylib_cmd_sizes);

    let text_file_offset = executable_text_file_offset_from_lc_size(total_lc_size);
    let text_segment_filesize = text_file_offset + text_size_aligned;
    let text_segment_vmsize = align_to(text_segment_filesize, PAGE_SIZE);
    let text_section_vmaddr = text_vmaddr + text_file_offset;
    let data_file_offset = text_segment_filesize;
    let linkedit_file_offset = if has_data {
        data_file_offset + data_size_aligned
    } else {
        text_segment_filesize
    };
    let linkedit_vmaddr = if has_data {
        data_vmaddr + data_size_aligned
    } else {
        text_vmaddr + text_segment_vmsize
    };
    let linkedit_payload = build_linkedit_payload(
        linkedit_file_offset,
        segment_count,
        fixup_segment.as_ref(),
        dylib_symbols,
        &import_ordinals,
    );
    let linkedit_filesize =
        linkedit_payload.data.len() as u64 + linkedit_payload.code_signature_size as u64;
    let linkedit_vmsize = align_to(linkedit_filesize, PAGE_SIZE);

    let total_file_size = linkedit_file_offset + linkedit_filesize;

    let mut buf = Vec::with_capacity(total_file_size as usize);

    // --- Header ---
    buf.extend_from_slice(&MH_MAGIC_64.to_le_bytes());
    buf.extend_from_slice(&CPU_TYPE_ARM64.to_le_bytes());
    buf.extend_from_slice(&CPU_SUBTYPE_ARM64_ALL.to_le_bytes());
    buf.extend_from_slice(&MH_EXECUTE.to_le_bytes());
    buf.extend_from_slice(&ncmds.to_le_bytes());
    buf.extend_from_slice(&total_lc_size.to_le_bytes());
    buf.extend_from_slice(&MH_EXECUTE_FLAGS.to_le_bytes());
    buf.extend_from_slice(&0u32.to_le_bytes()); // reserved

    // --- __PAGEZERO segment ---
    ExecutableEmitter::write_segment(
        &mut buf,
        b"__PAGEZERO",
        0,
        DEFAULT_BASE_ADDR,
        0,
        0,
        0,
        0,
        0,
        0,
    );

    // --- __TEXT segment ---
    ExecutableEmitter::write_segment(
        &mut buf,
        b"__TEXT",
        text_vmaddr,
        text_segment_vmsize,
        0,
        text_segment_filesize,
        VM_PROT_READ | VM_PROT_EXECUTE,
        VM_PROT_READ | VM_PROT_EXECUTE,
        text_nsects,
        0,
    );

    // __text section header
    let text_section_size = if has_stubs { stubs_offset } else { text_size };
    ExecutableEmitter::write_section_header(
        &mut buf,
        b"__text",
        b"__TEXT",
        text_section_vmaddr,
        text_section_size,
        text_file_offset as u32,
        2,
        0,
        0,
        S_REGULAR | S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS,
    );

    // __stubs section header (if dylib symbols present)
    if has_stubs {
        let stubs_vmaddr = text_section_vmaddr + stubs_offset;
        let stubs_size = (dylib_symbols.len() as u64) * (STUB_SIZE as u64);
        let stubs_file_offset = text_file_offset + stubs_offset;

        ExecutableEmitter::write_section_header(
            &mut buf,
            b"__stubs",
            b"__TEXT",
            stubs_vmaddr,
            stubs_size,
            stubs_file_offset as u32,
            2, // 4-byte aligned
            0,
            0,
            S_SYMBOL_STUBS | S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS,
        );
    }

    // --- __DATA segment (if needed) ---
    if has_data {
        let data_seg_vmsize = data_size_aligned;
        let data_nsects: u32 = if has_stubs { 2 } else { 1 };
        ExecutableEmitter::write_segment(
            &mut buf,
            b"__DATA",
            data_vmaddr,
            data_seg_vmsize,
            data_file_offset,
            data_size_aligned,
            VM_PROT_READ | VM_PROT_WRITE,
            VM_PROT_READ | VM_PROT_WRITE,
            data_nsects,
            0,
        );

        // __data section header
        let user_data_size = if has_stubs {
            data_size - (dylib_symbols.len() as u64 * 8)
        } else {
            data_size
        };
        ExecutableEmitter::write_section_header(
            &mut buf,
            b"__data",
            b"__DATA",
            data_vmaddr,
            user_data_size,
            data_file_offset as u32,
            3,
            0,
            0,
            S_REGULAR,
        );

        // __got section header (if dylib symbols present)
        if has_stubs {
            let got_size = (dylib_symbols.len() as u64) * 8;
            let got_offset_in_data = data_size - got_size;
            let got_vmaddr = data_vmaddr + got_offset_in_data;
            let got_file_offset = data_file_offset + got_offset_in_data;

            ExecutableEmitter::write_section_header(
                &mut buf,
                b"__got",
                b"__DATA",
                got_vmaddr,
                got_size,
                got_file_offset as u32,
                3, // 8-byte aligned
                0,
                0,
                S_NON_LAZY_SYMBOL_POINTERS,
            );
        }
    }

    // --- __LINKEDIT segment ---
    ExecutableEmitter::write_segment(
        &mut buf,
        b"__LINKEDIT",
        linkedit_vmaddr,
        linkedit_vmsize,
        linkedit_file_offset,
        linkedit_filesize,
        VM_PROT_READ,
        VM_PROT_READ,
        0,
        0,
    );

    // --- LC_BUILD_VERSION ---
    write_lc_build_version(&mut buf);

    // --- LC_UUID ---
    let uuid = deterministic_executable_uuid(
        text_data,
        &data_bytes,
        text_vmaddr,
        data_vmaddr,
        entry_offset,
        stubs_offset,
        needed_dylibs,
        dylib_symbols,
    );
    write_lc_uuid(&mut buf, uuid);

    // --- LC_MAIN ---
    buf.extend_from_slice(&LC_MAIN.to_le_bytes());
    buf.extend_from_slice(&LC_MAIN_SIZE.to_le_bytes());
    buf.extend_from_slice(&entry_offset.to_le_bytes());
    buf.extend_from_slice(&0u64.to_le_bytes()); // stacksize

    // --- LC_DYLD_CHAINED_FIXUPS / LC_DYLD_EXPORTS_TRIE ---
    write_lc_linkedit_data(
        &mut buf,
        LC_DYLD_CHAINED_FIXUPS,
        linkedit_payload.fixups_offset,
        linkedit_payload.fixups_size,
    );
    write_lc_linkedit_data(
        &mut buf,
        LC_DYLD_EXPORTS_TRIE,
        linkedit_payload.exports_offset,
        linkedit_payload.exports_size,
    );
    write_lc_linkedit_data(
        &mut buf,
        LC_CODE_SIGNATURE,
        linkedit_payload.code_signature_offset,
        linkedit_payload.code_signature_size,
    );

    // --- LC_SYMTAB (empty) ---
    buf.extend_from_slice(&LC_SYMTAB.to_le_bytes());
    buf.extend_from_slice(&SYMTAB_COMMAND_SIZE.to_le_bytes());
    buf.extend_from_slice(&0u32.to_le_bytes()); // symoff
    buf.extend_from_slice(&0u32.to_le_bytes()); // nsyms
    buf.extend_from_slice(&0u32.to_le_bytes()); // stroff
    buf.extend_from_slice(&0u32.to_le_bytes()); // strsize

    // --- LC_DYSYMTAB (empty, matching the empty LC_SYMTAB) ---
    write_empty_lc_dysymtab(&mut buf);

    // --- LC_LOAD_DYLINKER (tells macOS kernel to use /usr/lib/dyld) ---
    write_lc_load_dylinker(&mut buf);

    // --- LC_LOAD_DYLIB commands ---
    for (idx, dylib) in needed_dylibs.iter().enumerate() {
        let cmd_size = dylib_cmd_sizes[idx];

        buf.extend_from_slice(&LC_LOAD_DYLIB.to_le_bytes()); // cmd
        buf.extend_from_slice(&cmd_size.to_le_bytes()); // cmdsize
        // name offset: starts after the fixed dylib_command fields.
        buf.extend_from_slice(&LC_LOAD_DYLIB_HEADER_SIZE.to_le_bytes()); // name.offset
        buf.extend_from_slice(&2u32.to_le_bytes()); // timestamp (conventional: 2)
        // current_version: encode as 1.0.0 = 0x00010000
        buf.extend_from_slice(&0x0001_0000u32.to_le_bytes());
        // compatibility_version: 1.0.0
        buf.extend_from_slice(&0x0001_0000u32.to_le_bytes());

        // Name string (NUL-terminated, padded to alignment).
        let name_bytes = dylib.install_name.as_bytes();
        buf.extend_from_slice(name_bytes);
        buf.push(0); // NUL terminator

        // Pad to cmd_size.
        let written = LC_LOAD_DYLIB_HEADER_SIZE as usize + name_bytes.len() + 1;
        let padding = cmd_size as usize - written;
        buf.extend(std::iter::repeat_n(0, padding));
    }

    // --- Pad to text_file_offset ---
    while (buf.len() as u64) < text_file_offset {
        buf.push(0);
    }

    // --- Write text data ---
    buf.extend_from_slice(text_data);
    while (buf.len() as u64) < text_file_offset + text_size_aligned {
        buf.push(0);
    }

    // --- Write data ---
    if has_data {
        buf.extend_from_slice(&data_bytes);
        while (buf.len() as u64) < linkedit_file_offset {
            buf.push(0);
        }
    }

    // --- Write __LINKEDIT payloads ---
    while (buf.len() as u64) < linkedit_file_offset {
        buf.push(0);
    }
    buf.extend_from_slice(&linkedit_payload.data);
    debug_assert_eq!(buf.len() as u64, linkedit_payload.code_signature_offset);
    let code_signature = build_ad_hoc_code_signature(&buf, 0, text_segment_filesize);
    debug_assert_eq!(
        code_signature.len() as u32,
        linkedit_payload.code_signature_size
    );
    buf.extend_from_slice(&code_signature);
    while (buf.len() as u64) < total_file_size {
        buf.push(0);
    }

    buf
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::super::writer::MachOWriter;
    use super::*;

    // Helper to read a u32 from bytes.
    fn rd_u32(bytes: &[u8], off: usize) -> u32 {
        u32::from_le_bytes([bytes[off], bytes[off + 1], bytes[off + 2], bytes[off + 3]])
    }

    fn rd_u64(bytes: &[u8], off: usize) -> u64 {
        u64::from_le_bytes([
            bytes[off],
            bytes[off + 1],
            bytes[off + 2],
            bytes[off + 3],
            bytes[off + 4],
            bytes[off + 5],
            bytes[off + 6],
            bytes[off + 7],
        ])
    }

    fn rd_be_u32(bytes: &[u8], off: usize) -> u32 {
        u32::from_be_bytes([bytes[off], bytes[off + 1], bytes[off + 2], bytes[off + 3]])
    }

    fn rd_be_u64(bytes: &[u8], off: usize) -> u64 {
        u64::from_be_bytes([
            bytes[off],
            bytes[off + 1],
            bytes[off + 2],
            bytes[off + 3],
            bytes[off + 4],
            bytes[off + 5],
            bytes[off + 6],
            bytes[off + 7],
        ])
    }

    #[derive(Debug)]
    struct LoadCommand {
        cmd: u32,
        cmdsize: u32,
        offset: usize,
    }

    fn walk_load_commands(exe: &[u8]) -> Vec<LoadCommand> {
        assert_eq!(rd_u32(exe, 0), MH_MAGIC_64);
        let ncmds = rd_u32(exe, 16);
        let sizeofcmds = rd_u32(exe, 20) as usize;
        let lc_start = MACH_HEADER_64_SIZE as usize;
        let lc_end = lc_start + sizeofcmds;
        assert!(lc_end <= exe.len(), "load command area exceeds file size");

        let mut commands = Vec::new();
        let mut offset = lc_start;
        for _ in 0..ncmds {
            assert!(offset + 8 <= lc_end, "truncated load command header");
            let cmd = rd_u32(exe, offset);
            let cmdsize = rd_u32(exe, offset + 4) as usize;
            assert!(cmdsize >= 8, "invalid load command size {cmdsize}");
            assert!(
                offset + cmdsize <= lc_end,
                "load command extends past sizeofcmds"
            );
            commands.push(LoadCommand {
                cmd,
                cmdsize: cmdsize as u32,
                offset,
            });
            offset += cmdsize;
        }

        assert_eq!(commands.len(), ncmds as usize, "ncmds mismatch");
        assert_eq!(offset, lc_end, "sizeofcmds walk mismatch");
        let walked_size: u32 = commands.iter().map(|cmd| cmd.cmdsize).sum();
        assert_eq!(walked_size, sizeofcmds as u32, "sizeofcmds sum mismatch");
        commands
    }

    fn count_load_command(commands: &[LoadCommand], cmd: u32) -> usize {
        commands.iter().filter(|lc| lc.cmd == cmd).count()
    }

    fn single_load_command(commands: &[LoadCommand], cmd: u32) -> &LoadCommand {
        let mut matches = commands.iter().filter(|lc| lc.cmd == cmd);
        let command = matches.next().expect("load command not found");
        assert!(
            matches.next().is_none(),
            "expected exactly one load command 0x{cmd:X}"
        );
        command
    }

    #[derive(Debug)]
    struct SegmentCommand {
        name: String,
        vmaddr: u64,
        vmsize: u64,
        fileoff: u64,
        filesize: u64,
    }

    #[derive(Debug)]
    struct SectionCommand {
        name: String,
        segment: String,
        addr: u64,
        size: u64,
        offset: u32,
    }

    #[derive(Debug)]
    struct LinkeditDataCommand {
        dataoff: u64,
        datasize: u32,
    }

    fn segment_commands(exe: &[u8], commands: &[LoadCommand]) -> Vec<SegmentCommand> {
        commands
            .iter()
            .filter(|cmd| cmd.cmd == LC_SEGMENT_64)
            .map(|cmd| SegmentCommand {
                name: read_name16(exe, cmd.offset + 8),
                vmaddr: rd_u64(exe, cmd.offset + 24),
                vmsize: rd_u64(exe, cmd.offset + 32),
                fileoff: rd_u64(exe, cmd.offset + 40),
                filesize: rd_u64(exe, cmd.offset + 48),
            })
            .collect()
    }

    fn single_segment<'a>(segments: &'a [SegmentCommand], name: &str) -> &'a SegmentCommand {
        let mut matches = segments.iter().filter(|seg| seg.name == name);
        let segment = matches.next().expect("segment not found");
        assert!(
            matches.next().is_none(),
            "expected exactly one segment {name}"
        );
        segment
    }

    fn section_commands(exe: &[u8], commands: &[LoadCommand]) -> Vec<SectionCommand> {
        let mut sections = Vec::new();
        for cmd in commands.iter().filter(|cmd| cmd.cmd == LC_SEGMENT_64) {
            let nsects = rd_u32(exe, cmd.offset + 64) as usize;
            let sections_start = cmd.offset + SEGMENT_COMMAND_64_SIZE as usize;
            assert!(
                sections_start + nsects * SECTION_64_SIZE as usize
                    <= cmd.offset + cmd.cmdsize as usize,
                "section headers exceed segment command"
            );

            for idx in 0..nsects {
                let off = sections_start + idx * SECTION_64_SIZE as usize;
                sections.push(SectionCommand {
                    name: read_name16(exe, off),
                    segment: read_name16(exe, off + 16),
                    addr: rd_u64(exe, off + 32),
                    size: rd_u64(exe, off + 40),
                    offset: rd_u32(exe, off + 48),
                });
            }
        }
        sections
    }

    fn single_section<'a>(
        sections: &'a [SectionCommand],
        segment: &str,
        name: &str,
    ) -> &'a SectionCommand {
        let mut matches = sections
            .iter()
            .filter(|section| section.segment == segment && section.name == name);
        let section = matches.next().expect("section not found");
        assert!(
            matches.next().is_none(),
            "expected exactly one section {segment},{name}"
        );
        section
    }

    fn entryoff(exe: &[u8], commands: &[LoadCommand]) -> u64 {
        let command = single_load_command(commands, LC_MAIN);
        assert_eq!(command.cmdsize, LC_MAIN_SIZE);
        rd_u64(exe, command.offset + 8)
    }

    fn assert_mapped_text_layout(exe: &[u8], expected_entryoff: u64) {
        let commands = walk_load_commands(exe);
        let segments = segment_commands(exe, &commands);
        let sections = section_commands(exe, &commands);
        let text = single_segment(&segments, "__TEXT");
        let text_section = single_section(&sections, "__TEXT", "__text");
        let header_and_lc = MACH_HEADER_64_SIZE as u64 + rd_u32(exe, 20) as u64;

        assert_eq!(text.fileoff, 0, "__TEXT must map the Mach-O header");
        assert!(
            text.filesize >= header_and_lc,
            "__TEXT must cover the full load-command range"
        );
        assert_eq!(text.vmsize, align_to(text.filesize, PAGE_SIZE));
        assert!(
            text_section.offset as u64 >= header_and_lc,
            "__text must start after load commands"
        );
        assert_eq!(
            text_section.addr,
            text.vmaddr + text_section.offset as u64,
            "__text addr must agree with mapped __TEXT file offset"
        );
        assert_eq!(entryoff(exe, &commands), expected_entryoff);
        assert!(
            expected_entryoff >= text_section.offset as u64
                && expected_entryoff < text_section.offset as u64 + text_section.size,
            "LC_MAIN entryoff must point inside __TEXT,__text"
        );
    }

    fn linkedit_data_command(exe: &[u8], command: &LoadCommand) -> LinkeditDataCommand {
        assert_eq!(command.cmdsize, LINKEDIT_DATA_COMMAND_SIZE);
        LinkeditDataCommand {
            dataoff: rd_u32(exe, command.offset + 8) as u64,
            datasize: rd_u32(exe, command.offset + 12),
        }
    }

    fn assert_linkedit_range(exe: &[u8], linkedit: &SegmentCommand, command: &LinkeditDataCommand) {
        let start = command.dataoff;
        let end = start + command.datasize as u64;
        assert!(
            start >= linkedit.fileoff,
            "payload starts before __LINKEDIT"
        );
        assert!(
            end <= linkedit.fileoff + linkedit.filesize,
            "payload extends beyond __LINKEDIT"
        );
        assert!(end <= exe.len() as u64, "payload extends beyond file");
    }

    fn assert_exports_trie_payload(exe: &[u8], command: &LinkeditDataCommand) {
        assert_eq!(command.datasize, EMPTY_EXPORTS_TRIE.len() as u32);
        let start = command.dataoff as usize;
        assert_eq!(
            &exe[start..start + EMPTY_EXPORTS_TRIE.len()],
            EMPTY_EXPORTS_TRIE
        );
    }

    fn assert_chained_fixups_payload(
        exe: &[u8],
        command: &LinkeditDataCommand,
        expected_segment_count: u32,
        expected_imports: &[&str],
        data_segment: Option<&SegmentCommand>,
        text_segment: &SegmentCommand,
    ) {
        assert_eq!(
            command.dataoff % 8,
            0,
            "fixups payload must be 8-byte aligned"
        );
        let start = command.dataoff as usize;
        let size = command.datasize as usize;
        assert!(size >= 40, "fixups payload is too small to parse");

        assert_eq!(rd_u32(exe, start), 0, "fixups_version");
        let starts_offset = rd_u32(exe, start + 4) as usize;
        let imports_offset = rd_u32(exe, start + 8) as usize;
        let symbols_offset = rd_u32(exe, start + 12) as usize;
        let imports_count = rd_u32(exe, start + 16);
        assert_eq!(imports_count as usize, expected_imports.len());
        assert_eq!(rd_u32(exe, start + 20), DYLD_CHAINED_IMPORT);
        assert_eq!(rd_u32(exe, start + 24), DYLD_CHAINED_SYMBOLS_UNCOMPRESSED);
        assert!(starts_offset >= DYLD_CHAINED_FIXUPS_HEADER_SIZE as usize);
        assert_eq!(starts_offset % 8, 0);
        assert!(starts_offset + 4 <= size);

        let starts = start + starts_offset;
        let segment_count = rd_u32(exe, starts);
        assert_eq!(segment_count, expected_segment_count);
        let starts_table_size = align_to(4 + segment_count as u64 * 4, 8) as usize;
        assert!(starts_offset + starts_table_size <= size);

        if expected_imports.is_empty() {
            for idx in 0..segment_count as usize {
                assert_eq!(
                    rd_u32(exe, starts + 4 + idx * 4),
                    0,
                    "segment without fixups should have no starts entry"
                );
            }
        } else {
            let data_seg_info_offset = rd_u32(exe, starts + 4 + 2 * 4) as usize;
            assert_ne!(data_seg_info_offset, 0, "__DATA should have chained starts");
            let data_seg = data_segment.expect("__DATA segment expected for imports");
            let seg_start = starts + data_seg_info_offset;
            let seg_size = rd_u32(exe, seg_start) as usize;
            assert!(seg_size >= 24, "segment starts info too small");
            assert!(data_seg_info_offset + seg_size <= size - starts_offset);
            assert_eq!(rd_u32(exe, seg_start + 4) as u16, PAGE_SIZE as u16);
            assert_eq!(rd_u32(exe, seg_start + 6) as u16, DYLD_CHAINED_PTR_64);
            assert_eq!(
                rd_u64(exe, seg_start + 8),
                data_seg.vmaddr - text_segment.vmaddr
            );
            assert_eq!(rd_u32(exe, seg_start + 16), 0);
            let page_count = rd_u32(exe, seg_start + 20) as u16;
            assert!(page_count > 0);
            assert_ne!(
                rd_u32(exe, seg_start + 22) as u16,
                DYLD_CHAINED_PTR_START_NONE
            );
        }

        assert!(imports_offset <= symbols_offset);
        assert!(symbols_offset <= size);
        assert!(imports_offset + expected_imports.len() * 4 <= size);
        let mut expected_name_offset = 0u32;
        for (idx, expected) in expected_imports.iter().enumerate() {
            let raw = rd_u32(exe, start + imports_offset + idx * 4);
            let lib_ordinal = raw & 0xFF;
            let weak_import = (raw >> 8) & 1;
            let name_offset = raw >> 9;
            assert_eq!(lib_ordinal, 1);
            assert_eq!(weak_import, 0);
            assert_eq!(name_offset, expected_name_offset);
            assert_eq!(
                read_cstring(exe, start + symbols_offset + name_offset as usize),
                *expected
            );
            expected_name_offset += expected.len() as u32 + 1;
        }
    }

    fn assert_code_signature_payload(
        exe: &[u8],
        command: &LinkeditDataCommand,
        text_segment: &SegmentCommand,
    ) {
        assert_eq!(
            command.dataoff % CODE_SIGNATURE_ALIGNMENT,
            0,
            "code signature must be 16-byte aligned"
        );
        assert_eq!(
            command.dataoff + command.datasize as u64,
            exe.len() as u64,
            "code signature must be the final linkedit payload"
        );

        let start = command.dataoff as usize;
        let size = command.datasize as usize;
        assert!(size >= CS_FIXED_HEADERS_SIZE);
        assert_eq!(rd_be_u32(exe, start), CSMAGIC_EMBEDDED_SIGNATURE);
        assert_eq!(rd_be_u32(exe, start + 4), command.datasize);
        assert_eq!(rd_be_u32(exe, start + 8), 1);
        assert_eq!(rd_be_u32(exe, start + 12), CSSLOT_CODEDIRECTORY);
        assert_eq!(rd_be_u32(exe, start + 16), CS_BLOB_HEADERS_SIZE as u32);

        let code_dir = start + CS_BLOB_HEADERS_SIZE;
        let code_dir_size = size - CS_BLOB_HEADERS_SIZE;
        assert_eq!(rd_be_u32(exe, code_dir), CSMAGIC_CODEDIRECTORY);
        assert_eq!(rd_be_u32(exe, code_dir + 4), code_dir_size as u32);
        assert_eq!(rd_be_u32(exe, code_dir + 8), CS_SUPPORTSEXECSEG);
        assert_eq!(rd_be_u32(exe, code_dir + 12), CS_ADHOC | CS_LINKER_SIGNED);

        let hash_offset = rd_be_u32(exe, code_dir + 16) as usize;
        let ident_offset = rd_be_u32(exe, code_dir + 20) as usize;
        let n_special_slots = rd_be_u32(exe, code_dir + 24);
        let n_code_slots = rd_be_u32(exe, code_dir + 28);
        let code_limit = rd_be_u32(exe, code_dir + 32) as u64;
        assert_eq!(n_special_slots, 0);
        assert_eq!(n_code_slots, code_signature_block_count(command.dataoff));
        assert_eq!(code_limit, command.dataoff);
        assert_eq!(exe[code_dir + 36], CODE_SIGNATURE_HASH_SIZE as u8);
        assert_eq!(exe[code_dir + 37], CS_HASHTYPE_SHA256);
        assert_eq!(exe[code_dir + 38], 0);
        assert_eq!(exe[code_dir + 39], CODE_SIGNATURE_BLOCK_SIZE_SHIFT);
        assert_eq!(rd_be_u32(exe, code_dir + 40), 0);
        assert_eq!(rd_be_u32(exe, code_dir + 44), 0);
        assert_eq!(rd_be_u32(exe, code_dir + 48), 0);
        assert_eq!(rd_be_u32(exe, code_dir + 52), 0);
        assert_eq!(rd_be_u64(exe, code_dir + 56), 0);
        assert_eq!(rd_be_u64(exe, code_dir + 64), text_segment.fileoff);
        assert_eq!(rd_be_u64(exe, code_dir + 72), text_segment.filesize);
        assert_eq!(rd_be_u64(exe, code_dir + 80), CS_EXECSEG_MAIN_BINARY);

        assert_eq!(ident_offset, CS_CODE_DIRECTORY_SIZE);
        assert_eq!(
            read_cstring(exe, code_dir + ident_offset).as_bytes(),
            CODE_SIGNATURE_IDENTIFIER
        );
        assert!(hash_offset > ident_offset);
        assert!(
            hash_offset + n_code_slots as usize * CODE_SIGNATURE_HASH_SIZE <= code_dir_size,
            "code signature hashes exceed CodeDirectory"
        );

        let hashes_start = code_dir + hash_offset;
        for slot in 0..n_code_slots as usize {
            let block_start = slot * CODE_SIGNATURE_BLOCK_SIZE as usize;
            let block_end =
                ((slot as u64 + 1) * CODE_SIGNATURE_BLOCK_SIZE).min(command.dataoff) as usize;
            let expected = sha256_digest(&exe[block_start..block_end]);
            let actual_start = hashes_start + slot * CODE_SIGNATURE_HASH_SIZE;
            assert_eq!(
                &exe[actual_start..actual_start + CODE_SIGNATURE_HASH_SIZE],
                expected.as_slice(),
                "code signature hash slot {slot} mismatch"
            );
        }
    }

    fn assert_dyld_linkedit_payloads(exe: &[u8], expected_imports: &[&str]) {
        let commands = walk_load_commands(exe);
        let segments = segment_commands(exe, &commands);
        let linkedit = single_segment(&segments, "__LINKEDIT");
        let text = single_segment(&segments, "__TEXT");
        let data = segments.iter().find(|seg| seg.name == "__DATA");
        assert_eq!(
            segments.last().map(|seg| seg.name.as_str()),
            Some("__LINKEDIT")
        );
        assert_eq!(linkedit.fileoff + linkedit.filesize, exe.len() as u64);
        assert_eq!(linkedit.vmsize, align_to(linkedit.filesize, PAGE_SIZE));

        let fixups =
            linkedit_data_command(exe, single_load_command(&commands, LC_DYLD_CHAINED_FIXUPS));
        let exports =
            linkedit_data_command(exe, single_load_command(&commands, LC_DYLD_EXPORTS_TRIE));
        let code_signature =
            linkedit_data_command(exe, single_load_command(&commands, LC_CODE_SIGNATURE));
        assert_linkedit_range(exe, linkedit, &fixups);
        assert_linkedit_range(exe, linkedit, &exports);
        assert_linkedit_range(exe, linkedit, &code_signature);
        assert!(
            fixups.dataoff + fixups.datasize as u64 <= exports.dataoff
                || exports.dataoff + exports.datasize as u64 <= fixups.dataoff,
            "fixups and exports payloads must not overlap"
        );
        assert!(
            exports.dataoff + exports.datasize as u64 <= code_signature.dataoff,
            "code signature should follow dyld linkedit payloads"
        );
        assert_chained_fixups_payload(
            exe,
            &fixups,
            segments.len() as u32,
            expected_imports,
            data,
            text,
        );
        assert_exports_trie_payload(exe, &exports);
        assert_code_signature_payload(exe, &code_signature, text);
    }

    fn assert_build_version_command(exe: &[u8], command: &LoadCommand) {
        assert_eq!(command.cmdsize, BUILD_VERSION_COMMAND_SIZE);
        assert_eq!(rd_u32(exe, command.offset + 8), PLATFORM_MACOS);
        assert_eq!(rd_u32(exe, command.offset + 12), MACOS_14_0_0);
        assert_eq!(rd_u32(exe, command.offset + 16), MACOS_14_0_0);
        assert_eq!(rd_u32(exe, command.offset + 20), 0);
    }

    fn assert_empty_dysymtab_command(exe: &[u8], command: &LoadCommand) {
        assert_eq!(command.cmdsize, DYSYMTAB_COMMAND_SIZE);
        for field_off in
            (command.offset + 8..command.offset + DYSYMTAB_COMMAND_SIZE as usize).step_by(4)
        {
            assert_eq!(rd_u32(exe, field_off), 0);
        }
    }

    fn load_command_uuid(exe: &[u8], command: &LoadCommand) -> [u8; 16] {
        assert_eq!(command.cmdsize, UUID_COMMAND_SIZE);
        exe[command.offset + 8..command.offset + 24]
            .try_into()
            .unwrap()
    }

    // =======================================================================
    // Parser tests
    // =======================================================================

    #[test]
    fn test_parse_round_trip() {
        // Create a .o with MachOWriter, parse with MachOParser.
        let mut writer = MachOWriter::new();
        let nop = 0xD503201Fu32;
        let code: Vec<u8> = (0..4).flat_map(|_| nop.to_le_bytes()).collect();
        writer.add_text_section(&code);
        writer.add_symbol("_main", 1, 0, true).unwrap();

        let obj_bytes = writer.write().unwrap();
        let parsed = MachOParser::parse(&obj_bytes).expect("parse failed");

        assert_eq!(parsed.cputype, CPU_TYPE_ARM64);
        assert_eq!(parsed.sections.len(), 1);
        assert_eq!(parsed.sections[0].name, "__text");
        assert_eq!(parsed.sections[0].segment, "__TEXT");
        assert_eq!(parsed.sections[0].data.len(), 16);

        // Verify symbol.
        let main_sym = parsed
            .symbols
            .iter()
            .find(|s| s.name == "_main")
            .expect("_main not found");
        assert!(main_sym.is_defined());
        assert!(main_sym.is_external());
    }

    #[test]
    fn test_parse_header_fields() {
        let mut writer = MachOWriter::new();
        writer.add_text_section(&[0xC0, 0x03, 0x5F, 0xD6]); // RET
        let obj_bytes = writer.write().unwrap();

        let parsed = MachOParser::parse(&obj_bytes).unwrap();
        assert_eq!(parsed.cputype, CPU_TYPE_ARM64);
        assert_eq!(parsed.cpusubtype, CPU_SUBTYPE_ARM64_ALL);
        assert_eq!(
            parsed.flags & MH_SUBSECTIONS_VIA_SYMBOLS,
            MH_SUBSECTIONS_VIA_SYMBOLS
        );
    }

    #[test]
    fn test_parse_multiple_sections() {
        let mut writer = MachOWriter::new();
        writer.add_text_section(&[0x1F, 0x20, 0x03, 0xD5]);
        writer.add_data_section(&[1, 2, 3, 4, 5, 6, 7, 8]);
        writer.add_symbol("_main", 1, 0, true).unwrap();
        writer.add_symbol("_data", 2, 0, true).unwrap();

        let obj_bytes = writer.write().unwrap();
        let parsed = MachOParser::parse(&obj_bytes).unwrap();

        assert_eq!(parsed.sections.len(), 2);
        assert_eq!(parsed.sections[0].name, "__text");
        assert_eq!(parsed.sections[1].name, "__data");
        assert_eq!(parsed.sections[1].data, vec![1, 2, 3, 4, 5, 6, 7, 8]);
    }

    #[test]
    fn test_parse_relocations() {
        let mut writer = MachOWriter::new();
        let bl = 0x94000000u32; // BL #0
        let nop = 0xD503201Fu32;
        let mut code = Vec::new();
        code.extend_from_slice(&bl.to_le_bytes());
        for _ in 0..3 {
            code.extend_from_slice(&nop.to_le_bytes());
        }
        writer.add_text_section(&code);
        writer.add_symbol("_caller", 1, 0, true).unwrap();
        writer.add_symbol("_callee", 0, 0, true).unwrap();
        writer
            .add_relocation(0, Relocation::branch26(0, 1))
            .unwrap();

        let obj_bytes = writer.write().unwrap();
        let parsed = MachOParser::parse(&obj_bytes).unwrap();

        assert_eq!(parsed.sections[0].relocations.len(), 1);
        let reloc = &parsed.sections[0].relocations[0];
        assert_eq!(reloc.kind, AArch64RelocKind::Branch26);
        assert_eq!(reloc.offset, 0);
        assert!(reloc.is_extern);
        assert!(reloc.pc_relative);
    }

    #[test]
    fn test_parse_bad_magic() {
        let data = vec![0u8; 64]; // All zeros, magic is 0x00000000.
        let err = MachOParser::parse(&data).unwrap_err();
        assert!(matches!(err, LinkerError::BadMagic(0)));
    }

    #[test]
    fn test_parse_non_arm64_cputype_returns_err() {
        // RANK 7a: a valid Mach-O MH_OBJECT header whose cputype is NOT
        // CPU_TYPE_ARM64 (here CPU_TYPE_X86_64) must be rejected with a typed
        // UnsupportedCpuType, mirroring the bad-magic / not-object fail-closed
        // gates — never misparsed as ARM64.
        let mut data = Vec::with_capacity(32);
        data.extend_from_slice(&MH_MAGIC_64.to_le_bytes()); // magic (valid)
        data.extend_from_slice(&CPU_TYPE_X86_64.to_le_bytes()); // cputype (wrong)
        data.extend_from_slice(&0u32.to_le_bytes()); // cpusubtype
        data.extend_from_slice(&MH_OBJECT.to_le_bytes()); // filetype (valid)
        data.extend_from_slice(&0u32.to_le_bytes()); // ncmds
        data.extend_from_slice(&0u32.to_le_bytes()); // sizeofcmds
        data.extend_from_slice(&0u32.to_le_bytes()); // flags
        data.extend_from_slice(&0u32.to_le_bytes()); // reserved
        debug_assert_eq!(data.len(), 32);

        let err = MachOParser::parse(&data).unwrap_err();
        assert!(
            matches!(err, LinkerError::UnsupportedCpuType(ct) if ct == CPU_TYPE_X86_64),
            "expected UnsupportedCpuType(CPU_TYPE_X86_64), got {err:?}"
        );
    }

    #[test]
    fn test_parse_too_short() {
        let data = vec![0u8; 16]; // Too short for header.
        let err = MachOParser::parse(&data).unwrap_err();
        assert!(matches!(err, LinkerError::TooShort { .. }));
    }

    /// Build a minimal valid MH_OBJECT mach_header_64 (32 bytes) followed by
    /// the supplied raw load-command bytes. `ncmds`/`sizeofcmds` are derived
    /// from the command bytes so the only malformation is the command itself.
    #[cfg(test)]
    fn mk_object_with_one_lc(ncmds: u32, lc: &[u8]) -> Vec<u8> {
        let mut hdr = Vec::with_capacity(32 + lc.len());
        hdr.extend_from_slice(&MH_MAGIC_64.to_le_bytes()); // magic
        hdr.extend_from_slice(&CPU_TYPE_ARM64.to_le_bytes()); // cputype
        hdr.extend_from_slice(&0u32.to_le_bytes()); // cpusubtype
        hdr.extend_from_slice(&MH_OBJECT.to_le_bytes()); // filetype
        hdr.extend_from_slice(&ncmds.to_le_bytes()); // ncmds
        hdr.extend_from_slice(&(lc.len() as u32).to_le_bytes()); // sizeofcmds
        hdr.extend_from_slice(&0u32.to_le_bytes()); // flags
        hdr.extend_from_slice(&0u32.to_le_bytes()); // reserved
        debug_assert_eq!(hdr.len(), 32);
        hdr.extend_from_slice(lc);
        hdr
    }

    #[test]
    fn test_parse_undersized_segment64_returns_err_not_panic() {
        // FINDING #4: an LC_SEGMENT_64 with cmdsize=8 passes the generic
        // `cmdsize >= 8 && offset + cmdsize <= len` check, but reading nsects
        // at offset+64 would index past data.len() and PANIC. Must now return
        // a typed LoadCommandOverflow.
        let mut lc = Vec::new();
        lc.extend_from_slice(&LC_SEGMENT_64.to_le_bytes()); // cmd
        lc.extend_from_slice(&8u32.to_le_bytes()); // cmdsize = 8 (too small)
        let data = mk_object_with_one_lc(1, &lc);
        let err = MachOParser::parse(&data).unwrap_err();
        assert!(
            matches!(err, LinkerError::LoadCommandOverflow { .. }),
            "expected LoadCommandOverflow, got {err:?}"
        );
    }

    #[test]
    fn test_parse_undersized_symtab_returns_err_not_panic() {
        // FINDING #4: an LC_SYMTAB with cmdsize=8 would index offset+8..+24
        // out of bounds. Must return LoadCommandOverflow rather than panic.
        let mut lc = Vec::new();
        lc.extend_from_slice(&LC_SYMTAB.to_le_bytes()); // cmd
        lc.extend_from_slice(&8u32.to_le_bytes()); // cmdsize = 8 (too small)
        let data = mk_object_with_one_lc(1, &lc);
        let err = MachOParser::parse(&data).unwrap_err();
        assert!(
            matches!(err, LinkerError::LoadCommandOverflow { .. }),
            "expected LoadCommandOverflow, got {err:?}"
        );
    }

    #[test]
    fn test_parse_section_data_size_overflow_returns_err_not_panic() {
        // FINDING #4 (section-data arm): a well-formed LC_SEGMENT_64 with nsects=1
        // and a section_64 whose size = u64::MAX and file offset = u32::MAX makes
        // `sec_file_offset + sec_data_size` overflow usize (panic in debug / wrap
        // in release, defeating the `<= len` guard) and the zero-fill else-branch
        // `vec![0u8; sec_data_size]` an ~18 EB allocation bomb. Reachable with a
        // fully well-formed cmdsize. Must now return a typed LoadCommandOverflow.
        let mut seg = vec![0u8; SEGMENT_COMMAND_64_SIZE as usize];
        seg[0..4].copy_from_slice(&LC_SEGMENT_64.to_le_bytes());
        let cmdsize = SEGMENT_COMMAND_64_SIZE + SECTION_64_SIZE; // 72 + 80 = 152
        seg[4..8].copy_from_slice(&cmdsize.to_le_bytes());
        seg[64..68].copy_from_slice(&1u32.to_le_bytes()); // nsects = 1

        let mut sec = vec![0u8; SECTION_64_SIZE as usize];
        sec[40..48].copy_from_slice(&u64::MAX.to_le_bytes()); // section size
        sec[48..52].copy_from_slice(&u32::MAX.to_le_bytes()); // section file offset
        // nreloc (60..64) left 0

        let mut lc = seg;
        lc.extend_from_slice(&sec);
        let data = mk_object_with_one_lc(1, &lc);
        let err = MachOParser::parse(&data).unwrap_err();
        assert!(
            matches!(err, LinkerError::LoadCommandOverflow { .. }),
            "expected LoadCommandOverflow for an oversized section, got {err:?}"
        );
    }

    #[test]
    fn test_parse_wellformed_empty_segment64_and_symtab_ok() {
        // Boundary: a well-formed LC_SEGMENT_64 (cmdsize=72, nsects=0) followed
        // by a well-formed LC_SYMTAB (cmdsize=24, nsyms=0) must still parse
        // cleanly — the safety gate must not reject valid full-size commands.
        let mut seg = vec![0u8; SEGMENT_COMMAND_64_SIZE as usize];
        seg[0..4].copy_from_slice(&LC_SEGMENT_64.to_le_bytes());
        seg[4..8].copy_from_slice(&SEGMENT_COMMAND_64_SIZE.to_le_bytes());
        // nsects at offset+64 left 0.

        let mut sym = vec![0u8; SYMTAB_COMMAND_SIZE as usize];
        sym[0..4].copy_from_slice(&LC_SYMTAB.to_le_bytes());
        sym[4..8].copy_from_slice(&SYMTAB_COMMAND_SIZE.to_le_bytes());
        // symoff/nsyms/stroff/strsize at +8..+24 left 0 (nsyms = 0).

        let mut lc = Vec::new();
        lc.extend_from_slice(&seg);
        lc.extend_from_slice(&sym);
        let data = mk_object_with_one_lc(2, &lc);
        let parsed = MachOParser::parse(&data).expect("well-formed object must parse");
        assert!(parsed.sections.is_empty());
        assert!(parsed.symbols.is_empty());
    }

    // =======================================================================
    // Symbol resolution tests
    // =======================================================================

    #[test]
    fn test_symbol_resolution() {
        // Object 1 defines _callee, Object 2 references it.
        let mut writer1 = MachOWriter::new();
        let ret = 0xD65F03C0u32; // RET
        writer1.add_text_section(&ret.to_le_bytes());
        writer1.add_symbol("_callee", 1, 0, true).unwrap();
        let obj1_bytes = writer1.write().unwrap();
        let obj1 = MachOParser::parse(&obj1_bytes).unwrap();

        let mut writer2 = MachOWriter::new();
        let bl = 0x94000000u32;
        writer2.add_text_section(&bl.to_le_bytes());
        writer2.add_symbol("_main", 1, 0, true).unwrap();
        writer2.add_symbol("_callee", 0, 0, true).unwrap(); // undefined
        writer2
            .add_relocation(0, Relocation::branch26(0, 1))
            .unwrap();
        let obj2_bytes = writer2.write().unwrap();
        let obj2 = MachOParser::parse(&obj2_bytes).unwrap();

        let objects = vec![obj1, obj2];
        let layout = lay_out_sections(&objects, DEFAULT_BASE_ADDR);

        let mut resolver = SymbolResolver::new();
        resolver
            .add_object(0, &objects[0], &layout.section_addrs[0])
            .unwrap();
        resolver
            .add_object(1, &objects[1], &layout.section_addrs[1])
            .unwrap();

        let addrs = resolver.resolve().unwrap();
        assert!(addrs.contains_key("_callee"));
        assert!(addrs.contains_key("_main"));
    }

    #[test]
    fn test_symbol_resolution_undefined_error() {
        let mut writer = MachOWriter::new();
        writer.add_text_section(&[0; 4]);
        writer.add_symbol("_main", 1, 0, true).unwrap();
        writer.add_symbol("_missing", 0, 0, true).unwrap(); // undefined
        let obj_bytes = writer.write().unwrap();
        let obj = MachOParser::parse(&obj_bytes).unwrap();

        let objects = vec![obj];
        let layout = lay_out_sections(&objects, DEFAULT_BASE_ADDR);

        let mut resolver = SymbolResolver::new();
        resolver
            .add_object(0, &objects[0], &layout.section_addrs[0])
            .unwrap();

        let err = resolver.resolve().unwrap_err();
        assert!(matches!(err, LinkerError::UndefinedSymbol(ref s) if s == "_missing"));
    }

    #[test]
    fn test_symbol_resolution_keeps_local_symbols_object_scoped() {
        let mut writer1 = MachOWriter::new();
        writer1.add_text_section(&[0; 8]);
        writer1.add_symbol("Ltmp0", 1, 0, false).unwrap();
        let obj1 = MachOParser::parse(&writer1.write().unwrap()).unwrap();

        let mut writer2 = MachOWriter::new();
        writer2.add_text_section(&[0; 8]);
        writer2.add_symbol("Ltmp0", 1, 4, false).unwrap();
        let obj2 = MachOParser::parse(&writer2.write().unwrap()).unwrap();

        let objects = vec![obj1, obj2];
        let layout = lay_out_sections(&objects, DEFAULT_BASE_ADDR);
        let mut resolver = SymbolResolver::new();
        resolver
            .add_object(0, &objects[0], &layout.section_addrs[0])
            .unwrap();
        resolver
            .add_object(1, &objects[1], &layout.section_addrs[1])
            .unwrap();

        let local1 = objects[0]
            .symbols
            .iter()
            .position(|sym| sym.name == "Ltmp0")
            .expect("object 1 local symbol");
        let local2 = objects[1]
            .symbols
            .iter()
            .position(|sym| sym.name == "Ltmp0")
            .expect("object 2 local symbol");
        let object1_addrs = resolver.object_symbol_addrs(0);
        let object2_addrs = resolver.object_symbol_addrs(1);

        assert_eq!(
            object1_addrs[&local1], layout.section_addrs[0][0],
            "object 1 local symbol should resolve to object 1 text base"
        );
        assert_eq!(
            object2_addrs[&local2],
            layout.section_addrs[1][0] + 4,
            "object 2 local symbol should resolve to object 2 text base plus offset"
        );
        assert_ne!(object1_addrs[&local1], object2_addrs[&local2]);
        assert!(resolver.resolve().unwrap().is_empty());
    }

    // =======================================================================
    // Section layout tests
    // =======================================================================

    #[test]
    fn test_section_layout() {
        let mut writer = MachOWriter::new();
        writer.add_text_section(&[0u8; 32]);
        writer.add_data_section(&[0u8; 16]);
        let obj_bytes = writer.write().unwrap();
        let obj = MachOParser::parse(&obj_bytes).unwrap();

        let objects = vec![obj];
        let layout = lay_out_sections(&objects, DEFAULT_BASE_ADDR);

        // Text section starts at base.
        assert_eq!(layout.section_addrs[0][0], DEFAULT_BASE_ADDR);
        // Data section starts after text, page-aligned.
        let text_aligned = align_to(32, PAGE_SIZE);
        assert_eq!(layout.section_addrs[0][1], DEFAULT_BASE_ADDR + text_aligned);
        assert_eq!(layout.text_vmaddr, DEFAULT_BASE_ADDR);
        assert_eq!(layout.data_vmaddr, DEFAULT_BASE_ADDR + text_aligned);
    }

    // =======================================================================
    // Relocation application tests
    // =======================================================================

    #[test]
    fn test_relocation_branch26() {
        // BL instruction at address 0x100, target at 0x200.
        // displacement = 0x100, imm26 = 0x100 >> 2 = 0x40
        let bl = 0x94000000u32; // BL #0
        let mut data = bl.to_le_bytes().to_vec();

        let pc = 0x1_0000_0000u64;
        let target = 0x1_0000_0100u64;

        let relocs = vec![Relocation::branch26(0, 0)];
        let symbols = vec![ParsedSymbol {
            name: "_callee".into(),
            n_type: N_UNDF | N_EXT,
            section: 0,
            desc: 0,
            value: 0,
        }];
        let mut addrs = HashMap::new();
        addrs.insert("_callee".into(), target);

        RelocationApplicator::apply(&mut data, pc, &relocs, &symbols, &addrs, &[]).unwrap();

        let patched = u32::from_le_bytes([data[0], data[1], data[2], data[3]]);
        let imm26 = patched & 0x03FF_FFFF;
        let expected_imm26 = ((target as i64 - pc as i64) >> 2) as u32 & 0x03FF_FFFF;
        assert_eq!(imm26, expected_imm26);
        // Opcode bits should be preserved.
        assert_eq!(patched & 0xFC00_0000, 0x94000000);
    }

    #[test]
    fn test_relocation_page21() {
        // ADRP instruction at address 0x1_0000_0000, target at 0x1_0000_1234.
        let adrp = 0x90000000u32; // ADRP X0, #0
        let mut data = adrp.to_le_bytes().to_vec();

        let pc = 0x1_0000_0000u64;
        let target = 0x1_0000_1234u64;

        let relocs = vec![Relocation::page21(0, 0)];
        let symbols = vec![ParsedSymbol {
            name: "_sym".into(),
            n_type: N_UNDF | N_EXT,
            section: 0,
            desc: 0,
            value: 0,
        }];
        let mut addrs = HashMap::new();
        addrs.insert("_sym".into(), target);

        RelocationApplicator::apply(&mut data, pc, &relocs, &symbols, &addrs, &[]).unwrap();

        let patched = u32::from_le_bytes([data[0], data[1], data[2], data[3]]);
        // page_delta = (0x1_0000_1000 - 0x1_0000_0000) >> 12 = 1
        let immlo = (patched >> 29) & 0x3;
        let immhi = (patched >> 5) & 0x7FFFF;
        let imm21 = (immhi << 2) | immlo;
        assert_eq!(imm21, 1);
    }

    #[test]
    fn test_relocation_pageoff12() {
        // ADD instruction at some address, target at 0x1_0000_1234.
        // Page offset = 0x234.
        let add_inst = 0x91000000u32; // ADD X0, X0, #0
        let mut data = add_inst.to_le_bytes().to_vec();

        let pc = 0x1_0000_0000u64;
        let target = 0x1_0000_1234u64;

        let relocs = vec![Relocation::pageoff12(0, 0)];
        let symbols = vec![ParsedSymbol {
            name: "_sym".into(),
            n_type: N_UNDF | N_EXT,
            section: 0,
            desc: 0,
            value: 0,
        }];
        let mut addrs = HashMap::new();
        addrs.insert("_sym".into(), target);

        RelocationApplicator::apply(&mut data, pc, &relocs, &symbols, &addrs, &[]).unwrap();

        let patched = u32::from_le_bytes([data[0], data[1], data[2], data[3]]);
        let imm12 = (patched >> 10) & 0xFFF;
        assert_eq!(imm12, 0x234);
    }

    #[test]
    fn test_relocation_subtractor_unsigned_quad() {
        let mut data = 0i64.to_le_bytes().to_vec();
        let pc = 0x1_0000_0000u64;
        let base = 0x1_0000_0000u64;
        let target = 0x1_0000_0100u64;
        let relocs = vec![
            Relocation::subtractor(0, 0, 3),
            Relocation::unsigned_ptr(0, 1),
        ];
        let symbols = vec![
            ParsedSymbol {
                name: "EH_Frame".into(),
                n_type: N_UNDF | N_EXT,
                section: 0,
                desc: 0,
                value: 0,
            },
            ParsedSymbol {
                name: "_sym".into(),
                n_type: N_UNDF | N_EXT,
                section: 0,
                desc: 0,
                value: 0,
            },
        ];
        let mut addrs = HashMap::new();
        addrs.insert("EH_Frame".into(), base);
        addrs.insert("_sym".into(), target);

        RelocationApplicator::apply(&mut data, pc, &relocs, &symbols, &addrs, &[]).unwrap();

        let patched = i64::from_le_bytes(data[0..8].try_into().unwrap());
        assert_eq!(patched, 0x100);
    }

    #[test]
    fn test_relocation_subtractor_unsigned_quad_negative() {
        let mut data = 0i64.to_le_bytes().to_vec();
        let pc = 0x1_0000_0100u64;
        let base = 0x1_0000_0100u64;
        let target = 0x1_0000_0000u64;
        let relocs = vec![
            Relocation::subtractor(0, 0, 3),
            Relocation::unsigned_ptr(0, 1),
        ];
        let symbols = vec![
            ParsedSymbol {
                name: "EH_Frame".into(),
                n_type: N_UNDF | N_EXT,
                section: 0,
                desc: 0,
                value: 0,
            },
            ParsedSymbol {
                name: "_sym".into(),
                n_type: N_UNDF | N_EXT,
                section: 0,
                desc: 0,
                value: 0,
            },
        ];
        let mut addrs = HashMap::new();
        addrs.insert("EH_Frame".into(), base);
        addrs.insert("_sym".into(), target);

        RelocationApplicator::apply(&mut data, pc, &relocs, &symbols, &addrs, &[]).unwrap();

        let patched = i64::from_le_bytes(data[0..8].try_into().unwrap());
        assert_eq!(patched, -0x100);
    }

    #[test]
    fn test_relocation_subtractor_unsigned_quad_preserves_addend() {
        let mut data = 4i64.to_le_bytes().to_vec();
        let pc = 0x1_0000_0000u64;
        let base = 0x1_0000_0000u64;
        let target = 0x1_0000_0100u64;
        let relocs = vec![
            Relocation::subtractor(0, 0, 3),
            Relocation::unsigned_ptr(0, 1),
        ];
        let symbols = vec![
            ParsedSymbol {
                name: "EH_Frame".into(),
                n_type: N_UNDF | N_EXT,
                section: 0,
                desc: 0,
                value: 0,
            },
            ParsedSymbol {
                name: "_sym".into(),
                n_type: N_UNDF | N_EXT,
                section: 0,
                desc: 0,
                value: 0,
            },
        ];
        let mut addrs = HashMap::new();
        addrs.insert("EH_Frame".into(), base);
        addrs.insert("_sym".into(), target);

        RelocationApplicator::apply(&mut data, pc, &relocs, &symbols, &addrs, &[]).unwrap();

        let patched = i64::from_le_bytes(data[0..8].try_into().unwrap());
        assert_eq!(patched, 0x104);
    }

    #[test]
    fn test_relocation_subtractor_unsigned_word_overflow() {
        let mut data = 0i32.to_le_bytes().to_vec();
        let pc = 0u64;
        let target = i32::MAX as u64 + 1;
        let relocs = vec![
            Relocation::subtractor(0, 0, 2),
            Relocation::unsigned_word(0, 1),
        ];
        let symbols = vec![
            ParsedSymbol {
                name: "EH_Frame".into(),
                n_type: N_UNDF | N_EXT,
                section: 0,
                desc: 0,
                value: 0,
            },
            ParsedSymbol {
                name: "_sym".into(),
                n_type: N_UNDF | N_EXT,
                section: 0,
                desc: 0,
                value: 0,
            },
        ];
        let mut addrs = HashMap::new();
        addrs.insert("EH_Frame".into(), 0);
        addrs.insert("_sym".into(), target);

        let err =
            RelocationApplicator::apply(&mut data, pc, &relocs, &symbols, &addrs, &[]).unwrap_err();

        assert!(matches!(err, LinkerError::RelocationOverflow { .. }));
    }

    #[test]
    fn test_relocation_subtractor_unsigned_word_short_data_errors() {
        let mut data = vec![0u8; 3];
        let pc = 0u64;
        let relocs = vec![
            Relocation::subtractor(0, 0, 2),
            Relocation::unsigned_word(0, 1),
        ];
        let symbols = vec![
            ParsedSymbol {
                name: "EH_Frame".into(),
                n_type: N_UNDF | N_EXT,
                section: 0,
                desc: 0,
                value: 0,
            },
            ParsedSymbol {
                name: "_sym".into(),
                n_type: N_UNDF | N_EXT,
                section: 0,
                desc: 0,
                value: 0,
            },
        ];
        let mut addrs = HashMap::new();
        addrs.insert("EH_Frame".into(), 0);
        addrs.insert("_sym".into(), 4);

        let err =
            RelocationApplicator::apply(&mut data, pc, &relocs, &symbols, &addrs, &[]).unwrap_err();

        assert!(matches!(
            err,
            LinkerError::RelocationOverflow { ref detail }
                if detail == RELOC32_PATCH_OOB_DETAIL
        ));
    }

    #[test]
    fn test_relocation_subtractor_unsigned_quad_short_data_errors() {
        let mut data = vec![0u8; 7];
        let pc = 0u64;
        let relocs = vec![
            Relocation::subtractor(0, 0, 3),
            Relocation::unsigned_ptr(0, 1),
        ];
        let symbols = vec![
            ParsedSymbol {
                name: "EH_Frame".into(),
                n_type: N_UNDF | N_EXT,
                section: 0,
                desc: 0,
                value: 0,
            },
            ParsedSymbol {
                name: "_sym".into(),
                n_type: N_UNDF | N_EXT,
                section: 0,
                desc: 0,
                value: 0,
            },
        ];
        let mut addrs = HashMap::new();
        addrs.insert("EH_Frame".into(), 0);
        addrs.insert("_sym".into(), 8);

        let err =
            RelocationApplicator::apply(&mut data, pc, &relocs, &symbols, &addrs, &[]).unwrap_err();

        assert!(matches!(
            err,
            LinkerError::RelocationOverflow { ref detail }
                if detail == RELOC64_PATCH_OOB_DETAIL
        ));
    }

    #[test]
    fn test_relocation_subtractor_resolves_local_symbol_by_index() {
        let mut data = (-8i64).to_le_bytes().to_vec();
        let pc = 0x1_0000_0000u64;
        let relocs = vec![
            Relocation::subtractor(0, 0, 3),
            Relocation::unsigned_ptr(0, 1),
        ];
        let symbols = vec![
            ParsedSymbol {
                name: "EH_Frame".into(),
                n_type: N_SECT,
                section: 1,
                desc: 0,
                value: 0,
            },
            ParsedSymbol {
                name: "_func".into(),
                n_type: N_UNDF | N_EXT,
                section: 0,
                desc: 0,
                value: 0,
            },
        ];
        let mut addrs = HashMap::new();
        addrs.insert("_func".into(), 0x1_0000_0100);
        let mut local_addrs = HashMap::new();
        local_addrs.insert(0usize, 0x1_0000_0000);

        RelocationApplicator::apply_with_local_symbols(
            &mut data,
            pc,
            &relocs,
            &symbols,
            &addrs,
            &local_addrs,
            &[],
        )
        .unwrap();

        let patched = i64::from_le_bytes(data[0..8].try_into().unwrap());
        assert_eq!(patched, 0xF8);
    }

    #[test]
    fn test_relocation_apply_rejects_local_symbol_without_index_map() {
        let mut data = 0u64.to_le_bytes().to_vec();
        let relocs = vec![Relocation::unsigned_ptr(0, 0)];
        let symbols = vec![ParsedSymbol {
            name: "_local".into(),
            n_type: N_SECT,
            section: 1,
            desc: 0,
            value: 0,
        }];
        let mut addrs = HashMap::new();
        addrs.insert("_local".into(), 0x1_0000_1000);

        let err =
            RelocationApplicator::apply(&mut data, 0x1_0000_0000, &relocs, &symbols, &addrs, &[])
                .unwrap_err();

        assert!(matches!(err, LinkerError::MalformedRelocation(ref msg) if msg.contains("_local")));
        assert_eq!(u64::from_le_bytes(data[0..8].try_into().unwrap()), 0);
    }

    #[test]
    fn test_section_relative_reloc_resolves_to_section_base() {
        // RANK 6: a section-relative (is_extern=false) ARM64_RELOC_UNSIGNED
        // whose r_symbolnum is a 1-based SECTION ORDINAL must resolve to the
        // referenced section's MAPPED BASE address, not the raw ordinal.
        //
        // Build a section-relative UNSIGNED reloc (length=3, 8-byte slot)
        // targeting section ordinal 2; the resolved value must equal the mapped
        // base of section index 1 (ordinal 2 - 1) plus the inline addend.
        let inline_addend: u64 = 0x10;
        let mut data = inline_addend.to_le_bytes().to_vec();
        let section_addr = 0x1_0000_0000u64; // base of the patched section.
        let section_addrs = [0x1_0000_0000u64, 0x1_0000_0200u64];

        // Relocation::new defaults is_extern=true, so build via struct literal.
        let relocs = vec![Relocation {
            offset: 0,
            symbol_index: 2, // 1-based section ordinal -> section index 1.
            kind: AArch64RelocKind::Unsigned,
            pc_relative: false,
            length: 3,
            is_extern: false,
        }];
        let symbols: Vec<ParsedSymbol> = Vec::new();
        let symbol_addrs = HashMap::new();

        RelocationApplicator::apply(
            &mut data,
            section_addr,
            &relocs,
            &symbols,
            &symbol_addrs,
            &section_addrs,
        )
        .unwrap();

        let patched = u64::from_le_bytes(data[0..8].try_into().unwrap());
        // The correct result is the mapped base of section ordinal 2 plus the
        // inline addend — NOT the raw ordinal (which would be 2).
        assert_eq!(patched, section_addrs[1] + inline_addend);
        assert_ne!(patched, 2 + inline_addend);
    }

    #[test]
    fn test_section_relative_reloc_invalid_ordinal_errors() {
        // RANK 6: an out-of-range / zero section ordinal must surface as a
        // typed MalformedRelocation, not a wrong tiny-integer address.
        let mut data = 0u64.to_le_bytes().to_vec();
        let section_addrs = [0x1_0000_0000u64];
        let symbols: Vec<ParsedSymbol> = Vec::new();
        let symbol_addrs = HashMap::new();

        for bad_ordinal in [0u32, 2u32] {
            let relocs = vec![Relocation {
                offset: 0,
                symbol_index: bad_ordinal,
                kind: AArch64RelocKind::Unsigned,
                pc_relative: false,
                length: 3,
                is_extern: false,
            }];
            let err = RelocationApplicator::apply(
                &mut data,
                0x1_0000_0000,
                &relocs,
                &symbols,
                &symbol_addrs,
                &section_addrs,
            )
            .unwrap_err();
            assert!(
                matches!(err, LinkerError::MalformedRelocation(_)),
                "ordinal {bad_ordinal}: expected MalformedRelocation, got {err:?}"
            );
        }
    }

    #[test]
    fn test_relocation_unsigned_absolute_quad() {
        let mut data = 5u64.to_le_bytes().to_vec();
        let pc = 0x1_0000_0000u64;
        let target = 0x1_0000_0100u64;
        let relocs = vec![Relocation::unsigned_ptr(0, 0)];
        let symbols = vec![ParsedSymbol {
            name: "_sym".into(),
            n_type: N_UNDF | N_EXT,
            section: 0,
            desc: 0,
            value: 0,
        }];
        let mut addrs = HashMap::new();
        addrs.insert("_sym".into(), target);

        RelocationApplicator::apply(&mut data, pc, &relocs, &symbols, &addrs, &[]).unwrap();

        let patched = u64::from_le_bytes(data[0..8].try_into().unwrap());
        assert_eq!(patched, target + 5);
    }

    // =======================================================================
    // Executable emission tests
    // =======================================================================

    #[test]
    fn test_executable_emission() {
        let nop = 0xD503201Fu32;
        let text_data: Vec<u8> = (0..4).flat_map(|_| nop.to_le_bytes()).collect();
        let text_file_offset = plain_executable_text_file_offset(false);

        let exe = ExecutableEmitter::emit(
            &text_data,
            &[],
            DEFAULT_BASE_ADDR,
            DEFAULT_BASE_ADDR + PAGE_SIZE,
            text_file_offset,
        );

        // Verify header.
        assert_eq!(rd_u32(&exe, 0), MH_MAGIC_64);
        assert_eq!(rd_u32(&exe, 4), CPU_TYPE_ARM64);
        assert_eq!(rd_u32(&exe, 12), MH_EXECUTE);
        assert_eq!(rd_u32(&exe, 24), MH_EXECUTE_FLAGS);

        // Find __PAGEZERO segment.
        let seg_name_off = MACH_HEADER_64_SIZE as usize + 8; // after cmd + cmdsize
        let pagezero_name = read_name16(&exe, seg_name_off);
        assert_eq!(pagezero_name, "__PAGEZERO");

        // Verify __PAGEZERO vmaddr=0, vmsize=4GB.
        let pz_vmaddr = rd_u64(&exe, MACH_HEADER_64_SIZE as usize + 24);
        let pz_vmsize = rd_u64(&exe, MACH_HEADER_64_SIZE as usize + 32);
        assert_eq!(pz_vmaddr, 0);
        assert_eq!(pz_vmsize, DEFAULT_BASE_ADDR);
        assert_mapped_text_layout(&exe, text_file_offset);
    }

    #[test]
    fn test_executable_with_data() {
        let nop = 0xD503201Fu32;
        let text_data: Vec<u8> = (0..4).flat_map(|_| nop.to_le_bytes()).collect();
        let data_data = vec![0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE, 0xBA, 0xBE];

        let text_aligned = align_to(text_data.len() as u64, PAGE_SIZE);
        let text_file_offset = plain_executable_text_file_offset(true);
        let data_vmaddr = DEFAULT_BASE_ADDR + text_file_offset + text_aligned;

        let exe = ExecutableEmitter::emit(
            &text_data,
            &data_data,
            DEFAULT_BASE_ADDR,
            data_vmaddr,
            text_file_offset,
        );

        assert_eq!(rd_u32(&exe, 0), MH_MAGIC_64);
        assert_eq!(rd_u32(&exe, 12), MH_EXECUTE);

        // Should have 13 load commands when data and dyld linkedit payloads are present.
        assert_eq!(rd_u32(&exe, 16), 13);

        // Verify data is in the file.
        let found = exe.windows(4).any(|w| w == [0xDE, 0xAD, 0xBE, 0xEF]);
        assert!(found, "data section content should be in the executable");
        assert_mapped_text_layout(&exe, text_file_offset);
        assert_dyld_linkedit_payloads(&exe, &[]);
    }

    #[test]
    fn test_plain_linker_emits_preflight_load_commands() {
        let mut writer = MachOWriter::new();
        writer.add_text_section(&0xD65F03C0u32.to_le_bytes());
        writer.add_symbol("_main", 1, 0, true).unwrap();
        let obj_bytes = writer.write().unwrap();
        let obj = MachOParser::parse(&obj_bytes).unwrap();

        let exe = link(std::slice::from_ref(&obj)).unwrap();
        let commands = walk_load_commands(&exe);

        assert_eq!(count_load_command(&commands, LC_BUILD_VERSION), 1);
        assert_eq!(count_load_command(&commands, LC_UUID), 1);
        assert_eq!(count_load_command(&commands, LC_DYSYMTAB), 1);
        assert_eq!(count_load_command(&commands, LC_LOAD_DYLINKER), 1);
        assert_eq!(count_load_command(&commands, LC_DYLD_CHAINED_FIXUPS), 1);
        assert_eq!(count_load_command(&commands, LC_DYLD_EXPORTS_TRIE), 1);
        assert_eq!(count_load_command(&commands, LC_CODE_SIGNATURE), 1);

        assert_build_version_command(&exe, single_load_command(&commands, LC_BUILD_VERSION));
        assert_empty_dysymtab_command(&exe, single_load_command(&commands, LC_DYSYMTAB));
        assert_mapped_text_layout(&exe, plain_executable_text_file_offset(false));
        assert_dyld_linkedit_payloads(&exe, &[]);

        let uuid = load_command_uuid(&exe, single_load_command(&commands, LC_UUID));
        assert_ne!(uuid, [0; 16], "LC_UUID should not be all zeroes");

        let exe_again = link(&[obj]).unwrap();
        let commands_again = walk_load_commands(&exe_again);
        let uuid_again =
            load_command_uuid(&exe_again, single_load_command(&commands_again, LC_UUID));
        assert_eq!(uuid, uuid_again, "LC_UUID should be deterministic");
    }

    #[test]
    fn test_dylib_linker_emits_preflight_load_commands() {
        let mut writer = MachOWriter::new();
        let mov_x0_0 = 0xD2800000u32;
        let bl_exit = 0x94000000u32;
        let mut code = Vec::new();
        code.extend_from_slice(&mov_x0_0.to_le_bytes());
        code.extend_from_slice(&bl_exit.to_le_bytes());
        writer.add_text_section(&code);
        writer.add_symbol("_main", 1, 0, true).unwrap();
        writer.add_symbol("_exit", 0, 0, true).unwrap();
        writer
            .add_relocation(0, Relocation::branch26(4, 1))
            .unwrap();

        let obj_bytes = writer.write().unwrap();
        let obj = MachOParser::parse(&obj_bytes).unwrap();
        let mut obj_fixed = obj.clone();
        let exit_idx = obj_fixed
            .symbols
            .iter()
            .position(|s| s.name == "_exit")
            .unwrap();
        obj_fixed.sections[0].relocations[0].symbol_index = exit_idx as u32;

        let config = DylibConfig::with_libsystem();
        let exe = link_with_dylibs(&[obj_fixed.clone()], &config).unwrap();
        let commands = walk_load_commands(&exe);

        assert_eq!(count_load_command(&commands, LC_BUILD_VERSION), 1);
        assert_eq!(count_load_command(&commands, LC_UUID), 1);
        assert_eq!(count_load_command(&commands, LC_DYSYMTAB), 1);
        assert_eq!(count_load_command(&commands, LC_LOAD_DYLINKER), 1);
        assert_eq!(count_load_command(&commands, LC_LOAD_DYLIB), 1);
        assert_eq!(count_load_command(&commands, LC_DYLD_CHAINED_FIXUPS), 1);
        assert_eq!(count_load_command(&commands, LC_DYLD_EXPORTS_TRIE), 1);
        assert_eq!(count_load_command(&commands, LC_CODE_SIGNATURE), 1);

        assert_build_version_command(&exe, single_load_command(&commands, LC_BUILD_VERSION));
        assert_empty_dysymtab_command(&exe, single_load_command(&commands, LC_DYSYMTAB));
        let expected_entryoff = dylib_executable_text_file_offset(true, true, &[&config.dylibs[0]]);
        assert_mapped_text_layout(&exe, expected_entryoff);
        assert_dyld_linkedit_payloads(&exe, &["_exit"]);

        let uuid = load_command_uuid(&exe, single_load_command(&commands, LC_UUID));
        assert_ne!(uuid, [0; 16], "LC_UUID should not be all zeroes");

        let dylib_command = single_load_command(&commands, LC_LOAD_DYLIB);
        let name_offset = rd_u32(&exe, dylib_command.offset + 8) as usize;
        let name_start = dylib_command.offset + name_offset;
        let name = read_cstring(&exe, name_start);
        assert_eq!(name, "/usr/lib/libSystem.B.dylib");

        let exe_again = link_with_dylibs(&[obj_fixed], &config).unwrap();
        let commands_again = walk_load_commands(&exe_again);
        let uuid_again =
            load_command_uuid(&exe_again, single_load_command(&commands_again, LC_UUID));
        assert_eq!(uuid, uuid_again, "LC_UUID should be deterministic");
    }

    // =======================================================================
    // End-to-end link test
    // =======================================================================

    #[test]
    fn test_link_two_objects() {
        // Object 1: _callee returns (RET instruction).
        let mut writer1 = MachOWriter::new();
        let ret = 0xD65F03C0u32;
        writer1.add_text_section(&ret.to_le_bytes());
        writer1.add_symbol("_callee", 1, 0, true).unwrap();
        let obj1_bytes = writer1.write().unwrap();
        let obj1 = MachOParser::parse(&obj1_bytes).unwrap();

        // Object 2: _main calls _callee (BL) then returns (RET).
        let mut writer2 = MachOWriter::new();
        let bl = 0x94000000u32;
        let ret2 = 0xD65F03C0u32;
        let mut code = Vec::new();
        code.extend_from_slice(&bl.to_le_bytes());
        code.extend_from_slice(&ret2.to_le_bytes());
        writer2.add_text_section(&code);
        writer2.add_symbol("_main", 1, 0, true).unwrap();
        writer2.add_symbol("_callee", 0, 0, true).unwrap();

        // NOTE: the relocation symbol_index refers to the symbol's position
        // in the writer's symbol list. After parsing, the MachOWriter reorders
        // symbols (locals, extdef, undef). _callee is external-undefined so it
        // ends up last. In the parsed object, _main is at index 0 and _callee
        // is at index 1 (both are external, _main is defined, _callee undefined).
        // The writer encodes the relocation with the original pre-reorder index.
        // After round-tripping through write + parse, we need to check which
        // index _callee ended up at.
        writer2
            .add_relocation(0, Relocation::branch26(0, 1))
            .unwrap();
        let obj2_bytes = writer2.write().unwrap();
        let obj2 = MachOParser::parse(&obj2_bytes).unwrap();

        // Find _callee symbol index in the parsed object2.
        let callee_idx = obj2
            .symbols
            .iter()
            .position(|s| s.name == "_callee")
            .expect("_callee not found in parsed obj2");

        // Reconstruct with correct symbol index.
        let mut obj2_fixed = obj2.clone();
        if !obj2_fixed.sections[0].relocations.is_empty() {
            obj2_fixed.sections[0].relocations[0].symbol_index = callee_idx as u32;
        }

        let exe = link(&[obj1, obj2_fixed]).unwrap();

        // Verify executable header.
        assert_eq!(rd_u32(&exe, 0), MH_MAGIC_64);
        assert_eq!(rd_u32(&exe, 12), MH_EXECUTE);
        assert!(exe.len() > 100); // Non-trivial output.

        let text_file_offset = plain_executable_text_file_offset(false);
        assert_mapped_text_layout(&exe, text_file_offset + 4);

        let commands = walk_load_commands(&exe);
        let sections = section_commands(&exe, &commands);
        let text = single_section(&sections, "__TEXT", "__text");
        let branch_file_offset = text.offset as usize + 4;
        let patched = rd_u32(&exe, branch_file_offset);
        let imm26 = patched & 0x03FF_FFFF;
        let signed_imm26 = ((imm26 as i32) << 6) >> 6;
        let branch_pc = DEFAULT_BASE_ADDR as i64 + branch_file_offset as i64;
        let branch_target = branch_pc + ((signed_imm26 as i64) << 2);
        assert_eq!(
            branch_target as u64, text.addr,
            "BRANCH26 relocation must target the shifted mapped __text address"
        );
    }

    #[test]
    fn test_link_single_object() {
        // Single object with just _main.
        let mut writer = MachOWriter::new();
        let ret = 0xD65F03C0u32;
        writer.add_text_section(&ret.to_le_bytes());
        writer.add_symbol("_main", 1, 0, true).unwrap();
        let obj_bytes = writer.write().unwrap();
        let obj = MachOParser::parse(&obj_bytes).unwrap();

        let exe = link(&[obj]).unwrap();
        assert_eq!(rd_u32(&exe, 0), MH_MAGIC_64);
        assert_eq!(rd_u32(&exe, 12), MH_EXECUTE);
        assert_mapped_text_layout(&exe, plain_executable_text_file_offset(false));
    }

    #[test]
    fn test_link_no_main_error() {
        let mut writer = MachOWriter::new();
        let ret = 0xD65F03C0u32;
        writer.add_text_section(&ret.to_le_bytes());
        writer.add_symbol("_foo", 1, 0, true).unwrap();
        let obj_bytes = writer.write().unwrap();
        let obj = MachOParser::parse(&obj_bytes).unwrap();

        let err = link(&[obj]).unwrap_err();
        assert!(matches!(err, LinkerError::NoEntryPoint));
    }

    #[test]
    fn test_align_to() {
        assert_eq!(align_to(0, 4096), 0);
        assert_eq!(align_to(1, 4096), 4096);
        assert_eq!(align_to(4096, 4096), 4096);
        assert_eq!(align_to(4097, 4096), 8192);
        assert_eq!(align_to(100, 0), 100);
    }

    // =======================================================================
    // Multi-file linking tests
    // =======================================================================

    #[test]
    fn test_link_three_objects() {
        // Object 1: _add function (ADD X0, X0, X1; RET)
        let mut writer1 = MachOWriter::new();
        let add_inst = 0x8B010000u32; // ADD X0, X0, X1
        let ret1 = 0xD65F03C0u32; // RET
        let mut code1 = Vec::new();
        code1.extend_from_slice(&add_inst.to_le_bytes());
        code1.extend_from_slice(&ret1.to_le_bytes());
        writer1.add_text_section(&code1);
        writer1.add_symbol("_add", 1, 0, true).unwrap();
        let obj1_bytes = writer1.write().unwrap();
        let obj1 = MachOParser::parse(&obj1_bytes).unwrap();

        // Object 2: _sub function (SUB X0, X0, X1; RET)
        let mut writer2 = MachOWriter::new();
        let sub_inst = 0xCB010000u32; // SUB X0, X0, X1
        let ret2 = 0xD65F03C0u32;
        let mut code2 = Vec::new();
        code2.extend_from_slice(&sub_inst.to_le_bytes());
        code2.extend_from_slice(&ret2.to_le_bytes());
        writer2.add_text_section(&code2);
        writer2.add_symbol("_sub", 1, 0, true).unwrap();
        let obj2_bytes = writer2.write().unwrap();
        let obj2 = MachOParser::parse(&obj2_bytes).unwrap();

        // Object 3: _main calls _add then _sub (BL _add; BL _sub; RET)
        let mut writer3 = MachOWriter::new();
        let bl1 = 0x94000000u32; // BL #0 (placeholder)
        let bl2 = 0x94000000u32; // BL #0 (placeholder)
        let ret3 = 0xD65F03C0u32;
        let mut code3 = Vec::new();
        code3.extend_from_slice(&bl1.to_le_bytes());
        code3.extend_from_slice(&bl2.to_le_bytes());
        code3.extend_from_slice(&ret3.to_le_bytes());
        writer3.add_text_section(&code3);
        writer3.add_symbol("_main", 1, 0, true).unwrap();
        writer3.add_symbol("_add", 0, 0, true).unwrap(); // undefined
        writer3.add_symbol("_sub", 0, 0, true).unwrap(); // undefined
        writer3
            .add_relocation(0, Relocation::branch26(0, 1))
            .unwrap(); // BL _add
        writer3
            .add_relocation(0, Relocation::branch26(4, 2))
            .unwrap(); // BL _sub
        let obj3_bytes = writer3.write().unwrap();
        let obj3 = MachOParser::parse(&obj3_bytes).unwrap();

        // Fix up relocation symbol indices after parsing.
        let mut obj3_fixed = obj3.clone();
        let add_idx = obj3_fixed
            .symbols
            .iter()
            .position(|s| s.name == "_add")
            .unwrap();
        let sub_idx = obj3_fixed
            .symbols
            .iter()
            .position(|s| s.name == "_sub")
            .unwrap();
        obj3_fixed.sections[0].relocations[0].symbol_index = add_idx as u32;
        obj3_fixed.sections[0].relocations[1].symbol_index = sub_idx as u32;

        // Link all three objects.
        let exe = link(&[obj1, obj2, obj3_fixed]).unwrap();

        // Verify executable header.
        assert_eq!(rd_u32(&exe, 0), MH_MAGIC_64);
        assert_eq!(rd_u32(&exe, 12), MH_EXECUTE);
        assert!(exe.len() > 100);

        // Verify that both _add and _sub code are in the text segment.
        // ADD X0, X0, X1 = 0x8B010000
        let has_add = exe
            .windows(4)
            .any(|w| u32::from_le_bytes([w[0], w[1], w[2], w[3]]) == 0x8B010000);
        assert!(has_add, "ADD instruction should be in executable");

        // SUB X0, X0, X1 = 0xCB010000
        let has_sub = exe
            .windows(4)
            .any(|w| u32::from_le_bytes([w[0], w[1], w[2], w[3]]) == 0xCB010000);
        assert!(has_sub, "SUB instruction should be in executable");
    }

    #[test]
    fn test_link_three_objects_with_data() {
        // Object 1: defines _data1 (constant bytes)
        let mut writer1 = MachOWriter::new();
        writer1.add_text_section(&0xD503201Fu32.to_le_bytes()); // NOP
        writer1.add_data_section(&[0x11, 0x22, 0x33, 0x44]);
        writer1.add_symbol("_func1", 1, 0, true).unwrap();
        writer1.add_symbol("_data1", 2, 0, true).unwrap();
        let obj1_bytes = writer1.write().unwrap();
        let obj1 = MachOParser::parse(&obj1_bytes).unwrap();

        // Object 2: defines _data2
        let mut writer2 = MachOWriter::new();
        writer2.add_text_section(&0xD503201Fu32.to_le_bytes()); // NOP
        writer2.add_data_section(&[0xAA, 0xBB, 0xCC, 0xDD]);
        writer2.add_symbol("_func2", 1, 0, true).unwrap();
        writer2.add_symbol("_data2", 2, 0, true).unwrap();
        let obj2_bytes = writer2.write().unwrap();
        let obj2 = MachOParser::parse(&obj2_bytes).unwrap();

        // Object 3: _main
        let mut writer3 = MachOWriter::new();
        writer3.add_text_section(&0xD65F03C0u32.to_le_bytes()); // RET
        writer3.add_symbol("_main", 1, 0, true).unwrap();
        let obj3_bytes = writer3.write().unwrap();
        let obj3 = MachOParser::parse(&obj3_bytes).unwrap();

        let exe = link(&[obj1, obj2, obj3]).unwrap();

        assert_eq!(rd_u32(&exe, 0), MH_MAGIC_64);
        assert_eq!(rd_u32(&exe, 12), MH_EXECUTE);

        // Verify both data sections appear in the output.
        let has_data1 = exe.windows(4).any(|w| w == [0x11, 0x22, 0x33, 0x44]);
        let has_data2 = exe.windows(4).any(|w| w == [0xAA, 0xBB, 0xCC, 0xDD]);
        assert!(has_data1, "data1 should be in executable");
        assert!(has_data2, "data2 should be in executable");
    }

    // =======================================================================
    // Dylib linking tests
    // =======================================================================

    #[test]
    fn test_dylib_config_basic() {
        let config = DylibConfig::with_libsystem();
        assert!(config.is_dylib_symbol("_exit"));
        assert!(config.is_dylib_symbol("_printf"));
        assert!(!config.is_dylib_symbol("_my_custom_func"));
    }

    #[test]
    fn test_dylib_config_needed_dylibs() {
        let config = DylibConfig::with_libsystem();
        let needed = config.needed_dylibs(&["_exit".to_string(), "_printf".to_string()]);
        assert_eq!(needed.len(), 1);
        assert_eq!(needed[0], 0);

        // No undefined symbols -> no dylibs needed.
        let needed_empty = config.needed_dylibs(&[]);
        assert!(needed_empty.is_empty());
    }

    #[test]
    fn test_link_with_dylib_symbols() {
        // Object that calls _exit (a libSystem symbol).
        // _main: MOV X0, #0; BL _exit
        let mut writer = MachOWriter::new();
        let mov_x0_0 = 0xD2800000u32; // MOV X0, #0
        let bl_exit = 0x94000000u32; // BL #0 (placeholder, will be resolved to stub)
        let mut code = Vec::new();
        code.extend_from_slice(&mov_x0_0.to_le_bytes());
        code.extend_from_slice(&bl_exit.to_le_bytes());
        writer.add_text_section(&code);
        writer.add_symbol("_main", 1, 0, true).unwrap();
        writer.add_symbol("_exit", 0, 0, true).unwrap(); // undefined external
        writer
            .add_relocation(0, Relocation::branch26(4, 1))
            .unwrap(); // BL _exit at offset 4

        let obj_bytes = writer.write().unwrap();
        let obj = MachOParser::parse(&obj_bytes).unwrap();

        // Fix relocation symbol index.
        let mut obj_fixed = obj.clone();
        let exit_idx = obj_fixed
            .symbols
            .iter()
            .position(|s| s.name == "_exit")
            .unwrap();
        obj_fixed.sections[0].relocations[0].symbol_index = exit_idx as u32;

        let config = DylibConfig::with_libsystem();
        let exe = link_with_dylibs(&[obj_fixed], &config).unwrap();

        // Verify executable header.
        assert_eq!(rd_u32(&exe, 0), MH_MAGIC_64);
        assert_eq!(rd_u32(&exe, 12), MH_EXECUTE);

        // Verify LC_LOAD_DYLIB is present by scanning for the command type.
        let mut found_dylib_cmd = false;
        let mut offset = MACH_HEADER_64_SIZE as usize;
        let ncmds = rd_u32(&exe, 16);
        let sizeofcmds = rd_u32(&exe, 20) as usize;
        let lc_end = offset + sizeofcmds;

        for _ in 0..ncmds {
            if offset + 8 > lc_end {
                break;
            }
            let cmd = rd_u32(&exe, offset);
            let cmdsize = rd_u32(&exe, offset + 4) as usize;

            if cmd == LC_LOAD_DYLIB {
                found_dylib_cmd = true;
                // Verify the dylib name is present.
                let name_offset = rd_u32(&exe, offset + 8) as usize;
                let name_start = offset + name_offset;
                // Read NUL-terminated string.
                let mut name_end = name_start;
                while name_end < exe.len() && exe[name_end] != 0 {
                    name_end += 1;
                }
                let name = String::from_utf8_lossy(&exe[name_start..name_end]);
                assert_eq!(name, "/usr/lib/libSystem.B.dylib");
            }

            offset += cmdsize;
        }
        assert!(found_dylib_cmd, "LC_LOAD_DYLIB should be present");

        // Verify stubs are in the text segment (ADRP X16 = 0x90000010).
        let has_stub = exe
            .windows(4)
            .any(|w| u32::from_le_bytes([w[0], w[1], w[2], w[3]]) == 0x9000_0010);
        assert!(has_stub, "stub ADRP X16 instruction should be present");
    }

    #[test]
    fn test_link_with_dylib_undefined_non_dylib_error() {
        // Object that references a symbol not in any dylib.
        let mut writer = MachOWriter::new();
        writer.add_text_section(&0x94000000u32.to_le_bytes()); // BL
        writer.add_symbol("_main", 1, 0, true).unwrap();
        writer.add_symbol("_unknown_func", 0, 0, true).unwrap(); // undefined, not in any dylib
        writer
            .add_relocation(0, Relocation::branch26(0, 1))
            .unwrap();

        let obj_bytes = writer.write().unwrap();
        let obj = MachOParser::parse(&obj_bytes).unwrap();

        let mut obj_fixed = obj.clone();
        let idx = obj_fixed
            .symbols
            .iter()
            .position(|s| s.name == "_unknown_func")
            .unwrap();
        obj_fixed.sections[0].relocations[0].symbol_index = idx as u32;

        let config = DylibConfig::with_libsystem();
        let err = link_with_dylibs(&[obj_fixed], &config).unwrap_err();
        assert!(matches!(err, LinkerError::UndefinedSymbol(ref s) if s == "_unknown_func"));
    }

    #[test]
    fn test_link_with_dylib_multiple_objects_and_exit() {
        // Object 1: _helper function (just RET)
        let mut writer1 = MachOWriter::new();
        writer1.add_text_section(&0xD65F03C0u32.to_le_bytes()); // RET
        writer1.add_symbol("_helper", 1, 0, true).unwrap();
        let obj1_bytes = writer1.write().unwrap();
        let obj1 = MachOParser::parse(&obj1_bytes).unwrap();

        // Object 2: _main calls _helper then _exit
        let mut writer2 = MachOWriter::new();
        let bl_helper = 0x94000000u32;
        let mov_x0 = 0xD2800000u32;
        let bl_exit = 0x94000000u32;
        let mut code = Vec::new();
        code.extend_from_slice(&bl_helper.to_le_bytes());
        code.extend_from_slice(&mov_x0.to_le_bytes());
        code.extend_from_slice(&bl_exit.to_le_bytes());
        writer2.add_text_section(&code);
        writer2.add_symbol("_main", 1, 0, true).unwrap();
        writer2.add_symbol("_helper", 0, 0, true).unwrap();
        writer2.add_symbol("_exit", 0, 0, true).unwrap();
        writer2
            .add_relocation(0, Relocation::branch26(0, 1))
            .unwrap(); // BL _helper
        writer2
            .add_relocation(0, Relocation::branch26(8, 2))
            .unwrap(); // BL _exit
        let obj2_bytes = writer2.write().unwrap();
        let obj2 = MachOParser::parse(&obj2_bytes).unwrap();

        // Fix up symbol indices.
        let mut obj2_fixed = obj2.clone();
        let helper_idx = obj2_fixed
            .symbols
            .iter()
            .position(|s| s.name == "_helper")
            .unwrap();
        let exit_idx = obj2_fixed
            .symbols
            .iter()
            .position(|s| s.name == "_exit")
            .unwrap();
        obj2_fixed.sections[0].relocations[0].symbol_index = helper_idx as u32;
        obj2_fixed.sections[0].relocations[1].symbol_index = exit_idx as u32;

        let config = DylibConfig::with_libsystem();
        let exe = link_with_dylibs(&[obj1, obj2_fixed], &config).unwrap();

        // Basic validity checks.
        assert_eq!(rd_u32(&exe, 0), MH_MAGIC_64);
        assert_eq!(rd_u32(&exe, 12), MH_EXECUTE);
        assert!(exe.len() > PAGE_SIZE as usize); // Non-trivial output.
    }

    // =======================================================================
    // Weak symbol tests
    // =======================================================================

    #[test]
    fn test_weak_symbol_override() {
        // Object 1 defines _foo as weak.
        let obj1 = ParsedObject {
            cputype: CPU_TYPE_ARM64,
            cpusubtype: CPU_SUBTYPE_ARM64_ALL,
            flags: 0,
            sections: vec![ParsedSection {
                name: "__text".into(),
                segment: "__TEXT".into(),
                data: vec![0xC0, 0x03, 0x5F, 0xD6], // RET
                addr: 0,
                align: 2,
                flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS,
                relocations: vec![],
                vmsize: 4,
            }],
            symbols: vec![ParsedSymbol {
                name: "_foo".into(),
                n_type: N_SECT | N_EXT,
                section: 1,
                desc: N_WEAK_DEF, // weak definition
                value: 0,
            }],
        };

        // Object 2 defines _foo as strong + _main.
        let obj2 = ParsedObject {
            cputype: CPU_TYPE_ARM64,
            cpusubtype: CPU_SUBTYPE_ARM64_ALL,
            flags: 0,
            sections: vec![ParsedSection {
                name: "__text".into(),
                segment: "__TEXT".into(),
                data: vec![
                    0xC0, 0x03, 0x5F, 0xD6, // RET (_foo)
                    0xC0, 0x03, 0x5F, 0xD6, // RET (_main)
                ],
                addr: 0,
                align: 2,
                flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS,
                relocations: vec![],
                vmsize: 8,
            }],
            symbols: vec![
                ParsedSymbol {
                    name: "_foo".into(),
                    n_type: N_SECT | N_EXT,
                    section: 1,
                    desc: 0, // strong definition
                    value: 0,
                },
                ParsedSymbol {
                    name: "_main".into(),
                    n_type: N_SECT | N_EXT,
                    section: 1,
                    desc: 0,
                    value: 4,
                },
            ],
        };

        // Link should succeed (strong overrides weak).
        let objects = vec![obj1, obj2];
        let layout = lay_out_sections(&objects, DEFAULT_BASE_ADDR);
        let mut resolver = SymbolResolver::new();
        resolver
            .add_object(0, &objects[0], &layout.section_addrs[0])
            .unwrap();
        resolver
            .add_object(1, &objects[1], &layout.section_addrs[1])
            .unwrap();
        let addrs = resolver.resolve().unwrap();

        // _foo should resolve to object 2's address (the strong one).
        let foo_addr = addrs["_foo"];
        // Object 2's section starts after object 1's 4-byte section.
        assert_eq!(foo_addr, layout.section_addrs[1][0]);
    }

    #[test]
    fn test_weak_symbol_duplicate_weak() {
        // Two objects both define _foo as weak. No error, first wins.
        let obj1 = ParsedObject {
            cputype: CPU_TYPE_ARM64,
            cpusubtype: CPU_SUBTYPE_ARM64_ALL,
            flags: 0,
            sections: vec![ParsedSection {
                name: "__text".into(),
                segment: "__TEXT".into(),
                data: vec![0xC0, 0x03, 0x5F, 0xD6],
                addr: 0,
                align: 2,
                flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS,
                relocations: vec![],
                vmsize: 4,
            }],
            symbols: vec![
                ParsedSymbol {
                    name: "_foo".into(),
                    n_type: N_SECT | N_EXT,
                    section: 1,
                    desc: N_WEAK_DEF,
                    value: 0,
                },
                ParsedSymbol {
                    name: "_main".into(),
                    n_type: N_SECT | N_EXT,
                    section: 1,
                    desc: 0,
                    value: 0,
                },
            ],
        };

        let obj2 = ParsedObject {
            cputype: CPU_TYPE_ARM64,
            cpusubtype: CPU_SUBTYPE_ARM64_ALL,
            flags: 0,
            sections: vec![ParsedSection {
                name: "__text".into(),
                segment: "__TEXT".into(),
                data: vec![0xC0, 0x03, 0x5F, 0xD6],
                addr: 0,
                align: 2,
                flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS,
                relocations: vec![],
                vmsize: 4,
            }],
            symbols: vec![ParsedSymbol {
                name: "_foo".into(),
                n_type: N_SECT | N_EXT,
                section: 1,
                desc: N_WEAK_DEF,
                value: 0,
            }],
        };

        let objects = vec![obj1, obj2];
        let layout = lay_out_sections(&objects, DEFAULT_BASE_ADDR);
        let mut resolver = SymbolResolver::new();
        resolver
            .add_object(0, &objects[0], &layout.section_addrs[0])
            .unwrap();
        resolver
            .add_object(1, &objects[1], &layout.section_addrs[1])
            .unwrap();
        let addrs = resolver.resolve().unwrap();

        // First wins: _foo should be from object 0.
        assert_eq!(addrs["_foo"], layout.section_addrs[0][0]);
    }

    #[test]
    fn test_weak_symbol_strong_duplicate_error() {
        // Two objects both define _foo as strong. Should error.
        let obj1 = ParsedObject {
            cputype: CPU_TYPE_ARM64,
            cpusubtype: CPU_SUBTYPE_ARM64_ALL,
            flags: 0,
            sections: vec![ParsedSection {
                name: "__text".into(),
                segment: "__TEXT".into(),
                data: vec![0xC0, 0x03, 0x5F, 0xD6],
                addr: 0,
                align: 2,
                flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS,
                relocations: vec![],
                vmsize: 4,
            }],
            symbols: vec![ParsedSymbol {
                name: "_foo".into(),
                n_type: N_SECT | N_EXT,
                section: 1,
                desc: 0, // strong
                value: 0,
            }],
        };

        let obj2 = ParsedObject {
            cputype: CPU_TYPE_ARM64,
            cpusubtype: CPU_SUBTYPE_ARM64_ALL,
            flags: 0,
            sections: vec![ParsedSection {
                name: "__text".into(),
                segment: "__TEXT".into(),
                data: vec![0xC0, 0x03, 0x5F, 0xD6],
                addr: 0,
                align: 2,
                flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS,
                relocations: vec![],
                vmsize: 4,
            }],
            symbols: vec![ParsedSymbol {
                name: "_foo".into(),
                n_type: N_SECT | N_EXT,
                section: 1,
                desc: 0, // strong
                value: 0,
            }],
        };

        let objects = vec![obj1, obj2];
        let layout = lay_out_sections(&objects, DEFAULT_BASE_ADDR);
        let mut resolver = SymbolResolver::new();
        resolver
            .add_object(0, &objects[0], &layout.section_addrs[0])
            .unwrap();
        let err = resolver
            .add_object(1, &objects[1], &layout.section_addrs[1])
            .unwrap_err();
        assert!(matches!(err, LinkerError::DuplicateSymbolDetailed {
            ref name, first_obj: 0, second_obj: 1
        } if name == "_foo"));
    }

    #[test]
    fn test_weak_reference_unresolved() {
        // Object with a weak reference to _optional_func that has no definition.
        let obj = ParsedObject {
            cputype: CPU_TYPE_ARM64,
            cpusubtype: CPU_SUBTYPE_ARM64_ALL,
            flags: 0,
            sections: vec![ParsedSection {
                name: "__text".into(),
                segment: "__TEXT".into(),
                data: vec![0xC0, 0x03, 0x5F, 0xD6],
                addr: 0,
                align: 2,
                flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS,
                relocations: vec![],
                vmsize: 4,
            }],
            symbols: vec![
                ParsedSymbol {
                    name: "_main".into(),
                    n_type: N_SECT | N_EXT,
                    section: 1,
                    desc: 0,
                    value: 0,
                },
                ParsedSymbol {
                    name: "_optional_func".into(),
                    n_type: N_UNDF | N_EXT,
                    section: 0,
                    desc: N_WEAK_REF, // weak reference
                    value: 0,
                },
            ],
        };

        let objects = vec![obj];
        let layout = lay_out_sections(&objects, DEFAULT_BASE_ADDR);
        let mut resolver = SymbolResolver::new();
        resolver
            .add_object(0, &objects[0], &layout.section_addrs[0])
            .unwrap();

        // resolve() should succeed, with _optional_func at address 0.
        let addrs = resolver.resolve().unwrap();
        assert_eq!(addrs["_optional_func"], 0);
    }

    // =======================================================================
    // Dead code stripping tests
    // =======================================================================

    #[test]
    fn test_dead_strip_basic() {
        // Object with three text sections:
        // - Section 0: _main (referenced as entry)
        // - Section 1: _helper (referenced by _main via relocation)
        // - Section 2: _unused (unreferenced)
        let obj = ParsedObject {
            cputype: CPU_TYPE_ARM64,
            cpusubtype: CPU_SUBTYPE_ARM64_ALL,
            flags: 0,
            sections: vec![
                ParsedSection {
                    name: "__text".into(),
                    segment: "__TEXT".into(),
                    data: vec![0x94, 0x00, 0x00, 0x00], // BL placeholder
                    addr: 0,
                    align: 2,
                    flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS,
                    relocations: vec![Relocation::branch26(0, 2)], // refs _helper (sym idx 2)
                    vmsize: 4,
                },
                ParsedSection {
                    name: "__text".into(),
                    segment: "__TEXT".into(),
                    data: vec![0xC0, 0x03, 0x5F, 0xD6], // RET
                    addr: 4,
                    align: 2,
                    flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS,
                    relocations: vec![],
                    vmsize: 4,
                },
                ParsedSection {
                    name: "__text".into(),
                    segment: "__TEXT".into(),
                    data: vec![0xC0, 0x03, 0x5F, 0xD6], // RET
                    addr: 8,
                    align: 2,
                    flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS,
                    relocations: vec![],
                    vmsize: 4,
                },
            ],
            symbols: vec![
                ParsedSymbol {
                    name: "_main".into(),
                    n_type: N_SECT | N_EXT,
                    section: 1, // section ordinal 1 (first section)
                    desc: 0,
                    value: 0,
                },
                ParsedSymbol {
                    name: "_unused".into(),
                    n_type: N_SECT | N_EXT,
                    section: 3, // section ordinal 3 (third section)
                    desc: 0,
                    value: 0,
                },
                ParsedSymbol {
                    name: "_helper".into(),
                    n_type: N_SECT | N_EXT,
                    section: 2, // section ordinal 2 (second section)
                    desc: 0,
                    value: 0,
                },
            ],
        };

        let stripped = dead_strip_sections(&[obj], "_main");
        assert_eq!(stripped.len(), 1);
        // _unused's section should be removed (it was the third section).
        // We should have 2 sections left: _main's and _helper's.
        assert_eq!(stripped[0].sections.len(), 2);
    }

    #[test]
    fn test_dead_strip_middle_section_remaps_n_sect() {
        // RANK 7b: stripping a MIDDLE section re-indexes the surviving sections,
        // so each kept symbol's `section` (n_sect) ordinal must be remapped to
        // its section's NEW index. Here:
        //   - section 1: _main  (entry, references _helper)
        //   - section 2: _dead  (unreferenced -> stripped)
        //   - section 3: _helper (referenced by _main's reloc)
        // After strip, sections [1,3] survive and re-index to ordinals [1,2];
        // the kept _helper symbol must be remapped from section 3 to section 2,
        // and the symbol defined in the stripped section must be dropped.
        let obj = ParsedObject {
            cputype: CPU_TYPE_ARM64,
            cpusubtype: CPU_SUBTYPE_ARM64_ALL,
            flags: 0,
            sections: vec![
                ParsedSection {
                    name: "__text".into(),
                    segment: "__TEXT".into(),
                    data: vec![0x94, 0x00, 0x00, 0x00], // BL placeholder
                    addr: 0,
                    align: 2,
                    flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS,
                    relocations: vec![Relocation::branch26(0, 2)], // refs _helper (sym idx 2)
                    vmsize: 4,
                },
                ParsedSection {
                    name: "__text".into(),
                    segment: "__TEXT".into(),
                    data: vec![0xC0, 0x03, 0x5F, 0xD6], // RET (dead)
                    addr: 4,
                    align: 2,
                    flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS,
                    relocations: vec![],
                    vmsize: 4,
                },
                ParsedSection {
                    name: "__text".into(),
                    segment: "__TEXT".into(),
                    data: vec![0xC0, 0x03, 0x5F, 0xD6], // RET (_helper)
                    addr: 8,
                    align: 2,
                    flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS,
                    relocations: vec![],
                    vmsize: 4,
                },
            ],
            // Symbol order matches test_dead_strip_basic: _helper is at symbol
            // index 2, the target of _main's branch26(0, 2) relocation.
            symbols: vec![
                ParsedSymbol {
                    name: "_main".into(),
                    n_type: N_SECT | N_EXT,
                    section: 1,
                    desc: 0,
                    value: 0,
                },
                ParsedSymbol {
                    name: "_dead".into(),
                    n_type: N_SECT | N_EXT,
                    section: 2, // middle section -> stripped
                    desc: 0,
                    value: 0,
                },
                ParsedSymbol {
                    name: "_helper".into(),
                    n_type: N_SECT | N_EXT,
                    section: 3, // third section ordinal
                    desc: 0,
                    value: 0,
                },
            ],
        };

        let stripped = dead_strip_sections(&[obj], "_main");
        assert_eq!(stripped.len(), 1);
        // The middle (dead) section is removed; _main + _helper sections remain.
        assert_eq!(stripped[0].sections.len(), 2);

        let syms = &stripped[0].symbols;
        // _main stays at ordinal 1.
        let main_sym = syms.iter().find(|s| s.name == "_main").unwrap();
        assert_eq!(main_sym.section, 1);
        // _helper is remapped from section 3 to the new ordinal 2 (NOT stale 3).
        let helper_sym = syms.iter().find(|s| s.name == "_helper").unwrap();
        assert_eq!(helper_sym.section, 2);
        // The symbol whose defining section was stripped is dropped.
        assert!(syms.iter().all(|s| s.name != "_dead"));
        // No surviving symbol carries an ordinal past the kept section count.
        assert!(
            syms.iter()
                .all(|s| (s.section as usize) <= stripped[0].sections.len())
        );
    }

    #[test]
    fn test_dead_strip_keeps_data() {
        // Data section without any symbol reference should still be kept.
        let obj = ParsedObject {
            cputype: CPU_TYPE_ARM64,
            cpusubtype: CPU_SUBTYPE_ARM64_ALL,
            flags: 0,
            sections: vec![
                ParsedSection {
                    name: "__text".into(),
                    segment: "__TEXT".into(),
                    data: vec![0xC0, 0x03, 0x5F, 0xD6],
                    addr: 0,
                    align: 2,
                    flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS,
                    relocations: vec![],
                    vmsize: 4,
                },
                ParsedSection {
                    name: "__data".into(),
                    segment: "__DATA".into(),
                    data: vec![0xDE, 0xAD, 0xBE, 0xEF],
                    addr: 0,
                    align: 2,
                    flags: S_REGULAR,
                    relocations: vec![],
                    vmsize: 4,
                },
            ],
            symbols: vec![ParsedSymbol {
                name: "_main".into(),
                n_type: N_SECT | N_EXT,
                section: 1,
                desc: 0,
                value: 0,
            }],
        };

        let stripped = dead_strip_sections(&[obj], "_main");
        // Both sections should be kept (data is always preserved).
        assert_eq!(stripped[0].sections.len(), 2);
    }

    // =======================================================================
    // BSS and section method tests
    // =======================================================================

    #[test]
    fn test_bss_section_layout() {
        // Object with text, data, and bss sections.
        let obj = ParsedObject {
            cputype: CPU_TYPE_ARM64,
            cpusubtype: CPU_SUBTYPE_ARM64_ALL,
            flags: 0,
            sections: vec![
                ParsedSection {
                    name: "__text".into(),
                    segment: "__TEXT".into(),
                    data: vec![0xC0, 0x03, 0x5F, 0xD6],
                    addr: 0,
                    align: 2,
                    flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS,
                    relocations: vec![],
                    vmsize: 4,
                },
                ParsedSection {
                    name: "__data".into(),
                    segment: "__DATA".into(),
                    data: vec![0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08],
                    addr: 0,
                    align: 3, // 8-byte aligned
                    flags: S_REGULAR,
                    relocations: vec![],
                    vmsize: 8,
                },
                ParsedSection {
                    name: "__bss".into(),
                    segment: "__DATA".into(),
                    data: vec![], // zerofill: no file data
                    addr: 0,
                    align: 3,
                    flags: S_ZEROFILL,
                    relocations: vec![],
                    vmsize: 64, // 64 bytes of zero-initialized memory
                },
            ],
            symbols: vec![ParsedSymbol {
                name: "_main".into(),
                n_type: N_SECT | N_EXT,
                section: 1,
                desc: 0,
                value: 0,
            }],
        };

        let layout = lay_out_sections(&[obj], DEFAULT_BASE_ADDR);

        // Text section at base.
        assert_eq!(layout.section_addrs[0][0], DEFAULT_BASE_ADDR);
        // Data section after text (page-aligned gap).
        let text_aligned = align_to(4, PAGE_SIZE);
        let data_vmaddr = DEFAULT_BASE_ADDR + text_aligned;
        assert_eq!(layout.section_addrs[0][1], data_vmaddr);
        // BSS section after data.
        let bss_addr = layout.section_addrs[0][2];
        assert!(bss_addr >= data_vmaddr + 8, "BSS should be after data");
    }

    #[test]
    fn test_parsed_section_methods() {
        let regular = ParsedSection {
            name: "__text".into(),
            segment: "__TEXT".into(),
            data: vec![0u8; 32],
            addr: 0,
            align: 2,
            flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS,
            relocations: vec![],
            vmsize: 32,
        };
        assert_eq!(regular.section_type(), S_REGULAR);
        assert!(!regular.is_zerofill());
        assert_eq!(regular.effective_size(), 32);

        let bss = ParsedSection {
            name: "__bss".into(),
            segment: "__DATA".into(),
            data: vec![],
            addr: 0,
            align: 3,
            flags: S_ZEROFILL,
            relocations: vec![],
            vmsize: 256,
        };
        assert_eq!(bss.section_type(), S_ZEROFILL);
        assert!(bss.is_zerofill());
        assert_eq!(bss.effective_size(), 256);
    }

    #[test]
    fn test_parsed_symbol_weak_methods() {
        let strong_def = ParsedSymbol {
            name: "_foo".into(),
            n_type: N_SECT | N_EXT,
            section: 1,
            desc: 0,
            value: 0,
        };
        assert!(!strong_def.is_weak_def());
        assert!(!strong_def.is_weak_ref());
        assert!(!strong_def.is_no_dead_strip());

        let weak_def = ParsedSymbol {
            name: "_bar".into(),
            n_type: N_SECT | N_EXT,
            section: 1,
            desc: N_WEAK_DEF,
            value: 0,
        };
        assert!(weak_def.is_weak_def());
        assert!(!weak_def.is_weak_ref());

        let weak_ref = ParsedSymbol {
            name: "_baz".into(),
            n_type: N_UNDF | N_EXT,
            section: 0,
            desc: N_WEAK_REF,
            value: 0,
        };
        assert!(!weak_ref.is_weak_def());
        assert!(weak_ref.is_weak_ref());

        let no_dead_strip = ParsedSymbol {
            name: "_keep".into(),
            n_type: N_SECT | N_EXT,
            section: 1,
            desc: N_NO_DEAD_STRIP,
            value: 0,
        };
        assert!(no_dead_strip.is_no_dead_strip());
    }
}
