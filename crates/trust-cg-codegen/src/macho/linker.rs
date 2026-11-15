// trust-cg-codegen/macho/linker.rs - Mach-O linker: read .o files, resolve symbols, emit executables
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Minimal Mach-O linker for Trust Codegen-generated object files.
//!
//! Reads Mach-O MH_OBJECT (.o) files, resolves symbols across objects, applies
//! relocations (branches, page addresses, GOT and TLV-pointer loads, absolute
//! pointers, and subtractor pairs), and emits an ad-hoc-signed Mach-O
//! MH_EXECUTE ([`link`], [`link_with_dylibs`]) or MH_DYLIB ([`link_dylib`])
//! image whose pointers dyld slides or binds through chained fixups.
//!
//! This is a limited AArch64 macOS linker, not a general system-linker
//! replacement. Layout reserves dynamic stubs, GOT slots and TLV pointer slots
//! before resolving addresses, then places aligned zero-fill storage after
//! file-backed data. Executables use dyld, including when no external dylib
//! symbols are imported. A dylib exports its external, non-private
//! definitions through the exports trie and binds its own references to its
//! strong definitions directly (no interposition, no re-exports). A dylib's
//! default-visibility weak definitions are exported `[weak-def]` and every
//! reference to one binds through dyld's weak-definition lookup, so dyld
//! coalesces them with an earlier image's definition of the same name. An
//! executable exports nothing, so its own weak definitions are resolved
//! statically and take no part in that coalescing. The symbol table stays
//! empty, and `S_ATTR_DEBUG` input (`__LD,__compact_unwind`, `__DWARF`) is
//! not loaded, so images carry no unwind or debug tables.
//!
//! # Layout of emitted images
//!
//! A dylib has the same segments without `__PAGEZERO`, based at 0.
//!
//! ```text
//! __PAGEZERO    vmaddr=0x0            vmsize=0x1_0000_0000  (no file data)
//! __TEXT        vmaddr=0x1_0000_0000  (rx) headers, __text, optional __stubs
//! __DATA_CONST  optional (rw, SG_READ_ONLY) __got, __thread_ptrs, __const
//!               (input `__DATA,__const` and `__DATA_CONST` data; dyld makes
//!               the segment read-only once its fixups are applied)
//! __DATA        optional (rw) __data, __thread_vars, __thread_data,
//!               zero-fill __thread_bss, then other zero-fill storage
//! __LINKEDIT    (r) chained fixups, exports trie and code signature
//! ```
//!
//! GOT and TLV pointer slots are never relaxed into direct addressing: every
//! `ARM64_RELOC_GOT_LOAD_*`/`ARM64_RELOC_TLVP_LOAD_*` pair keeps its `LDR` and
//! loads a slot that dyld binds (imports) or rebases (image definitions).

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

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

/// Dynamic shared library file type.
const MH_DYLIB: u32 = 0x6;

/// The dylib re-exports no other dylib.
const MH_NO_REEXPORTED_DYLIBS: u32 = 0x0010_0000;

/// Standard flags for MH_DYLIB output (dylibs are never PIE-flagged).
const MH_DYLIB_FLAGS: u32 = MH_NOUNDEFS | MH_DYLDLINK | MH_TWOLEVEL | MH_NO_REEXPORTED_DYLIBS;

/// LC_ID_DYLIB load command type (a dylib's own install name).
const LC_ID_DYLIB: u32 = 0x0D;

/// Exports-trie terminal flags: a regular symbol or a TLV descriptor.
const EXPORT_SYMBOL_FLAGS_KIND_REGULAR: u64 = 0x00;
const EXPORT_SYMBOL_FLAGS_KIND_THREAD_LOCAL: u64 = 0x01;

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

/// The image contains thread-local variable descriptors; dyld initializes
/// `__thread_vars` only when this header flag is set.
const MH_HAS_TLV_DESCRIPTORS: u32 = 0x0080_0000;

/// dyld makes this segment read-only after applying its fixups (`__DATA_CONST`).
const SG_READ_ONLY: u32 = 0x10;

/// Header flag: the image exports weak definitions dyld may coalesce.
const MH_WEAK_DEFINES: u32 = 0x0000_8000;

/// Header flag: the image binds references through dyld's weak-definition
/// lookup.
const MH_BINDS_TO_WEAK: u32 = 0x0001_0000;

/// Exports-trie flag: a weak definition dyld may coalesce.
const EXPORT_SYMBOL_FLAGS_WEAK_DEFINITION: u64 = 0x04;

/// `BIND_SPECIAL_DYLIB_WEAK_LOOKUP` (-3) in a chained import's 8-bit
/// library-ordinal field: dyld binds the first definition of the name in load
/// order, preferring a strong one, among images with `MH_WEAK_DEFINES`.
const BIND_SPECIAL_DYLIB_WEAK_LOOKUP_ORDINAL: u32 = 0xFD;

/// Section attribute: debug content that the static linker does not load.
const S_ATTR_DEBUG: u32 = 0x0200_0000;

/// Zero-fill section type used for large (>4 GiB capable) zero-fill storage.
const S_GB_ZEROFILL: u32 = 0x0C;

// Section types whose meaning depends on linker processing this linker does
// not implement (indirect symbol tables, initializers, interposing, DTrace).
// Concatenating them as plain data would silently drop that meaning.
const S_LAZY_SYMBOL_POINTERS: u32 = 0x07;
const S_MOD_INIT_FUNC_POINTERS: u32 = 0x09;
const S_MOD_TERM_FUNC_POINTERS: u32 = 0x0A;
const S_INTERPOSING: u32 = 0x0D;
const S_DTRACE_DOF: u32 = 0x0F;
const S_LAZY_DYLIB_SYMBOL_POINTERS: u32 = 0x10;
const S_THREAD_LOCAL_INIT_FUNCTION_POINTERS: u32 = 0x15;
const S_INIT_FUNC_OFFSETS: u32 = 0x16;

/// Darwin TLV descriptor `{thunk, key, offset}` size and field offsets.
const TLV_DESCRIPTOR_SIZE: u64 = 24;
const TLV_DESCRIPTOR_KEY_OFFSET: u64 = 8;
const TLV_DESCRIPTOR_OFFSET_FIELD: u64 = 16;

/// The dyld thunk every TLV descriptor binds before dyld installs its getter.
const TLV_BOOTSTRAP_SYMBOL: &str = "__tlv_bootstrap";

/// dyld copies TLV templates into malloc'd storage, which guarantees 16-byte
/// alignment; stricter template alignment cannot be honored per thread.
const TLS_TEMPLATE_MAX_ALIGNMENT: u64 = 16;

/// `dyld_chained_ptr_64_rebase.target` holds a 36-bit unslid vmaddr.
const DYLD_CHAINED_PTR_64_TARGET_LIMIT: u64 = 1 << 36;

/// `dyld_chained_ptr_64_bind.ordinal` holds a 24-bit import ordinal.
const DYLD_CHAINED_PTR_64_BIND_ORDINAL_LIMIT: usize = 1 << 24;

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
    #[error("Mach-O layout overflow while computing {0}")]
    LayoutOverflow(&'static str),

    #[error("section '{section}' has unrepresentable alignment exponent {exponent}")]
    InvalidAlignment { section: String, exponent: u32 },

    #[error("could not reserve linked image storage: {0}")]
    ImageAllocation(#[source] std::collections::TryReserveError),

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

    /// `ARM64_RELOC_UNSIGNED` with `r_pcrel=1`. It is not a valid arm64
    /// Mach-O relocation (the platform linker rejects it as unsupported);
    /// pc-relative data differences are `SUBTRACTOR`/`UNSIGNED` pairs.
    #[error(
        "pc-relative ARM64_RELOC_UNSIGNED at offset {offset:#x} is not a valid arm64 Mach-O relocation; use a SUBTRACTOR/UNSIGNED pair"
    )]
    PcRelativeUnsigned { offset: u32 },

    /// The instruction at a relocation site is not the form its kind patches.
    #[error(
        "relocation {kind:?} at offset {offset:#x} does not name a matching instruction ({instruction:#010x})"
    )]
    RelocationInstructionMismatch {
        kind: AArch64RelocKind,
        offset: u32,
        instruction: u32,
    },

    /// An absolute pointer to an image address needs a slide fixup that the
    /// relocation site cannot carry (a 32-bit field or a `__TEXT` location).
    #[error("absolute pointer at {section}+{offset:#x} cannot be slid by dyld: {detail}")]
    UnslidablePointer {
        section: String,
        offset: u32,
        detail: &'static str,
    },

    /// A PC-relative or difference relocation names a symbol that lives in a
    /// dylib. Only branches (via stubs), GOT/TLV slots and 64-bit data
    /// pointers (dyld binds) may name an import.
    #[error("relocation {kind:?} cannot address dylib import '{symbol}' directly")]
    DirectImportReference {
        kind: AArch64RelocKind,
        symbol: String,
    },

    /// A thread-local variable is referenced through a non-TLV relocation, a
    /// TLVP relocation names a non-TLV symbol, or a descriptor is malformed.
    #[error("thread-local variable misuse: {0}")]
    ThreadLocal(String),

    /// A relocation targets a section that is not loaded into the image.
    #[error("relocation targets unloaded debug section '{0}'")]
    UnloadedSectionReference(String),

    /// An input section type needs linker processing that is not implemented.
    #[error("unsupported input section type {section_type:#x} for section '{section}'")]
    UnsupportedSectionType { section: String, section_type: u32 },

    /// A direct page reference names a dylib weak definition that dyld may
    /// coalesce with another image's: the patched instruction would keep this
    /// image's copy. Such a definition must be addressed through the GOT.
    #[error(
        "relocation {kind:?} addresses coalescable weak definition '{symbol}' directly; \
         dyld may bind it to another image's definition, so it must be reached through the GOT"
    )]
    DirectWeakDefinitionReference {
        kind: AArch64RelocKind,
        symbol: String,
    },

    /// A dylib would export a symbol whose cross-image meaning this linker
    /// does not implement.
    #[error("dylib cannot export '{symbol}': {detail}")]
    UnsupportedDylibExport {
        symbol: String,
        detail: &'static str,
    },

    /// A dyld chained fixup cannot be represented as DYLD_CHAINED_PTR_64.
    #[error("unrepresentable chained fixup at {address:#x}: {detail}")]
    ChainedFixup { address: u64, detail: String },

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

    /// The emitted image's ad-hoc code signature failed the independent
    /// verifier ([`super::codesign::verify_ad_hoc_signature`]). No image is
    /// returned: Apple Silicon kills arm64 code whose signature is missing or
    /// invalid.
    #[error("emitted image failed its ad-hoc code-signature self-check: {0}")]
    CodeSignatureSelfCheck(#[source] super::codesign::CodeSignatureError),

    /// The emitted image's signature verifies but is not the one this linker
    /// writes.
    #[error("emitted image's code signature departs from the linker contract: {0}")]
    CodeSignatureContract(String),
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

    /// Returns true for every zero-fill section type (`S_ZEROFILL`,
    /// `S_GB_ZEROFILL` and the thread-local `S_THREAD_LOCAL_ZEROFILL`). These
    /// have no file bytes; their size is [`Self::vmsize`].
    pub fn is_zerofill(&self) -> bool {
        matches!(
            self.section_type(),
            S_ZEROFILL | S_GB_ZEROFILL | S_THREAD_LOCAL_ZEROFILL
        )
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

/// A symbol name that shares its bytes with the other names read from the
/// same string-table run.
///
/// A Mach-O string table may tail-merge names (`_S1_A` is the tail of
/// `_S2_S1_A`), and any number of symbols may name one string. A copy per
/// symbol therefore costs memory quadratic in the input. The parser instead
/// keeps each referenced run (the bytes up to a terminator) once, and every
/// name is a tail of its run, so all names together cost the string table's
/// size plus a fixed amount per symbol. Cloning bumps a reference count.
#[derive(Clone)]
pub struct SymbolName {
    run: Arc<str>,
    start: usize,
}

impl SymbolName {
    /// The name `run[start..]`, which must start on a character boundary.
    fn tail_of(run: &Arc<str>, start: usize) -> Self {
        debug_assert!(run.is_char_boundary(start));
        Self {
            run: Arc::clone(run),
            start,
        }
    }

    /// The name as a string slice.
    pub fn as_str(&self) -> &str {
        &self.run[self.start..]
    }
}

impl std::ops::Deref for SymbolName {
    type Target = str;

    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<str> for SymbolName {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl std::borrow::Borrow<str> for SymbolName {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl PartialEq for SymbolName {
    fn eq(&self, other: &Self) -> bool {
        self.as_str() == other.as_str()
    }
}

impl Eq for SymbolName {}

impl std::hash::Hash for SymbolName {
    // Hashes exactly as `str` does, as `Borrow<str>` requires.
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl PartialOrd for SymbolName {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SymbolName {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl PartialEq<str> for SymbolName {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<&str> for SymbolName {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

impl PartialEq<String> for SymbolName {
    fn eq(&self, other: &String) -> bool {
        self.as_str() == other.as_str()
    }
}

impl PartialEq<SymbolName> for str {
    fn eq(&self, other: &SymbolName) -> bool {
        self == other.as_str()
    }
}

impl PartialEq<SymbolName> for &str {
    fn eq(&self, other: &SymbolName) -> bool {
        *self == other.as_str()
    }
}

impl PartialEq<SymbolName> for String {
    fn eq(&self, other: &SymbolName) -> bool {
        self.as_str() == other.as_str()
    }
}

impl std::fmt::Display for SymbolName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.as_str(), f)
    }
}

impl std::fmt::Debug for SymbolName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self.as_str(), f)
    }
}

impl From<&str> for SymbolName {
    fn from(name: &str) -> Self {
        Self {
            run: Arc::from(name),
            start: 0,
        }
    }
}

impl From<String> for SymbolName {
    fn from(name: String) -> Self {
        Self {
            run: Arc::from(name),
            start: 0,
        }
    }
}

impl From<&String> for SymbolName {
    fn from(name: &String) -> Self {
        Self::from(name.as_str())
    }
}

impl From<SymbolName> for String {
    fn from(name: SymbolName) -> Self {
        name.as_str().to_owned()
    }
}

/// One LC_SYMTAB string table's names, read without copying or rescanning
/// shared bytes: the terminators are found once, and each referenced run is
/// checked once and kept once (`SymbolName`).
struct StringTableNames<'a> {
    strings: &'a [u8],
    /// Offsets of every NUL byte, ascending.
    terminators: Vec<u32>,
    /// For each referenced run (by terminator index): the start of its
    /// longest UTF-8 tail within the run, and that tail.
    runs: HashMap<usize, (usize, Arc<str>)>,
}

impl<'a> StringTableNames<'a> {
    fn new(strings: &'a [u8]) -> Self {
        let terminators = strings
            .iter()
            .enumerate()
            .filter(|&(_, &byte)| byte == 0)
            // The table's size is a u32 field, so every offset fits.
            .map(|(offset, _)| offset as u32)
            .collect();
        Self {
            strings,
            terminators,
            runs: HashMap::new(),
        }
    }

    /// The name at string index `strx`: the bytes from `strx` to the next
    /// NUL, which must be UTF-8.
    fn name(&mut self, strx: usize) -> Result<SymbolName, &'static str> {
        if strx > self.strings.len() {
            return Err("symbol name lies outside the string table");
        }
        let index = self
            .terminators
            .partition_point(|&terminator| (terminator as usize) < strx);
        let end = *self
            .terminators
            .get(index)
            .ok_or("symbol name has no terminator inside the string table")?
            as usize;
        let run_start = match index {
            0 => 0,
            _ => self.terminators[index - 1] as usize + 1,
        };
        let strings = self.strings;
        let (valid_from, tail) = self
            .runs
            .entry(index)
            .or_insert_with(|| longest_utf8_tail(&strings[run_start..end]));
        // A tail of the run is UTF-8 exactly when it starts inside the run's
        // longest UTF-8 tail, on a character boundary.
        let start = (strx - run_start)
            .checked_sub(*valid_from)
            .filter(|&start| tail.is_char_boundary(start))
            .ok_or("symbol name is not UTF-8")?;
        Ok(SymbolName::tail_of(tail, start))
    }
}

/// The start of the longest suffix of `run` that is UTF-8, and that suffix.
/// Linear in `run`: no suffix starting at or before an invalid sequence is
/// UTF-8, so the scan resumes after each one.
fn longest_utf8_tail(run: &[u8]) -> (usize, Arc<str>) {
    let mut from = 0;
    loop {
        match std::str::from_utf8(&run[from..]) {
            Ok(tail) => return (from, Arc::from(tail)),
            // A sequence cut off by the end of the run leaves only the
            // empty tail.
            Err(error) => {
                from = match error.error_len() {
                    Some(length) => from + error.valid_up_to() + length,
                    None => run.len(),
                };
            }
        }
    }
}

/// A parsed symbol from a Mach-O object file.
#[derive(Debug, Clone)]
pub struct ParsedSymbol {
    /// Symbol name from the string table, sharing its bytes with the other
    /// names of the same string-table run.
    pub name: SymbolName,
    /// n_type field from nlist_64.
    pub n_type: u8,
    /// Section number (1-based, 0 = undefined).
    pub section: u8,
    /// n_desc field.
    pub desc: u16,
    /// Raw n_value: an address in the input object's section address space.
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
#[cfg(test)]
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
        // File bytes owned by all sections, and by all relocation tables.
        let mut section_file_bytes = 0usize;
        let mut relocation_table_bytes = 0usize;
        // Whether an LC_SYMTAB has been read.
        let mut seen_symtab = false;

        for _ in 0..ncmds {
            if offset + 8 > lc_end || offset + 8 > data.len() {
                return Err(LinkerError::LoadCommandOverflow { offset });
            }

            let cmd = read_u32(data, offset);
            let cmdsize = read_u32(data, offset + 4) as usize;

            // A command must also end inside the `sizeofcmds` area it was
            // found in, or its body would be read from section data.
            if cmdsize < 8 || offset + cmdsize > data.len() || offset + cmdsize > lc_end {
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
                    // Every section_64 header lies inside this command. They
                    // used to be read up to the end of the input, so a
                    // command whose `nsects` overran its `cmdsize` took later
                    // load commands (or section data) as section headers.
                    let headers_fit = (nsects as usize)
                        .checked_mul(SECTION_64_SIZE as usize)
                        .and_then(|size| size.checked_add(SEGMENT_COMMAND_64_SIZE as usize))
                        .is_some_and(|size| size <= cmdsize);
                    if !headers_fit {
                        return Err(LinkerError::MalformedInput {
                            file: "LC_SEGMENT_64".into(),
                            detail: format!(
                                "{nsects} section headers do not fit in the command's \
                                 {cmdsize}-byte cmdsize"
                            ),
                        });
                    }

                    // Parse each section_64 header.
                    let mut sec_offset = offset + SEGMENT_COMMAND_64_SIZE as usize;
                    for _ in 0..nsects {
                        let sec_size = SECTION_64_SIZE as usize;

                        let sec_name = read_name16(data, sec_offset);
                        let seg_name = read_name16(data, sec_offset + 16);
                        let sec_addr = read_u64(data, sec_offset + 32);
                        let sec_data_size = read_u64(data, sec_offset + 40) as usize;
                        let sec_file_offset = read_u32(data, sec_offset + 48) as usize;
                        let sec_align = read_u32(data, sec_offset + 52);
                        let sec_reloff = read_u32(data, sec_offset + 56) as usize;
                        let sec_nreloc = read_u32(data, sec_offset + 60);
                        let sec_flags = read_u32(data, sec_offset + 64);

                        // Read section data. Zero-fill sections own no file
                        // bytes: their offset field is conventionally 0, so
                        // reading `size` bytes there would copy the Mach-O header
                        // into the section. Keep them empty and carry the size in
                        // `vmsize` without allocating it. Every other section's
                        // bytes must lie inside the input: one that ran past the
                        // end used to be silently zero-filled (a truncated
                        // `__text` parsed as zeros), and each section could copy
                        // or zero-fill up to the whole input, so memory grew with
                        // the square of the input. Distinct sections own disjoint
                        // file bytes, so together they cannot exceed the input.
                        // Offset and size are attacker-controlled (u32/u64), so
                        // every sum is checked.
                        let zerofill_type = matches!(
                            sec_flags & SECTION_TYPE_MASK,
                            S_ZEROFILL | S_GB_ZEROFILL | S_THREAD_LOCAL_ZEROFILL
                        );
                        let malformed = |detail: String| LinkerError::MalformedInput {
                            file: "LC_SEGMENT_64".into(),
                            detail: format!("section {sec_name}: {detail}"),
                        };
                        let sec_data = if zerofill_type || sec_data_size == 0 {
                            Vec::new()
                        } else {
                            let bytes = sec_file_offset
                                .checked_add(sec_data_size)
                                .and_then(|end| data.get(sec_file_offset..end))
                                .ok_or_else(|| {
                                    malformed(format!(
                                        "{sec_data_size} bytes of file data at offset \
                                         {sec_file_offset} run past the end of the \
                                         {}-byte input",
                                        data.len()
                                    ))
                                })?;
                            section_file_bytes += sec_data_size;
                            if section_file_bytes > data.len() {
                                return Err(malformed(format!(
                                    "sections claim {section_file_bytes} bytes of file \
                                     data, more than the {}-byte input",
                                    data.len()
                                )));
                            }
                            bytes.to_vec()
                        };

                        // Read relocations for this section. Validate the whole
                        // table range before walking the attacker-supplied count,
                        // as LC_SYMTAB does: an entry past the input used to be
                        // skipped, so a truncated table silently lost relocations
                        // and a count near u32::MAX spun over billions of
                        // nonexistent entries (a 327-byte input took 10 s under
                        // the fuzz_macho_fixup libFuzzer target). A section with
                        // no relocations carries no meaningful table offset.
                        // Tables of distinct sections are disjoint too, so all of
                        // them together fit in the input.
                        let reloc_size = RELOCATION_INFO_SIZE as usize;
                        let reloc_table: &[u8] = if sec_nreloc == 0 {
                            &[]
                        } else {
                            let table = (sec_nreloc as usize)
                                .checked_mul(reloc_size)
                                .and_then(|size| sec_reloff.checked_add(size))
                                .and_then(|end| data.get(sec_reloff..end))
                                .ok_or_else(|| {
                                    malformed(format!(
                                        "relocation table of {sec_nreloc} entries at offset \
                                         {sec_reloff} exceeds input"
                                    ))
                                })?;
                            relocation_table_bytes += table.len();
                            if relocation_table_bytes > data.len() {
                                return Err(malformed(format!(
                                    "relocation tables total {relocation_table_bytes} bytes, \
                                     more than the {}-byte input",
                                    data.len()
                                )));
                            }
                            table
                        };
                        let mut relocations = Vec::with_capacity(sec_nreloc as usize);
                        for reloc_bytes in reloc_table.as_chunks::<8>().0 {
                            match decode_relocation(reloc_bytes) {
                                Ok(reloc) => relocations.push(reloc),
                                Err(e) => {
                                    return Err(LinkerError::RelocDecode {
                                        section: sec_name.clone(),
                                        detail: e.to_string(),
                                    });
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
                    let strsize = read_u32(data, offset + 20) as usize;
                    let malformed = |detail: &str| LinkerError::MalformedInput {
                        file: "LC_SYMTAB".into(),
                        detail: detail.into(),
                    };
                    // Validate complete ranges before walking the attacker-
                    // supplied count. Truncated tables must not silently lose
                    // symbols or spin over billions of nonexistent entries.
                    let sym_end = nsyms
                        .checked_mul(NLIST_64_SIZE as usize)
                        .and_then(|size| symoff.checked_add(size))
                        .ok_or_else(|| malformed("symbol table range overflow"))?;
                    let table = data
                        .get(symoff..sym_end)
                        .ok_or_else(|| malformed("symbol table exceeds input"))?;
                    let str_end = stroff
                        .checked_add(strsize)
                        .ok_or_else(|| malformed("string table range overflow"))?;
                    let strings = data
                        .get(stroff..str_end)
                        .ok_or_else(|| malformed("string table exceeds input"))?;
                    // An object has one symbol table. Each LC_SYMTAB indexes
                    // its whole string table once, so a command list repeating
                    // it would cost time quadratic in the input.
                    if seen_symtab {
                        return Err(malformed("more than one LC_SYMTAB"));
                    }
                    seen_symtab = true;
                    let mut names = StringTableNames::new(strings);
                    for nlist_bytes in table.as_chunks::<16>().0 {
                        let nlist = NList64::decode(nlist_bytes);
                        // Lossy decoding could merge distinct byte names into
                        // one symbol identity. This linker admits UTF-8 names.
                        let name = names.name(nlist.strx as usize).map_err(malformed)?;
                        symbols.push(ParsedSymbol {
                            name,
                            n_type: nlist.typ,
                            section: nlist.sect,
                            desc: nlist.desc,
                            value: nlist.value,
                        });
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
    defined: HashMap<SymbolName, ResolvedSymbol>,
    /// Map from (object index, symbol table index) to defined symbol address.
    ///
    /// Mach-O `r_extern=1` relocations name a symbol table index. That symbol
    /// may be local, so local defined symbols must remain object-scoped instead
    /// of being published through the global name map.
    defined_by_index: HashMap<(usize, usize), u64>,
    /// List of (object_index, symbol_index, name) for undefined references.
    undefined: Vec<(usize, usize, SymbolName)>,
    /// Names with at least one strong undefined reference. A weak reference in
    /// another object must never make these required definitions optional.
    strong_refs: HashSet<SymbolName>,
}

impl SymbolResolver {
    /// Create a new empty resolver.
    pub fn new() -> Self {
        Self {
            defined: HashMap::new(),
            defined_by_index: HashMap::new(),
            undefined: Vec::new(),
            strong_refs: HashSet::new(),
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
                let invalid = || LinkerError::MalformedInput {
                    file: format!("object {obj_index}"),
                    detail: format!(
                        "symbol '{}' has an invalid section or section-relative value",
                        sym.name
                    ),
                };
                let sec_idx = usize::from(sym.section)
                    .checked_sub(1)
                    .ok_or_else(invalid)?;
                let section = obj.sections.get(sec_idx).ok_or_else(invalid)?;
                let base = section_addrs.get(sec_idx).ok_or_else(invalid)?;
                let offset = sym
                    .value
                    .checked_sub(section.addr)
                    .filter(|offset| *offset <= section.effective_size())
                    .ok_or_else(invalid)?;
                let address = layout_add(*base, offset, "symbol address")?;
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
                            name: sym.name.to_string(),
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
                // Null resolution is allowed only when every reference to
                // this name is weak, independent of object order.
                if !sym.is_weak_ref() {
                    self.strong_refs.insert(sym.name.clone());
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
            result.insert(name.to_string(), sym.address);
        }

        // Verify all undefined symbols have definitions.
        for (_obj_idx, _sym_idx, name) in &self.undefined {
            if !result.contains_key(name.as_str()) {
                if !self.strong_refs.contains(name) {
                    // Exclusively weak references resolve to 0 if not defined.
                    result.insert(name.to_string(), 0);
                } else {
                    return Err(LinkerError::UndefinedSymbol(name.to_string()));
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
// Section classification and layout
// ---------------------------------------------------------------------------

/// Where an input section is placed in the linked image.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SectionClass {
    /// `__TEXT` input (code, literals, `__eh_frame`), mapped into `__TEXT,__text`.
    Text,
    /// Other file-backed input, merged into `__DATA,__data`.
    Data,
    /// `__DATA,__const` and `__DATA_CONST` input: data written only by dyld's
    /// fixups, merged into `__DATA_CONST,__const`, which dyld makes read-only
    /// once the fixups are applied (the Mach-O equivalent of ELF RELRO).
    ConstData,
    /// `S_THREAD_LOCAL_VARIABLES` descriptors, merged into `__DATA,__thread_vars`.
    ThreadVars,
    /// `S_THREAD_LOCAL_REGULAR` initial-value templates (`__DATA,__thread_data`).
    ThreadData,
    /// `S_THREAD_LOCAL_ZEROFILL` zero templates (`__DATA,__thread_bss`).
    ThreadBss,
    /// Ordinary zero-fill storage, placed after every file-backed byte.
    ZeroFill,
    /// `S_ATTR_DEBUG` input (`__LD,__compact_unwind`, `__DWARF`): not loaded.
    Debug,
}

impl SectionClass {
    /// TLV descriptors and templates: only TLV-aware relocations may name them.
    fn is_thread_local(self) -> bool {
        matches!(self, Self::ThreadVars | Self::ThreadData | Self::ThreadBss)
    }
}

fn section_label(section: &ParsedSection) -> String {
    format!("{},{}", section.segment, section.name)
}

/// Classify one input section, rejecting section types whose meaning this
/// linker would otherwise drop.
fn classify_section(
    object_index: usize,
    section: &ParsedSection,
) -> Result<SectionClass, LinkerError> {
    let section_type = section.section_type();
    if matches!(
        section_type,
        S_NON_LAZY_SYMBOL_POINTERS
            | S_LAZY_SYMBOL_POINTERS
            | S_SYMBOL_STUBS
            | S_MOD_INIT_FUNC_POINTERS
            | S_MOD_TERM_FUNC_POINTERS
            | S_INTERPOSING
            | S_DTRACE_DOF
            | S_LAZY_DYLIB_SYMBOL_POINTERS
            | S_THREAD_LOCAL_VARIABLE_POINTERS
            | S_THREAD_LOCAL_INIT_FUNCTION_POINTERS
            | S_INIT_FUNC_OFFSETS
    ) {
        return Err(LinkerError::UnsupportedSectionType {
            section: section_label(section),
            section_type,
        });
    }
    if section.flags & S_ATTR_DEBUG != 0 {
        return Ok(SectionClass::Debug);
    }
    let zerofill = section.is_zerofill();
    if zerofill
        && (section.segment == "__TEXT"
            || !section.data.is_empty()
            || !section.relocations.is_empty())
    {
        return Err(LinkerError::MalformedInput {
            file: format!("object {object_index}"),
            detail: format!(
                "zerofill section '{}' must be non-text with no file bytes or relocations",
                section.name
            ),
        });
    }
    let thread_local = matches!(
        section_type,
        S_THREAD_LOCAL_REGULAR | S_THREAD_LOCAL_ZEROFILL | S_THREAD_LOCAL_VARIABLES
    );
    if section.segment == "__TEXT" {
        if thread_local {
            return Err(LinkerError::ThreadLocal(format!(
                "object {object_index}: thread-local section '{}' must not be placed in __TEXT",
                section_label(section)
            )));
        }
        return Ok(SectionClass::Text);
    }
    let read_only_after_fixups = section.segment == "__DATA_CONST"
        || (section.segment == "__DATA" && section.name == "__const");
    if read_only_after_fixups && (thread_local || zerofill) {
        return Err(LinkerError::MalformedInput {
            file: format!("object {object_index}"),
            detail: format!(
                "section '{}' is read-only after fixups and cannot hold thread-local or zero-fill storage",
                section_label(section)
            ),
        });
    }
    Ok(match section_type {
        S_THREAD_LOCAL_VARIABLES => SectionClass::ThreadVars,
        S_THREAD_LOCAL_REGULAR => SectionClass::ThreadData,
        S_THREAD_LOCAL_ZEROFILL => SectionClass::ThreadBss,
        _ if zerofill => SectionClass::ZeroFill,
        _ if read_only_after_fixups => SectionClass::ConstData,
        _ => SectionClass::Data,
    })
}

fn classify_objects(objects: &[ParsedObject]) -> Result<Vec<Vec<SectionClass>>, LinkerError> {
    objects
        .iter()
        .enumerate()
        .map(|(object_index, object)| {
            object
                .sections
                .iter()
                .map(|section| classify_section(object_index, section))
                .collect()
        })
        .collect()
}

/// Which optional segments, sections and synthesized slots an image has.
///
/// Presence depends only on sizes and slot counts, never on absolute
/// addresses, so the load-command size (and therefore the mapped text base)
/// can be fixed before any address is assigned.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct ImageShape {
    stubs: usize,
    got: usize,
    tlv_pointers: usize,
    const_data: bool,
    data: bool,
    thread_vars: bool,
    thread_data: bool,
    thread_bss: bool,
}

impl ImageShape {
    fn new(
        objects: &[ParsedObject],
        classes: &[Vec<SectionClass>],
        stubs: usize,
        got: usize,
        tlv_pointers: usize,
    ) -> Self {
        let class_has_bytes = |wanted: fn(SectionClass) -> bool| {
            objects.iter().zip(classes).any(|(object, classes)| {
                object
                    .sections
                    .iter()
                    .zip(classes)
                    .any(|(section, class)| wanted(*class) && section.effective_size() > 0)
            })
        };
        Self {
            stubs,
            got,
            tlv_pointers,
            const_data: class_has_bytes(|class| class == SectionClass::ConstData),
            data: class_has_bytes(|class| {
                matches!(
                    class,
                    SectionClass::Data
                        | SectionClass::ThreadVars
                        | SectionClass::ThreadData
                        | SectionClass::ThreadBss
                        | SectionClass::ZeroFill
                )
            }),
            thread_vars: class_has_bytes(|class| class == SectionClass::ThreadVars),
            thread_data: class_has_bytes(|class| class == SectionClass::ThreadData),
            thread_bss: class_has_bytes(|class| class == SectionClass::ThreadBss),
        }
    }

    fn has_const(&self) -> bool {
        self.got > 0 || self.tlv_pointers > 0 || self.const_data
    }

    fn text_nsects(&self) -> u32 {
        1 + u32::from(self.stubs > 0)
    }

    fn const_nsects(&self) -> u32 {
        u32::from(self.got > 0) + u32::from(self.tlv_pointers > 0) + u32::from(self.const_data)
    }

    fn data_nsects(&self) -> u32 {
        if !self.data {
            return 0;
        }
        1 + u32::from(self.thread_vars) + u32::from(self.thread_data) + u32::from(self.thread_bss)
    }
}

/// The Mach-O file type an image link produces.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ImageKind<'a> {
    /// `MH_EXECUTE` at `DEFAULT_BASE_ADDR` behind `__PAGEZERO`, entered
    /// through `LC_MAIN`, with an empty exports trie.
    Executable,
    /// `MH_DYLIB` at base 0 named by `LC_ID_DYLIB`, exporting its external,
    /// non-private definitions through the exports trie.
    Dylib { install_name: &'a str },
}

impl ImageKind<'_> {
    /// The unslid address of the Mach-O header.
    fn base(self) -> u64 {
        match self {
            Self::Executable => DEFAULT_BASE_ADDR,
            Self::Dylib { .. } => 0,
        }
    }

    fn filetype(self) -> u32 {
        match self {
            Self::Executable => MH_EXECUTE,
            Self::Dylib { .. } => MH_DYLIB,
        }
    }

    fn header_flags(self) -> u32 {
        match self {
            Self::Executable => MH_EXECUTE_FLAGS,
            Self::Dylib { .. } => MH_DYLIB_FLAGS,
        }
    }

    /// Segment index of the first data segment (after `[__PAGEZERO,] __TEXT`).
    fn first_data_segment(self) -> usize {
        match self {
            Self::Executable => 2,
            Self::Dylib { .. } => 1,
        }
    }

    /// Code-directory `execSegFlags`: only the main executable is marked.
    fn exec_seg_flags(self) -> u64 {
        match self {
            Self::Executable => CS_EXECSEG_MAIN_BINARY,
            Self::Dylib { .. } => 0,
        }
    }

    /// Count and bytes of every load command except `__TEXT`, the data
    /// segments, `__LINKEDIT` and `LC_LOAD_DYLIB`: build version, UUID, the
    /// three linkedit-data commands, symtab and dysymtab, plus `__PAGEZERO`,
    /// `LC_MAIN` and `LC_LOAD_DYLINKER` (executables) or `LC_ID_DYLIB` (dylibs).
    fn fixed_commands(self) -> (u32, u64) {
        let common = u64::from(
            BUILD_VERSION_COMMAND_SIZE
                + UUID_COMMAND_SIZE
                + 3 * LINKEDIT_DATA_COMMAND_SIZE
                + SYMTAB_COMMAND_SIZE
                + DYSYMTAB_COMMAND_SIZE,
        );
        match self {
            Self::Executable => (
                10,
                common
                    + u64::from(SEGMENT_COMMAND_64_SIZE + LC_MAIN_SIZE + dylinker_command_size()),
            ),
            Self::Dylib { install_name } => (8, common + id_dylib_command_size(install_name)),
        }
    }
}

fn id_dylib_command_size(install_name: &str) -> u64 {
    align_to(
        u64::from(LC_LOAD_DYLIB_HEADER_SIZE) + install_name.len() as u64 + 1,
        8,
    )
}

/// Addresses planned for one image before symbol resolution.
#[derive(Debug, Clone)]
struct ImageLayout {
    section_addrs: Vec<Vec<u64>>,
    /// First text-content address (after the mapped headers).
    text_vmaddr: u64,
    stubs_addr: u64,
    text_end: u64,
    const_vmaddr: u64,
    got_addr: u64,
    tlv_pointers_addr: u64,
    /// End of the TLV pointer slots. `__DATA_CONST,__const` may start later
    /// when its inputs need more than 8-byte alignment.
    tlv_pointers_end: u64,
    /// `__DATA_CONST,__const`: placed after the TLV pointer slots.
    const_data: (u64, u64),
    const_end: u64,
    data_vmaddr: u64,
    regular_end: u64,
    thread_vars: (u64, u64),
    thread_data: (u64, u64),
    data_file_end: u64,
    thread_bss: (u64, u64),
    data_end: u64,
    /// Start of the contiguous TLV template image (`__thread_data` then
    /// `__thread_bss`); descriptor offsets are relative to it.
    tls_base: Option<u64>,
    tls_alignment: u64,
}

/// Result of laying out sections across multiple objects.
#[derive(Debug, Clone)]
pub struct LayoutResult {
    /// Base addresses for each section, in order: all sections from obj 0,
    /// then all sections from obj 1, etc. Unloaded `S_ATTR_DEBUG` sections
    /// have no image address and report 0.
    pub section_addrs: Vec<Vec<u64>>,
    /// Total size of the __TEXT segment content.
    pub text_size: u64,
    /// Virtual size of __DATA, including alignment gaps and zero-fill storage.
    pub data_size: u64,
    /// File-backed __DATA bytes, excluding zero-fill storage.
    pub data_file_size: u64,
    /// Offset of reserved dynamic-link stubs within the text content.
    pub stubs_offset: u64,
    /// Virtual address where text content begins, after the mapped headers.
    pub text_vmaddr: u64,
    /// Virtual address of __DATA segment.
    pub data_vmaddr: u64,
}

/// Assign final virtual addresses to sections from multiple objects.
///
/// Zero-fill sections occupy virtual address space but not file space and are
/// placed after every file-backed byte of `__DATA`. Thread-local templates are
/// kept contiguous (`__thread_data` then `__thread_bss`). No stubs or GOT/TLV
/// slots are reserved; the image linker plans those before calling the same
/// layout.
pub fn lay_out_sections(
    objects: &[ParsedObject],
    base_addr: u64,
) -> Result<LayoutResult, LinkerError> {
    let classes = classify_objects(objects)?;
    let shape = ImageShape::new(objects, &classes, 0, 0, 0);
    let layout = plan_layout(objects, &classes, &shape, base_addr)?;
    Ok(LayoutResult {
        text_size: layout.text_end - base_addr,
        data_size: layout.data_end - layout.data_vmaddr,
        data_file_size: layout.data_file_end - layout.data_vmaddr,
        stubs_offset: layout.stubs_addr - base_addr,
        text_vmaddr: base_addr,
        data_vmaddr: layout.data_vmaddr,
        section_addrs: layout.section_addrs,
    })
}

fn layout_add(left: u64, right: u64, context: &'static str) -> Result<u64, LinkerError> {
    left.checked_add(right)
        .ok_or(LinkerError::LayoutOverflow(context))
}

fn checked_align_to(value: u64, alignment: u64) -> Result<u64, LinkerError> {
    let padding = (alignment - value % alignment) % alignment;
    layout_add(value, padding, "aligned address")
}

fn section_alignment(section: &ParsedSection) -> Result<u64, LinkerError> {
    1u64.checked_shl(section.align)
        .ok_or_else(|| LinkerError::InvalidAlignment {
            section: section.name.clone(),
            exponent: section.align,
        })
}

/// Place every input section of `class` at `cursor`, returning the occupied
/// `(start, end)` range. An absent output section (no bytes) assigns its
/// zero-size inputs the cursor without alignment, so it cannot move later
/// addresses or create an unplanned segment.
#[allow(clippy::too_many_arguments)]
fn place_class(
    objects: &[ParsedObject],
    classes: &[Vec<SectionClass>],
    class: SectionClass,
    present: bool,
    minimum_alignment: u64,
    cursor: &mut u64,
    section_addrs: &mut [Vec<u64>],
    context: &'static str,
) -> Result<(u64, u64), LinkerError> {
    let mut start = None;
    for (object_index, object) in objects.iter().enumerate() {
        for (section_index, section) in object.sections.iter().enumerate() {
            if classes[object_index][section_index] != class {
                continue;
            }
            if present {
                let alignment = section_alignment(section)?.max(minimum_alignment);
                *cursor = checked_align_to(*cursor, alignment)?;
            }
            start.get_or_insert(*cursor);
            section_addrs[object_index][section_index] = *cursor;
            *cursor = layout_add(*cursor, section.effective_size(), context)?;
        }
    }
    Ok((start.unwrap_or(*cursor), *cursor))
}

/// Plan every occupied byte before resolving symbols. Stubs extend text; the
/// GOT and TLV pointer slots and then read-only-after-fixup data form
/// `__DATA_CONST`; `__DATA` holds regular data,
/// TLV descriptors, the contiguous TLV template image, then zero-fill storage.
/// Alignment applies to absolute addresses, not offsets from an unaligned base.
fn plan_layout(
    objects: &[ParsedObject],
    classes: &[Vec<SectionClass>],
    shape: &ImageShape,
    base_addr: u64,
) -> Result<ImageLayout, LinkerError> {
    let slot_extent = |count: usize, width: u64, context| {
        u64::try_from(count)
            .ok()
            .and_then(|count| count.checked_mul(width))
            .ok_or(LinkerError::LayoutOverflow(context))
    };
    let stub_size = slot_extent(shape.stubs, u64::from(STUB_SIZE), "stub extent")?;
    let got_size = slot_extent(shape.got, 8, "GOT extent")?;
    let tlv_size = slot_extent(shape.tlv_pointers, 8, "TLV pointer extent")?;
    let mut section_addrs: Vec<Vec<u64>> = objects
        .iter()
        .map(|object| vec![0; object.sections.len()])
        .collect();

    let mut cursor = base_addr;
    place_class(
        objects,
        classes,
        SectionClass::Text,
        true,
        1,
        &mut cursor,
        &mut section_addrs,
        "text extent",
    )?;
    if shape.stubs > 0 {
        cursor = checked_align_to(cursor, 4)?;
    }
    let stubs_addr = cursor;
    let text_end = layout_add(cursor, stub_size, "text plus stubs")?;

    let const_vmaddr = checked_align_to(text_end, PAGE_SIZE)?;
    let got_addr = const_vmaddr;
    let tlv_pointers_addr = layout_add(got_addr, got_size, "GOT extent")?;
    let tlv_pointers_end = layout_add(tlv_pointers_addr, tlv_size, "TLV pointer extent")?;
    cursor = tlv_pointers_end;
    // Relocated constants carry pointer fixups; keep each pointer-aligned.
    let const_data = place_class(
        objects,
        classes,
        SectionClass::ConstData,
        shape.const_data,
        8,
        &mut cursor,
        &mut section_addrs,
        "read-only-after-fixup data extent",
    )?;
    let const_end = cursor;
    let data_vmaddr = if shape.has_const() {
        checked_align_to(const_end, PAGE_SIZE)?
    } else {
        const_vmaddr
    };

    cursor = data_vmaddr;
    place_class(
        objects,
        classes,
        SectionClass::Data,
        shape.data,
        1,
        &mut cursor,
        &mut section_addrs,
        "data extent",
    )?;
    let regular_end = cursor;
    // Descriptors carry pointer fixups; keep each one pointer-aligned.
    let thread_vars = place_class(
        objects,
        classes,
        SectionClass::ThreadVars,
        shape.thread_vars,
        8,
        &mut cursor,
        &mut section_addrs,
        "TLV descriptor extent",
    )?;

    let mut tls_alignment = 1;
    for (object, classes) in objects.iter().zip(classes) {
        for (section, class) in object.sections.iter().zip(classes) {
            if matches!(class, SectionClass::ThreadData | SectionClass::ThreadBss)
                && section.effective_size() > 0
            {
                tls_alignment = tls_alignment.max(section_alignment(section)?);
            }
        }
    }
    if tls_alignment > TLS_TEMPLATE_MAX_ALIGNMENT {
        return Err(LinkerError::ThreadLocal(format!(
            "thread-local template alignment {tls_alignment} exceeds the {TLS_TEMPLATE_MAX_ALIGNMENT}-byte alignment of dyld's per-thread copies"
        )));
    }
    if shape.thread_data || shape.thread_bss {
        cursor = checked_align_to(cursor, tls_alignment)?;
    }
    let thread_data = place_class(
        objects,
        classes,
        SectionClass::ThreadData,
        shape.thread_data,
        1,
        &mut cursor,
        &mut section_addrs,
        "TLV template extent",
    )?;
    let data_file_end = cursor;
    let thread_bss = place_class(
        objects,
        classes,
        SectionClass::ThreadBss,
        shape.thread_bss,
        1,
        &mut cursor,
        &mut section_addrs,
        "TLV zero-fill extent",
    )?;
    place_class(
        objects,
        classes,
        SectionClass::ZeroFill,
        shape.data,
        1,
        &mut cursor,
        &mut section_addrs,
        "BSS extent",
    )?;
    let data_end = cursor;
    // dyld copies each thread's template from the first emitted TLV template
    // section, so descriptor offsets are relative to that section's start. An
    // empty input section placed first may be aligned beyond `tls_alignment`
    // and start the section after the aligned cursor.
    let tls_base = if shape.thread_data {
        Some(thread_data.0)
    } else if shape.thread_bss {
        Some(thread_bss.0)
    } else {
        None
    };
    // Emission rounds the VM extent to complete pages. Reject that overflow
    // here too, including a huge BSS which needs no corresponding allocation.
    checked_align_to(data_end, PAGE_SIZE)?;
    Ok(ImageLayout {
        section_addrs,
        text_vmaddr: base_addr,
        stubs_addr,
        text_end,
        const_vmaddr,
        got_addr,
        tlv_pointers_addr,
        tlv_pointers_end,
        const_data,
        const_end,
        data_vmaddr,
        regular_end,
        thread_vars,
        thread_data,
        data_file_end,
        thread_bss,
        data_end,
        tls_base,
        tls_alignment,
    })
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

/// Number of 4 KiB code-signing blocks covering `code_limit` bytes. The
/// CodeDirectory's 32-bit `codeLimit` field bounds the signed prefix; this
/// linker does not write `codeLimit64`, so a larger image is refused.
fn code_signature_block_count(code_limit: u64) -> Result<u32, LinkerError> {
    if code_limit > u64::from(u32::MAX) {
        return Err(LinkerError::LayoutOverflow(
            "code signature codeLimit (images over 4 GiB need codeLimit64)",
        ));
    }
    Ok(code_limit.div_ceil(CODE_SIGNATURE_BLOCK_SIZE) as u32)
}

fn code_signature_headers_size() -> usize {
    align_to(
        (CS_FIXED_HEADERS_SIZE + CODE_SIGNATURE_IDENTIFIER.len() + 1) as u64,
        CODE_SIGNATURE_ALIGNMENT,
    ) as usize
}

fn code_signature_size(code_limit: u64) -> Result<u32, LinkerError> {
    let size = code_signature_headers_size() as u64
        + u64::from(code_signature_block_count(code_limit)?) * CODE_SIGNATURE_HASH_SIZE as u64;
    u32::try_from(size).map_err(|_| LinkerError::LayoutOverflow("code signature size"))
}

fn build_ad_hoc_code_signature(
    file_prefix: &[u8],
    text_file_offset: u64,
    text_file_size: u64,
    exec_seg_flags: u64,
) -> Result<Vec<u8>, LinkerError> {
    let code_limit = file_prefix.len() as u64;
    let block_count = code_signature_block_count(code_limit)?;
    let all_headers_size = code_signature_headers_size();
    let hash_offset = all_headers_size - CS_BLOB_HEADERS_SIZE;
    let code_directory_length = hash_offset + block_count as usize * CODE_SIGNATURE_HASH_SIZE;
    let signature_size = CS_BLOB_HEADERS_SIZE + code_directory_length;
    if signature_size != code_signature_size(code_limit)? as usize {
        return Err(LinkerError::CodeSignatureContract(format!(
            "signature of {signature_size} bytes disagrees with its reserved size"
        )));
    }

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
    write_be_u64(&mut buf, exec_seg_flags);
    debug_assert_eq!(buf.len(), CS_FIXED_HEADERS_SIZE);

    buf.extend_from_slice(CODE_SIGNATURE_IDENTIFIER);
    buf.resize(all_headers_size, 0);

    for block_idx in 0..block_count as usize {
        let start = block_idx * CODE_SIGNATURE_BLOCK_SIZE as usize;
        let end = ((block_idx as u64 + 1) * CODE_SIGNATURE_BLOCK_SIZE).min(code_limit) as usize;
        buf.extend_from_slice(&sha256_digest(&file_prefix[start..end]));
    }

    debug_assert_eq!(buf.len(), signature_size);
    Ok(buf)
}

/// Run the independent verifier over a finished image and hold it to this
/// linker's signature contract: an ad-hoc, linker-signed SHA-256
/// CodeDirectory over 4 KiB pages with the `trust-cg` identifier, no special
/// slots or alternate CodeDirectories, an executable segment that is exactly
/// the `__TEXT` file range, and the main-binary flag exactly when the image is
/// an executable. Standalone output never requests the hardened
/// runtime or carries entitlements; such a program must be re-signed with
/// `codesign`.
fn self_check_code_signature(
    image: &[u8],
    text_segment_filesize: u64,
    exec_seg_flags: u64,
) -> Result<(), LinkerError> {
    let signature = super::codesign::verify_ad_hoc_signature(image)
        .map_err(LinkerError::CodeSignatureSelfCheck)?;
    let directory = &signature.code_directory;
    let exec_segment = directory
        .exec_segment
        .map(|segment| (segment.base, segment.limit, segment.flags));
    let departures = [
        (directory.flags != CS_ADHOC | CS_LINKER_SIGNED, "flags"),
        (
            directory.page_size != CODE_SIGNATURE_BLOCK_SIZE,
            "page size",
        ),
        (
            directory.identifier.as_bytes() != CODE_SIGNATURE_IDENTIFIER,
            "identifier",
        ),
        (directory.special_slots != 0, "special slots"),
        (
            exec_segment != Some((0, text_segment_filesize, exec_seg_flags)),
            "executable segment",
        ),
        (
            !signature.alternate_code_directories.is_empty(),
            "alternate CodeDirectories",
        ),
    ];
    match departures.iter().find(|(departs, _)| *departs) {
        Some((_, field)) => Err(LinkerError::CodeSignatureContract(format!(
            "unexpected {field} in {directory:?}"
        ))),
        None => Ok(()),
    }
}

fn sha256_digest(data: &[u8]) -> [u8; 32] {
    // Reuse the crate's existing SHA-256 implementation without allocating a
    // padded copy of the input. CodeDirectory validation below keeps a separate
    // scalar implementation as its independent test oracle.
    use sha2::{Digest, Sha256};
    Sha256::digest(data).into()
}

#[cfg(test)]
fn reference_sha256_digest(data: &[u8]) -> [u8; 32] {
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

    for chunk in padded.as_chunks::<64>().0 {
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
        lib_ordinal <= 0xF0 || lib_ordinal == BIND_SPECIAL_DYLIB_WEAK_LOOKUP_ORDINAL,
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
    fixup_segments: &[ChainedFixupSegmentInfo],
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

    for segment in fixup_segments {
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
    fixup_segments: &[ChainedFixupSegmentInfo],
    import_symbols: &[String],
    import_ordinals: &[u32],
    exports_trie: &[u8],
) -> Result<LinkeditPayload, LinkerError> {
    let fixups = build_chained_fixups_payload(
        segment_count,
        fixup_segments,
        import_symbols,
        import_ordinals,
    );
    let fixups_size = fixups.len() as u32;
    let mut data = fixups;
    pad_vec_to_alignment(&mut data, 8);

    let exports_offset = linkedit_file_offset + data.len() as u64;
    let exports_size = exports_trie.len() as u32;
    data.extend_from_slice(exports_trie);
    pad_vec_to_alignment(&mut data, 8);

    let code_signature_offset = align_to(
        linkedit_file_offset + data.len() as u64,
        CODE_SIGNATURE_ALIGNMENT,
    );
    let code_signature_padding =
        (code_signature_offset - (linkedit_file_offset + data.len() as u64)) as usize;
    data.resize(data.len() + code_signature_padding, 0);
    let code_signature_size = code_signature_size(code_signature_offset)?;

    Ok(LinkeditPayload {
        data,
        fixups_offset: linkedit_file_offset,
        fixups_size,
        exports_offset,
        exports_size,
        code_signature_offset,
        code_signature_size,
    })
}

fn dylib_command_size(dylib: &DylibEntry) -> u32 {
    let name_len = dylib.install_name.len() as u32 + 1;
    let raw_size = LC_LOAD_DYLIB_HEADER_SIZE + name_len;
    align_to(raw_size as u64, 8) as u32
}

/// The largest optional-section shape, used to bound load-command sizes before
/// the real shape is known.
const MAXIMAL_IMAGE_SHAPE: ImageShape = ImageShape {
    stubs: 1,
    got: 1,
    tlv_pointers: 1,
    const_data: true,
    data: true,
    thread_vars: true,
    thread_data: true,
    thread_bss: true,
};

/// Admit the compact import representation before the infallible encoders.
/// Library ordinals are eight bits (0xF1..0xFF are reserved), symbol-name
/// offsets are 23 bits, and bind ordinals are 24 bits.
fn validate_dylib_imports(
    needed_dylibs: &[&DylibEntry],
    symbols: &[String],
) -> Result<(), LinkerError> {
    validate_import_table(needed_dylibs, symbols, |_| false)
}

/// [`validate_dylib_imports`] where `weak_lookup` names the imports bound
/// through dyld's weak-definition lookup, which no needed dylib provides.
fn validate_import_table(
    needed_dylibs: &[&DylibEntry],
    symbols: &[String],
    weak_lookup: impl Fn(&str) -> bool,
) -> Result<(), LinkerError> {
    if needed_dylibs.len() > 0xF0 || symbols.len() > DYLD_CHAINED_PTR_64_BIND_ORDINAL_LIMIT {
        return Err(LinkerError::LayoutOverflow("compact dylib import count"));
    }
    let invalid_name = || LinkerError::MalformedInput {
        file: "dynamic imports".into(),
        detail: "dylib and symbol names must be nonempty and contain no NUL".into(),
    };
    let mut command_size = u64::from(image_load_command_size(
        ImageKind::Executable,
        &MAXIMAL_IMAGE_SHAPE,
        &[],
    )?);
    for dylib in needed_dylibs {
        if dylib.install_name.is_empty() || dylib.install_name.as_bytes().contains(&0) {
            return Err(invalid_name());
        }
        let size = layout_add(
            dylib.install_name.len() as u64,
            u64::from(LC_LOAD_DYLIB_HEADER_SIZE) + 1,
            "dylib command",
        )?;
        command_size = layout_add(command_size, checked_align_to(size, 8)?, "load commands")?;
    }
    if command_size > u64::from(u32::MAX) {
        return Err(LinkerError::LayoutOverflow("load command size"));
    }
    let mut name_offset = 0u64;
    for symbol in symbols {
        if symbol.is_empty() || symbol.as_bytes().contains(&0) {
            return Err(invalid_name());
        }
        if name_offset >= 1 << 23 {
            return Err(LinkerError::LayoutOverflow("compact import name offset"));
        }
        name_offset = layout_add(
            name_offset,
            layout_add(symbol.len() as u64, 1, "import name")?,
            "import name table",
        )?;
        if name_offset > u64::from(u32::MAX) {
            return Err(LinkerError::LayoutOverflow("import name table size"));
        }
        if !weak_lookup(symbol)
            && !needed_dylibs
                .iter()
                .any(|dylib| dylib.symbols.contains(symbol))
        {
            return Err(LinkerError::UndefinedSymbol(symbol.clone()));
        }
    }
    Ok(())
}

/// Total `sizeofcmds` for a `kind` image of `shape` loading `dylib_cmd_sizes`.
fn image_load_command_size(
    kind: ImageKind<'_>,
    shape: &ImageShape,
    dylib_cmd_sizes: &[u32],
) -> Result<u32, LinkerError> {
    let segment = |nsects: u32| u64::from(SEGMENT_COMMAND_64_SIZE + nsects * SECTION_64_SIZE);
    let mut size = segment(shape.text_nsects())
        + segment(0) // __LINKEDIT
        + kind.fixed_commands().1;
    if shape.has_const() {
        size += segment(shape.const_nsects());
    }
    if shape.data {
        size += segment(shape.data_nsects());
    }
    for &dylib in dylib_cmd_sizes {
        size = layout_add(size, u64::from(dylib), "load commands")?;
    }
    u32::try_from(size).map_err(|_| LinkerError::LayoutOverflow("load command size"))
}

fn executable_text_file_offset_from_lc_size(total_lc_size: u32) -> u64 {
    align_to(MACH_HEADER_64_SIZE as u64 + total_lc_size as u64, PAGE_SIZE)
}

/// Text-content file offset of a dylib-free image with one optional `__DATA`.
#[cfg(test)]
fn plain_executable_text_file_offset(has_data: bool) -> u64 {
    let shape = ImageShape {
        data: has_data,
        ..ImageShape::default()
    };
    executable_text_file_offset_from_lc_size(
        image_load_command_size(ImageKind::Executable, &shape, &[])
            .expect("fixed plain load commands fit"),
    )
}

fn dylib_ordinal_for_symbol(needed_dylibs: &[&DylibEntry], symbol: &str) -> u32 {
    needed_dylibs
        .iter()
        .position(|dylib| dylib.symbols.contains(symbol))
        .map(|idx| idx as u32 + 1)
        .expect("dylib symbol must be provided by a loaded dylib")
}

// ---------------------------------------------------------------------------
// Chained fixups
// ---------------------------------------------------------------------------

/// What dyld stores in one 64-bit pointer slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PointerFixupKind {
    /// Slide an image address (DYLD_CHAINED_PTR_64 rebase of an unslid vmaddr).
    Rebase { target: u64 },
    /// Bind an import (index into the chained-fixups import table) plus addend.
    Bind { import: usize, addend: u8 },
}

/// A pointer slot at an absolute (unslid) image address.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PointerFixup {
    address: u64,
    kind: PointerFixupKind,
}

/// Encode one segment's pointer fixups as DYLD_CHAINED_PTR_64 chains in
/// `bytes` (the segment's file-backed content starting at `segment_vmaddr`).
/// Each fixup must be 8-byte aligned inside the file-backed bytes; fixups on
/// one 16 KiB page form one chain with 4-byte-stride `next` deltas.
fn encode_segment_chains(
    segment_index: usize,
    segment_vmaddr: u64,
    image_base: u64,
    bytes: &mut [u8],
    fixups: &mut [PointerFixup],
) -> Result<Option<ChainedFixupSegmentInfo>, LinkerError> {
    if fixups.is_empty() {
        return Ok(None);
    }
    fixups.sort_by_key(|fixup| fixup.address);
    let fail = |address: u64, detail: String| LinkerError::ChainedFixup { address, detail };
    let mut page_starts: Vec<(u16, u16)> = Vec::new();
    for index in 0..fixups.len() {
        let fixup = fixups[index];
        if !fixup.address.is_multiple_of(8) {
            return Err(fail(
                fixup.address,
                "pointer slot is not 8-byte aligned".into(),
            ));
        }
        let offset = fixup
            .address
            .checked_sub(segment_vmaddr)
            .filter(|offset| {
                offset
                    .checked_add(8)
                    .is_some_and(|end| end <= bytes.len() as u64)
            })
            .ok_or_else(|| {
                fail(
                    fixup.address,
                    "pointer slot is outside its segment's file-backed bytes".into(),
                )
            })?;
        let page = offset / PAGE_SIZE;
        if page >= u64::from(u16::MAX) {
            return Err(LinkerError::LayoutOverflow(
                "compact chained-fixup import/page fields",
            ));
        }
        let previous_page = index
            .checked_sub(1)
            .map(|previous| (fixups[previous].address - segment_vmaddr) / PAGE_SIZE);
        if previous_page == Some(page) {
            if fixup.address - fixups[index - 1].address < 8 {
                return Err(fail(fixup.address, "pointer slots overlap".into()));
            }
        } else {
            page_starts.push((page as u16, (offset % PAGE_SIZE) as u16));
        }
        // Slots on the same page chain with 4-byte strides; the largest
        // in-page delta (16376 bytes) fits the 12-bit field.
        let next = fixups
            .get(index + 1)
            .filter(|next| (next.address - segment_vmaddr) / PAGE_SIZE == page)
            .map_or(0, |next| (next.address - fixup.address) / 4);
        debug_assert!(next < 1 << 12);
        let raw = match fixup.kind {
            PointerFixupKind::Rebase { target } => {
                if target >= DYLD_CHAINED_PTR_64_TARGET_LIMIT {
                    return Err(fail(
                        fixup.address,
                        format!("rebase target {target:#x} exceeds the 36-bit vmaddr field"),
                    ));
                }
                target | (next << 51)
            }
            PointerFixupKind::Bind { import, addend } => {
                if import >= DYLD_CHAINED_PTR_64_BIND_ORDINAL_LIMIT {
                    return Err(fail(
                        fixup.address,
                        format!("import ordinal {import} exceeds the 24-bit bind field"),
                    ));
                }
                import as u64 | (u64::from(addend) << 24) | (next << 51) | (1 << 63)
            }
        };
        let start = offset as usize;
        bytes[start..start + 8].copy_from_slice(&raw.to_le_bytes());
    }
    Ok(Some(ChainedFixupSegmentInfo {
        segment_index,
        segment_offset: segment_vmaddr - image_base,
        page_starts,
    }))
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

/// One relocation operation after pairing each `ARM64_RELOC_ADDEND` and
/// `ARM64_RELOC_SUBTRACTOR` record with the relocation it modifies.
#[derive(Debug, Clone, Copy)]
enum RelocOp<'r> {
    /// A relocation plus the addend of a preceding `ARM64_RELOC_ADDEND`.
    Single { reloc: &'r Relocation, addend: i64 },
    /// `minuend - subtrahend` from a `SUBTRACTOR`/`UNSIGNED` pair.
    Difference {
        subtrahend: &'r Relocation,
        minuend: &'r Relocation,
    },
}

/// Pair modifier records with their partner relocation. `ARM64_RELOC_ADDEND`
/// must be a non-extern, non-pc-relative 32-bit record immediately preceding a
/// `BRANCH26`, `PAGE21` or `PAGEOFF12` at the same offset; its `r_symbolnum`
/// is a signed 24-bit addend. A `SUBTRACTOR` must be followed by a matching
/// absolute `UNSIGNED`.
fn relocation_ops(relocations: &[Relocation]) -> Result<Vec<RelocOp<'_>>, LinkerError> {
    let mut ops = Vec::with_capacity(relocations.len());
    let mut index = 0usize;
    while index < relocations.len() {
        let reloc = &relocations[index];
        match reloc.kind {
            AArch64RelocKind::Subtractor => {
                let Some(unsigned) = relocations.get(index + 1) else {
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
                if unsigned.pc_relative {
                    return Err(LinkerError::PcRelativeUnsigned {
                        offset: unsigned.offset,
                    });
                }
                if reloc.pc_relative || !matches!(reloc.length, 2 | 3) {
                    return Err(LinkerError::MalformedRelocation(
                        "ARM64_RELOC_SUBTRACTOR must name an absolute 32- or 64-bit field".into(),
                    ));
                }
                ops.push(RelocOp::Difference {
                    subtrahend: reloc,
                    minuend: unsigned,
                });
                index += 2;
            }
            AArch64RelocKind::Addend => {
                if reloc.is_extern || reloc.pc_relative || reloc.length != 2 {
                    return Err(LinkerError::MalformedRelocation(
                        "ARM64_RELOC_ADDEND must be a non-extern, non-pc-relative 32-bit record"
                            .into(),
                    ));
                }
                let partner = relocations.get(index + 1).filter(|next| {
                    next.offset == reloc.offset
                        && matches!(
                            next.kind,
                            AArch64RelocKind::Branch26
                                | AArch64RelocKind::Page21
                                | AArch64RelocKind::Pageoff12
                        )
                });
                let Some(partner) = partner else {
                    return Err(LinkerError::MalformedRelocation(
                        "ARM64_RELOC_ADDEND must immediately precede a BRANCH26, PAGE21 or \
                         PAGEOFF12 relocation at the same offset"
                            .into(),
                    ));
                };
                let addend = i64::from(((reloc.symbol_index << 8) as i32) >> 8);
                ops.push(RelocOp::Single {
                    reloc: partner,
                    addend,
                });
                index += 2;
            }
            _ => {
                ops.push(RelocOp::Single { reloc, addend: 0 });
                index += 1;
            }
        }
    }
    Ok(ops)
}

/// Check the `r_pcrel`/`r_length`/`r_extern` shape each kind requires.
fn validate_relocation_shape(reloc: &Relocation) -> Result<(), LinkerError> {
    use AArch64RelocKind as K;
    let malformed = |detail: &str| {
        LinkerError::MalformedRelocation(format!(
            "{:?} at offset {:#x}: {detail}",
            reloc.kind, reloc.offset
        ))
    };
    match reloc.kind {
        K::Branch26 | K::Page21 | K::GotLoadPage21 | K::TlvpLoadPage21 => {
            if !reloc.pc_relative || reloc.length != 2 {
                return Err(malformed("must be a pc-relative 32-bit instruction field"));
            }
        }
        K::Pageoff12 | K::GotLoadPageoff12 | K::TlvpLoadPageoff12 => {
            if reloc.pc_relative || reloc.length != 2 {
                return Err(malformed(
                    "must be a non-pc-relative 32-bit instruction field",
                ));
            }
        }
        K::PointerToGot => {
            // A 64-bit absolute pointer-to-GOT would need a rebased GOT
            // address; only the pc-relative 32-bit form is implemented.
            if !reloc.pc_relative || reloc.length != 2 {
                return Err(LinkerError::UnsupportedRelocation(K::PointerToGot));
            }
        }
        K::Unsigned => {
            if reloc.pc_relative {
                return Err(LinkerError::PcRelativeUnsigned {
                    offset: reloc.offset,
                });
            }
            if !matches!(reloc.length, 2 | 3) {
                return Err(malformed("must be a 32- or 64-bit field"));
            }
        }
        K::Subtractor | K::Addend => {
            return Err(malformed("must be paired with the relocation it modifies"));
        }
        other => return Err(LinkerError::UnsupportedRelocation(other)),
    }
    if matches!(
        reloc.kind,
        K::GotLoadPage21
            | K::GotLoadPageoff12
            | K::TlvpLoadPage21
            | K::TlvpLoadPageoff12
            | K::PointerToGot
    ) && !reloc.is_extern
    {
        return Err(malformed("must name a symbol (r_extern=1)"));
    }
    Ok(())
}

fn read_instruction(
    data: &[u8],
    offset: usize,
    kind: AArch64RelocKind,
) -> Result<u32, LinkerError> {
    let bytes = offset
        .checked_add(4)
        .and_then(|end| data.get(offset..end))
        .ok_or_else(|| LinkerError::RelocationOverflow {
            detail: match kind {
                AArch64RelocKind::Branch26 => "BRANCH26 patch offset out of bounds".into(),
                AArch64RelocKind::Page21 => "PAGE21 patch offset out of bounds".into(),
                AArch64RelocKind::Pageoff12 => "PAGEOFF12 patch offset out of bounds".into(),
                other => format!("{other:?} patch offset out of bounds"),
            },
        })?;
    Ok(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
}

fn instruction_mismatch(kind: AArch64RelocKind, offset: usize, instruction: u32) -> LinkerError {
    LinkerError::RelocationInstructionMismatch {
        kind,
        offset: offset as u32,
        instruction,
    }
}

/// Offset a resolved address by a signed addend inside the u64 domain.
fn offset_address(address: u64, addend: i64) -> Result<u64, LinkerError> {
    u64::try_from(i128::from(address) + i128::from(addend)).map_err(|_| {
        LinkerError::RelocationOverflow {
            detail: format!("target {address:#x} plus addend {addend} leaves the address space"),
        }
    })
}

/// Access scale of an instruction a `PAGEOFF12` may patch: ADD (immediate,
/// unshifted) is byte-granular; a load/store (unsigned immediate), including
/// SIMD&FP and PRFM, scales by its access size (16 for Q registers).
fn pageoff12_scale(instruction: u32) -> Option<u64> {
    if instruction & 0x7FC0_0000 == 0x1100_0000 {
        return Some(1);
    }
    if instruction & 0x3B00_0000 == 0x3900_0000 {
        let size = instruction >> 30;
        let vector = (instruction >> 26) & 1 == 1;
        let opc = (instruction >> 22) & 3;
        return Some(if vector && size == 0 && opc >= 2 {
            16
        } else {
            1 << size
        });
    }
    None
}

/// Patch a B/BL imm26 with `target - pc`.
fn patch_branch26(data: &mut [u8], offset: usize, pc: u64, target: u64) -> Result<(), LinkerError> {
    let kind = AArch64RelocKind::Branch26;
    let instruction = read_instruction(data, offset, kind)?;
    if instruction & 0x7C00_0000 != 0x1400_0000 {
        return Err(instruction_mismatch(kind, offset, instruction));
    }
    let displacement = i128::from(target) - i128::from(pc);
    if displacement % 4 != 0 {
        return Err(LinkerError::RelocationOverflow {
            detail: format!("BRANCH26 displacement {displacement:#x} is not word-aligned"),
        });
    }
    let imm26 = displacement >> 2;
    if !(-(1i128 << 25)..(1i128 << 25)).contains(&imm26) {
        return Err(LinkerError::RelocationOverflow {
            detail: format!("BRANCH26 displacement {displacement:#x} out of +/-128MiB range"),
        });
    }
    let patched = (instruction & !0x03FF_FFFF) | ((imm26 as u32) & 0x03FF_FFFF);
    data[offset..offset + 4].copy_from_slice(&patched.to_le_bytes());
    Ok(())
}

/// Patch an ADRP with the page delta from `pc` to `target`.
fn patch_page21(
    data: &mut [u8],
    offset: usize,
    pc: u64,
    target: u64,
    kind: AArch64RelocKind,
) -> Result<(), LinkerError> {
    let instruction = read_instruction(data, offset, kind)?;
    if instruction & 0x9F00_0000 != 0x9000_0000 {
        return Err(instruction_mismatch(kind, offset, instruction));
    }
    let page_delta = (i128::from(target & !0xFFF) - i128::from(pc & !0xFFF)) >> 12;
    if !(-(1i128 << 20)..(1i128 << 20)).contains(&page_delta) {
        return Err(LinkerError::RelocationOverflow {
            detail: format!("PAGE21 page delta {page_delta:#x} out of +/-4GiB range"),
        });
    }
    let imm21 = (page_delta as u32) & 0x001F_FFFF;
    let patched = (instruction & !((0x7FFFF << 5) | (0x3 << 29)))
        | (((imm21 >> 2) & 0x7FFFF) << 5)
        | ((imm21 & 0x3) << 29);
    data[offset..offset + 4].copy_from_slice(&patched.to_le_bytes());
    Ok(())
}

/// Patch the imm12 page offset of `target`. `PAGEOFF12` accepts ADD
/// (immediate) and scaled loads/stores; the GOT/TLVP forms accept only the
/// 64-bit `LDR Xt, [Xn, #imm]` that loads their slot. A target offset that the
/// access size cannot represent is refused instead of truncated.
fn patch_pageoff12(
    data: &mut [u8],
    offset: usize,
    target: u64,
    kind: AArch64RelocKind,
) -> Result<(), LinkerError> {
    let instruction = read_instruction(data, offset, kind)?;
    let scale = match kind {
        AArch64RelocKind::Pageoff12 => pageoff12_scale(instruction),
        _ => (instruction & 0xFFC0_0000 == 0xF940_0000).then_some(8),
    }
    .ok_or_else(|| instruction_mismatch(kind, offset, instruction))?;
    let page_offset = target & 0xFFF;
    if !page_offset.is_multiple_of(scale) {
        return Err(LinkerError::RelocationOverflow {
            detail: format!(
                "{kind:?} target {target:#x} is not aligned to its {scale}-byte access"
            ),
        });
    }
    let imm12 = (page_offset / scale) as u32;
    let patched = (instruction & !(0xFFF << 10)) | ((imm12 & 0xFFF) << 10);
    data[offset..offset + 4].copy_from_slice(&patched.to_le_bytes());
    Ok(())
}

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
    /// This is relocation arithmetic only. `ARM64_RELOC_UNSIGNED` writes the
    /// link-time value without recording the dyld rebase/bind an image needs,
    /// and the GOT/TLVP/`POINTER_TO_GOT` kinds, which need linker-planned
    /// slots, return [`LinkerError::UnsupportedRelocation`]; [`link`] and
    /// [`link_with_dylibs`] apply both.
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
        let target = |reloc: &Relocation| {
            Self::target_addr(
                reloc,
                symbols,
                symbol_addrs,
                local_symbol_addrs,
                section_addrs,
            )
        };
        for op in relocation_ops(relocations)? {
            match op {
                RelocOp::Difference {
                    subtrahend,
                    minuend,
                } => {
                    let subtrahend_addr = target(subtrahend)?;
                    let target_addr = target(minuend)?;
                    Self::apply_subtractor_pair(
                        section_data,
                        subtrahend.offset as usize,
                        target_addr,
                        subtrahend_addr,
                        subtrahend.length,
                    )?;
                }
                RelocOp::Single { reloc, addend } => {
                    validate_relocation_shape(reloc)?;
                    let target_addr = offset_address(target(reloc)?, addend)?;
                    let pc = layout_add(section_addr, u64::from(reloc.offset), "relocation site")?;
                    let patch_offset = reloc.offset as usize;
                    match reloc.kind {
                        AArch64RelocKind::Branch26 => {
                            patch_branch26(section_data, patch_offset, pc, target_addr)?;
                        }
                        AArch64RelocKind::Page21 => {
                            patch_page21(section_data, patch_offset, pc, target_addr, reloc.kind)?;
                        }
                        AArch64RelocKind::Pageoff12 => {
                            patch_pageoff12(section_data, patch_offset, target_addr, reloc.kind)?;
                        }
                        AArch64RelocKind::Unsigned => {
                            let value =
                                Self::read_signed_addend(section_data, patch_offset, reloc.length)?
                                    + i128::from(target_addr);
                            Self::write_sized_value(
                                section_data,
                                patch_offset,
                                reloc.length,
                                value,
                            )?;
                        }
                        other => return Err(LinkerError::UnsupportedRelocation(other)),
                    }
                }
            }
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
            // referenced section's mapped base address. Inline and
            // ARM64_RELOC_ADDEND addends are applied by the caller.
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
            .get(sym.name.as_str())
            .copied()
            .ok_or_else(|| LinkerError::UndefinedSymbol(sym.name.to_string()))
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
// Image symbols, imports and synthesized slots
// ---------------------------------------------------------------------------

/// Symbol identity of a GOT or TLV pointer slot. Global names share one slot
/// across objects; local definitions stay object-scoped.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum SlotKey {
    Global(SymbolName),
    Local { object: usize, symbol: usize },
}

/// What a relocation's symbol resolves to in the image being linked.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RelocTarget {
    /// A definition inside this image.
    Defined { address: u64, class: SectionClass },
    /// A dylib's exported weak definition, which dyld may coalesce with
    /// another image's: pointers to it bind through the weak-lookup import
    /// `import`, and only image-relative differences use `address`.
    Coalesced {
        import: usize,
        address: u64,
        class: SectionClass,
    },
    /// A dylib import (index into the chained-fixups import table).
    Import(usize),
    /// An exclusively weak reference with no definition or provider.
    Null,
}

/// Dylib imports in object symbol-table order, with their library ordinals.
struct ImportTable<'c> {
    names: Vec<String>,
    index: HashMap<String, usize>,
    ordinals: Vec<u32>,
    dylibs: Vec<&'c DylibEntry>,
    /// Weak-lookup imports for a dylib's coalescable weak definitions.
    coalesced: HashMap<String, usize>,
}

impl<'c> ImportTable<'c> {
    /// Every undefined name a configured dylib provides becomes an import;
    /// a strong reference nobody provides is an undefined-symbol error.
    fn collect(resolver: &SymbolResolver, config: &'c DylibConfig) -> Result<Self, LinkerError> {
        let (_, names) = resolver.resolve_with_dylibs(config, 0)?;
        let dylibs: Vec<&DylibEntry> = config
            .needed_dylibs(&names)
            .into_iter()
            .map(|index| &config.dylibs[index])
            .collect();
        validate_dylib_imports(&dylibs, &names)?;
        let ordinals = names
            .iter()
            .map(|name| dylib_ordinal_for_symbol(&dylibs, name))
            .collect();
        let index = names
            .iter()
            .enumerate()
            .map(|(index, name)| (name.clone(), index))
            .collect();
        Ok(Self {
            names,
            index,
            ordinals,
            dylibs,
            coalesced: HashMap::new(),
        })
    }

    /// Append one weak-lookup import per coalescable weak definition, in name
    /// order, after the dylib imports, and re-admit the combined table into
    /// the compact import format.
    fn add_coalesced(&mut self, names: &[String]) -> Result<(), LinkerError> {
        for name in names {
            let import = self.names.len();
            self.names.push(name.clone());
            self.ordinals.push(BIND_SPECIAL_DYLIB_WEAK_LOOKUP_ORDINAL);
            self.coalesced.insert(name.clone(), import);
        }
        validate_import_table(&self.dylibs, &self.names, |symbol| {
            self.coalesced.contains_key(symbol)
        })
    }
}

/// Relocation-target resolution over one planned layout.
struct ImageSymbols<'a> {
    objects: &'a [ParsedObject],
    classes: &'a [Vec<SectionClass>],
    section_addrs: &'a [Vec<u64>],
    resolver: &'a SymbolResolver,
    locals: Vec<HashMap<usize, u64>>,
    imports: &'a ImportTable<'a>,
}

impl<'a> ImageSymbols<'a> {
    fn new(
        objects: &'a [ParsedObject],
        classes: &'a [Vec<SectionClass>],
        section_addrs: &'a [Vec<u64>],
        resolver: &'a SymbolResolver,
        imports: &'a ImportTable<'a>,
    ) -> Self {
        let locals = (0..objects.len())
            .map(|object| resolver.object_symbol_addrs(object))
            .collect();
        Self {
            objects,
            classes,
            section_addrs,
            resolver,
            locals,
            imports,
        }
    }

    fn defined(
        &self,
        object: usize,
        section: usize,
        address: u64,
    ) -> Result<RelocTarget, LinkerError> {
        let class = self.classes[object][section];
        if class == SectionClass::Debug {
            return Err(LinkerError::UnloadedSectionReference(section_label(
                &self.objects[object].sections[section],
            )));
        }
        Ok(RelocTarget::Defined { address, class })
    }

    /// Resolve a global name that some relocation already named validly.
    fn resolve_global(&self, name: &str) -> Result<RelocTarget, LinkerError> {
        if let Some(definition) = self.resolver.defined.get(name) {
            let target = self.defined(
                definition.object_index,
                definition.section_index,
                definition.address,
            )?;
            if let (Some(&import), RelocTarget::Defined { address, class }) =
                (self.imports.coalesced.get(name), target)
            {
                return Ok(RelocTarget::Coalesced {
                    import,
                    address,
                    class,
                });
            }
            return Ok(target);
        }
        if let Some(&import) = self.imports.index.get(name) {
            return Ok(RelocTarget::Import(import));
        }
        let referenced = self
            .resolver
            .undefined
            .iter()
            .any(|(_, _, undefined)| undefined == name);
        if referenced && !self.resolver.strong_refs.contains(name) {
            return Ok(RelocTarget::Null);
        }
        Err(LinkerError::UndefinedSymbol(name.to_owned()))
    }

    /// Resolve a relocation's target and, for symbol relocations, its slot key.
    fn resolve(
        &self,
        object: usize,
        reloc: &Relocation,
    ) -> Result<(RelocTarget, Option<SlotKey>), LinkerError> {
        let parsed = &self.objects[object];
        if !reloc.is_extern {
            let ordinal = reloc.symbol_index as usize;
            let section = ordinal
                .checked_sub(1)
                .filter(|section| *section < parsed.sections.len())
                .ok_or_else(|| {
                    LinkerError::MalformedRelocation(format!(
                        "section ordinal {ordinal} out of range (have {} sections)",
                        parsed.sections.len()
                    ))
                })?;
            let address = self.section_addrs[object][section];
            return Ok((self.defined(object, section, address)?, None));
        }
        let symbol_index = reloc.symbol_index as usize;
        let symbol = parsed.symbols.get(symbol_index).ok_or_else(|| {
            LinkerError::MalformedRelocation(format!(
                "symbol index {} out of range",
                reloc.symbol_index
            ))
        })?;
        if symbol.is_defined() && !symbol.is_external() {
            let address = self.locals[object].get(&symbol_index).copied().ok_or_else(|| {
                LinkerError::MalformedRelocation(format!(
                    "local defined symbol '{}' at index {symbol_index} has no object-local resolved address",
                    symbol.name
                ))
            })?;
            let target = self.defined(object, usize::from(symbol.section) - 1, address)?;
            return Ok((
                target,
                Some(SlotKey::Local {
                    object,
                    symbol: symbol_index,
                }),
            ));
        }
        if !symbol.is_defined() && !(symbol.is_undefined() && symbol.is_external()) {
            // Absolute, indirect and prebound symbols are not linkable here.
            return Err(LinkerError::UndefinedSymbol(symbol.name.to_string()));
        }
        let target = self.resolve_global(&symbol.name)?;
        Ok((target, Some(SlotKey::Global(symbol.name.clone()))))
    }

    fn resolve_key(&self, key: &SlotKey) -> Result<RelocTarget, LinkerError> {
        match key {
            SlotKey::Global(name) => self.resolve_global(name),
            &SlotKey::Local { object, symbol } => {
                let parsed = &self.objects[object].symbols[symbol];
                let address = self.locals[object].get(&symbol).copied().ok_or_else(|| {
                    LinkerError::MalformedRelocation(format!(
                        "local slot symbol '{}' has no resolved address",
                        parsed.name
                    ))
                })?;
                self.defined(object, usize::from(parsed.section) - 1, address)
            }
        }
    }

    fn import_name(&self, import: usize) -> &str {
        &self.imports.names[import]
    }
}

/// Stubs, GOT slots and TLV pointer slots an image needs, in slot order.
#[derive(Debug, Clone, Default)]
struct SlotPlan {
    /// Imports called through `__stubs` (import-table indices).
    stubs: Vec<usize>,
    /// GOT slots: every stubbed import first (in stub order), then the other
    /// `GOT_LOAD`/`POINTER_TO_GOT` targets in first-reference order.
    got: Vec<SlotKey>,
    /// `__thread_ptrs` slots in first-reference order.
    tlv_pointers: Vec<SlotKey>,
}

/// Collect the stubs and GOT/TLV slots named by every loaded section. Shape
/// errors are reported here, before any address is planned.
fn plan_slots(symbols: &ImageSymbols<'_>) -> Result<SlotPlan, LinkerError> {
    let mut stubbed = vec![false; symbols.imports.names.len()];
    let mut got_refs = Vec::new();
    let mut got_seen = HashSet::new();
    let mut tlv_pointers = Vec::new();
    let mut tlv_seen = HashSet::new();
    for (object_index, object) in symbols.objects.iter().enumerate() {
        for (section_index, section) in object.sections.iter().enumerate() {
            if matches!(
                symbols.classes[object_index][section_index],
                SectionClass::Debug | SectionClass::ThreadVars
            ) {
                continue;
            }
            for op in relocation_ops(&section.relocations)? {
                let RelocOp::Single { reloc, .. } = op else {
                    continue;
                };
                validate_relocation_shape(reloc)?;
                match reloc.kind {
                    AArch64RelocKind::Branch26 => {
                        if let (
                            RelocTarget::Import(import) | RelocTarget::Coalesced { import, .. },
                            _,
                        ) = symbols.resolve(object_index, reloc)?
                        {
                            stubbed[import] = true;
                        }
                    }
                    AArch64RelocKind::GotLoadPage21
                    | AArch64RelocKind::GotLoadPageoff12
                    | AArch64RelocKind::PointerToGot => {
                        let (_, key) = symbols.resolve(object_index, reloc)?;
                        let key = key.ok_or_else(|| {
                            LinkerError::MalformedRelocation(
                                "GOT relocation names no symbol".into(),
                            )
                        })?;
                        if got_seen.insert(key.clone()) {
                            got_refs.push(key);
                        }
                    }
                    AArch64RelocKind::TlvpLoadPage21 | AArch64RelocKind::TlvpLoadPageoff12 => {
                        let (_, key) = symbols.resolve(object_index, reloc)?;
                        let key = key.ok_or_else(|| {
                            LinkerError::MalformedRelocation(
                                "TLVP relocation names no symbol".into(),
                            )
                        })?;
                        if tlv_seen.insert(key.clone()) {
                            tlv_pointers.push(key);
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    let stubs: Vec<usize> = stubbed
        .iter()
        .enumerate()
        .filter_map(|(import, stubbed)| stubbed.then_some(import))
        .collect();
    let mut got: Vec<SlotKey> = stubs
        .iter()
        .map(|&import| SlotKey::Global(symbols.imports.names[import].as_str().into()))
        .collect();
    let stub_keys: HashSet<SlotKey> = got.iter().cloned().collect();
    got.extend(got_refs.into_iter().filter(|key| !stub_keys.contains(key)));
    Ok(SlotPlan {
        stubs,
        got,
        tlv_pointers,
    })
}

/// Applies one image's relocations against its final layout, recording every
/// pointer that dyld must rebase or bind.
struct ImageRelocator<'a> {
    symbols: &'a ImageSymbols<'a>,
    layout: &'a ImageLayout,
    got: HashMap<SlotKey, u64>,
    tlv_pointers: HashMap<SlotKey, u64>,
    stubs: HashMap<usize, u64>,
}

impl ImageRelocator<'_> {
    fn apply_section(
        &self,
        object: usize,
        section_index: usize,
        bytes: &mut [u8],
        address: u64,
        fixups: &mut Vec<PointerFixup>,
    ) -> Result<(), LinkerError> {
        let section = &self.symbols.objects[object].sections[section_index];
        let class = self.symbols.classes[object][section_index];
        if class == SectionClass::ThreadVars {
            return self.apply_thread_vars(object, section, bytes, address, fixups);
        }
        for op in relocation_ops(&section.relocations)? {
            match op {
                RelocOp::Difference {
                    subtrahend,
                    minuend,
                } => {
                    let subtrahend_addr = self.difference_operand(object, subtrahend)?;
                    let minuend_addr = self.difference_operand(object, minuend)?;
                    RelocationApplicator::apply_subtractor_pair(
                        bytes,
                        subtrahend.offset as usize,
                        minuend_addr,
                        subtrahend_addr,
                        subtrahend.length,
                    )?;
                }
                RelocOp::Single { reloc, addend } => self.apply_single(
                    object, section, class, reloc, addend, bytes, address, fixups,
                )?,
            }
        }
        Ok(())
    }

    /// A symbol difference is image-relative: no fixup, no imports, no TLVs.
    fn difference_operand(&self, object: usize, reloc: &Relocation) -> Result<u64, LinkerError> {
        match self.symbols.resolve(object, reloc)?.0 {
            RelocTarget::Defined { class, .. } if class.is_thread_local() => {
                Err(LinkerError::ThreadLocal(format!(
                    "a symbol difference at offset {:#x} names a thread-local variable",
                    reloc.offset
                )))
            }
            RelocTarget::Coalesced { class, .. } if class.is_thread_local() => {
                Err(LinkerError::ThreadLocal(format!(
                    "a symbol difference at offset {:#x} names a thread-local variable",
                    reloc.offset
                )))
            }
            // An image-relative difference (unwind/FDE ranges) describes this
            // image's own copy, whichever copy dyld binds pointers to.
            RelocTarget::Defined { address, .. } | RelocTarget::Coalesced { address, .. } => {
                Ok(address)
            }
            RelocTarget::Import(import) => Err(LinkerError::DirectImportReference {
                kind: reloc.kind,
                symbol: self.symbols.import_name(import).to_owned(),
            }),
            RelocTarget::Null => Ok(0),
        }
    }

    fn slot(
        &self,
        slots: &HashMap<SlotKey, u64>,
        key: Option<SlotKey>,
        kind: AArch64RelocKind,
    ) -> Result<u64, LinkerError> {
        key.and_then(|key| slots.get(&key).copied()).ok_or_else(|| {
            LinkerError::MalformedRelocation(format!("{kind:?} relocation has no planned slot"))
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn apply_single(
        &self,
        object: usize,
        section: &ParsedSection,
        class: SectionClass,
        reloc: &Relocation,
        addend: i64,
        bytes: &mut [u8],
        address: u64,
        fixups: &mut Vec<PointerFixup>,
    ) -> Result<(), LinkerError> {
        use AArch64RelocKind as K;
        validate_relocation_shape(reloc)?;
        let offset = reloc.offset as usize;
        let pc = layout_add(address, u64::from(reloc.offset), "relocation site")?;
        let (target, key) = self.symbols.resolve(object, reloc)?;
        let tlvp = matches!(reloc.kind, K::TlvpLoadPage21 | K::TlvpLoadPageoff12);
        let site = || {
            format!(
                "{:?} at {}+{:#x}",
                reloc.kind,
                section_label(section),
                reloc.offset
            )
        };
        match target {
            RelocTarget::Defined { class, .. } | RelocTarget::Coalesced { class, .. }
                if class.is_thread_local() && !tlvp =>
            {
                return Err(LinkerError::ThreadLocal(format!(
                    "{} names a thread-local variable or template; only ARM64_RELOC_TLVP_LOAD_* may address one",
                    site()
                )));
            }
            RelocTarget::Defined { class, .. } if tlvp && class != SectionClass::ThreadVars => {
                return Err(LinkerError::ThreadLocal(format!(
                    "{} names a symbol outside __thread_vars",
                    site()
                )));
            }
            RelocTarget::Null if tlvp => {
                return Err(LinkerError::ThreadLocal(format!(
                    "{} names an undefined weak thread-local variable",
                    site()
                )));
            }
            _ => {}
        }
        let direct = |target: RelocTarget| match target {
            RelocTarget::Defined { address, .. } => Ok(address),
            RelocTarget::Coalesced { import, .. } => {
                Err(LinkerError::DirectWeakDefinitionReference {
                    kind: reloc.kind,
                    symbol: self.symbols.import_name(import).to_owned(),
                })
            }
            RelocTarget::Import(import) => Err(LinkerError::DirectImportReference {
                kind: reloc.kind,
                symbol: self.symbols.import_name(import).to_owned(),
            }),
            RelocTarget::Null => Ok(0),
        };
        match reloc.kind {
            K::Branch26 => {
                let destination = match target {
                    RelocTarget::Import(import) | RelocTarget::Coalesced { import, .. } => {
                        *self.stubs.get(&import).ok_or_else(|| {
                            LinkerError::MalformedRelocation(
                                "branch to an import or coalescable weak definition has no stub"
                                    .into(),
                            )
                        })?
                    }
                    other => direct(other)?,
                };
                patch_branch26(bytes, offset, pc, offset_address(destination, addend)?)
            }
            K::Page21 => {
                let destination = offset_address(direct(target)?, addend)?;
                patch_page21(bytes, offset, pc, destination, reloc.kind)
            }
            K::Pageoff12 => {
                let destination = offset_address(direct(target)?, addend)?;
                patch_pageoff12(bytes, offset, destination, reloc.kind)
            }
            K::GotLoadPage21 => patch_page21(
                bytes,
                offset,
                pc,
                self.slot(&self.got, key, reloc.kind)?,
                reloc.kind,
            ),
            K::GotLoadPageoff12 => patch_pageoff12(
                bytes,
                offset,
                self.slot(&self.got, key, reloc.kind)?,
                reloc.kind,
            ),
            K::PointerToGot => {
                let slot = self.slot(&self.got, key, reloc.kind)?;
                let inline = RelocationApplicator::read_signed_addend(bytes, offset, 2)?;
                RelocationApplicator::write_sized_value(
                    bytes,
                    offset,
                    2,
                    i128::from(slot) + inline - i128::from(pc),
                )
            }
            K::TlvpLoadPage21 => patch_page21(
                bytes,
                offset,
                pc,
                self.slot(&self.tlv_pointers, key, reloc.kind)?,
                reloc.kind,
            ),
            K::TlvpLoadPageoff12 => patch_pageoff12(
                bytes,
                offset,
                self.slot(&self.tlv_pointers, key, reloc.kind)?,
                reloc.kind,
            ),
            K::Unsigned => self.apply_pointer(section, class, reloc, target, bytes, pc, fixups),
            other => Err(LinkerError::UnsupportedRelocation(other)),
        }
    }

    /// An absolute `UNSIGNED` pointer. Image addresses become rebases and
    /// imports become binds; both need a 64-bit data slot.
    #[allow(clippy::too_many_arguments)]
    fn apply_pointer(
        &self,
        section: &ParsedSection,
        class: SectionClass,
        reloc: &Relocation,
        target: RelocTarget,
        bytes: &mut [u8],
        pc: u64,
        fixups: &mut Vec<PointerFixup>,
    ) -> Result<(), LinkerError> {
        let offset = reloc.offset as usize;
        let inline = RelocationApplicator::read_signed_addend(bytes, offset, reloc.length)?;
        let unslidable = |detail| LinkerError::UnslidablePointer {
            section: section_label(section),
            offset: reloc.offset,
            detail,
        };
        let kind = match target {
            // An exclusively weak reference stays null plus its addend.
            RelocTarget::Null => {
                return RelocationApplicator::write_sized_value(
                    bytes,
                    offset,
                    reloc.length,
                    inline,
                );
            }
            _ if class == SectionClass::Text => {
                return Err(unslidable(
                    "__TEXT carries no dyld fixups; absolute pointers must live in a data section",
                ));
            }
            _ if reloc.length != 3 => {
                return Err(unslidable(
                    "a 32-bit field cannot hold a slid 64-bit image address",
                ));
            }
            RelocTarget::Defined { address, .. } => {
                let value = u64::try_from(i128::from(address) + inline).map_err(|_| {
                    LinkerError::RelocationOverflow {
                        detail: format!("UNSIGNED target {address:#x} plus addend overflowed"),
                    }
                })?;
                RelocationApplicator::write_sized_value(bytes, offset, 3, i128::from(value))?;
                PointerFixupKind::Rebase { target: value }
            }
            RelocTarget::Import(import) | RelocTarget::Coalesced { import, .. } => {
                let addend = u8::try_from(inline).map_err(|_| LinkerError::ChainedFixup {
                    address: pc,
                    detail: format!(
                        "bind of '{}' carries addend {inline}, outside the 0..=255 bind field",
                        self.symbols.import_name(import)
                    ),
                })?;
                RelocationApplicator::write_sized_value(bytes, offset, 3, 0)?;
                PointerFixupKind::Bind { import, addend }
            }
        };
        fixups.push(PointerFixup { address: pc, kind });
        Ok(())
    }

    /// Resolve `__thread_vars` descriptors `{thunk, key, offset}`: the thunk
    /// binds `__tlv_bootstrap`, the key stays zero for dyld, and the offset
    /// becomes the template's position in the contiguous TLV template image.
    fn apply_thread_vars(
        &self,
        object: usize,
        section: &ParsedSection,
        bytes: &mut [u8],
        address: u64,
        fixups: &mut Vec<PointerFixup>,
    ) -> Result<(), LinkerError> {
        let malformed = |detail: String| {
            LinkerError::ThreadLocal(format!(
                "object {object} {}: {detail}",
                section_label(section)
            ))
        };
        if !(bytes.len() as u64).is_multiple_of(TLV_DESCRIPTOR_SIZE) {
            return Err(malformed(
                "size is not a whole number of 24-byte TLV descriptors".into(),
            ));
        }
        let count = bytes.len() / TLV_DESCRIPTOR_SIZE as usize;
        let mut thunks = vec![false; count];
        let mut templates = vec![false; count];
        for op in relocation_ops(&section.relocations)? {
            let reloc = match op {
                RelocOp::Single { reloc, addend: 0 }
                    if reloc.kind == AArch64RelocKind::Unsigned
                        && !reloc.pc_relative
                        && reloc.length == 3 =>
                {
                    reloc
                }
                _ => {
                    return Err(malformed(
                        "descriptors accept only absolute 64-bit ARM64_RELOC_UNSIGNED relocations"
                            .into(),
                    ));
                }
            };
            let field = u64::from(reloc.offset);
            let descriptor = (field / TLV_DESCRIPTOR_SIZE) as usize;
            if descriptor >= count {
                return Err(malformed(format!(
                    "relocation at {field:#x} lies outside the descriptor table"
                )));
            }
            let slot_address = layout_add(address, field, "TLV descriptor slot")?;
            let (target, _) = self.symbols.resolve(object, reloc)?;
            let inline = RelocationApplicator::read_signed_addend(bytes, reloc.offset as usize, 3)?;
            match field % TLV_DESCRIPTOR_SIZE {
                0 => {
                    let bootstrap = match target {
                        RelocTarget::Import(import)
                            if self.symbols.import_name(import) == TLV_BOOTSTRAP_SYMBOL
                                && inline == 0 =>
                        {
                            import
                        }
                        _ => {
                            return Err(malformed(format!(
                                "descriptor {descriptor} thunk must bind dylib symbol {TLV_BOOTSTRAP_SYMBOL} with no addend"
                            )));
                        }
                    };
                    if std::mem::replace(&mut thunks[descriptor], true) {
                        return Err(malformed(format!(
                            "descriptor {descriptor} has two thunk relocations"
                        )));
                    }
                    RelocationApplicator::write_sized_value(bytes, reloc.offset as usize, 3, 0)?;
                    fixups.push(PointerFixup {
                        address: slot_address,
                        kind: PointerFixupKind::Bind {
                            import: bootstrap,
                            addend: 0,
                        },
                    });
                }
                TLV_DESCRIPTOR_OFFSET_FIELD => {
                    let template_address = match target {
                        RelocTarget::Defined {
                            address,
                            class: SectionClass::ThreadData | SectionClass::ThreadBss,
                        } => address,
                        _ => {
                            return Err(malformed(format!(
                                "descriptor {descriptor} offset must name a __thread_data/__thread_bss template"
                            )));
                        }
                    };
                    let base = self
                        .layout
                        .tls_base
                        .ok_or_else(|| malformed("the image has no TLV template".into()))?;
                    let image_size = self.layout.thread_bss.1 - base;
                    let template_offset = i128::from(template_address) + inline - i128::from(base);
                    if !(0..=i128::from(image_size)).contains(&template_offset) {
                        return Err(malformed(format!(
                            "descriptor {descriptor} template offset {template_offset} lies outside the {image_size}-byte TLV template image"
                        )));
                    }
                    if std::mem::replace(&mut templates[descriptor], true) {
                        return Err(malformed(format!(
                            "descriptor {descriptor} has two template relocations"
                        )));
                    }
                    RelocationApplicator::write_sized_value(
                        bytes,
                        reloc.offset as usize,
                        3,
                        template_offset,
                    )?;
                }
                _ => {
                    return Err(malformed(format!(
                        "relocation at {field:#x} is not a descriptor thunk or offset word"
                    )));
                }
            }
        }
        for descriptor in 0..count {
            if !thunks[descriptor] || !templates[descriptor] {
                return Err(malformed(format!(
                    "descriptor {descriptor} lacks its {TLV_BOOTSTRAP_SYMBOL} thunk or template-offset relocation"
                )));
            }
            let key =
                descriptor * TLV_DESCRIPTOR_SIZE as usize + TLV_DESCRIPTOR_KEY_OFFSET as usize;
            if bytes[key..key + 8].iter().any(|&byte| byte != 0) {
                return Err(malformed(format!(
                    "descriptor {descriptor} key word must be zero"
                )));
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Executable emission
// ---------------------------------------------------------------------------

/// One section header of the linked image (absolute address).
#[derive(Debug, Clone)]
struct OutputSection {
    sectname: &'static [u8],
    addr: u64,
    size: u64,
    align: u32,
    flags: u32,
}

impl OutputSection {
    fn is_zerofill(&self) -> bool {
        matches!(
            self.flags & SECTION_TYPE_MASK,
            S_ZEROFILL | S_GB_ZEROFILL | S_THREAD_LOCAL_ZEROFILL
        )
    }
}

/// A segment after `__TEXT` (`__DATA_CONST` or `__DATA`).
#[derive(Debug, Clone)]
struct OutputSegment {
    name: &'static [u8],
    vmaddr: u64,
    /// File-backed content starting at `vmaddr`.
    bytes: Vec<u8>,
    /// Virtual extent from `vmaddr`, including trailing zero-fill.
    virtual_size: u64,
    flags: u32,
    sections: Vec<OutputSection>,
    fixups: Vec<PointerFixup>,
}

/// Everything the emitter writes, fully planned.
struct ImagePlan<'a> {
    kind: ImageKind<'a>,
    /// `__TEXT` segment base (the Mach-O header's address).
    text_vmaddr: u64,
    /// Text content, starting at the first text section's address.
    text: Vec<u8>,
    text_sections: Vec<OutputSection>,
    /// `LC_MAIN` entry offset; executables only.
    entry_offset: Option<u64>,
    stubs_offset: u64,
    segments: Vec<OutputSegment>,
    dylibs: &'a [&'a DylibEntry],
    imports: &'a [String],
    import_ordinals: &'a [u32],
    exports_trie: Vec<u8>,
    /// Flags added to the kind's standard header flags.
    header_flags: u32,
}

/// Checked file/virtual extents of one planned image. Zero-fill contributes
/// to virtual extent only. Every address is validated before a payload is
/// allocated or narrowed to a Mach-O 32-bit file offset.
struct ExecutableLayout {
    text_file_offset: u64,
    text_segment_filesize: u64,
    /// `(fileoff, filesize, vmsize)` of each segment after `__TEXT`.
    segments: Vec<(u64, u64, u64)>,
    linkedit_file_offset: u64,
    linkedit_vmaddr: u64,
}

impl ExecutableLayout {
    /// `segments` lists `(vmaddr, file_size, virtual_size)` in address order.
    /// An executable needs an entry inside its text and a base outside
    /// `__PAGEZERO`; a dylib has neither.
    fn new(
        kind: ImageKind<'_>,
        text_size: u64,
        text_vmaddr: u64,
        entry_offset: Option<u64>,
        total_lc_size: u32,
        segments: &[(u64, u64, u64)],
    ) -> Result<Self, LinkerError> {
        let text_file_offset = executable_text_file_offset_from_lc_size(total_lc_size);
        let text_segment_filesize = layout_add(
            text_file_offset,
            checked_align_to(text_size, PAGE_SIZE)?,
            "text file extent",
        )?;
        layout_add(text_vmaddr, text_file_offset, "text content address")?;
        let text_end = layout_add(text_vmaddr, text_segment_filesize, "text segment end")?;
        let malformed = || {
            LinkerError::MalformedInput {
            file: "executable layout".into(),
            detail: "segments must be page-aligned, non-overlapping, outside __PAGEZERO, and cover their file bytes".into(),
        }
        };
        if text_vmaddr < kind.base() || !text_vmaddr.is_multiple_of(PAGE_SIZE) {
            return Err(malformed());
        }
        let mut file_cursor = text_segment_filesize;
        let mut vm_cursor = text_end;
        let mut extents = Vec::with_capacity(segments.len());
        for &(vmaddr, file_size, virtual_size) in segments {
            if virtual_size == 0
                || file_size > virtual_size
                || vmaddr < vm_cursor
                || !vmaddr.is_multiple_of(PAGE_SIZE)
            {
                return Err(malformed());
            }
            let filesize = checked_align_to(file_size, PAGE_SIZE)?;
            let vmsize = checked_align_to(virtual_size, PAGE_SIZE)?;
            extents.push((file_cursor, filesize, vmsize));
            file_cursor = layout_add(file_cursor, filesize, "data file extent")?;
            vm_cursor = layout_add(vmaddr, vmsize, "data virtual extent")?;
        }
        match (kind, entry_offset) {
            (ImageKind::Executable, Some(entry))
                if entry >= text_file_offset && entry - text_file_offset < text_size => {}
            (ImageKind::Dylib { .. }, None) => {}
            _ => return Err(LinkerError::NoEntryPoint),
        }
        if file_cursor > u64::from(u32::MAX) {
            return Err(LinkerError::LayoutOverflow("Mach-O file offsets"));
        }
        Ok(Self {
            text_file_offset,
            text_segment_filesize,
            segments: extents,
            linkedit_file_offset: file_cursor,
            linkedit_vmaddr: vm_cursor,
        })
    }

    /// Validate the last segment and reserve the complete image fallibly.
    fn reserve_image(&self, linkedit_filesize: u64) -> Result<Vec<u8>, LinkerError> {
        layout_add(
            self.linkedit_vmaddr,
            checked_align_to(linkedit_filesize, PAGE_SIZE)?,
            "linkedit virtual extent",
        )?;
        let total = layout_add(
            self.linkedit_file_offset,
            linkedit_filesize,
            "executable file extent",
        )?;
        if total > u64::from(u32::MAX) {
            return Err(LinkerError::LayoutOverflow("Mach-O file offsets"));
        }
        let capacity = usize::try_from(total)
            .map_err(|_| LinkerError::LayoutOverflow("image allocation size"))?;
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(capacity)
            .map_err(LinkerError::ImageAllocation)?;
        Ok(bytes)
    }
}

fn deterministic_image_uuid(plan: &ImagePlan<'_>) -> [u8; 16] {
    let mut lo = 0xCBF2_9CE4_8422_2325u64;
    let mut hi = 0x8422_2325_CBF2_9CE4u64;

    update_uuid_bytes(&mut lo, &mut hi, b"trust-cg-macho-image-v2");
    update_uuid_u64(&mut lo, &mut hi, u64::from(plan.kind.filetype()));
    if let ImageKind::Dylib { install_name } = plan.kind {
        update_uuid_bytes(&mut lo, &mut hi, install_name.as_bytes());
    }
    update_uuid_u64(&mut lo, &mut hi, plan.text_vmaddr);
    update_uuid_u64(&mut lo, &mut hi, plan.entry_offset.unwrap_or(u64::MAX));
    update_uuid_bytes(&mut lo, &mut hi, &plan.exports_trie);
    update_uuid_u64(&mut lo, &mut hi, plan.stubs_offset);
    update_uuid_u64(&mut lo, &mut hi, u64::from(plan.header_flags));
    update_uuid_bytes(&mut lo, &mut hi, &plan.text);
    update_uuid_u64(&mut lo, &mut hi, plan.segments.len() as u64);
    for segment in &plan.segments {
        update_uuid_bytes(&mut lo, &mut hi, segment.name);
        update_uuid_u64(&mut lo, &mut hi, segment.vmaddr);
        update_uuid_u64(&mut lo, &mut hi, segment.virtual_size);
        update_uuid_u64(&mut lo, &mut hi, u64::from(segment.flags));
        // Hashed after chain encoding, so every fixup is covered.
        update_uuid_bytes(&mut lo, &mut hi, &segment.bytes);
    }
    update_uuid_u64(&mut lo, &mut hi, plan.dylibs.len() as u64);
    for dylib in plan.dylibs {
        update_uuid_bytes(&mut lo, &mut hi, dylib.install_name.as_bytes());
    }
    update_uuid_u64(&mut lo, &mut hi, plan.imports.len() as u64);
    for symbol in plan.imports {
        update_uuid_bytes(&mut lo, &mut hi, symbol.as_bytes());
    }

    let mut uuid = [0u8; 16];
    uuid[..8].copy_from_slice(&lo.to_le_bytes());
    uuid[8..].copy_from_slice(&hi.to_le_bytes());
    uuid
}

/// Load-command bytes for a plan's actual section counts.
fn plan_load_command_size(
    plan: &ImagePlan<'_>,
    dylib_cmd_sizes: &[u32],
) -> Result<u32, LinkerError> {
    let mut size = u64::from(SEGMENT_COMMAND_64_SIZE) // __LINKEDIT
        + plan.kind.fixed_commands().1;
    let segment = |nsects: usize| {
        u64::from(SEGMENT_COMMAND_64_SIZE) + nsects as u64 * u64::from(SECTION_64_SIZE)
    };
    size += segment(plan.text_sections.len());
    for output in &plan.segments {
        size = layout_add(size, segment(output.sections.len()), "load commands")?;
    }
    for &dylib in dylib_cmd_sizes {
        size = layout_add(size, u64::from(dylib), "load commands")?;
    }
    u32::try_from(size).map_err(|_| LinkerError::LayoutOverflow("load command size"))
}

/// Emit a planned MH_EXECUTE or MH_DYLIB: header, load commands, segment
/// content, chained fixups, the exports trie and an ad-hoc code signature.
fn emit_image(mut plan: ImagePlan<'_>) -> Result<Vec<u8>, LinkerError> {
    let dylib_cmd_sizes: Vec<u32> = plan
        .dylibs
        .iter()
        .map(|dylib| dylib_command_size(dylib))
        .collect();
    let total_lc_size = plan_load_command_size(&plan, &dylib_cmd_sizes)?;
    let extents: Vec<(u64, u64, u64)> = plan
        .segments
        .iter()
        .map(|segment| {
            (
                segment.vmaddr,
                segment.bytes.len() as u64,
                segment.virtual_size,
            )
        })
        .collect();
    let base = plan.text_vmaddr;
    let layout = ExecutableLayout::new(
        plan.kind,
        plan.text.len() as u64,
        base,
        plan.entry_offset,
        total_lc_size,
        &extents,
    )?;
    let text_section_vmaddr = base + layout.text_file_offset;
    if plan
        .text_sections
        .first()
        .is_none_or(|section| section.addr != text_section_vmaddr)
    {
        return Err(LinkerError::MalformedInput {
            file: "executable layout".into(),
            detail: "planned text addresses disagree with the load-command size".into(),
        });
    }

    // Segment indices: [__PAGEZERO,] __TEXT, the data segments, __LINKEDIT.
    let first_data_segment = plan.kind.first_data_segment();
    let mut fixup_segments = Vec::new();
    for (index, segment) in plan.segments.iter_mut().enumerate() {
        if let Some(info) = encode_segment_chains(
            first_data_segment + index,
            segment.vmaddr,
            base,
            &mut segment.bytes,
            &mut segment.fixups,
        )? {
            fixup_segments.push(info);
        }
    }
    let segment_count = first_data_segment + plan.segments.len() + 1;
    // __TEXT, data segments and __LINKEDIT, the kind's fixed commands, dylibs.
    let ncmds =
        plan.segments.len() as u32 + 2 + plan.kind.fixed_commands().0 + plan.dylibs.len() as u32;
    let linkedit_payload = build_linkedit_payload(
        layout.linkedit_file_offset,
        segment_count,
        &fixup_segments,
        plan.imports,
        plan.import_ordinals,
        &plan.exports_trie,
    )?;
    let linkedit_filesize =
        linkedit_payload.data.len() as u64 + linkedit_payload.code_signature_size as u64;
    let linkedit_vmsize = align_to(linkedit_filesize, PAGE_SIZE);
    let total_file_size = layout.linkedit_file_offset + linkedit_filesize;
    let mut buf = layout.reserve_image(linkedit_filesize)?;

    // --- Header ---
    buf.extend_from_slice(&MH_MAGIC_64.to_le_bytes());
    buf.extend_from_slice(&CPU_TYPE_ARM64.to_le_bytes());
    buf.extend_from_slice(&CPU_SUBTYPE_ARM64_ALL.to_le_bytes());
    buf.extend_from_slice(&plan.kind.filetype().to_le_bytes());
    buf.extend_from_slice(&ncmds.to_le_bytes());
    buf.extend_from_slice(&total_lc_size.to_le_bytes());
    buf.extend_from_slice(&(plan.kind.header_flags() | plan.header_flags).to_le_bytes());
    buf.extend_from_slice(&0u32.to_le_bytes()); // reserved

    // --- __PAGEZERO (executables only) ---
    if plan.kind == ImageKind::Executable {
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
    }

    // --- __TEXT (maps the header and load commands from file offset 0) ---
    ExecutableEmitter::write_segment(
        &mut buf,
        b"__TEXT",
        base,
        layout.text_segment_filesize,
        0,
        layout.text_segment_filesize,
        VM_PROT_READ | VM_PROT_EXECUTE,
        VM_PROT_READ | VM_PROT_EXECUTE,
        plan.text_sections.len() as u32,
        0,
    );
    for section in &plan.text_sections {
        ExecutableEmitter::write_section_header(
            &mut buf,
            section.sectname,
            b"__TEXT",
            section.addr,
            section.size,
            (section.addr - base) as u32,
            section.align,
            0,
            0,
            section.flags,
        );
    }

    // --- __DATA_CONST / __DATA ---
    for (segment, &(fileoff, filesize, vmsize)) in plan.segments.iter().zip(&layout.segments) {
        ExecutableEmitter::write_segment(
            &mut buf,
            segment.name,
            segment.vmaddr,
            vmsize,
            fileoff,
            filesize,
            VM_PROT_READ | VM_PROT_WRITE,
            VM_PROT_READ | VM_PROT_WRITE,
            segment.sections.len() as u32,
            segment.flags,
        );
        for section in &segment.sections {
            let offset = if section.is_zerofill() {
                0
            } else {
                (fileoff + (section.addr - segment.vmaddr)) as u32
            };
            ExecutableEmitter::write_section_header(
                &mut buf,
                section.sectname,
                segment.name,
                section.addr,
                section.size,
                offset,
                section.align,
                0,
                0,
                section.flags,
            );
        }
    }

    // --- __LINKEDIT ---
    ExecutableEmitter::write_segment(
        &mut buf,
        b"__LINKEDIT",
        layout.linkedit_vmaddr,
        linkedit_vmsize,
        layout.linkedit_file_offset,
        linkedit_filesize,
        VM_PROT_READ,
        VM_PROT_READ,
        0,
        0,
    );

    write_lc_build_version(&mut buf);
    write_lc_uuid(&mut buf, deterministic_image_uuid(&plan));

    match (plan.kind, plan.entry_offset) {
        (ImageKind::Executable, Some(entry_offset)) => {
            // --- LC_MAIN ---
            buf.extend_from_slice(&LC_MAIN.to_le_bytes());
            buf.extend_from_slice(&LC_MAIN_SIZE.to_le_bytes());
            buf.extend_from_slice(&entry_offset.to_le_bytes());
            buf.extend_from_slice(&0u64.to_le_bytes()); // stacksize (0 = default)
        }
        (ImageKind::Dylib { install_name }, None) => {
            // --- LC_ID_DYLIB ---
            write_dylib_command(&mut buf, LC_ID_DYLIB, 1, install_name);
        }
        _ => return Err(LinkerError::NoEntryPoint),
    }

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

    // --- LC_SYMTAB / LC_DYSYMTAB (empty, for format compliance) ---
    buf.extend_from_slice(&LC_SYMTAB.to_le_bytes());
    buf.extend_from_slice(&SYMTAB_COMMAND_SIZE.to_le_bytes());
    buf.extend_from_slice(&[0u8; 16]); // symoff, nsyms, stroff, strsize
    write_empty_lc_dysymtab(&mut buf);

    if plan.kind == ImageKind::Executable {
        write_lc_load_dylinker(&mut buf);
    }

    // --- LC_LOAD_DYLIB commands ---
    for dylib in plan.dylibs {
        write_dylib_command(&mut buf, LC_LOAD_DYLIB, 2, &dylib.install_name);
    }
    debug_assert_eq!(
        buf.len() as u64,
        MACH_HEADER_64_SIZE as u64 + u64::from(total_lc_size)
    );

    // --- Segment content ---
    buf.resize(layout.text_file_offset as usize, 0);
    buf.extend_from_slice(&plan.text);
    buf.resize(layout.text_segment_filesize as usize, 0);
    for (segment, &(fileoff, filesize, _)) in plan.segments.iter().zip(&layout.segments) {
        debug_assert_eq!(buf.len() as u64, fileoff);
        buf.extend_from_slice(&segment.bytes);
        buf.resize((fileoff + filesize) as usize, 0);
    }

    // --- __LINKEDIT payloads ---
    debug_assert_eq!(buf.len() as u64, layout.linkedit_file_offset);
    buf.extend_from_slice(&linkedit_payload.data);
    debug_assert_eq!(buf.len() as u64, linkedit_payload.code_signature_offset);
    let code_signature = build_ad_hoc_code_signature(
        &buf,
        0,
        layout.text_segment_filesize,
        plan.kind.exec_seg_flags(),
    )?;
    debug_assert_eq!(
        code_signature.len() as u32,
        linkedit_payload.code_signature_size
    );
    buf.extend_from_slice(&code_signature);
    buf.resize(total_file_size as usize, 0);
    self_check_code_signature(
        &buf,
        layout.text_segment_filesize,
        plan.kind.exec_seg_flags(),
    )?;
    Ok(buf)
}

/// Append a `dylib_command` (`LC_LOAD_DYLIB` or `LC_ID_DYLIB`) naming
/// `install_name`, version 1.0.0, padded to 8 bytes.
fn write_dylib_command(buf: &mut Vec<u8>, cmd: u32, timestamp: u32, install_name: &str) {
    let cmd_size = id_dylib_command_size(install_name) as u32;
    buf.extend_from_slice(&cmd.to_le_bytes());
    buf.extend_from_slice(&cmd_size.to_le_bytes());
    buf.extend_from_slice(&LC_LOAD_DYLIB_HEADER_SIZE.to_le_bytes()); // name.offset
    buf.extend_from_slice(&timestamp.to_le_bytes());
    buf.extend_from_slice(&0x0001_0000u32.to_le_bytes()); // current_version 1.0.0
    buf.extend_from_slice(&0x0001_0000u32.to_le_bytes()); // compatibility_version 1.0.0
    let name_bytes = install_name.as_bytes();
    buf.extend_from_slice(name_bytes);
    buf.push(0);
    let written = LC_LOAD_DYLIB_HEADER_SIZE as usize + name_bytes.len() + 1;
    buf.extend(std::iter::repeat_n(0, cmd_size as usize - written));
}

/// Emits a Mach-O MH_EXECUTE binary from linked sections.
pub struct ExecutableEmitter;

impl ExecutableEmitter {
    /// Emit a complete MH_EXECUTE Mach-O file.
    ///
    /// - `text_data`: concatenated, relocated __TEXT section data.
    /// - `data_data`: concatenated, relocated __DATA section data.
    /// - `text_vmaddr`: virtual address of the __TEXT segment.
    /// - `data_vmaddr`: virtual address of the __DATA segment.
    /// - `entry_offset`: offset of _main within the __TEXT segment (from text_vmaddr).
    ///
    /// The data carries no dyld fixups, so it must not contain image pointers.
    pub fn emit(
        text_data: &[u8],
        data_data: &[u8],
        text_vmaddr: u64,
        data_vmaddr: u64,
        entry_offset: u64,
    ) -> Result<Vec<u8>, LinkerError> {
        Self::emit_with_virtual_data(
            text_data,
            data_data,
            text_vmaddr,
            data_vmaddr,
            entry_offset,
            data_data.len() as u64,
        )
    }

    /// The layout may reserve a zero-fill tail larger than the file payload.
    fn emit_with_virtual_data(
        text_data: &[u8],
        data_data: &[u8],
        text_vmaddr: u64,
        data_vmaddr: u64,
        entry_offset: u64,
        data_virtual_size: u64,
    ) -> Result<Vec<u8>, LinkerError> {
        let has_data = data_virtual_size > 0;
        if !has_data && !data_data.is_empty() {
            return Err(LinkerError::MalformedInput {
                file: "executable layout".into(),
                detail: "file-backed data needs a virtual data extent".into(),
            });
        }
        let shape = ImageShape {
            data: has_data,
            ..ImageShape::default()
        };
        let text_file_offset = executable_text_file_offset_from_lc_size(image_load_command_size(
            ImageKind::Executable,
            &shape,
            &[],
        )?);
        let text_addr = layout_add(text_vmaddr, text_file_offset, "text content address")?;
        let segments = if has_data {
            vec![OutputSegment {
                name: b"__DATA",
                vmaddr: data_vmaddr,
                bytes: data_data.to_vec(),
                virtual_size: data_virtual_size,
                flags: 0,
                sections: vec![OutputSection {
                    sectname: b"__data",
                    addr: data_vmaddr,
                    size: data_data.len() as u64,
                    align: 3,
                    flags: S_REGULAR,
                }],
                fixups: Vec::new(),
            }]
        } else {
            Vec::new()
        };
        emit_image(ImagePlan {
            kind: ImageKind::Executable,
            text_vmaddr,
            text: text_data.to_vec(),
            text_sections: vec![OutputSection {
                sectname: b"__text",
                addr: text_addr,
                size: text_data.len() as u64,
                align: 2,
                flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS,
            }],
            entry_offset: Some(entry_offset),
            stubs_offset: 0,
            segments,
            dylibs: &[],
            imports: &[],
            import_ordinals: &[],
            exports_trie: EMPTY_EXPORTS_TRIE.to_vec(),
            header_flags: 0,
        })
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
        // S_SYMBOL_STUBS uses reserved2 for the instruction-stub byte size.
        let reserved2 = if flags & SECTION_TYPE_MASK == S_SYMBOL_STUBS {
            STUB_SIZE
        } else {
            0
        };
        buf.extend_from_slice(&reserved2.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes()); // reserved3
    }
}

// ---------------------------------------------------------------------------
// Dead code stripping
// ---------------------------------------------------------------------------

/// Perform basic dead code stripping by removing unreferenced sections.
///
/// This is conservative: retain the entry point, all relocation targets (even
/// from otherwise dead sections), non-__TEXT sections, and N_NO_DEAD_STRIP
/// definitions. Both symbol-index and local section-ordinal relocations are
/// remapped alongside the surviving symbols. ADDEND payloads are not indices.
///
/// Returns a filtered set of objects with unreferenced __TEXT sections removed.
/// Invalid symbol/section references return an error rather than becoming a
/// different valid reference after filtering.
pub fn dead_strip_sections(
    objects: &[ParsedObject],
    entry_symbol: &str,
) -> Result<Vec<ParsedObject>, LinkerError> {
    // Seed from every relocation, so no iterative name closure is necessary.
    // Local section references remain object-scoped; names conservatively
    // retain all matching definitions across objects.
    let mut referenced_symbols: HashSet<SymbolName> = HashSet::new();
    referenced_symbols.insert(entry_symbol.into());
    let mut referenced_sections = Vec::with_capacity(objects.len());
    for (object_index, obj) in objects.iter().enumerate() {
        if obj.sections.len() > usize::from(u8::MAX)
            || obj.symbols.iter().any(|sym| {
                usize::from(sym.section) > obj.sections.len()
                    || (sym.is_defined() && sym.section == 0)
            })
        {
            return Err(LinkerError::MalformedInput {
                file: format!("object {object_index}"),
                detail: "dead stripping requires representable, valid symbol section ordinals"
                    .into(),
            });
        }
        let mut section_targets = HashSet::new();
        for sec in &obj.sections {
            for reloc in &sec.relocations {
                if reloc.kind == AArch64RelocKind::Addend {
                    continue;
                }
                if reloc.is_extern {
                    let sym = obj.symbols.get(reloc.symbol_index as usize).ok_or_else(|| {
                        LinkerError::MalformedRelocation(format!(
                            "object {object_index}: symbol index {} out of range during dead stripping",
                            reloc.symbol_index
                        ))
                    })?;
                    referenced_symbols.insert(sym.name.clone());
                } else {
                    let ordinal = reloc.symbol_index as usize;
                    if ordinal == 0 || ordinal > obj.sections.len() {
                        return Err(LinkerError::MalformedRelocation(format!(
                            "object {object_index}: section ordinal {ordinal} out of range during dead stripping"
                        )));
                    }
                    section_targets.insert(ordinal - 1);
                }
            }
        }
        referenced_sections.push(section_targets);
    }

    // Filter sections and symbols, retaining both old-to-new index maps.
    objects
        .iter()
        .zip(&referenced_sections)
        .map(|(obj, section_targets)| {
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

                if has_referenced_sym
                    || has_no_dead_strip
                    || is_data
                    || section_targets.contains(&sec_idx)
                {
                    sections.push(sec.clone());
                    ordinal_map.push(Some(sections.len() as u8));
                } else {
                    ordinal_map.push(None);
                }
            }

            // Remap each kept symbol's section ordinal to its new index. Drop a
            // symbol whose defining section was stripped (it can no longer be
            // located); undefined symbols (section == 0) pass through unchanged.
            let mut symbols = Vec::new();
            let mut symbol_map = Vec::with_capacity(obj.symbols.len());
            for sym in &obj.symbols {
                let new_ordinal = if sym.section == 0 {
                    Some(0)
                } else {
                    ordinal_map[usize::from(sym.section) - 1]
                };
                if let Some(section) = new_ordinal {
                    let index = u32::try_from(symbols.len())
                        .map_err(|_| LinkerError::LayoutOverflow("stripped symbol index"))?;
                    symbol_map.push(Some(index));
                    let mut symbol = sym.clone();
                    symbol.section = section;
                    symbols.push(symbol);
                } else {
                    symbol_map.push(None);
                }
            }

            for section in &mut sections {
                for reloc in &mut section.relocations {
                    if reloc.kind == AArch64RelocKind::Addend {
                        continue;
                    }
                    let remapped = if reloc.is_extern {
                        symbol_map
                            .get(reloc.symbol_index as usize)
                            .copied()
                            .flatten()
                    } else {
                        reloc
                            .symbol_index
                            .checked_sub(1)
                            .and_then(|index| ordinal_map.get(index as usize))
                            .copied()
                            .flatten()
                            .map(u32::from)
                    };
                    reloc.symbol_index = remapped.ok_or_else(|| {
                        LinkerError::MalformedRelocation(
                            "live relocation target was removed during dead stripping".into(),
                        )
                    })?;
                }
            }

            Ok(ParsedObject {
                cputype: obj.cputype,
                cpusubtype: obj.cpusubtype,
                flags: obj.flags,
                sections,
                symbols,
            })
        })
        .collect()
}

// ---------------------------------------------------------------------------
// High-level link API
// ---------------------------------------------------------------------------

fn append_at(output: &mut Vec<u8>, offset: u64, bytes: &[u8]) -> Result<(), LinkerError> {
    let end = layout_add(offset, bytes.len() as u64, "file-backed section end")?;
    // Mach-O section and linkedit payload offsets are u32 fields. Diagnose an
    // unrepresentable image before a large alignment gap causes allocation.
    u32::try_from(end).map_err(|_| LinkerError::LayoutOverflow("file offset domain"))?;
    let offset =
        usize::try_from(offset).map_err(|_| LinkerError::LayoutOverflow("host file offset"))?;
    let end = usize::try_from(end).map_err(|_| LinkerError::LayoutOverflow("host image length"))?;
    let extra = end
        .checked_sub(output.len())
        .filter(|_| offset >= output.len())
        .ok_or(LinkerError::LayoutOverflow("overlapping section placement"))?;
    output
        .try_reserve(extra)
        .map_err(LinkerError::ImageAllocation)?;
    output.resize(offset, 0);
    output.extend_from_slice(bytes);
    Ok(())
}

/// Link multiple parsed object files into an executable.
///
/// No dylib is loaded, so every strong undefined symbol is an error. GOT
/// slots for image definitions are rebased; thread-local variables need
/// `__tlv_bootstrap` from libSystem and therefore [`link_with_dylibs`].
///
/// Returns the raw bytes of a Mach-O MH_EXECUTE file.
pub fn link(objects: &[ParsedObject]) -> Result<Vec<u8>, LinkerError> {
    link_image(objects, &DylibConfig::new(), ImageKind::Executable).map(|placed| placed.image)
}

/// Link multiple parsed object files into an `MH_DYLIB` identified by
/// `install_name` (its `LC_ID_DYLIB`).
///
/// Relocations, imports, GOT/TLV slots and chained fixups follow
/// [`link_with_dylibs`]; the image is based at 0 and has no entry point.
/// Every external, non-private definition is exported through the exports
/// trie (TLV descriptors as thread-local exports), and references inside the
/// dylib bind directly to its own definitions (two-level namespace, no
/// interposition). Weak exports, which need dyld weak-definition coalescing,
/// are refused.
pub fn link_dylib(
    objects: &[ParsedObject],
    dylib_config: &DylibConfig,
    install_name: &str,
) -> Result<Vec<u8>, LinkerError> {
    link_dylib_placed(objects, dylib_config, install_name).map(|placed| placed.image)
}

// ---------------------------------------------------------------------------
// Exports trie
// ---------------------------------------------------------------------------

/// One exported symbol: its name, `EXPORT_SYMBOL_FLAGS_*` and image offset.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ExportEntry {
    name: String,
    flags: u64,
    offset: u64,
}

fn push_uleb128(buf: &mut Vec<u8>, mut value: u64) {
    loop {
        let byte = (value & 0x7F) as u8;
        value >>= 7;
        if value == 0 {
            buf.push(byte);
            return;
        }
        buf.push(byte | 0x80);
    }
}

fn uleb128_len(value: u64) -> u64 {
    let mut len = 1;
    let mut rest = value >> 7;
    while rest != 0 {
        len += 1;
        rest >>= 7;
    }
    len
}

#[derive(Debug, Default)]
struct TrieNode {
    terminal: Option<(u64, u64)>,
    edges: Vec<(Vec<u8>, usize)>,
    offset: u64,
}

impl TrieNode {
    fn terminal_bytes(&self) -> u64 {
        match self.terminal {
            None => 1,
            Some((flags, offset)) => {
                let info = uleb128_len(flags) + uleb128_len(offset);
                uleb128_len(info) + info
            }
        }
    }
}

/// Insert `entries` (sorted, unique suffixes) below `node` as a radix tree:
/// an empty suffix makes the node terminal; the rest share one edge per
/// first byte, labeled with the group's longest common prefix.
fn build_trie_node(nodes: &mut Vec<TrieNode>, node: usize, entries: &[(&[u8], (u64, u64))]) {
    let mut rest = entries;
    if let Some((suffix, info)) = rest.first()
        && suffix.is_empty()
    {
        nodes[node].terminal = Some(*info);
        rest = &rest[1..];
    }
    let mut start = 0;
    while start < rest.len() {
        let first = rest[start].0[0];
        let end = start
            + rest[start..]
                .iter()
                .take_while(|(suffix, _)| suffix[0] == first)
                .count();
        let group = &rest[start..end];
        let prefix = group[1..]
            .iter()
            .fold(group[0].0.len(), |prefix, (suffix, _)| {
                prefix.min(
                    group[0]
                        .0
                        .iter()
                        .zip(suffix.iter())
                        .take_while(|(left, right)| left == right)
                        .count(),
                )
            });
        let child = nodes.len();
        nodes.push(TrieNode::default());
        nodes[node]
            .edges
            .push((group[0].0[..prefix].to_vec(), child));
        let suffixes: Vec<_> = group
            .iter()
            .map(|(suffix, info)| (&suffix[prefix..], *info))
            .collect();
        build_trie_node(nodes, child, &suffixes);
        start = end;
    }
}

/// Serialize the dyld exports trie for `exports` (unique names). Node offsets
/// are ULEB128-encoded in their parents, so they are iterated to a fixed
/// point in preorder before the bytes are written.
fn build_exports_trie(exports: &[ExportEntry]) -> Result<Vec<u8>, LinkerError> {
    let mut sorted: Vec<&ExportEntry> = exports.iter().collect();
    sorted.sort_by(|left, right| left.name.cmp(&right.name));
    if sorted.windows(2).any(|pair| pair[0].name == pair[1].name) {
        return Err(LinkerError::MalformedInput {
            file: "exports trie".into(),
            detail: "duplicate exported symbol".into(),
        });
    }
    let entries: Vec<(&[u8], (u64, u64))> = sorted
        .iter()
        .map(|entry| (entry.name.as_bytes(), (entry.flags, entry.offset)))
        .collect();
    let mut nodes = vec![TrieNode::default()];
    build_trie_node(&mut nodes, 0, &entries);
    if nodes
        .iter()
        .any(|node| node.edges.len() > usize::from(u8::MAX))
    {
        return Err(LinkerError::LayoutOverflow("exports trie child count"));
    }
    let mut order = Vec::with_capacity(nodes.len());
    let mut stack = vec![0usize];
    while let Some(node) = stack.pop() {
        order.push(node);
        stack.extend(nodes[node].edges.iter().rev().map(|(_, child)| *child));
    }
    loop {
        let mut offset = 0u64;
        let mut changed = false;
        for &node in &order {
            if nodes[node].offset != offset {
                nodes[node].offset = offset;
                changed = true;
            }
            let edges: u64 = nodes[node]
                .edges
                .iter()
                .map(|(label, child)| label.len() as u64 + 1 + uleb128_len(nodes[*child].offset))
                .sum();
            offset = layout_add(
                offset,
                nodes[node].terminal_bytes() + 1 + edges,
                "exports trie",
            )?;
        }
        if !changed {
            break;
        }
    }
    let mut trie = Vec::new();
    for &node in &order {
        debug_assert_eq!(trie.len() as u64, nodes[node].offset);
        match nodes[node].terminal {
            None => trie.push(0),
            Some((flags, offset)) => {
                push_uleb128(&mut trie, uleb128_len(flags) + uleb128_len(offset));
                push_uleb128(&mut trie, flags);
                push_uleb128(&mut trie, offset);
            }
        }
        trie.push(nodes[node].edges.len() as u8);
        for (label, child) in &nodes[node].edges {
            trie.extend_from_slice(label);
            trie.push(0);
            push_uleb128(&mut trie, nodes[*child].offset);
        }
    }
    Ok(trie)
}

/// The default-visibility (non-private) weak definitions a dylib exports,
/// sorted by name: every reference to one binds through dyld's weak lookup.
fn coalescable_weak_definitions(
    objects: &[ParsedObject],
    resolver: &SymbolResolver,
) -> Vec<String> {
    let mut names: Vec<String> = resolver
        .defined
        .iter()
        .filter(|(name, definition)| {
            definition.is_weak
                && !objects[definition.object_index]
                    .symbols
                    .iter()
                    .any(|symbol| {
                        &symbol.name == *name
                            && symbol.is_defined()
                            && symbol.is_external()
                            && symbol.n_type & N_PEXT != 0
                    })
        })
        .map(|(name, _)| name.to_string())
        .collect();
    names.sort();
    names
}

/// The external, non-private definitions a dylib exports, as image offsets.
fn collect_dylib_exports(
    objects: &[ParsedObject],
    classes: &[Vec<SectionClass>],
    resolver: &SymbolResolver,
    base: u64,
) -> Result<Vec<ExportEntry>, LinkerError> {
    let mut names: Vec<&SymbolName> = resolver.defined.keys().collect();
    names.sort();
    let mut exports = Vec::new();
    for name in names {
        let definition = &resolver.defined[name];
        let private = objects[definition.object_index]
            .symbols
            .iter()
            .find(|symbol| &symbol.name == name && symbol.is_defined() && symbol.is_external())
            .is_some_and(|symbol| symbol.n_type & N_PEXT != 0);
        if private {
            continue;
        }
        let refuse = |detail| LinkerError::UnsupportedDylibExport {
            symbol: name.to_string(),
            detail,
        };
        let flags = match classes[definition.object_index][definition.section_index] {
            SectionClass::Debug => {
                return Err(refuse("it is defined in an unloaded debug section"));
            }
            SectionClass::ThreadData | SectionClass::ThreadBss => {
                return Err(refuse(
                    "a thread-local template is not a variable; export its TLV descriptor",
                ));
            }
            SectionClass::ThreadVars if definition.is_weak => {
                return Err(refuse(
                    "a weak thread-local descriptor needs weak TLV coalescing, which this linker does not emit",
                ));
            }
            SectionClass::ThreadVars => EXPORT_SYMBOL_FLAGS_KIND_THREAD_LOCAL,
            _ if definition.is_weak => {
                EXPORT_SYMBOL_FLAGS_KIND_REGULAR | EXPORT_SYMBOL_FLAGS_WEAK_DEFINITION
            }
            _ => EXPORT_SYMBOL_FLAGS_KIND_REGULAR,
        };
        exports.push(ExportEntry {
            name: name.to_string(),
            flags,
            offset: definition.address - base,
        });
    }
    Ok(exports)
}

/// Refuse, before relocated bytes are allocated, any pointer slot whose page
/// index cannot be expressed in the 16-bit chained-fixup page fields.
fn check_fixup_pages(
    objects: &[ParsedObject],
    classes: &[Vec<SectionClass>],
    layout: &ImageLayout,
    shape: &ImageShape,
) -> Result<(), LinkerError> {
    let overflow = || LinkerError::LayoutOverflow("compact chained-fixup import/page fields");
    let page_limit = u64::from(u16::MAX);
    if shape.has_const() && (layout.const_end - layout.const_vmaddr) / PAGE_SIZE >= page_limit {
        return Err(overflow());
    }
    for ((object, classes), addresses) in objects.iter().zip(classes).zip(&layout.section_addrs) {
        for ((section, class), &address) in object.sections.iter().zip(classes).zip(addresses) {
            let segment_vmaddr = match class {
                SectionClass::Data | SectionClass::ThreadVars | SectionClass::ThreadData => {
                    layout.data_vmaddr
                }
                SectionClass::ConstData => layout.const_vmaddr,
                _ => continue,
            };
            for op in relocation_ops(&section.relocations)? {
                if let RelocOp::Single { reloc, .. } = op
                    && reloc.kind == AArch64RelocKind::Unsigned
                {
                    let slot = layout_add(address, u64::from(reloc.offset), "relocation site")?;
                    if (slot - segment_vmaddr) / PAGE_SIZE >= page_limit {
                        return Err(overflow());
                    }
                }
            }
        }
    }
    Ok(())
}

/// The shared image linker behind [`link`], [`link_with_dylibs`] and
/// [`link_dylib`].
fn link_image(
    objects: &[ParsedObject],
    config: &DylibConfig,
    kind: ImageKind<'_>,
) -> Result<PlacedImage, LinkerError> {
    let classes = classify_objects(objects)?;
    let base = kind.base();

    // 1. Name-level prepass at provisional addresses: symbol identities,
    // imports, stubs and GOT/TLV slots. Their counts fix the load commands,
    // and therefore the mapped text base, before any final address exists.
    let provisional_shape = ImageShape::new(objects, &classes, 0, 0, 0);
    let provisional = plan_layout(objects, &classes, &provisional_shape, base)?;
    let mut prepass = SymbolResolver::new();
    for (index, object) in objects.iter().enumerate() {
        prepass.add_object(index, object, &provisional.section_addrs[index])?;
    }
    let mut imports = ImportTable::collect(&prepass, config)?;
    // Only a dylib exports its weak definitions for dyld to coalesce; an
    // executable resolves its own weak definitions statically. The set is
    // name-level, so the prepass resolver fixes it before any address.
    let coalesced = match kind {
        ImageKind::Dylib { .. } => coalescable_weak_definitions(objects, &prepass),
        ImageKind::Executable => Vec::new(),
    };
    imports.add_coalesced(&coalesced)?;
    let slots = plan_slots(&ImageSymbols::new(
        objects,
        &classes,
        &provisional.section_addrs,
        &prepass,
        &imports,
    ))?;
    let shape = ImageShape::new(
        objects,
        &classes,
        slots.stubs.len(),
        slots.got.len(),
        slots.tlv_pointers.len(),
    );
    let dylib_cmd_sizes: Vec<u32> = imports
        .dylibs
        .iter()
        .map(|dylib| dylib_command_size(dylib))
        .collect();
    let text_file_offset = executable_text_file_offset_from_lc_size(image_load_command_size(
        kind,
        &shape,
        &dylib_cmd_sizes,
    )?);
    let text_vmaddr = layout_add(base, text_file_offset, "text content address")?;

    // 2. Final layout and symbol resolution.
    let layout = plan_layout(objects, &classes, &shape, text_vmaddr)?;
    let mut resolver = SymbolResolver::new();
    for (index, object) in objects.iter().enumerate() {
        resolver.add_object(index, object, &layout.section_addrs[index])?;
    }
    let (entry_offset, exports_trie) = match kind {
        ImageKind::Executable => {
            let entry_addr = resolver
                .defined
                .get("_main")
                .map(|symbol| symbol.address)
                .ok_or(LinkerError::NoEntryPoint)?;
            let entry_offset = entry_addr
                .checked_sub(base)
                .ok_or(LinkerError::NoEntryPoint)?;
            (Some(entry_offset), EMPTY_EXPORTS_TRIE.to_vec())
        }
        ImageKind::Dylib { .. } => (
            None,
            build_exports_trie(&collect_dylib_exports(objects, &classes, &resolver, base)?)?,
        ),
    };
    check_fixup_pages(objects, &classes, &layout, &shape)?;
    let symbols = ImageSymbols::new(
        objects,
        &classes,
        &layout.section_addrs,
        &resolver,
        &imports,
    );
    let slot_addresses = |base: u64, keys: &[SlotKey]| -> HashMap<SlotKey, u64> {
        keys.iter()
            .enumerate()
            .map(|(index, key)| (key.clone(), base + index as u64 * 8))
            .collect()
    };
    let relocator = ImageRelocator {
        symbols: &symbols,
        layout: &layout,
        got: slot_addresses(layout.got_addr, &slots.got),
        tlv_pointers: slot_addresses(layout.tlv_pointers_addr, &slots.tlv_pointers),
        stubs: slots
            .stubs
            .iter()
            .enumerate()
            .map(|(index, &import)| {
                (
                    import,
                    layout.stubs_addr + index as u64 * u64::from(STUB_SIZE),
                )
            })
            .collect(),
    };

    // 3. Relocate every loaded section at its planned address.
    let mut text = Vec::new();
    let mut data_pieces = Vec::new();
    let mut data_fixups = Vec::new();
    let mut const_pieces = Vec::new();
    let mut const_data_fixups = Vec::new();
    for (object_index, object) in objects.iter().enumerate() {
        for (section_index, section) in object.sections.iter().enumerate() {
            let class = classes[object_index][section_index];
            if matches!(
                class,
                SectionClass::Debug | SectionClass::ThreadBss | SectionClass::ZeroFill
            ) {
                continue;
            }
            let address = layout.section_addrs[object_index][section_index];
            let mut bytes = section.data.clone();
            let fixups = if class == SectionClass::ConstData {
                &mut const_data_fixups
            } else {
                &mut data_fixups
            };
            relocator.apply_section(object_index, section_index, &mut bytes, address, fixups)?;
            match class {
                SectionClass::Text => {
                    append_at(&mut text, address - layout.text_vmaddr, &bytes)?;
                }
                SectionClass::ConstData => const_pieces.push((address, bytes)),
                _ => data_pieces.push((address, bytes)),
            }
        }
    }
    // Data classes are placed class by class, not in input order; copy them
    // in address order so the append-only image builder sees rising offsets.
    data_pieces.sort_by_key(|(address, _)| *address);
    let mut data = Vec::new();
    for (address, bytes) in &data_pieces {
        append_at(&mut data, address - layout.data_vmaddr, bytes)?;
    }
    drop(data_pieces);
    // Stubs load their own GOT slot: stubbed imports occupy the first slots.
    if !slots.stubs.is_empty() {
        let stubs = generate_stubs(slots.stubs.len(), layout.stubs_addr, layout.got_addr)?;
        append_at(&mut text, layout.stubs_addr - layout.text_vmaddr, &stubs)?;
    }
    append_at(&mut text, layout.text_end - layout.text_vmaddr, &[])?;
    if shape.data {
        append_at(&mut data, layout.data_file_end - layout.data_vmaddr, &[])?;
    } else if !data.is_empty() || !data_fixups.is_empty() {
        return Err(LinkerError::MalformedInput {
            file: "executable layout".into(),
            detail: "data bytes were produced for an image planned without __DATA".into(),
        });
    }

    // 4. GOT and TLV pointer slots: binds for imports, rebases for image
    // definitions, zero for exclusively weak references.
    let const_size = usize::try_from(layout.const_end - layout.const_vmaddr)
        .map_err(|_| LinkerError::LayoutOverflow("GOT extent"))?;
    let mut const_bytes = Vec::new();
    const_bytes
        .try_reserve_exact(const_size)
        .map_err(LinkerError::ImageAllocation)?;
    const_bytes.resize(const_size, 0);
    for (address, bytes) in &const_pieces {
        let start = usize::try_from(address - layout.const_vmaddr)
            .map_err(|_| LinkerError::LayoutOverflow("read-only-after-fixup data offset"))?;
        const_bytes
            .get_mut(start..start + bytes.len())
            .ok_or(LinkerError::LayoutOverflow(
                "read-only-after-fixup data extent",
            ))?
            .copy_from_slice(bytes);
    }
    drop(const_pieces);
    let mut const_fixups = const_data_fixups;
    for (index, key) in slots.got.iter().enumerate() {
        let address = layout.got_addr + index as u64 * 8;
        match symbols.resolve_key(key)? {
            RelocTarget::Defined { class, .. } if class.is_thread_local() => {
                return Err(LinkerError::ThreadLocal(format!(
                    "GOT slot {key:?} names a thread-local variable"
                )));
            }
            RelocTarget::Coalesced { class, .. } if class.is_thread_local() => {
                return Err(LinkerError::ThreadLocal(format!(
                    "GOT slot {key:?} names a thread-local variable"
                )));
            }
            RelocTarget::Defined {
                address: target, ..
            } => const_fixups.push(PointerFixup {
                address,
                kind: PointerFixupKind::Rebase { target },
            }),
            RelocTarget::Import(import) | RelocTarget::Coalesced { import, .. } => const_fixups
                .push(PointerFixup {
                    address,
                    kind: PointerFixupKind::Bind { import, addend: 0 },
                }),
            RelocTarget::Null => {}
        }
    }
    for (index, key) in slots.tlv_pointers.iter().enumerate() {
        let address = layout.tlv_pointers_addr + index as u64 * 8;
        let kind = match symbols.resolve_key(key)? {
            RelocTarget::Defined {
                address: target,
                class: SectionClass::ThreadVars,
            } => PointerFixupKind::Rebase { target },
            RelocTarget::Import(import) => PointerFixupKind::Bind { import, addend: 0 },
            _ => {
                return Err(LinkerError::ThreadLocal(format!(
                    "TLV pointer slot {key:?} does not name a TLV descriptor"
                )));
            }
        };
        const_fixups.push(PointerFixup { address, kind });
    }

    // 5. Assemble segments and emit.
    let mut text_sections = vec![OutputSection {
        sectname: b"__text",
        addr: layout.text_vmaddr,
        size: if slots.stubs.is_empty() {
            layout.text_end
        } else {
            layout.stubs_addr
        } - layout.text_vmaddr,
        align: 2,
        flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS,
    }];
    if !slots.stubs.is_empty() {
        text_sections.push(OutputSection {
            sectname: b"__stubs",
            addr: layout.stubs_addr,
            size: layout.text_end - layout.stubs_addr,
            align: 2,
            flags: S_SYMBOL_STUBS | S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS,
        });
    }
    let alignment_exponent = |alignment: u64| alignment.trailing_zeros();
    let mut segments = Vec::new();
    if shape.has_const() {
        let mut sections = Vec::new();
        if shape.got > 0 {
            sections.push(OutputSection {
                sectname: b"__got",
                addr: layout.got_addr,
                size: layout.tlv_pointers_addr - layout.got_addr,
                align: 3,
                flags: S_NON_LAZY_SYMBOL_POINTERS,
            });
        }
        if shape.tlv_pointers > 0 {
            sections.push(OutputSection {
                sectname: b"__thread_ptrs",
                addr: layout.tlv_pointers_addr,
                size: layout.tlv_pointers_end - layout.tlv_pointers_addr,
                align: 3,
                flags: S_THREAD_LOCAL_VARIABLE_POINTERS,
            });
        }
        if shape.const_data {
            sections.push(OutputSection {
                sectname: b"__const",
                addr: layout.const_data.0,
                size: layout.const_data.1 - layout.const_data.0,
                align: 3,
                flags: S_REGULAR,
            });
        }
        segments.push(OutputSegment {
            name: b"__DATA_CONST",
            vmaddr: layout.const_vmaddr,
            virtual_size: layout.const_end - layout.const_vmaddr,
            bytes: const_bytes,
            flags: SG_READ_ONLY,
            sections,
            fixups: const_fixups,
        });
    }
    if shape.data {
        let mut sections = vec![OutputSection {
            sectname: b"__data",
            addr: layout.data_vmaddr,
            size: layout.regular_end - layout.data_vmaddr,
            align: 3,
            flags: S_REGULAR,
        }];
        let ranges = [
            (
                shape.thread_vars,
                b"__thread_vars" as &'static [u8],
                layout.thread_vars,
                3,
                S_THREAD_LOCAL_VARIABLES,
            ),
            (
                shape.thread_data,
                b"__thread_data",
                layout.thread_data,
                alignment_exponent(layout.tls_alignment),
                S_THREAD_LOCAL_REGULAR,
            ),
            (
                shape.thread_bss,
                b"__thread_bss",
                layout.thread_bss,
                alignment_exponent(layout.tls_alignment),
                S_THREAD_LOCAL_ZEROFILL,
            ),
        ];
        for (present, sectname, (start, end), align, flags) in ranges {
            if present {
                sections.push(OutputSection {
                    sectname,
                    addr: start,
                    size: end - start,
                    align,
                    flags,
                });
            }
        }
        segments.push(OutputSegment {
            name: b"__DATA",
            vmaddr: layout.data_vmaddr,
            virtual_size: layout.data_end - layout.data_vmaddr,
            bytes: data,
            flags: 0,
            sections,
            fixups: data_fixups,
        });
    }
    let section_addresses = layout
        .section_addrs
        .iter()
        .zip(&classes)
        .map(|(addresses, classes)| {
            addresses
                .iter()
                .zip(classes)
                .map(|(&address, &class)| (class != SectionClass::Debug).then_some(address))
                .collect()
        })
        .collect();
    let image = emit_image(ImagePlan {
        kind,
        text_vmaddr: base,
        text,
        text_sections,
        entry_offset,
        stubs_offset: layout.stubs_addr - layout.text_vmaddr,
        segments,
        dylibs: &imports.dylibs,
        imports: &imports.names,
        import_ordinals: &imports.ordinals,
        exports_trie,
        header_flags: (if shape.thread_vars {
            MH_HAS_TLV_DESCRIPTORS
        } else {
            0
        }) | (if coalesced.is_empty() {
            0
        } else {
            MH_WEAK_DEFINES | MH_BINDS_TO_WEAK
        }),
    })?;
    Ok(PlacedImage {
        image,
        section_addresses,
    })
}

/// A standalone link's image and where it placed every input section.
///
/// The placement is what [`super::linked_image::AtomPlacement::SectionAddresses`]
/// takes: the image carries no symbol table, so the linked-image replay
/// needs the linker's section addresses, which it checks against the
/// image's content, exports and entry point.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlacedImage {
    /// The Mach-O image bytes ([`link_with_dylibs`] and [`link_dylib`]
    /// return exactly these).
    pub image: Vec<u8>,
    /// Per object and section, in input order: the section's image address,
    /// or `None` for a section this linker does not load (`S_ATTR_DEBUG`).
    pub section_addresses: Vec<Vec<Option<u64>>>,
}

/// [`link_with_dylibs`], also returning where each input section was placed.
pub fn link_with_dylibs_placed(
    objects: &[ParsedObject],
    dylib_config: &DylibConfig,
) -> Result<PlacedImage, LinkerError> {
    link_image(objects, dylib_config, ImageKind::Executable)
}

/// [`link_dylib`], also returning where each input section was placed.
pub fn link_dylib_placed(
    objects: &[ParsedObject],
    dylib_config: &DylibConfig,
    install_name: &str,
) -> Result<PlacedImage, LinkerError> {
    if install_name.is_empty() || install_name.as_bytes().contains(&0) {
        return Err(LinkerError::MalformedInput {
            file: "dylib install name".into(),
            detail: "an install name must be nonempty and contain no NUL".into(),
        });
    }
    link_image(objects, dylib_config, ImageKind::Dylib { install_name })
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
            // dyld's TLV bootstrap thunk, bound by every `__thread_vars` descriptor.
            TLV_BOOTSTRAP_SYMBOL,
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
/// in the object graph. This name-level helper assigns every dylib symbol a
/// provisional stub address; the image linker uses only its import list and
/// allocates stubs for branch targets alone.
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
            result.insert(name.to_string(), sym.address);
        }

        // Process undefined symbols.
        let mut stub_offset = 0u64;
        for (_obj_idx, _sym_idx, name) in &self.undefined {
            let name = name.as_str();
            if result.contains_key(name) {
                continue;
            }
            if dylib_config.is_dylib_symbol(name) {
                // Assign a stub address for this dylib symbol.
                let stub_addr = layout_add(stub_base_addr, stub_offset, "import stub address")?;
                result.insert(name.to_owned(), stub_addr);
                if !dylib_symbols.iter().any(|symbol| symbol == name) {
                    dylib_symbols.push(name.to_owned());
                    stub_offset =
                        layout_add(stub_offset, u64::from(STUB_SIZE), "import stub offset")?;
                }
            } else if !self.strong_refs.contains(name) {
                // Only exclusively weak references may remain unresolved.
                result.insert(name.to_owned(), 0);
            } else {
                return Err(LinkerError::UndefinedSymbol(name.to_owned()));
            }
        }

        Ok((result, dylib_symbols))
    }
}

/// Link multiple parsed object files into an executable with dylib support.
///
/// Every undefined symbol a configured dylib provides becomes a chained-fixups
/// import. Branches to an import go through `__stubs`; `GOT_LOAD`,
/// `POINTER_TO_GOT` and `TLVP_LOAD` relocations load `__DATA_CONST` slots that
/// dyld binds (imports) or rebases (image definitions); 64-bit data pointers
/// are bound or rebased in place. PC-relative or difference relocations that
/// name an import are refused.
///
/// Returns the raw bytes of a Mach-O MH_EXECUTE file.
pub fn link_with_dylibs(
    objects: &[ParsedObject],
    dylib_config: &DylibConfig,
) -> Result<Vec<u8>, LinkerError> {
    link_image(objects, dylib_config, ImageKind::Executable).map(|placed| placed.image)
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
    num_stubs: usize,
    stub_base_addr: u64,
    got_base_addr: u64,
) -> Result<Vec<u8>, LinkerError> {
    let length = num_stubs
        .checked_mul(STUB_SIZE as usize)
        .ok_or(LinkerError::LayoutOverflow("stub bytes"))?;
    let mut stubs = Vec::new();
    stubs
        .try_reserve(length)
        .map_err(LinkerError::ImageAllocation)?;
    for index in 0..num_stubs {
        let pc = layout_add(
            stub_base_addr,
            index as u64 * u64::from(STUB_SIZE),
            "stub PC",
        )?;
        let got = layout_add(got_base_addr, index as u64 * 8, "GOT entry")?;
        let page_delta = (i128::from(got & !0xfff) - i128::from(pc & !0xfff)) >> 12;
        if !(-(1i128 << 20)..(1i128 << 20)).contains(&page_delta) || got % 8 != 0 {
            return Err(LinkerError::RelocationOverflow {
                detail: "stub cannot address its aligned GOT entry".to_string(),
            });
        }
        let immediate = (page_delta as u32) & 0x1f_ffff;
        let adrp_x16 = 0x9000_0010u32 | ((immediate & 3) << 29) | ((immediate >> 2) << 5);
        let ldr_x16 = 0xF940_0210u32 | (((got & 0xfff) as u32 / 8) << 10);
        let br_x16 = 0xD61F_0200u32; // BR X16

        stubs.extend_from_slice(&adrp_x16.to_le_bytes());
        stubs.extend_from_slice(&ldr_x16.to_le_bytes());
        stubs.extend_from_slice(&br_x16.to_le_bytes());
    }

    Ok(stubs)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

// The integration tests' executable runner, whose deadline excludes the time
// macOS holds a freshly linked executable before its first instruction.
#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
#[path = "../../tests/common/rosetta.rs"]
mod native_process;

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

    /// One pointer slot decoded from the chained fixups, independently of the
    /// encoder: `(unslid address, meaning)`.
    #[derive(Debug, Clone, PartialEq, Eq)]
    enum DecodedFixup {
        Rebase(u64),
        Bind { symbol: String, addend: u8 },
    }

    /// Walk every DYLD_CHAINED_PTR_64 chain following `<mach-o/fixup-chains.h>`:
    /// starts-in-image, per-segment page starts, 4-byte-stride `next` deltas,
    /// 36-bit rebase vmaddrs and 24-bit import ordinals.
    fn decode_chained_fixups(exe: &[u8]) -> Vec<(u64, DecodedFixup)> {
        let commands = walk_load_commands(exe);
        let segments = segment_commands(exe, &commands);
        let image_base = single_segment(&segments, "__TEXT").vmaddr;
        let payload =
            linkedit_data_command(exe, single_load_command(&commands, LC_DYLD_CHAINED_FIXUPS));
        let start = payload.dataoff as usize;
        let starts = start + rd_u32(exe, start + 4) as usize;
        let imports_offset = start + rd_u32(exe, start + 8) as usize;
        let symbols_offset = start + rd_u32(exe, start + 12) as usize;
        let imports_count = rd_u32(exe, start + 16) as usize;
        assert_eq!(rd_u32(exe, starts) as usize, segments.len());
        let mut decoded = Vec::new();
        for (index, segment) in segments.iter().enumerate() {
            let info = rd_u32(exe, starts + 4 + index * 4) as usize;
            if info == 0 {
                continue;
            }
            let seg = starts + info;
            assert_eq!(
                u16::from_le_bytes([exe[seg + 4], exe[seg + 5]]),
                PAGE_SIZE as u16
            );
            assert_eq!(
                u16::from_le_bytes([exe[seg + 6], exe[seg + 7]]),
                DYLD_CHAINED_PTR_64
            );
            assert_eq!(rd_u64(exe, seg + 8), segment.vmaddr - image_base);
            assert_eq!(rd_u32(exe, seg + 16), 0, "max_valid_pointer");
            let page_count = u16::from_le_bytes([exe[seg + 20], exe[seg + 21]]) as u64;
            assert!(page_count * PAGE_SIZE <= segment.vmsize);
            let mut chains = 0;
            for page in 0..page_count {
                let entry = seg + 22 + page as usize * 2;
                let page_start = u16::from_le_bytes([exe[entry], exe[entry + 1]]);
                if page_start == DYLD_CHAINED_PTR_START_NONE {
                    continue;
                }
                chains += 1;
                let mut offset = page * PAGE_SIZE + u64::from(page_start);
                loop {
                    assert!(offset + 8 <= segment.filesize, "chain leaves file bytes");
                    assert_eq!(offset / PAGE_SIZE, page, "chain leaves its page");
                    let raw = rd_u64(exe, (segment.fileoff + offset) as usize);
                    let next = (raw >> 51) & 0xFFF;
                    let address = segment.vmaddr + offset;
                    if raw >> 63 == 1 {
                        assert_eq!((raw >> 32) & 0x7FFFF, 0, "bind reserved bits");
                        let ordinal = (raw & 0xFF_FFFF) as usize;
                        assert!(ordinal < imports_count, "bind ordinal out of range");
                        let entry = rd_u32(exe, imports_offset + ordinal * 4);
                        let symbol = read_cstring(exe, symbols_offset + (entry >> 9) as usize);
                        decoded.push((
                            address,
                            DecodedFixup::Bind {
                                symbol,
                                addend: ((raw >> 24) & 0xFF) as u8,
                            },
                        ));
                    } else {
                        assert_eq!((raw >> 44) & 0x7F, 0, "rebase reserved bits");
                        let target = (raw & ((1 << 36) - 1)) | (((raw >> 36) & 0xFF) << 56);
                        decoded.push((address, DecodedFixup::Rebase(target)));
                    }
                    if next == 0 {
                        break;
                    }
                    offset += next * 4;
                }
            }
            assert!(chains > 0, "a segment starts entry must name a chain");
        }
        decoded
    }

    fn assert_chained_fixups_payload(
        exe: &[u8],
        command: &LinkeditDataCommand,
        expected_segment_count: u32,
        expected_imports: &[&str],
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

        // Every chain decodes, and binds name only the listed imports.
        for (address, fixup) in decode_chained_fixups(exe) {
            if let DecodedFixup::Bind { symbol, .. } = fixup {
                assert!(
                    expected_imports.contains(&symbol.as_str()),
                    "unexpected bind of {symbol} at {address:#x}"
                );
            }
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
        assert_eq!(
            n_code_slots,
            code_signature_block_count(command.dataoff).unwrap()
        );
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
            let expected = reference_sha256_digest(&exe[block_start..block_end]);
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
        assert_chained_fixups_payload(exe, &fixups, segments.len() as u32, expected_imports);
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
    fn signature_hash_matches_known_vectors_and_independent_padding_oracle() {
        for (input, expected) in [
            (
                b"".as_slice(),
                "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            ),
            (
                b"abc".as_slice(),
                "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
            ),
        ] {
            let digest = sha256_digest(input);
            let encoded: String = digest.iter().map(|byte| format!("{byte:02x}")).collect();
            assert_eq!(encoded, expected);
            assert_eq!(digest, reference_sha256_digest(input));
        }
        for len in [1, 55, 56, 63, 64, 65, 119, 120, 127, 128, 4095, 4096, 16384] {
            let input: Vec<u8> = (0..len).map(|index| (index * 37) as u8).collect();
            assert_eq!(
                sha256_digest(&input),
                reference_sha256_digest(&input),
                "CodeDirectory hash changed at input length {len}"
            );
        }
    }

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
            matches!(&err, LinkerError::MalformedInput { detail, .. }
                if detail.contains("run past the end of the")),
            "expected the oversized section to be refused, got {err:?}"
        );
    }

    /// One LC_SEGMENT_64 carrying the given section_64 headers (as
    /// `(size, file offset, flags)`), followed by `tail` after the commands.
    #[cfg(test)]
    fn mk_object_with_sections(sections: &[(u64, u32, u32)], tail: &[u8]) -> Vec<u8> {
        let mut seg = vec![0u8; SEGMENT_COMMAND_64_SIZE as usize];
        seg[0..4].copy_from_slice(&LC_SEGMENT_64.to_le_bytes());
        let cmdsize = SEGMENT_COMMAND_64_SIZE + SECTION_64_SIZE * sections.len() as u32;
        seg[4..8].copy_from_slice(&cmdsize.to_le_bytes());
        seg[64..68].copy_from_slice(&(sections.len() as u32).to_le_bytes());
        for &(size, offset, flags) in sections {
            let mut sec = vec![0u8; SECTION_64_SIZE as usize];
            sec[0..6].copy_from_slice(b"__data");
            sec[16..22].copy_from_slice(b"__DATA");
            sec[40..48].copy_from_slice(&size.to_le_bytes());
            sec[48..52].copy_from_slice(&offset.to_le_bytes());
            sec[64..68].copy_from_slice(&flags.to_le_bytes());
            seg.extend_from_slice(&sec);
        }
        let mut data = mk_object_with_one_lc(1, &seg);
        data.extend_from_slice(tail);
        data
    }

    /// A regular section whose file data runs past the end of the input is
    /// refused. The parser used to zero-fill it: a truncated 16-byte `__data`
    /// parsed as 16 zero bytes. A zero-fill section still owns no file bytes.
    #[test]
    fn test_parse_section_data_past_the_input_is_refused_not_zero_filled() {
        let data_offset = 32 + SEGMENT_COMMAND_64_SIZE + SECTION_64_SIZE;
        let whole = mk_object_with_sections(&[(16, data_offset, 0)], &[0xAB; 16]);
        let parsed = MachOParser::parse(&whole).expect("in-bounds section data parses");
        assert_eq!(parsed.sections[0].data, vec![0xAB; 16]);

        let truncated = mk_object_with_sections(&[(16, data_offset, 0)], &[0xAB; 4]);
        let err = MachOParser::parse(&truncated).unwrap_err();
        assert!(
            matches!(&err, LinkerError::MalformedInput { detail, .. }
                if detail.contains("16 bytes of file data") && detail.contains("run past the end")),
            "expected the truncated section to be refused, got {err:?}"
        );

        let bss = mk_object_with_sections(&[(1 << 20, 0, S_ZEROFILL)], &[]);
        let parsed = MachOParser::parse(&bss).expect("a zero-fill section owns no file bytes");
        assert!(parsed.sections[0].data.is_empty());
        assert_eq!(parsed.sections[0].vmsize, 1 << 20);
    }

    /// Sections together cannot own more file bytes than the input. Before,
    /// every section could copy (or zero-fill) up to the whole input, so the
    /// memory a crafted input cost grew with the square of its length.
    #[test]
    fn test_parse_sections_claiming_more_bytes_than_the_input_are_refused() {
        let data_offset = 32 + SEGMENT_COMMAND_64_SIZE + 4 * SECTION_64_SIZE;
        let shared = [(200, data_offset, 0); 4];
        let data = mk_object_with_sections(&shared, &[0x11; 200]);
        assert!(data.len() < 4 * 200);
        let err = MachOParser::parse(&data).unwrap_err();
        assert!(
            matches!(&err, LinkerError::MalformedInput { detail, .. }
                if detail.contains("sections claim") && detail.contains("more than the")),
            "expected sections claiming 800 bytes of a {}-byte input to be refused, got {err:?}",
            data.len()
        );
    }

    /// Section headers lie inside their LC_SEGMENT_64. A command whose
    /// `nsects` overruns its `cmdsize` used to take the next load command as a
    /// section header.
    #[test]
    fn test_parse_section_headers_beyond_the_segment_cmdsize_are_refused() {
        let mut seg = vec![0u8; SEGMENT_COMMAND_64_SIZE as usize];
        seg[0..4].copy_from_slice(&LC_SEGMENT_64.to_le_bytes());
        seg[4..8].copy_from_slice(&SEGMENT_COMMAND_64_SIZE.to_le_bytes());
        seg[64..68].copy_from_slice(&1u32.to_le_bytes()); // nsects = 1, no room for it
        let mut sym = vec![0u8; SYMTAB_COMMAND_SIZE as usize];
        sym[0..4].copy_from_slice(&LC_SYMTAB.to_le_bytes());
        sym[4..8].copy_from_slice(&SYMTAB_COMMAND_SIZE.to_le_bytes());
        let mut lc = seg;
        lc.extend_from_slice(&sym);
        let mut data = mk_object_with_one_lc(2, &lc);
        data.extend_from_slice(&[0u8; 80]);
        let err = MachOParser::parse(&data).unwrap_err();
        assert!(
            matches!(&err, LinkerError::MalformedInput { detail, .. }
                if detail.contains("section headers do not fit")),
            "expected the overrunning section header to be refused, got {err:?}"
        );
    }

    /// One LC_SYMTAB whose symbols name the string indices `strx` of the
    /// string table `strings`. Each nlist is 16 bytes; the string table
    /// follows the symbols.
    #[cfg(test)]
    fn mk_object_with_symbol_names(strx: &[u32], strings: &[u8]) -> Vec<u8> {
        let nsyms = strx.len() as u32;
        let symoff = 32 + SYMTAB_COMMAND_SIZE;
        let stroff = symoff + nsyms * 16;
        let mut sym = vec![0u8; SYMTAB_COMMAND_SIZE as usize];
        sym[0..4].copy_from_slice(&LC_SYMTAB.to_le_bytes());
        sym[4..8].copy_from_slice(&SYMTAB_COMMAND_SIZE.to_le_bytes());
        sym[8..12].copy_from_slice(&symoff.to_le_bytes());
        sym[12..16].copy_from_slice(&nsyms.to_le_bytes());
        sym[16..20].copy_from_slice(&stroff.to_le_bytes());
        sym[20..24].copy_from_slice(&(strings.len() as u32).to_le_bytes());
        let mut data = mk_object_with_one_lc(1, &sym);
        for index in strx {
            let mut nlist = [0u8; 16];
            nlist[0..4].copy_from_slice(&index.to_le_bytes());
            nlist[4] = 0x0f; // N_SECT | N_EXT
            data.extend_from_slice(&nlist);
        }
        data.extend_from_slice(strings);
        data
    }

    /// Whether every symbol name is a tail of the first one's bytes: one
    /// shared allocation, not a copy per symbol.
    #[cfg(test)]
    fn names_share_storage(symbols: &[ParsedSymbol]) -> bool {
        let longest = symbols
            .iter()
            .max_by_key(|symbol| symbol.name.len())
            .expect("at least one symbol");
        let range = longest.name.as_bytes().as_ptr_range();
        symbols.iter().all(|symbol| {
            let end = symbol.name.as_bytes().as_ptr_range().end;
            symbol.name.is_empty() || (range.contains(&symbol.name.as_ptr()) && end == range.end)
        })
    }

    /// Many symbols naming one long string, or tails of it, parse without a
    /// copy per symbol. Each name used to be scanned and copied separately:
    /// 4095 symbols sharing a 256 KiB name copied 1.07 GB. A later bound
    /// refused such inputs, and with them valid tail-merged objects.
    #[test]
    fn test_parse_symbols_sharing_one_long_name_share_its_bytes() {
        let long = 256 * 1024;
        let mut strings = vec![0u8];
        strings.extend(std::iter::repeat_n(b'a', long));
        strings.push(0);
        // The same string 4095 times, then 4095 distinct tails of it.
        let same = vec![1u32; 4095];
        let tails: Vec<u32> = (1..=4095).collect();
        for strx in [same, tails] {
            let data = mk_object_with_symbol_names(&strx, &strings);
            let parsed = MachOParser::parse(&data).expect("shared names parse");
            assert_eq!(parsed.symbols.len(), strx.len());
            for (symbol, index) in parsed.symbols.iter().zip(&strx) {
                assert_eq!(symbol.name.len(), long + 1 - *index as usize);
            }
            // Every name is a tail of the first symbol's, which is all `a`s.
            assert!(parsed.symbols[0].name.bytes().all(|byte| byte == b'a'));
            assert!(names_share_storage(&parsed.symbols));
        }
    }

    /// Tail-merged names parse to their own tails of one run.
    #[test]
    fn test_parse_tail_merged_names() {
        let strings = b"\0_foo_bar\0baz\0";
        let data = mk_object_with_symbol_names(&[1, 5, 8, 9, 0, 10], strings);
        let parsed = MachOParser::parse(&data).expect("tail-merged names parse");
        let names: Vec<&str> = parsed
            .symbols
            .iter()
            .map(|symbol| symbol.name.as_str())
            .collect();
        assert_eq!(names, ["_foo_bar", "_bar", "r", "", "", "baz"]);
        assert!(names_share_storage(&parsed.symbols[..4]));
    }

    /// rustc tail-merges the Mach-O string table: this arm64 object's 42
    /// symbols name 2,937 bytes (terminators included) from a 168-byte table
    /// in a 1,272-byte object. It must parse, every name intact.
    #[test]
    fn test_parse_rustc_tail_merged_object() {
        let data = include_bytes!("../../tests/fixtures/macho_tail_merged/tail_merged.macho");
        assert_eq!(data.len(), 1272);
        let parsed = MachOParser::parse(data).expect("rustc's tail-merged object parses");
        assert_eq!(parsed.symbols.len(), 42);
        let chain = |n: usize| {
            let mut name = String::from("_");
            for k in (1..=n).rev() {
                name.push_str(&format!("S{k}_"));
            }
            name.push('A');
            name
        };
        let mut names: Vec<String> = parsed
            .symbols
            .iter()
            .map(|symbol| symbol.name.to_string())
            .collect();
        names.sort();
        let mut expected: Vec<String> = (0..=39).map(chain).collect();
        expected.extend(["ltmp0".to_string(), "ltmp1".to_string()]);
        expected.sort();
        assert_eq!(names, expected);
        let total: usize = parsed
            .symbols
            .iter()
            .map(|symbol| symbol.name.len() + 1)
            .sum();
        assert_eq!(total, 2937);
        let global: Vec<ParsedSymbol> = parsed
            .symbols
            .iter()
            .filter(|symbol| symbol.name.starts_with('_'))
            .cloned()
            .collect();
        assert_eq!(global.len(), 40);
        assert!(names_share_storage(&global));
    }

    /// A name is UTF-8 exactly as before names were shared: a valid tail of
    /// a run with invalid bytes earlier parses, and a name that is not UTF-8
    /// (invalid bytes, or starting inside a character) is refused.
    #[test]
    fn test_parse_symbol_name_utf8_is_checked_per_name() {
        let strings = b"\0\xffab\0x\xc3\xa9\0\xe0\xa0\0";
        let parsed = MachOParser::parse(&mk_object_with_symbol_names(&[2, 5, 6, 11], strings))
            .expect("UTF-8 tails parse");
        let names: Vec<&str> = parsed
            .symbols
            .iter()
            .map(|symbol| symbol.name.as_str())
            .collect();
        assert_eq!(names, ["ab", "x\u{e9}", "\u{e9}", ""]);
        for strx in [1u32, 7, 9, 10] {
            let err =
                MachOParser::parse(&mk_object_with_symbol_names(&[strx], strings)).unwrap_err();
            assert!(
                matches!(&err, LinkerError::MalformedInput { detail, .. }
                    if detail.contains("symbol name is not UTF-8")),
                "strx {strx}: expected a UTF-8 refusal, got {err:?}"
            );
        }
    }

    /// Only one LC_SYMTAB is read: each indexes its whole string table, so a
    /// command list repeating it would cost time quadratic in the input.
    #[test]
    fn test_parse_second_symtab_is_refused() {
        let one = mk_object_with_symbol_names(&[1], b"\0_a\0");
        let parsed = MachOParser::parse(&one).expect("one LC_SYMTAB parses");
        assert_eq!(parsed.symbols[0].name, "_a");
        // The same command twice, both naming one symbol and string table.
        let size = SYMTAB_COMMAND_SIZE;
        let symoff = 32 + 2 * size;
        let mut command = vec![0u8; size as usize];
        command[0..4].copy_from_slice(&LC_SYMTAB.to_le_bytes());
        command[4..8].copy_from_slice(&size.to_le_bytes());
        command[8..12].copy_from_slice(&symoff.to_le_bytes());
        command[12..16].copy_from_slice(&1u32.to_le_bytes());
        command[16..20].copy_from_slice(&(symoff + 16).to_le_bytes());
        command[20..24].copy_from_slice(&4u32.to_le_bytes());
        let mut data = mk_object_with_one_lc(2, &[command.clone(), command].concat());
        let mut nlist = [0u8; 16];
        nlist[0..4].copy_from_slice(&1u32.to_le_bytes());
        nlist[4] = 0x0f;
        data.extend_from_slice(&nlist);
        data.extend_from_slice(b"\0_a\0");
        let err = MachOParser::parse(&data).unwrap_err();
        assert!(
            matches!(&err, LinkerError::MalformedInput { detail, .. }
                if detail.contains("more than one LC_SYMTAB")),
            "expected the second LC_SYMTAB to be refused, got {err:?}"
        );
    }

    /// A load command must end inside the `sizeofcmds` area.
    #[test]
    fn test_parse_load_command_past_sizeofcmds_is_refused() {
        let mut sym = vec![0u8; SYMTAB_COMMAND_SIZE as usize];
        sym[0..4].copy_from_slice(&LC_SYMTAB.to_le_bytes());
        sym[4..8].copy_from_slice(&SYMTAB_COMMAND_SIZE.to_le_bytes());
        let mut data = mk_object_with_one_lc(1, &sym);
        data[20..24].copy_from_slice(&16u32.to_le_bytes()); // sizeofcmds = 16 < cmdsize 24
        let err = MachOParser::parse(&data).unwrap_err();
        assert!(
            matches!(err, LinkerError::LoadCommandOverflow { offset: 32 }),
            "expected the command past sizeofcmds to be refused, got {err:?}"
        );
    }

    /// One LC_SEGMENT_64 with a single `__TEXT,__text` section whose
    /// relocation table is `nreloc` entries at `reloff`, followed by `tail`.
    #[cfg(test)]
    fn mk_object_with_relocation_table(reloff: u32, nreloc: u32, tail: &[u8]) -> Vec<u8> {
        let mut seg = vec![0u8; SEGMENT_COMMAND_64_SIZE as usize];
        seg[0..4].copy_from_slice(&LC_SEGMENT_64.to_le_bytes());
        let cmdsize = SEGMENT_COMMAND_64_SIZE + SECTION_64_SIZE;
        seg[4..8].copy_from_slice(&cmdsize.to_le_bytes());
        seg[64..68].copy_from_slice(&1u32.to_le_bytes()); // nsects = 1
        let mut sec = vec![0u8; SECTION_64_SIZE as usize];
        sec[0..6].copy_from_slice(b"__text");
        sec[16..22].copy_from_slice(b"__TEXT");
        sec[56..60].copy_from_slice(&reloff.to_le_bytes());
        sec[60..64].copy_from_slice(&nreloc.to_le_bytes());
        let mut lc = seg;
        lc.extend_from_slice(&sec);
        let mut data = mk_object_with_one_lc(1, &lc);
        data.extend_from_slice(tail);
        data
    }

    /// A relocation table that runs past the input is refused. The parser used
    /// to skip the missing entries, returning the section with fewer
    /// relocations than it declares, and to walk every one of a count near
    /// u32::MAX (L13-P7 fuzz lane: 10 s on a 327-byte fuzz_macho_fixup input).
    #[test]
    fn test_parse_relocation_table_beyond_input_is_refused() {
        // A valid ARM64_RELOC_UNSIGNED entry (r_address 0, r_symbolnum 0,
        // r_length 3, not pc-relative, not extern).
        let entry: [u8; 8] = [0, 0, 0, 0, 0, 0, 0, 0x06];
        let reloff = 32 + SEGMENT_COMMAND_64_SIZE + SECTION_64_SIZE;
        let complete = mk_object_with_relocation_table(reloff, 1, &entry);
        let parsed = MachOParser::parse(&complete).expect("one in-bounds relocation parses");
        assert_eq!(parsed.sections[0].relocations.len(), 1);

        for (label, nreloc) in [("truncated", 2), ("near u32::MAX", u32::MAX)] {
            let data = mk_object_with_relocation_table(reloff, nreloc, &entry);
            let err = MachOParser::parse(&data).unwrap_err();
            assert!(
                matches!(&err, LinkerError::MalformedInput { detail, .. }
                    if detail.contains("relocation table") && detail.contains("exceeds input")),
                "{label}: expected the relocation table to be refused, got {err:?}"
            );
        }
        // No relocations: the table offset is not consulted.
        let empty = mk_object_with_relocation_table(u32::MAX, 0, &[]);
        let parsed = MachOParser::parse(&empty).expect("a section without relocations parses");
        assert!(parsed.sections[0].relocations.is_empty());
    }

    /// The fuzz lane's slow unit (fuzz_macho_fixup, seed 20260924, source
    /// e26b6e17d): section relocation counts of 0x2d2d2d32 and more over a
    /// 327-byte input, which took 10 s to walk. It must be refused, not walked.
    /// Since section headers must fit in their command, its first segment
    /// (nsects 488447261 in a 91-byte command) is refused before any section.
    #[test]
    fn test_parse_fuzz_slow_unit_relocation_counts_are_refused() {
        const SLOW_UNIT: [u8; 327] = [
            0xcf, 0xfa, 0xed, 0xfe, 0x0c, 0x00, 0x00, 0x01, 0xff, 0xff, 0x00, 0x42, 0x01, 0x00,
            0x00, 0x00, 0xfa, 0x1c, 0xfe, 0xf4, 0xff, 0xff, 0xfe, 0x00, 0x00, 0xff, 0xbd, 0x5d,
            0x01, 0x00, 0x00, 0x42, 0x19, 0x00, 0x00, 0x00, 0x5b, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x42, 0x02, 0x00, 0x00, 0x00, 0x2e, 0x00, 0x02,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x2d, 0x2d, 0x2c, 0x2d, 0x32, 0x2d, 0x2d, 0x2d, 0x2d, 0x00, 0x00, 0x28, 0x1d,
            0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d,
            0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x3a, 0x1c, 0xfe, 0xf4, 0xff, 0xff, 0xfe,
            0x00, 0x00, 0xff, 0xbd, 0x5d, 0x01, 0x00, 0x00, 0x42, 0x19, 0x00, 0x00, 0x00, 0x5b,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x42, 0x02, 0x00,
            0x00, 0x00, 0x2e, 0x00, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2d, 0x2d, 0x2d, 0x2d, 0x32, 0x2d, 0x2d, 0x2d,
            0x1d, 0x00, 0x00, 0x28, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d,
            0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d,
            0x1d, 0x1d, 0xff, 0x5d, 0xbd, 0xff, 0xbd, 0x5d, 0x01, 0x00, 0x00, 0x42, 0x02, 0x00,
            0x00, 0x00, 0x2e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x5b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d,
            0xff, 0x5d, 0xbd, 0xff, 0xff, 0xff, 0xfe, 0x00, 0x00, 0xff, 0xbd, 0x5d, 0x01, 0x00,
            0x00, 0x42, 0x02, 0x00, 0x2f, 0x00, 0x00, 0x00, 0x1d, 0x1d, 0x1d, 0xff, 0x5d, 0xbd,
            0xff, 0xbd, 0x5d, 0x01, 0x00, 0x00, 0x42, 0x02, 0x00, 0x00, 0x00, 0x2e, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5b, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0xff, 0x1d, 0x1d, 0x1d, 0x1d, 0x1d, 0xff, 0x5d, 0xbd, 0xff, 0xff,
            0xff, 0xfe, 0x00, 0x00, 0xff, 0xbd, 0x5d, 0x01, 0x00, 0x00, 0x42, 0x02, 0x00, 0x2f,
            0x00, 0x00, 0x00, 0x00, 0x00,
        ];
        let err = MachOParser::parse(&SLOW_UNIT).unwrap_err();
        assert!(
            matches!(&err, LinkerError::MalformedInput { detail, .. }
                if detail.contains("section headers do not fit")
                    || detail.contains("relocation table")),
            "expected the slow unit to be refused, got {err:?}"
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
        let layout = lay_out_sections(&objects, DEFAULT_BASE_ADDR).unwrap();

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
        let layout = lay_out_sections(&objects, DEFAULT_BASE_ADDR).unwrap();

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
        let layout = lay_out_sections(&objects, DEFAULT_BASE_ADDR).unwrap();
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
        let layout = lay_out_sections(&objects, DEFAULT_BASE_ADDR).unwrap();

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
        )
        .unwrap();

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
        )
        .unwrap();

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
        let shape = ImageShape {
            stubs: 1,
            got: 1,
            ..ImageShape::default()
        };
        let expected_entryoff = executable_text_file_offset_from_lc_size(
            image_load_command_size(
                ImageKind::Executable,
                &shape,
                &[dylib_command_size(&config.dylibs[0])],
            )
            .unwrap(),
        );
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

        assert_stubs_address_got(&exe);
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
        let layout = lay_out_sections(&objects, DEFAULT_BASE_ADDR).unwrap();
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
        let layout = lay_out_sections(&objects, DEFAULT_BASE_ADDR).unwrap();
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
        let layout = lay_out_sections(&objects, DEFAULT_BASE_ADDR).unwrap();
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
        let layout = lay_out_sections(&objects, DEFAULT_BASE_ADDR).unwrap();
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
    fn mixed_weak_and_strong_references_require_a_definition_in_either_order() {
        let reference = |weak| ParsedObject {
            cputype: CPU_TYPE_ARM64,
            cpusubtype: CPU_SUBTYPE_ARM64_ALL,
            flags: 0,
            sections: vec![],
            symbols: vec![ParsedSymbol {
                name: "_optional_func".into(),
                n_type: N_UNDF | N_EXT,
                section: 0,
                desc: if weak { N_WEAK_REF } else { 0 },
                value: 0,
            }],
        };
        for references in [[true, false], [false, true], [true, true]] {
            let mut resolver = SymbolResolver::new();
            for (index, weak) in references.into_iter().enumerate() {
                resolver.add_object(index, &reference(weak), &[]).unwrap();
            }
            let plain = resolver.resolve();
            let dynamic = resolver.resolve_with_dylibs(&DylibConfig::new(), DEFAULT_BASE_ADDR);
            if references.contains(&false) {
                assert!(matches!(
                    plain,
                    Err(LinkerError::UndefinedSymbol(ref name)) if name == "_optional_func"
                ));
                assert!(matches!(
                    dynamic,
                    Err(LinkerError::UndefinedSymbol(ref name)) if name == "_optional_func"
                ));
            } else {
                assert_eq!(plain.unwrap()["_optional_func"], 0);
                let (addresses, imports) = dynamic.unwrap();
                assert_eq!(addresses["_optional_func"], 0);
                assert!(imports.is_empty());
            }

            // A real provider satisfies either kind of reference; duplicate
            // references must still allocate exactly one dynamic stub.
            let config = DylibConfig {
                dylibs: vec![DylibEntry {
                    install_name: "/test/provider.dylib".into(),
                    symbols: HashSet::from(["_optional_func".into()]),
                }],
            };
            let (addresses, imports) = resolver
                .resolve_with_dylibs(&config, DEFAULT_BASE_ADDR)
                .unwrap();
            assert_eq!(addresses["_optional_func"], DEFAULT_BASE_ADDR);
            assert_eq!(imports, ["_optional_func"]);
        }
    }

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

        let stripped = dead_strip_sections(&[obj], "_main").unwrap();
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

        let stripped = dead_strip_sections(&[obj], "_main").unwrap();
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
        let relocation = &stripped[0].sections[0].relocations[0];
        assert_eq!(
            syms.get(relocation.symbol_index as usize)
                .map(|s| s.name.as_str()),
            Some("_helper"),
            "stripping a preceding symbol must remap external relocation indices too"
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

        let stripped = dead_strip_sections(&[obj], "_main").unwrap();
        // Both sections should be kept (data is always preserved).
        assert_eq!(stripped[0].sections.len(), 2);
    }

    fn dead_strip_relocation_fixture() -> ParsedObject {
        ParsedObject {
            cputype: CPU_TYPE_ARM64,
            cpusubtype: CPU_SUBTYPE_ARM64_ALL,
            flags: 0,
            sections: [0x9400_0000u32, 0xD65F_03C0, 0xD65F_03C0]
                .into_iter()
                .enumerate()
                .map(|(index, instruction)| ParsedSection {
                    name: format!("__text_{index}"),
                    segment: "__TEXT".into(),
                    data: instruction.to_le_bytes().to_vec(),
                    addr: index as u64 * 4,
                    align: 2,
                    flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS,
                    relocations: if index == 0 {
                        vec![Relocation::branch26(0, 2)]
                    } else {
                        vec![]
                    },
                    vmsize: 4,
                })
                .collect(),
            symbols: ["_main", "_dead", "_helper"]
                .into_iter()
                .enumerate()
                .map(|(index, name)| ParsedSymbol {
                    name: name.into(),
                    n_type: N_SECT | N_EXT,
                    section: index as u8 + 1,
                    desc: 0,
                    value: index as u64 * 4,
                })
                .collect(),
        }
    }

    #[test]
    fn dead_strip_remaps_symbol_and_local_section_targets_through_linking() {
        for local in [false, true] {
            let mut object = dead_strip_relocation_fixture();
            if local {
                object.sections[0].relocations[0].is_extern = false;
                object.sections[0].relocations[0].symbol_index = 3;
                // A section-ordinal relocation needs no symbol at its target.
                object.symbols.pop();
            }
            let stripped = dead_strip_sections(&[object], "_main").unwrap();
            assert_eq!(stripped[0].sections.len(), 2);
            assert_eq!(stripped[0].sections[1].name, "__text_2");
            assert_eq!(
                stripped[0].sections[0].relocations[0].symbol_index,
                if local { 2 } else { 1 }
            );
            let executable = link(&stripped).expect("stripped references remain linkable");
            let sections = section_commands(&executable, &walk_load_commands(&executable));
            let text = sections.iter().find(|s| s.name == "__text").unwrap();
            assert_eq!(text.size, 8);
            assert_eq!(rd_u32(&executable, text.offset as usize), 0x9400_0001);
            assert_eq!(rd_u32(&executable, text.offset as usize + 4), 0xD65F_03C0);
        }
    }

    #[test]
    fn dead_strip_preserves_addend_payloads_and_rejects_invalid_indices() {
        let mut object = dead_strip_relocation_fixture();
        let mut addend = Relocation::branch26(0, 0x00FF_FFFF);
        addend.kind = AArch64RelocKind::Addend;
        addend.is_extern = false;
        object.sections[0].relocations.insert(0, addend.clone());
        let stripped = dead_strip_sections(&[object], "_main").unwrap();
        let retained = &stripped[0].sections[0].relocations[0];
        assert_eq!(retained.kind, AArch64RelocKind::Addend);
        assert_eq!(retained.symbol_index, addend.symbol_index);
        assert_eq!(retained.is_extern, addend.is_extern);

        for (external, index) in [(true, 3), (true, u32::MAX), (false, 0), (false, 4)] {
            let mut object = dead_strip_relocation_fixture();
            object.sections[0].relocations[0].is_extern = external;
            object.sections[0].relocations[0].symbol_index = index;
            assert!(matches!(
                dead_strip_sections(&[object], "_main"),
                Err(LinkerError::MalformedRelocation(_))
            ));
        }
        let mut object = dead_strip_relocation_fixture();
        object.symbols[0].section = 4;
        assert!(matches!(
            dead_strip_sections(&[object], "_main"),
            Err(LinkerError::MalformedInput { .. })
        ));
        let mut object = dead_strip_relocation_fixture();
        object.sections.resize(256, object.sections[0].clone());
        assert!(matches!(
            dead_strip_sections(&[object], "_main"),
            Err(LinkerError::MalformedInput { .. })
        ));
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

        let layout = lay_out_sections(&[obj], DEFAULT_BASE_ADDR).unwrap();

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

    fn object_with_bss(data: Vec<u8>, bss_size: u64) -> ParsedObject {
        ParsedObject {
            cputype: CPU_TYPE_ARM64,
            cpusubtype: CPU_SUBTYPE_ARM64_ALL,
            flags: 0,
            sections: vec![
                ParsedSection {
                    name: "__text".into(),
                    segment: "__TEXT".into(),
                    data: [0x52800000u32, 0xD65F03C0]
                        .into_iter()
                        .flat_map(u32::to_le_bytes)
                        .collect(),
                    addr: 0,
                    align: 2,
                    flags: S_REGULAR | S_ATTR_PURE_INSTRUCTIONS,
                    relocations: vec![],
                    vmsize: 8,
                },
                ParsedSection {
                    name: "__data".into(),
                    segment: "__DATA".into(),
                    vmsize: data.len() as u64,
                    data,
                    addr: 0,
                    align: 0,
                    flags: S_REGULAR,
                    relocations: vec![],
                },
                ParsedSection {
                    name: "__bss".into(),
                    segment: "__DATA".into(),
                    data: vec![],
                    addr: 0,
                    align: 4,
                    flags: S_ZEROFILL,
                    relocations: vec![],
                    vmsize: bss_size,
                },
            ],
            symbols: ["_main", "_data", "_zero"]
                .into_iter()
                .enumerate()
                .map(|(index, name)| ParsedSymbol {
                    name: name.into(),
                    n_type: N_SECT | N_EXT,
                    section: index as u8 + 1,
                    desc: 0,
                    value: 0,
                })
                .collect(),
        }
    }

    fn assert_stubs_address_got(executable: &[u8]) {
        let commands = walk_load_commands(executable);
        let sections = section_commands(executable, &commands);
        let stubs = single_section(&sections, "__TEXT", "__stubs");
        let got = single_section(&sections, "__DATA_CONST", "__got");
        for index in 0..stubs.size / u64::from(STUB_SIZE) {
            let offset = stubs.offset as usize + index as usize * STUB_SIZE as usize;
            let adrp = rd_u32(executable, offset);
            let ldr = rd_u32(executable, offset + 4);
            assert_eq!(adrp & 0x9f00_001f, 0x9000_0010);
            assert_eq!(ldr & !(0xfff << 10), 0xF940_0210);
            assert_eq!(rd_u32(executable, offset + 8), 0xD61F_0200);
            let immediate = (((adrp >> 5) & 0x7ffff) << 2) | ((adrp >> 29) & 3);
            let signed_pages = (i64::from(immediate) << 43) >> 43;
            let pc_page = (stubs.addr + index * u64::from(STUB_SIZE)) & !0xfff;
            let address = i128::from(pc_page)
                + i128::from(signed_pages) * 4096
                + i128::from((ldr >> 10) & 0xfff) * 8;
            assert_eq!(
                address,
                i128::from(got.addr + index * 8),
                "stub must load its own GOT slot"
            );
        }
    }

    #[test]
    fn layout_rejects_alignment_and_virtual_address_overflow() {
        let object = object_with_bss(vec![1], 16);
        for exponent in [64, u32::MAX] {
            let mut malformed = object.clone();
            malformed.sections[0].align = exponent;
            assert!(matches!(
                lay_out_sections(&[malformed], DEFAULT_BASE_ADDR),
                Err(LinkerError::InvalidAlignment { .. })
            ));
        }
        assert!(matches!(
            lay_out_sections(std::slice::from_ref(&object), u64::MAX),
            Err(LinkerError::LayoutOverflow(_))
        ));
        let huge_bss = object_with_bss(vec![], u64::MAX);
        assert!(matches!(
            lay_out_sections(&[huge_bss], DEFAULT_BASE_ADDR),
            Err(LinkerError::LayoutOverflow(_))
        ));
    }

    #[test]
    fn parser_rejects_truncated_symbol_tables_and_out_of_table_names() {
        let mut writer = MachOWriter::new();
        writer.add_text_section(&0xD65F03C0u32.to_le_bytes());
        writer.add_symbol("_main", 1, 0, true).unwrap();
        let original = writer.write().unwrap();
        let commands = walk_load_commands(&original);
        let command = single_load_command(&commands, LC_SYMTAB);
        let symoff = rd_u32(&original, command.offset + 8) as usize;
        let stroff = rd_u32(&original, command.offset + 16) as usize;
        let strsize = rd_u32(&original, command.offset + 20);
        let name_offset = rd_u32(&original, symoff) as usize;
        let mut cases = Vec::new();
        let mut truncated_symbols = original.clone();
        patch_u32(&mut truncated_symbols, command.offset + 12, u32::MAX);
        cases.push(truncated_symbols);
        let mut truncated_strings = original.clone();
        patch_u32(&mut truncated_strings, command.offset + 20, u32::MAX);
        cases.push(truncated_strings);
        let mut out_of_table = original.clone();
        patch_u32(&mut out_of_table, symoff, strsize);
        out_of_table.extend_from_slice(b"not-in-string-table\0");
        cases.push(out_of_table);
        let mut missing_terminator = original.clone();
        patch_u32(
            &mut missing_terminator,
            command.offset + 20,
            (name_offset + 5) as u32,
        );
        cases.push(missing_terminator);
        let mut invalid_utf8 = original;
        invalid_utf8[stroff + name_offset] = 0xff;
        cases.push(invalid_utf8);
        for (index, bytes) in cases.into_iter().enumerate() {
            assert!(
                matches!(
                    MachOParser::parse(&bytes),
                    Err(LinkerError::MalformedInput { .. })
                ),
                "case {index}"
            );
        }
    }

    #[test]
    fn bss_alignment_uses_the_absolute_base_after_all_file_backed_data() {
        let first = object_with_bss(vec![1], 17);
        let second = object_with_bss(vec![2, 3], 8);
        let layout = lay_out_sections(&[first, second], DEFAULT_BASE_ADDR + 1).unwrap();
        assert_eq!(layout.section_addrs[0][0] % 4, 0);
        assert_eq!(layout.section_addrs[0][2] % 16, 0);
        assert_eq!(layout.section_addrs[1][2] % 16, 0);
        assert!(layout.section_addrs[0][2] >= layout.section_addrs[1][1] + 2);
        assert!(layout.section_addrs[1][2] >= layout.section_addrs[0][2] + 17);
        assert_eq!(layout.data_file_size, 3);
    }

    #[test]
    fn executable_emitter_rejects_overflow_overlaps_and_invalid_entry_points() {
        let text = 0xD65F03C0u32.to_le_bytes();
        let offset = plain_executable_text_file_offset(true);
        let data_addr = DEFAULT_BASE_ADDR + offset + PAGE_SIZE;
        for (text_addr, data_addr, entry) in [
            (u64::MAX, data_addr, offset),
            (DEFAULT_BASE_ADDR, u64::MAX, offset),
            (DEFAULT_BASE_ADDR, DEFAULT_BASE_ADDR + offset, offset),
            (DEFAULT_BASE_ADDR + 1, data_addr, offset),
            (0, data_addr, offset),
            (DEFAULT_BASE_ADDR, data_addr, 0),
            (DEFAULT_BASE_ADDR, data_addr, offset + text.len() as u64),
        ] {
            assert!(ExecutableEmitter::emit(&text, &[1], text_addr, data_addr, entry).is_err());
        }
        assert!(
            ExecutableEmitter::emit_with_virtual_data(
                &text,
                &[1],
                DEFAULT_BASE_ADDR,
                data_addr,
                offset,
                u64::MAX
            )
            .is_err()
        );
        assert!(
            ExecutableEmitter::emit_with_virtual_data(
                &text,
                &[1],
                DEFAULT_BASE_ADDR,
                data_addr,
                offset,
                0
            )
            .is_err()
        );
        let lc_size = image_load_command_size(
            ImageKind::Executable,
            &ImageShape {
                data: true,
                ..ImageShape::default()
            },
            &[],
        )
        .unwrap();
        let executable = ImageKind::Executable;
        assert!(
            ExecutableLayout::new(
                executable,
                u64::from(u32::MAX),
                DEFAULT_BASE_ADDR,
                Some(offset),
                lc_size,
                &[(DEFAULT_BASE_ADDR * 3, 1, 1)],
            )
            .is_err()
        );
        let layout = ExecutableLayout::new(
            executable,
            4,
            DEFAULT_BASE_ADDR,
            Some(offset),
            lc_size,
            &[(data_addr, 1, 1)],
        )
        .unwrap();
        assert!(layout.reserve_image(u64::from(u32::MAX)).is_err());
        // A later segment may not overlap an earlier one.
        assert!(
            ExecutableLayout::new(
                executable,
                4,
                DEFAULT_BASE_ADDR,
                Some(offset),
                lc_size,
                &[(data_addr, 1, PAGE_SIZE * 2), (data_addr + PAGE_SIZE, 1, 1)],
            )
            .is_err()
        );
        // Executables need an entry; dylibs may not carry one, and only a
        // dylib may be based inside the first 4 GiB.
        let dylib = ImageKind::Dylib {
            install_name: "@rpath/libx.dylib",
        };
        assert!(
            ExecutableLayout::new(executable, 4, DEFAULT_BASE_ADDR, None, lc_size, &[]).is_err()
        );
        assert!(ExecutableLayout::new(dylib, 4, 0, Some(offset), lc_size, &[]).is_err());
        assert!(ExecutableLayout::new(executable, 4, 0, Some(offset), lc_size, &[]).is_err());
        assert!(ExecutableLayout::new(dylib, 4, 0, None, lc_size, &[]).is_ok());
    }

    #[test]
    fn dylib_link_rejects_unrepresentable_import_metadata_before_emission() {
        let mut object = object_with_bss(vec![7], 8);
        object.symbols.push(ParsedSymbol {
            name: "_exit".into(),
            n_type: N_UNDF | N_EXT,
            section: 0,
            desc: 0,
            value: 0,
        });
        let entry = DylibConfig::with_libsystem().dylibs.remove(0);
        let too_many = DylibConfig {
            dylibs: vec![entry.clone(); 0xF1],
        };
        assert!(matches!(
            link_with_dylibs(std::slice::from_ref(&object), &too_many),
            Err(LinkerError::LayoutOverflow("compact dylib import count"))
        ));
        let mut invalid_name = DylibConfig {
            dylibs: vec![entry],
        };
        invalid_name.dylibs[0].install_name.push('\0');
        assert!(matches!(
            link_with_dylibs(std::slice::from_ref(&object), &invalid_name),
            Err(LinkerError::MalformedInput { .. })
        ));
        // A small payload with a large alignment gap places a rebased pointer
        // beyond the u16 page-count field. The page admission runs before
        // relocated bytes exist, so no multi-gigabyte allocation is needed.
        object.sections[1].data = vec![0; 8];
        object.sections[1].vmsize = 8;
        object.sections[1].align = 31;
        object.sections[1]
            .relocations
            .push(Relocation::unsigned_ptr(0, 1));
        assert!(matches!(
            link_with_dylibs(&[object], &DylibConfig::with_libsystem()),
            Err(LinkerError::LayoutOverflow(
                "compact chained-fixup import/page fields"
            ))
        ));
    }

    #[test]
    fn executable_uuid_includes_zero_fill_extent() {
        let first = link(&[object_with_bss(vec![7], PAGE_SIZE)]).unwrap();
        let second = link(&[object_with_bss(vec![7], PAGE_SIZE * 2)]).unwrap();
        let first_commands = walk_load_commands(&first);
        let second_commands = walk_load_commands(&second);
        assert_ne!(
            load_command_uuid(&first, single_load_command(&first_commands, LC_UUID)),
            load_command_uuid(&second, single_load_command(&second_commands, LC_UUID))
        );
    }

    #[test]
    fn executable_reserves_bss_virtual_pages_without_file_backing() {
        for data in [vec![], vec![7]] {
            let object = object_with_bss(data, PAGE_SIZE * 3);
            let layout = lay_out_sections(
                std::slice::from_ref(&object),
                DEFAULT_BASE_ADDR + plain_executable_text_file_offset(true),
            )
            .unwrap();
            let exe = link(&[object]).unwrap();
            let commands = walk_load_commands(&exe);
            let segments = segment_commands(&exe, &commands);
            let data = single_segment(&segments, "__DATA");
            let linkedit = single_segment(&segments, "__LINKEDIT");
            assert_eq!(data.vmaddr, layout.data_vmaddr);
            assert!(data.vmaddr + data.vmsize >= layout.section_addrs[0][2] + PAGE_SIZE * 3);
            assert!(data.filesize < data.vmsize);
            assert!(linkedit.vmaddr >= data.vmaddr + data.vmsize);
            assert_dyld_linkedit_payloads(&exe, &[]);
        }
    }

    #[test]
    fn imported_stubs_crossing_a_page_do_not_stale_data_relocations() {
        let mut object = object_with_bss(vec![0xa5], PAGE_SIZE * 2);
        // ADRP x8, _data@PAGE; ADD x8, x8, _data@PAGEOFF at the end of one full
        // text page, so the planned stub pushes __DATA a page further out.
        object.sections[0].data.resize(PAGE_SIZE as usize, 0);
        object.sections[0].data[8..16].copy_from_slice(
            &[0x9000_0008u32, 0x9100_0108]
                .into_iter()
                .flat_map(u32::to_le_bytes)
                .collect::<Vec<_>>(),
        );
        object.sections[0].relocations.extend([
            Relocation::page21(8, 1),
            Relocation::pageoff12(12, 1),
            Relocation::branch26(4, 3),
        ]);
        object.sections[0].data[4..8].copy_from_slice(&0x9400_0000u32.to_le_bytes());
        object.symbols.push(ParsedSymbol {
            name: "_exit".into(),
            n_type: N_UNDF | N_EXT,
            section: 0,
            desc: 0,
            value: 0,
        });
        let config = DylibConfig::with_libsystem();
        let exe = link_with_dylibs(&[object], &config).unwrap();
        let commands = walk_load_commands(&exe);
        let sections = section_commands(&exe, &commands);
        let segments = segment_commands(&exe, &commands);
        let text = single_section(&sections, "__TEXT", "__text");
        let data = single_segment(&segments, "__DATA");
        let data_const = single_segment(&segments, "__DATA_CONST");
        let got = single_section(&sections, "__DATA_CONST", "__got");
        assert_eq!(data_const.vmaddr, text.addr + PAGE_SIZE * 2);
        assert_eq!(data.vmaddr, data_const.vmaddr + PAGE_SIZE);
        let adrp = rd_u32(&exe, text.offset as usize + 8);
        let add = rd_u32(&exe, text.offset as usize + 12);
        let pages = (i64::from((((adrp >> 5) & 0x7ffff) << 2) | ((adrp >> 29) & 3)) << 43) >> 43;
        let address = (((text.addr + 8) & !0xfff) as i64 + pages * 4096) as u64
            + u64::from((add >> 10) & 0xfff);
        assert_eq!(
            address, data.vmaddr,
            "ADRP/ADD must reach the shifted __data"
        );
        assert_eq!(exe[data.fileoff as usize], 0xa5);
        assert_eq!(got.addr, data_const.vmaddr);
        assert!(data.vmsize > data.filesize);
        assert_stubs_address_got(&exe);
        assert_dyld_linkedit_payloads(&exe, &["_exit"]);
        assert_eq!(
            decode_chained_fixups(&exe),
            [(
                got.addr,
                DecodedFixup::Bind {
                    symbol: "_exit".into(),
                    addend: 0
                }
            )]
        );
    }

    #[test]
    fn symbol_resolution_rebases_input_section_addresses_and_rejects_invalid_values() {
        let mut object = object_with_bss(vec![1, 2, 3, 4], 16);
        object.sections[1].addr = 0x80;
        object.symbols[1].value = 0x82;
        let layout = lay_out_sections(std::slice::from_ref(&object), DEFAULT_BASE_ADDR).unwrap();
        let mut resolver = SymbolResolver::new();
        resolver
            .add_object(0, &object, &layout.section_addrs[0])
            .unwrap();
        assert_eq!(resolver.lookup("_data"), Some(layout.data_vmaddr + 2));
        for value in [0x7f, 0x85, u64::MAX] {
            object.symbols[1].value = value;
            assert!(
                SymbolResolver::new()
                    .add_object(0, &object, &layout.section_addrs[0])
                    .is_err()
            );
        }
    }

    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    #[test]
    fn native_dylib_executable_reads_and_writes_distant_zero_fill_memory() {
        use std::os::unix::fs::PermissionsExt;
        use std::time::Duration;
        for write_value in [None, Some(73u32)] {
            let mut object = object_with_bss(vec![7], PAGE_SIZE * 3);
            object.symbols[2].value = PAGE_SIZE * 2;
            let mut words = vec![0x9000_0008u32, 0x9100_0108, 0xB940_0100]; // ADRP; ADD; LDR w0
            if let Some(value) = write_value {
                words.extend([0x5280_0009 | (value << 5), 0xB900_0109, 0xB940_0100]);
            }
            words.push(0x9400_0000); // BL _exit
            object.sections[0].relocations = vec![
                Relocation::page21(0, 2),
                Relocation::pageoff12(4, 2),
                Relocation::branch26((words.len() as u32 - 1) * 4, 3),
            ];
            object.sections[0].data = words.into_iter().flat_map(u32::to_le_bytes).collect();
            object.symbols.push(ParsedSymbol {
                name: "_exit".into(),
                n_type: N_UNDF | N_EXT,
                section: 0,
                desc: 0,
                value: 0,
            });
            let executable = link_with_dylibs(&[object], &DylibConfig::with_libsystem()).unwrap();
            let directory = tempfile::tempdir().unwrap();
            let path = directory.path().join("zero-fill-executable");
            std::fs::write(&path, executable).unwrap();
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
            let run = super::native_process::run_executable_with_timeout(
                &path,
                super::native_process::exec_timeout(Duration::from_secs(10)),
            )
            .unwrap();
            assert!(
                !run.timed_out,
                "linked executable did not terminate: {:?}",
                run.output
            );
            assert_eq!(
                run.output.status.code(),
                Some(write_value.unwrap_or(0) as i32),
                "{:?}",
                run.output
            );
        }
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

    // =======================================================================
    // GOT, TLV pointer and chained-fixup image tests
    // =======================================================================

    const ADRP_X8: u32 = 0x9000_0008;
    const LDR_X8_X8: u32 = 0xF940_0108;
    const ADD_X8_X8: u32 = 0x9100_0108;
    const RET: u32 = 0xD65F_03C0;

    fn words(instructions: &[u32]) -> Vec<u8> {
        instructions
            .iter()
            .flat_map(|word| word.to_le_bytes())
            .collect()
    }

    fn input_section(
        name: &str,
        segment: &str,
        data: Vec<u8>,
        align: u32,
        flags: u32,
        relocations: Vec<Relocation>,
    ) -> ParsedSection {
        ParsedSection {
            name: name.into(),
            segment: segment.into(),
            vmsize: data.len() as u64,
            data,
            addr: 0,
            align,
            flags,
            relocations,
        }
    }

    fn text_section(instructions: &[u32], relocations: Vec<Relocation>) -> ParsedSection {
        input_section(
            "__text",
            "__TEXT",
            words(instructions),
            2,
            S_REGULAR | S_ATTR_PURE_INSTRUCTIONS,
            relocations,
        )
    }

    fn zerofill_section(name: &str, size: u64, align: u32, flags: u32) -> ParsedSection {
        ParsedSection {
            name: name.into(),
            segment: "__DATA".into(),
            data: vec![],
            addr: 0,
            align,
            flags,
            relocations: vec![],
            vmsize: size,
        }
    }

    fn defined_symbol(name: &str, section: u8, value: u64, external: bool) -> ParsedSymbol {
        ParsedSymbol {
            name: name.into(),
            n_type: N_SECT | if external { N_EXT } else { 0 },
            section,
            desc: 0,
            value,
        }
    }

    fn undefined_symbol(name: &str, weak: bool) -> ParsedSymbol {
        ParsedSymbol {
            name: name.into(),
            n_type: N_UNDF | N_EXT,
            section: 0,
            desc: if weak { N_WEAK_REF } else { 0 },
            value: 0,
        }
    }

    fn parsed(sections: Vec<ParsedSection>, symbols: Vec<ParsedSymbol>) -> ParsedObject {
        ParsedObject {
            cputype: CPU_TYPE_ARM64,
            cpusubtype: CPU_SUBTYPE_ARM64_ALL,
            flags: 0,
            sections,
            symbols,
        }
    }

    fn with_relocation(mut reloc: Relocation, edit: impl FnOnce(&mut Relocation)) -> Relocation {
        edit(&mut reloc);
        reloc
    }

    fn provider(symbols: &[&str]) -> DylibConfig {
        DylibConfig {
            dylibs: vec![DylibEntry {
                install_name: "/usr/lib/libSystem.B.dylib".into(),
                symbols: symbols.iter().map(|symbol| symbol.to_string()).collect(),
            }],
        }
    }

    fn section_flags(exe: &[u8], segment: &str, name: &str) -> u32 {
        let commands = walk_load_commands(exe);
        for command in commands
            .iter()
            .filter(|command| command.cmd == LC_SEGMENT_64)
        {
            for index in 0..rd_u32(exe, command.offset + 64) as usize {
                let header = command.offset + SEGMENT_COMMAND_64_SIZE as usize + index * 80;
                if read_name16(exe, header) == name && read_name16(exe, header + 16) == segment {
                    return rd_u32(exe, header + 64);
                }
            }
        }
        panic!("missing {segment},{name}");
    }

    fn segment_flags(exe: &[u8], name: &str) -> u32 {
        let commands = walk_load_commands(exe);
        let command = commands
            .iter()
            .find(|command| {
                command.cmd == LC_SEGMENT_64 && read_name16(exe, command.offset + 8) == name
            })
            .expect("segment");
        rd_u32(exe, command.offset + 68)
    }

    fn file_offset_of(exe: &[u8], address: u64) -> usize {
        let commands = walk_load_commands(exe);
        let segment = segment_commands(exe, &commands)
            .into_iter()
            .find(|segment| (segment.vmaddr..segment.vmaddr + segment.filesize).contains(&address))
            .expect("address is file-backed");
        (segment.fileoff + address - segment.vmaddr) as usize
    }

    /// `ADRP Xd` + `LDR/ADD` decoded to the address they form.
    fn page_pair_target(exe: &[u8], adrp_address: u64, second_address: u64, scale: u64) -> u64 {
        let adrp = rd_u32(exe, file_offset_of(exe, adrp_address));
        let second = rd_u32(exe, file_offset_of(exe, second_address));
        assert_eq!(adrp & 0x9F00_0000, 0x9000_0000);
        let immediate = (((adrp >> 5) & 0x7FFFF) << 2) | ((adrp >> 29) & 3);
        let pages = (i64::from(immediate) << 43) >> 43;
        let page = ((adrp_address & !0xFFF) as i64 + pages * 4096) as u64;
        page + u64::from((second >> 10) & 0xFFF) * scale
    }

    fn text_addr(exe: &[u8]) -> u64 {
        let commands = walk_load_commands(exe);
        single_section(&section_commands(exe, &commands), "__TEXT", "__text").addr
    }

    #[test]
    fn got_load_of_a_local_definition_is_a_rebased_slot_and_keeps_its_ldr() {
        let object = parsed(
            vec![
                text_section(
                    &[ADRP_X8, LDR_X8_X8, RET],
                    vec![
                        Relocation::got_load_page21(0, 1),
                        Relocation::got_load_pageoff12(4, 1),
                    ],
                ),
                input_section(
                    "__data",
                    "__DATA",
                    7u64.to_le_bytes().to_vec(),
                    3,
                    S_REGULAR,
                    vec![],
                ),
            ],
            vec![
                defined_symbol("_main", 1, 0, true),
                defined_symbol("_counter", 2, 0, false),
            ],
        );
        let exe = link(&[object]).unwrap();
        let commands = walk_load_commands(&exe);
        let sections = section_commands(&exe, &commands);
        let got = single_section(&sections, "__DATA_CONST", "__got");
        let data = single_section(&sections, "__DATA", "__data");
        assert_eq!(got.size, 8);
        assert_eq!(
            section_flags(&exe, "__DATA_CONST", "__got") & SECTION_TYPE_MASK,
            S_NON_LAZY_SYMBOL_POINTERS
        );
        assert_eq!(segment_flags(&exe, "__DATA_CONST"), SG_READ_ONLY);
        assert_eq!(
            decode_chained_fixups(&exe),
            [(got.addr, DecodedFixup::Rebase(data.addr))]
        );
        let text = text_addr(&exe);
        assert_eq!(page_pair_target(&exe, text, text + 4, 8), got.addr);
        let ldr = rd_u32(&exe, file_offset_of(&exe, text + 4));
        assert_eq!(ldr & 0xFFC0_0000, 0xF940_0000, "no GOT relaxation to ADD");
        assert_dyld_linkedit_payloads(&exe, &[]);
    }

    #[test]
    fn got_slots_deduplicate_bind_imports_null_weak_references_and_feed_pointer_to_got() {
        let object = parsed(
            vec![text_section(
                &[
                    ADRP_X8, LDR_X8_X8, ADRP_X8, LDR_X8_X8, ADRP_X8, LDR_X8_X8, RET, 0,
                ],
                vec![
                    Relocation::got_load_page21(0, 1),
                    Relocation::got_load_pageoff12(4, 1),
                    Relocation::got_load_page21(8, 1),
                    Relocation::got_load_pageoff12(12, 1),
                    Relocation::got_load_page21(16, 2),
                    Relocation::got_load_pageoff12(20, 2),
                    Relocation::pointer_to_got_pcrel(28, 1),
                ],
            )],
            vec![
                defined_symbol("_main", 1, 0, true),
                undefined_symbol("_imported", false),
                undefined_symbol("_weak_missing", true),
            ],
        );
        let exe = link_with_dylibs(&[object], &provider(&["_imported"])).unwrap();
        let commands = walk_load_commands(&exe);
        let sections = section_commands(&exe, &commands);
        assert!(
            !sections.iter().any(|section| section.name == "__stubs"),
            "GOT-only imports need no stub"
        );
        let got = single_section(&sections, "__DATA_CONST", "__got");
        assert_eq!(got.size, 16, "one slot per distinct target");
        let text = text_addr(&exe);
        assert_eq!(page_pair_target(&exe, text, text + 4, 8), got.addr);
        assert_eq!(page_pair_target(&exe, text + 8, text + 12, 8), got.addr);
        assert_eq!(
            page_pair_target(&exe, text + 16, text + 20, 8),
            got.addr + 8
        );
        assert_eq!(
            decode_chained_fixups(&exe),
            [(
                got.addr,
                DecodedFixup::Bind {
                    symbol: "_imported".into(),
                    addend: 0
                }
            )]
        );
        assert_eq!(
            rd_u64(&exe, file_offset_of(&exe, got.addr + 8)),
            0,
            "weak null slot"
        );
        let delta = rd_u32(&exe, file_offset_of(&exe, text + 28)) as i32;
        assert_eq!(
            i128::from(text + 28) + i128::from(delta),
            i128::from(got.addr)
        );
        assert_dyld_linkedit_payloads(&exe, &["_imported"]);
    }

    fn pointer_object(
        relocations: Vec<Relocation>,
        data: Vec<u8>,
        text_relocations: Vec<Relocation>,
    ) -> ParsedObject {
        parsed(
            vec![
                text_section(&[RET, 0, 0, 0], text_relocations),
                input_section("__data", "__DATA", data, 3, S_REGULAR, relocations),
            ],
            vec![
                defined_symbol("_main", 1, 0, true),
                undefined_symbol("_imported", false),
                undefined_symbol("_weak_missing", true),
                defined_symbol("_data", 2, 0, true),
            ],
        )
    }

    #[test]
    fn data_pointers_rebase_definitions_bind_imports_and_keep_weak_nulls() {
        let mut data = vec![0u8; 32];
        data[0..8].copy_from_slice(&4u64.to_le_bytes());
        data[8..16].copy_from_slice(&16u64.to_le_bytes());
        data[16..24].copy_from_slice(&3u64.to_le_bytes());
        let object = pointer_object(
            vec![
                Relocation::unsigned_ptr(0, 0),
                Relocation::unsigned_ptr(8, 1),
                Relocation::unsigned_ptr(16, 2),
                // Section-relative pointer to this data section.
                with_relocation(Relocation::unsigned_ptr(24, 2), |reloc| {
                    reloc.is_extern = false
                }),
            ],
            data,
            vec![],
        );
        let exe = link_with_dylibs(&[object], &provider(&["_imported"])).unwrap();
        let commands = walk_load_commands(&exe);
        let sections = section_commands(&exe, &commands);
        let data = single_section(&sections, "__DATA", "__data");
        let text = text_addr(&exe);
        assert_eq!(
            decode_chained_fixups(&exe),
            [
                (data.addr, DecodedFixup::Rebase(text + 4)),
                (
                    data.addr + 8,
                    DecodedFixup::Bind {
                        symbol: "_imported".into(),
                        addend: 16
                    }
                ),
                (data.addr + 24, DecodedFixup::Rebase(data.addr)),
            ]
        );
        assert_eq!(rd_u64(&exe, file_offset_of(&exe, data.addr + 16)), 3);
        assert_dyld_linkedit_payloads(&exe, &["_imported"]);
    }

    #[test]
    fn unslidable_or_direct_import_pointers_are_refused_by_name() {
        let config = provider(&["_imported"]);
        let link_one = |object: ParsedObject| link_with_dylibs(&[object], &config).unwrap_err();

        let narrow = pointer_object(vec![Relocation::unsigned_word(0, 0)], vec![0; 8], vec![]);
        assert!(matches!(
            link_one(narrow),
            LinkerError::UnslidablePointer { .. }
        ));
        let mut in_text = pointer_object(vec![], vec![0; 8], vec![Relocation::unsigned_ptr(8, 3)]);
        in_text.sections[0].data = vec![0; 16];
        assert!(matches!(
            link_one(in_text),
            LinkerError::UnslidablePointer { .. }
        ));
        let mut wide_addend = vec![0u8; 8];
        wide_addend.copy_from_slice(&300u64.to_le_bytes());
        let addend = pointer_object(vec![Relocation::unsigned_ptr(0, 1)], wide_addend, vec![]);
        assert!(matches!(link_one(addend), LinkerError::ChainedFixup { .. }));
        let misaligned = pointer_object(vec![Relocation::unsigned_ptr(4, 0)], vec![0; 16], vec![]);
        assert!(matches!(
            link_one(misaligned),
            LinkerError::ChainedFixup { .. }
        ));
        let difference = pointer_object(
            vec![
                Relocation::subtractor(0, 1, 3),
                Relocation::unsigned_ptr(0, 0),
            ],
            vec![0; 8],
            vec![],
        );
        assert!(matches!(
            link_one(difference),
            LinkerError::DirectImportReference {
                kind: AArch64RelocKind::Subtractor,
                ..
            }
        ));
        let mut page = pointer_object(vec![], vec![0; 8], vec![Relocation::page21(0, 1)]);
        page.sections[0].data = words(&[ADRP_X8]);
        assert!(matches!(
            link_one(page),
            LinkerError::DirectImportReference { kind: AArch64RelocKind::Page21, ref symbol } if symbol == "_imported"
        ));
        let pc_relative = pointer_object(
            vec![with_relocation(Relocation::unsigned_ptr(0, 0), |reloc| {
                reloc.pc_relative = true
            })],
            vec![0; 8],
            vec![],
        );
        assert!(matches!(
            link_one(pc_relative),
            LinkerError::PcRelativeUnsigned { offset: 0 }
        ));
    }

    /// One object defining a TLV `name` with a template in `template` and a
    /// `_reader` (when `reader`) that loads it through TLVP relocations.
    fn tlv_object(name: &str, template: ParsedSection, reader: bool) -> ParsedObject {
        let text = if reader {
            text_section(
                &[ADRP_X8, LDR_X8_X8, RET],
                vec![
                    Relocation::tlvp_load_page21(0, 1),
                    Relocation::tlvp_load_pageoff12(4, 1),
                ],
            )
        } else {
            text_section(&[RET], vec![])
        };
        let vars = input_section(
            "__thread_vars",
            "__DATA",
            vec![0; 24],
            3,
            S_THREAD_LOCAL_VARIABLES,
            vec![
                Relocation::unsigned_ptr(0, 3),
                Relocation::unsigned_ptr(16, 2),
            ],
        );
        parsed(
            vec![text, vars, template],
            vec![
                defined_symbol(if reader { "_main" } else { "_other" }, 1, 0, true),
                defined_symbol(&format!("_{name}"), 2, 0, true),
                defined_symbol(&format!("_{name}$tlv$init"), 3, 0, false),
                undefined_symbol(TLV_BOOTSTRAP_SYMBOL, false),
            ],
        )
    }

    #[test]
    fn tlv_descriptors_bind_the_bootstrap_and_offset_templates_across_objects() {
        let first = tlv_object(
            "first",
            input_section(
                "__thread_data",
                "__DATA",
                11u64.to_le_bytes().to_vec(),
                3,
                S_THREAD_LOCAL_REGULAR,
                vec![],
            ),
            true,
        );
        let second = tlv_object(
            "second",
            zerofill_section("__thread_bss", 16, 4, S_THREAD_LOCAL_ZEROFILL),
            false,
        );
        let exe = link_with_dylibs(&[first, second], &DylibConfig::with_libsystem()).unwrap();
        assert_ne!(rd_u32(&exe, 24) & MH_HAS_TLV_DESCRIPTORS, 0);
        let commands = walk_load_commands(&exe);
        let sections = section_commands(&exe, &commands);
        let pointers = single_section(&sections, "__DATA_CONST", "__thread_ptrs");
        let vars = single_section(&sections, "__DATA", "__thread_vars");
        let data = single_section(&sections, "__DATA", "__thread_data");
        let bss = single_section(&sections, "__DATA", "__thread_bss");
        assert_eq!(
            section_flags(&exe, "__DATA_CONST", "__thread_ptrs"),
            S_THREAD_LOCAL_VARIABLE_POINTERS
        );
        assert_eq!(
            section_flags(&exe, "__DATA", "__thread_vars"),
            S_THREAD_LOCAL_VARIABLES
        );
        assert_eq!(
            section_flags(&exe, "__DATA", "__thread_data"),
            S_THREAD_LOCAL_REGULAR
        );
        assert_eq!(
            section_flags(&exe, "__DATA", "__thread_bss"),
            S_THREAD_LOCAL_ZEROFILL
        );
        assert_eq!(bss.offset, 0, "zero-fill template has no file bytes");
        assert_eq!(vars.size, 48);
        assert_eq!((data.size, bss.size), (8, 16));
        assert_eq!(
            bss.addr,
            data.addr + 16,
            "templates stay contiguous, 16-aligned"
        );
        let text = text_addr(&exe);
        assert_eq!(page_pair_target(&exe, text, text + 4, 8), pointers.addr);
        let bind = |address| {
            (
                address,
                DecodedFixup::Bind {
                    symbol: TLV_BOOTSTRAP_SYMBOL.into(),
                    addend: 0,
                },
            )
        };
        assert_eq!(
            decode_chained_fixups(&exe),
            [
                (pointers.addr, DecodedFixup::Rebase(vars.addr)),
                bind(vars.addr),
                bind(vars.addr + 24),
            ]
        );
        let offset_word =
            |descriptor: u64| rd_u64(&exe, file_offset_of(&exe, vars.addr + descriptor * 24 + 16));
        assert_eq!(offset_word(0), 0);
        assert_eq!(offset_word(1), bss.addr - data.addr);
        assert_eq!(rd_u64(&exe, file_offset_of(&exe, vars.addr + 8)), 0, "key");
        assert_eq!(rd_u64(&exe, file_offset_of(&exe, data.addr)), 11);
        assert_dyld_linkedit_payloads(&exe, &[TLV_BOOTSTRAP_SYMBOL]);
    }

    #[test]
    fn empty_overaligned_leading_tls_template_does_not_shift_descriptor_offsets() {
        // An empty `__thread_data` input placed first, aligned beyond every
        // non-empty template, starts the emitted section past the aligned
        // cursor. dyld copies templates from that section start, so the
        // descriptor offset must stay relative to it.
        let empty = parsed(
            vec![
                text_section(&[RET], vec![]),
                input_section(
                    "__thread_data",
                    "__DATA",
                    vec![],
                    5,
                    S_THREAD_LOCAL_REGULAR,
                    vec![],
                ),
            ],
            vec![defined_symbol("_other", 1, 0, true)],
        );
        let reader = tlv_object(
            "value",
            input_section(
                "__thread_data",
                "__DATA",
                11u64.to_le_bytes().to_vec(),
                3,
                S_THREAD_LOCAL_REGULAR,
                vec![],
            ),
            true,
        );
        let exe = link_with_dylibs(&[empty, reader], &DylibConfig::with_libsystem()).unwrap();
        let commands = walk_load_commands(&exe);
        let sections = section_commands(&exe, &commands);
        let vars = single_section(&sections, "__DATA", "__thread_vars");
        let data = single_section(&sections, "__DATA", "__thread_data");
        assert_eq!(data.addr % 32, 0, "the empty input keeps its alignment");
        assert_ne!(
            data.addr,
            align_to(vars.addr + vars.size, 8),
            "control: the section starts past the template-aligned cursor"
        );
        assert_eq!(data.size, 8);
        assert_eq!(rd_u64(&exe, file_offset_of(&exe, data.addr)), 11);
        assert_eq!(
            rd_u64(&exe, file_offset_of(&exe, vars.addr + 16)),
            0,
            "the only template starts the emitted __thread_data"
        );
    }

    #[test]
    fn tlvp_load_of_a_dylib_thread_local_binds_its_pointer_slot() {
        // An executable that only imports a thread-local has no descriptors
        // of its own: dyld binds the `__thread_ptrs` slot to the provider's
        // descriptor, and the LDR is kept.
        let object = parsed(
            vec![text_section(
                &[ADRP_X8, LDR_X8_X8, RET],
                vec![
                    Relocation::tlvp_load_page21(0, 1),
                    Relocation::tlvp_load_pageoff12(4, 1),
                ],
            )],
            vec![
                defined_symbol("_main", 1, 0, true),
                undefined_symbol("_provided_tls", false),
            ],
        );
        let exe = link_with_dylibs(&[object], &provider(&["_provided_tls"])).unwrap();
        assert_eq!(rd_u32(&exe, 24) & MH_HAS_TLV_DESCRIPTORS, 0);
        let commands = walk_load_commands(&exe);
        let sections = section_commands(&exe, &commands);
        let pointers = single_section(&sections, "__DATA_CONST", "__thread_ptrs");
        assert_eq!(pointers.size, 8);
        assert_eq!(
            decode_chained_fixups(&exe),
            [(
                pointers.addr,
                DecodedFixup::Bind {
                    symbol: "_provided_tls".into(),
                    addend: 0,
                },
            )]
        );
        let text = text_addr(&exe);
        assert_eq!(page_pair_target(&exe, text, text + 4, 8), pointers.addr);
        let ldr = rd_u32(&exe, file_offset_of(&exe, text + 4));
        assert_eq!(ldr & 0xFFC0_0000, 0xF940_0000, "no TLVP relaxation");
        assert_dyld_linkedit_payloads(&exe, &["_provided_tls"]);
    }

    #[test]
    fn over_aligned_read_only_after_fixup_data_does_not_widen_thread_pointers() {
        // One TLV pointer slot ends 8 bytes into the page; a 16-byte-aligned
        // `__DATA,__const` input then starts 16 bytes in. The alignment gap
        // belongs to neither section: `__thread_ptrs` keeps exactly its slot.
        let object = parsed(
            vec![
                text_section(
                    &[ADRP_X8, LDR_X8_X8, RET],
                    vec![
                        Relocation::tlvp_load_page21(0, 1),
                        Relocation::tlvp_load_pageoff12(4, 1),
                    ],
                ),
                input_section("__const", "__DATA", vec![0x5A; 16], 4, S_REGULAR, vec![]),
            ],
            vec![
                defined_symbol("_main", 1, 0, true),
                undefined_symbol("_provided_tls", false),
                defined_symbol("_table", 2, 0, true),
            ],
        );
        let exe = link_with_dylibs(&[object], &provider(&["_provided_tls"])).unwrap();
        let commands = walk_load_commands(&exe);
        let sections = section_commands(&exe, &commands);
        let pointers = single_section(&sections, "__DATA_CONST", "__thread_ptrs");
        let constant = single_section(&sections, "__DATA_CONST", "__const");
        assert_eq!(pointers.size, 8);
        assert_eq!(constant.addr, pointers.addr + 16);
        assert_eq!(constant.size, 16);
        assert_eq!(
            rd_u64(&exe, file_offset_of(&exe, constant.addr)),
            0x5A5A_5A5A_5A5A_5A5A
        );
    }

    #[test]
    fn malformed_tlv_descriptors_and_references_are_refused_by_name() {
        let config = DylibConfig::with_libsystem();
        let template = || {
            input_section(
                "__thread_data",
                "__DATA",
                vec![0; 8],
                3,
                S_THREAD_LOCAL_REGULAR,
                vec![],
            )
        };
        let refused = |object: ParsedObject| {
            let error = link_with_dylibs(&[object], &config).unwrap_err();
            assert!(matches!(error, LinkerError::ThreadLocal(_)), "{error:?}");
        };
        let mut short = tlv_object("v", template(), true);
        short.sections[1].data.truncate(20);
        refused(short);
        let mut keyed = tlv_object("v", template(), true);
        keyed.sections[1].data[8] = 1;
        refused(keyed);
        let mut regular_template = tlv_object("v", template(), true);
        regular_template.sections[2].flags = S_REGULAR;
        refused(regular_template);
        let mut missing_thunk = tlv_object("v", template(), true);
        missing_thunk.sections[1].relocations.remove(0);
        refused(missing_thunk);
        let mut wrong_thunk = tlv_object("v", template(), true);
        wrong_thunk.symbols[3].name = "_exit".into();
        refused(wrong_thunk);
        let mut aligned = tlv_object("v", template(), true);
        aligned.sections[2].align = 5;
        refused(aligned);
        let mut in_text = tlv_object("v", template(), true);
        in_text.sections[2].segment = "__TEXT".into();
        refused(in_text);
        // GOT loads and direct page references may not name a TLV.
        let mut got = tlv_object("v", template(), true);
        got.sections[0].relocations = vec![
            Relocation::got_load_page21(0, 1),
            Relocation::got_load_pageoff12(4, 1),
        ];
        refused(got);
        let mut template_reference = tlv_object("v", template(), true);
        template_reference.sections[0].relocations = vec![Relocation::page21(0, 2)];
        refused(template_reference);
        // A TLVP load of an undefined weak variable would call a null thunk.
        let mut weak = tlv_object("v", template(), true);
        weak.symbols.push(undefined_symbol("_missing", true));
        weak.sections[0].relocations = vec![
            Relocation::tlvp_load_page21(0, 4),
            Relocation::tlvp_load_pageoff12(4, 4),
        ];
        refused(weak);
        // TLVP loads keep their 64-bit LDR; an ADD is not relaxed or accepted.
        let mut add = tlv_object("v", template(), true);
        add.sections[0].data[4..8].copy_from_slice(&ADD_X8_X8.to_le_bytes());
        assert!(matches!(
            link_with_dylibs(&[add], &config),
            Err(LinkerError::RelocationInstructionMismatch {
                kind: AArch64RelocKind::TlvpLoadPageoff12,
                ..
            })
        ));
    }

    #[test]
    fn addend_pairs_offset_page_references_and_malformed_pairs_are_refused() {
        let addend = |value: i32| {
            with_relocation(
                Relocation::page21(0, (value as u32) & 0x00FF_FFFF),
                |reloc| {
                    reloc.kind = AArch64RelocKind::Addend;
                    reloc.is_extern = false;
                    reloc.pc_relative = false;
                },
            )
        };
        let mut addend_at_4 = addend(8);
        addend_at_4.offset = 4;
        let object = pointer_object(
            vec![],
            vec![0; 16],
            vec![
                addend(8),
                Relocation::page21(0, 3),
                addend_at_4,
                Relocation::pageoff12(4, 3),
            ],
        );
        let mut object = object;
        object.sections[0].data = words(&[ADRP_X8, ADD_X8_X8, RET]);
        let exe =
            link_with_dylibs(std::slice::from_ref(&object), &provider(&["_imported"])).unwrap();
        let commands = walk_load_commands(&exe);
        let data = single_section(&section_commands(&exe, &commands), "__DATA", "__data").addr;
        let text = text_addr(&exe);
        assert_eq!(page_pair_target(&exe, text, text + 4, 1), data + 8);

        for relocations in [
            vec![addend(8)],
            vec![addend(8), Relocation::got_load_page21(0, 3)],
            vec![
                with_relocation(addend(8), |reloc| reloc.is_extern = true),
                Relocation::page21(0, 3),
            ],
        ] {
            let mut malformed = object.clone();
            malformed.sections[0].relocations = relocations;
            assert!(matches!(
                link_with_dylibs(&[malformed], &provider(&["_imported"])),
                Err(LinkerError::MalformedRelocation(_))
            ));
        }
    }

    #[test]
    fn pageoff12_scales_by_access_size_and_refuses_truncation() {
        let symbols = vec![undefined_symbol("_target", false)];
        let patch = |instruction: u32, target: u64| {
            let mut data = instruction.to_le_bytes().to_vec();
            let addresses = HashMap::from([("_target".to_string(), target)]);
            RelocationApplicator::apply(
                &mut data,
                DEFAULT_BASE_ADDR,
                &[Relocation::pageoff12(0, 0)],
                &symbols,
                &addresses,
                &[],
            )
            .map(|()| (u32::from_le_bytes(data[..4].try_into().unwrap()) >> 10) & 0xFFF)
        };
        let base = DEFAULT_BASE_ADDR + 0x4000;
        assert_eq!(
            patch(0x3DC0_0100, base + 0x30).unwrap(),
            3,
            "LDR Q scales by 16"
        );
        assert_eq!(
            patch(0xB940_0108, base + 0x34).unwrap(),
            13,
            "LDR W scales by 4"
        );
        assert_eq!(
            patch(0x3940_0108, base + 0x35).unwrap(),
            0x35,
            "LDRB is byte-scaled"
        );
        assert_eq!(
            patch(0xF900_0108, base + 0x38).unwrap(),
            7,
            "STR X scales by 8"
        );
        assert_eq!(patch(ADD_X8_X8, base + 0x35).unwrap(), 0x35);
        assert!(matches!(
            patch(0x3DC0_0100, base + 0x38),
            Err(LinkerError::RelocationOverflow { .. })
        ));
        assert!(matches!(
            patch(0xD280_0000, base),
            Err(LinkerError::RelocationInstructionMismatch { .. })
        ));
        // The low-level applicator has no GOT/TLV slots and refuses those kinds.
        let mut data = LDR_X8_X8.to_le_bytes().to_vec();
        assert!(matches!(
            RelocationApplicator::apply(
                &mut data,
                DEFAULT_BASE_ADDR,
                &[Relocation::got_load_pageoff12(0, 0)],
                &symbols,
                &HashMap::from([("_target".to_string(), base)]),
                &[],
            ),
            Err(LinkerError::UnsupportedRelocation(
                AArch64RelocKind::GotLoadPageoff12
            ))
        ));
    }

    #[test]
    fn parser_keeps_zerofill_sections_out_of_the_file() {
        let mut writer = MachOWriter::new();
        writer.add_text_section(&RET.to_le_bytes());
        writer.add_custom_section(
            b"__thread_bss",
            b"__DATA",
            &[0xAA; 16],
            3,
            S_THREAD_LOCAL_ZEROFILL,
        );
        writer.add_custom_section(b"__bss", b"__DATA", &[0xBB; 32], 4, S_ZEROFILL);
        writer.add_symbol("_main", 1, 0, true).unwrap();
        let mut bytes = writer.write().unwrap();
        // Zero-fill sections conventionally name file offset 0 (the header)
        // and may be larger than the whole object.
        let commands = walk_load_commands(&bytes);
        let segment = commands
            .iter()
            .find(|command| command.cmd == LC_SEGMENT_64)
            .unwrap();
        for index in 0..rd_u32(&bytes, segment.offset + 64) as usize {
            let header = segment.offset + SEGMENT_COMMAND_64_SIZE as usize + index * 80;
            if read_name16(&bytes, header) == "__bss" {
                patch_u32(&mut bytes, header + 48, 0);
                bytes[header + 40..header + 48].copy_from_slice(&(1u64 << 20).to_le_bytes());
            } else if read_name16(&bytes, header) == "__thread_bss" {
                patch_u32(&mut bytes, header + 48, 0);
            }
        }
        let object = MachOParser::parse(&bytes).unwrap();
        let tbss = object
            .sections
            .iter()
            .find(|section| section.name == "__thread_bss")
            .unwrap();
        let bss = object
            .sections
            .iter()
            .find(|section| section.name == "__bss")
            .unwrap();
        assert!(
            tbss.data.is_empty() && bss.data.is_empty(),
            "no header bytes"
        );
        assert!(tbss.is_zerofill() && bss.is_zerofill());
        assert_eq!((tbss.effective_size(), bss.effective_size()), (16, 1 << 20));
    }

    #[test]
    fn debug_sections_are_not_loaded_and_references_into_them_fail() {
        let unwind = input_section(
            "__compact_unwind",
            "__LD",
            vec![0; 32],
            3,
            S_REGULAR | S_ATTR_DEBUG,
            vec![with_relocation(Relocation::unsigned_ptr(0, 1), |reloc| {
                reloc.is_extern = false
            })],
        );
        let object = parsed(
            vec![text_section(&[RET], vec![]), unwind.clone()],
            vec![
                defined_symbol("_main", 1, 0, true),
                defined_symbol("ltmp1", 2, 0, false),
            ],
        );
        let exe = link(std::slice::from_ref(&object)).unwrap();
        let commands = walk_load_commands(&exe);
        assert!(
            !segment_commands(&exe, &commands)
                .iter()
                .any(|segment| segment.name == "__DATA"),
            "debug input is not loaded"
        );
        assert!(decode_chained_fixups(&exe).is_empty());
        let mut referencing = object;
        referencing.sections[0] = text_section(&[ADRP_X8, RET], vec![Relocation::page21(0, 1)]);
        assert!(matches!(
            link(&[referencing]),
            Err(LinkerError::UnloadedSectionReference(ref section)) if section == "__LD,__compact_unwind"
        ));
    }

    #[test]
    fn section_types_needing_unimplemented_linker_work_are_refused() {
        for section_type in [
            S_MOD_INIT_FUNC_POINTERS,
            S_THREAD_LOCAL_INIT_FUNCTION_POINTERS,
            S_LAZY_SYMBOL_POINTERS,
        ] {
            let object = parsed(
                vec![
                    text_section(&[RET], vec![]),
                    input_section("__special", "__DATA", vec![0; 8], 3, section_type, vec![]),
                ],
                vec![defined_symbol("_main", 1, 0, true)],
            );
            assert!(matches!(
                link(&[object]),
                Err(LinkerError::UnsupportedSectionType { section_type: found, .. }) if found == section_type
            ));
        }
    }

    #[test]
    fn chained_fixups_chain_within_pages_and_restart_on_each_page() {
        let size = PAGE_SIZE as usize * 2 + 64;
        let pointers = [
            0u32,
            8,
            4096,
            PAGE_SIZE as u32 + 16,
            PAGE_SIZE as u32 * 2 + 8,
        ];
        let object = pointer_object(
            pointers
                .iter()
                .map(|&offset| Relocation::unsigned_ptr(offset, 3))
                .collect(),
            vec![0; size],
            vec![],
        );
        let exe = link_with_dylibs(&[object], &provider(&["_imported"])).unwrap();
        let commands = walk_load_commands(&exe);
        let data = single_section(&section_commands(&exe, &commands), "__DATA", "__data").addr;
        let decoded = decode_chained_fixups(&exe);
        assert_eq!(
            decoded,
            pointers
                .iter()
                .map(|&offset| (data + u64::from(offset), DecodedFixup::Rebase(data)))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn chain_encoder_rejects_unrepresentable_fixups() {
        let encode = |fixups: &mut [PointerFixup], bytes: usize| {
            let mut data = vec![0; bytes];
            encode_segment_chains(
                3,
                DEFAULT_BASE_ADDR + PAGE_SIZE,
                DEFAULT_BASE_ADDR,
                &mut data,
                fixups,
            )
        };
        let base = DEFAULT_BASE_ADDR + PAGE_SIZE;
        let rebase = |address, target| PointerFixup {
            address,
            kind: PointerFixupKind::Rebase { target },
        };
        for (mut fixups, bytes) in [
            (vec![rebase(base, DYLD_CHAINED_PTR_64_TARGET_LIMIT)], 8),
            (
                vec![PointerFixup {
                    address: base,
                    kind: PointerFixupKind::Bind {
                        import: DYLD_CHAINED_PTR_64_BIND_ORDINAL_LIMIT,
                        addend: 0,
                    },
                }],
                8,
            ),
            (vec![rebase(base + 4, base)], 16),
            (vec![rebase(base + 8, base)], 8),
            (vec![rebase(base - 8, base)], 8),
        ] {
            assert!(matches!(
                encode(&mut fixups, bytes),
                Err(LinkerError::ChainedFixup { .. })
            ));
        }
        let mut duplicate = [rebase(base, base), rebase(base, base)];
        assert!(encode(&mut duplicate, 8).is_err());
        let mut ok = [rebase(base + 8, base), rebase(base, base + 8)];
        let info = encode(&mut ok, 16).unwrap().unwrap();
        assert_eq!(info.segment_index, 3);
        assert_eq!(info.segment_offset, PAGE_SIZE);
        assert_eq!(info.page_starts, [(0, 0)]);
    }

    // =======================================================================
    // MH_DYLIB output and exports trie
    // =======================================================================

    fn read_uleb128(bytes: &[u8], cursor: &mut usize) -> u64 {
        let mut value = 0u64;
        let mut shift = 0;
        loop {
            let byte = bytes[*cursor];
            *cursor += 1;
            value |= u64::from(byte & 0x7F) << shift;
            if byte & 0x80 == 0 {
                return value;
            }
            shift += 7;
        }
    }

    /// Walk an exports trie the way dyld does: every root-to-terminal path
    /// spells one exported name.
    fn walk_exports_trie(trie: &[u8]) -> Vec<(String, u64, u64)> {
        let mut found = Vec::new();
        let mut pending = vec![(0usize, Vec::new())];
        let mut visited = 0;
        while let Some((node, prefix)) = pending.pop() {
            visited += 1;
            assert!(visited <= trie.len(), "trie cycles");
            let mut cursor = node;
            let terminal_size = read_uleb128(trie, &mut cursor) as usize;
            let children_at = cursor + terminal_size;
            if terminal_size != 0 {
                let flags = read_uleb128(trie, &mut cursor);
                let address = read_uleb128(trie, &mut cursor);
                assert_eq!(cursor, children_at, "terminal size covers its payload");
                found.push((String::from_utf8(prefix.clone()).unwrap(), flags, address));
            }
            cursor = children_at;
            let children = trie[cursor];
            cursor += 1;
            for _ in 0..children {
                let end = cursor + trie[cursor..].iter().position(|&byte| byte == 0).unwrap();
                let mut name = prefix.clone();
                name.extend_from_slice(&trie[cursor..end]);
                cursor = end + 1;
                let child = read_uleb128(trie, &mut cursor) as usize;
                assert!(child < trie.len() && child != node);
                pending.push((child, name));
            }
        }
        found.sort();
        found
    }

    #[test]
    fn exports_trie_round_trips_through_an_independent_walker() {
        assert_eq!(build_exports_trie(&[]).unwrap(), EMPTY_EXPORTS_TRIE);
        // Shared prefixes, a name that is a prefix of another, and offsets
        // wide enough that child offsets need multi-byte ULEB128 fixpoints.
        let mut exports: Vec<ExportEntry> = [
            "_a", "_ab", "_abc", "_abd", "_b", "_cg_add", "_cg_tls", "_zz",
        ]
        .iter()
        .enumerate()
        .map(|(index, name)| ExportEntry {
            name: (*name).into(),
            flags: if name.ends_with("tls") {
                EXPORT_SYMBOL_FLAGS_KIND_THREAD_LOCAL
            } else {
                EXPORT_SYMBOL_FLAGS_KIND_REGULAR
            },
            offset: 0x4000 + (index as u64) * 0x1_0000_0001,
        })
        .collect();
        for index in 0..300 {
            exports.push(ExportEntry {
                name: format!("_many_{index:03}_{}", "x".repeat(index % 7)),
                flags: 0,
                offset: index as u64 * 24,
            });
        }
        let trie = build_exports_trie(&exports).unwrap();
        let mut expected: Vec<_> = exports
            .iter()
            .map(|export| (export.name.clone(), export.flags, export.offset))
            .collect();
        expected.sort();
        assert_eq!(walk_exports_trie(&trie), expected);
        let mut duplicate = exports[..2].to_vec();
        duplicate[1].name = duplicate[0].name.clone();
        assert!(build_exports_trie(&duplicate).is_err());
    }

    fn dylib_object() -> ParsedObject {
        let mut object = tlv_object(
            "tls_value",
            input_section(
                "__thread_data",
                "__DATA",
                9u64.to_le_bytes().to_vec(),
                3,
                S_THREAD_LOCAL_REGULAR,
                vec![],
            ),
            true,
        );
        // Section 4: exported data holding a pointer to its own text.
        object.sections.push(input_section(
            "__data",
            "__DATA",
            vec![0; 8],
            3,
            S_REGULAR,
            vec![Relocation::unsigned_ptr(0, 0)],
        ));
        object.symbols[0].name = "_reader".into();
        object.symbols.extend([
            defined_symbol("_value", 4, 0, true),
            ParsedSymbol {
                name: "_hidden".into(),
                n_type: N_SECT | N_EXT | N_PEXT,
                section: 1,
                desc: 0,
                value: 4,
            },
            defined_symbol("_local", 1, 8, false),
        ]);
        object
    }

    #[test]
    fn dylib_images_are_based_at_zero_named_by_id_and_export_their_definitions() {
        let install_name = "@executable_path/libtrust.dylib";
        let dylib = link_dylib(
            &[dylib_object()],
            &DylibConfig::with_libsystem(),
            install_name,
        )
        .unwrap();
        assert_eq!(rd_u32(&dylib, 12), MH_DYLIB);
        assert_eq!(rd_u32(&dylib, 24), MH_DYLIB_FLAGS | MH_HAS_TLV_DESCRIPTORS);
        let commands = walk_load_commands(&dylib);
        for absent in [LC_MAIN, LC_LOAD_DYLINKER] {
            assert_eq!(count_load_command(&commands, absent), 0);
        }
        let id = single_load_command(&commands, LC_ID_DYLIB);
        assert_eq!(
            read_cstring(&dylib, id.offset + rd_u32(&dylib, id.offset + 8) as usize),
            install_name
        );
        let segments = segment_commands(&dylib, &commands);
        assert_eq!(segments[0].name, "__TEXT");
        assert_eq!((segments[0].vmaddr, segments[0].fileoff), (0, 0));
        let sections = section_commands(&dylib, &commands);
        let text = single_section(&sections, "__TEXT", "__text");
        let vars = single_section(&sections, "__DATA", "__thread_vars");
        let data = single_section(&sections, "__DATA", "__data");
        let pointers = single_section(&sections, "__DATA_CONST", "__thread_ptrs");
        // Rebase targets are image offsets from base 0.
        let fixups = decode_chained_fixups(&dylib);
        assert!(fixups.contains(&(data.addr, DecodedFixup::Rebase(text.addr))));
        assert!(fixups.contains(&(pointers.addr, DecodedFixup::Rebase(vars.addr))));
        let exports_command =
            linkedit_data_command(&dylib, single_load_command(&commands, LC_DYLD_EXPORTS_TRIE));
        let start = exports_command.dataoff as usize;
        let exports = walk_exports_trie(&dylib[start..start + exports_command.datasize as usize]);
        assert_eq!(
            exports,
            [
                (
                    "_reader".to_string(),
                    EXPORT_SYMBOL_FLAGS_KIND_REGULAR,
                    text.addr
                ),
                (
                    "_tls_value".to_string(),
                    EXPORT_SYMBOL_FLAGS_KIND_THREAD_LOCAL,
                    vars.addr
                ),
                (
                    "_value".to_string(),
                    EXPORT_SYMBOL_FLAGS_KIND_REGULAR,
                    data.addr
                ),
            ],
            "private-extern and local symbols stay unexported"
        );
        // Only the main executable's code directory claims MAIN_BINARY.
        let signature =
            linkedit_data_command(&dylib, single_load_command(&commands, LC_CODE_SIGNATURE));
        let code_directory = signature.dataoff as usize + CS_BLOB_HEADERS_SIZE;
        assert_eq!(rd_be_u64(&dylib, code_directory + 80), 0);
        let again = link_dylib(
            &[dylib_object()],
            &DylibConfig::with_libsystem(),
            install_name,
        )
        .unwrap();
        assert_eq!(dylib, again, "dylib output is deterministic");
    }

    #[test]
    fn dylib_refuses_weak_thread_locals_templates_and_malformed_install_names() {
        let mut weak = dylib_object();
        weak.symbols[1].desc = N_WEAK_DEF;
        assert!(matches!(
            link_dylib(&[weak], &DylibConfig::with_libsystem(), "@rpath/libx.dylib"),
            Err(LinkerError::UnsupportedDylibExport { ref symbol, .. }) if symbol == "_tls_value"
        ));
        let mut template = dylib_object();
        template.symbols[2].n_type |= N_EXT;
        assert!(matches!(
            link_dylib(
                &[template],
                &DylibConfig::with_libsystem(),
                "@rpath/libx.dylib"
            ),
            Err(LinkerError::UnsupportedDylibExport { .. })
        ));
        for name in ["", "bad\0name"] {
            assert!(matches!(
                link_dylib(&[dylib_object()], &DylibConfig::with_libsystem(), name),
                Err(LinkerError::MalformedInput { .. })
            ));
        }
    }

    const BL: u32 = 0x9400_0000;
    const MOVZ_X0_1: u32 = 0xD280_0020;

    /// `_entry` calls `_weak_fn` (a weak definition later in `__text`) and
    /// loads `_weak_data`'s GOT slot; `__DATA,__const` points at `_weak_data`
    /// and at `_strong_data`. `_hidden_weak` is weak but private extern.
    fn weak_object() -> ParsedObject {
        let text = text_section(
            &[BL, ADRP_X8, LDR_X8_X8, RET, MOVZ_X0_1, RET],
            vec![
                Relocation::branch26(0, 1),
                Relocation::got_load_page21(4, 2),
                Relocation::got_load_pageoff12(8, 2),
            ],
        );
        let data = input_section("__data", "__DATA", vec![7; 24], 3, S_REGULAR, vec![]);
        let constant = input_section(
            "__const",
            "__DATA",
            vec![0; 16],
            3,
            S_REGULAR,
            vec![
                Relocation::unsigned_ptr(0, 2),
                Relocation::unsigned_ptr(8, 3),
            ],
        );
        let weak = |mut symbol: ParsedSymbol| {
            symbol.desc = N_WEAK_DEF;
            symbol
        };
        let mut hidden_weak = weak(defined_symbol("_hidden_weak", 2, 16, true));
        hidden_weak.n_type |= N_PEXT;
        parsed(
            vec![text, data, constant],
            vec![
                defined_symbol("_entry", 1, 0, true),
                weak(defined_symbol("_weak_fn", 1, 16, true)),
                weak(defined_symbol("_weak_data", 2, 0, true)),
                defined_symbol("_strong_data", 2, 8, true),
                hidden_weak,
            ],
        )
    }

    fn main_object() -> ParsedObject {
        parsed(
            vec![text_section(&[RET], vec![])],
            vec![defined_symbol("_main", 1, 0, true)],
        )
    }

    fn import_ordinals(image: &[u8]) -> Vec<(String, u32)> {
        let commands = walk_load_commands(image);
        let payload = linkedit_data_command(
            image,
            single_load_command(&commands, LC_DYLD_CHAINED_FIXUPS),
        );
        let start = payload.dataoff as usize;
        let imports = start + rd_u32(image, start + 8) as usize;
        let symbols = start + rd_u32(image, start + 12) as usize;
        (0..rd_u32(image, start + 16) as usize)
            .map(|index| {
                let entry = rd_u32(image, imports + index * 4);
                assert_eq!((entry >> 8) & 1, 0, "no weak-import bit");
                (
                    read_cstring(image, symbols + (entry >> 9) as usize),
                    entry & 0xFF,
                )
            })
            .collect()
    }

    fn branch_target(image: &[u8], text: &SectionCommand, offset: u64) -> u64 {
        let word = rd_u32(image, text.offset as usize + offset as usize);
        assert_eq!(word & 0xFC00_0000, BL, "BL expected");
        let delta = ((i64::from(word & 0x03FF_FFFF) << 38) >> 36) as u64;
        (text.addr + offset).wrapping_add(delta)
    }

    #[test]
    fn dylib_weak_definitions_are_exported_weak_and_bound_through_weak_lookup() {
        let dylib = link_dylib(
            &[weak_object()],
            &DylibConfig::with_libsystem(),
            "@rpath/libweak.dylib",
        )
        .unwrap();
        assert_eq!(
            rd_u32(&dylib, 24),
            MH_DYLIB_FLAGS | MH_WEAK_DEFINES | MH_BINDS_TO_WEAK
        );
        let commands = walk_load_commands(&dylib);
        let sections = section_commands(&dylib, &commands);
        let text = single_section(&sections, "__TEXT", "__text");
        let stubs = single_section(&sections, "__TEXT", "__stubs");
        let got = single_section(&sections, "__DATA_CONST", "__got");
        let constant = single_section(&sections, "__DATA_CONST", "__const");
        let data = single_section(&sections, "__DATA", "__data");
        assert_eq!(
            section_flags(&dylib, "__DATA_CONST", "__const"),
            S_REGULAR,
            "relocated constants keep S_REGULAR in the read-only segment"
        );
        // The call goes through the stub, never straight to this image's copy.
        assert_eq!(branch_target(&dylib, text, 0), stubs.addr);
        assert_eq!(stubs.size, u64::from(STUB_SIZE));
        let fixups = decode_chained_fixups(&dylib);
        let bind = |symbol: &str| DecodedFixup::Bind {
            symbol: symbol.into(),
            addend: 0,
        };
        assert!(fixups.contains(&(got.addr, bind("_weak_fn"))), "{fixups:?}");
        assert!(
            fixups.contains(&(got.addr + 8, bind("_weak_data"))),
            "{fixups:?}"
        );
        assert!(
            fixups.contains(&(constant.addr, bind("_weak_data"))),
            "{fixups:?}"
        );
        assert!(
            fixups.contains(&(constant.addr + 8, DecodedFixup::Rebase(data.addr + 8))),
            "{fixups:?}"
        );
        assert_eq!(
            import_ordinals(&dylib),
            [
                (
                    "_weak_data".to_string(),
                    BIND_SPECIAL_DYLIB_WEAK_LOOKUP_ORDINAL
                ),
                (
                    "_weak_fn".to_string(),
                    BIND_SPECIAL_DYLIB_WEAK_LOOKUP_ORDINAL
                ),
            ]
        );
        let exports_command =
            linkedit_data_command(&dylib, single_load_command(&commands, LC_DYLD_EXPORTS_TRIE));
        let start = exports_command.dataoff as usize;
        let exports = walk_exports_trie(&dylib[start..start + exports_command.datasize as usize]);
        let weak = EXPORT_SYMBOL_FLAGS_KIND_REGULAR | EXPORT_SYMBOL_FLAGS_WEAK_DEFINITION;
        assert_eq!(
            exports,
            [
                (
                    "_entry".to_string(),
                    EXPORT_SYMBOL_FLAGS_KIND_REGULAR,
                    text.addr
                ),
                (
                    "_strong_data".to_string(),
                    EXPORT_SYMBOL_FLAGS_KIND_REGULAR,
                    data.addr + 8
                ),
                ("_weak_data".to_string(), weak, data.addr),
                ("_weak_fn".to_string(), weak, text.addr + 16),
            ],
            "hidden weak definitions stay unexported"
        );
    }

    #[test]
    fn executables_resolve_their_weak_definitions_statically() {
        let exe = link_with_dylibs(
            &[weak_object(), main_object()],
            &DylibConfig::with_libsystem(),
        )
        .unwrap();
        assert_eq!(rd_u32(&exe, 24) & (MH_WEAK_DEFINES | MH_BINDS_TO_WEAK), 0);
        let commands = walk_load_commands(&exe);
        let sections = section_commands(&exe, &commands);
        let text = single_section(&sections, "__TEXT", "__text");
        let got = single_section(&sections, "__DATA_CONST", "__got");
        let data = single_section(&sections, "__DATA", "__data");
        let constant = single_section(&sections, "__DATA_CONST", "__const");
        assert_eq!(branch_target(&exe, text, 0), text.addr + 16);
        let fixups = decode_chained_fixups(&exe);
        assert!(fixups.contains(&(got.addr, DecodedFixup::Rebase(data.addr))));
        assert!(fixups.contains(&(constant.addr, DecodedFixup::Rebase(data.addr))));
        assert!(
            import_ordinals(&exe)
                .iter()
                .all(|(_, ordinal)| *ordinal == 1)
        );
    }

    #[test]
    fn direct_page_references_to_coalescable_weak_definitions_are_refused_in_dylibs() {
        let mut object = weak_object();
        object.sections[0].relocations = vec![
            Relocation::branch26(0, 1),
            Relocation::page21(4, 2),
            Relocation::pageoff12(8, 2),
        ];
        object.sections[0].data = words(&[BL, ADRP_X8, ADD_X8_X8, RET, MOVZ_X0_1, RET]);
        assert!(matches!(
            link_dylib(&[object.clone()], &DylibConfig::with_libsystem(), "@rpath/l.dylib"),
            Err(LinkerError::DirectWeakDefinitionReference { ref symbol, .. })
                if symbol == "_weak_data"
        ));
        // A hidden weak definition is not coalesced, so it may be direct.
        object.sections[0].relocations[1].symbol_index = 4;
        object.sections[0].relocations[2].symbol_index = 4;
        link_dylib(
            &[object.clone()],
            &DylibConfig::with_libsystem(),
            "@rpath/l.dylib",
        )
        .expect("hidden weak definitions bind directly");
        // An executable resolves weak definitions statically.
        link_with_dylibs(&[object, main_object()], &DylibConfig::with_libsystem())
            .expect("executables keep direct weak references");
    }

    #[test]
    fn read_only_after_fixup_input_rejects_thread_local_and_zero_fill_storage() {
        for section in [
            zerofill_section("__const", 16, 3, S_ZEROFILL),
            input_section(
                "__x",
                "__DATA_CONST",
                vec![0; 8],
                3,
                S_THREAD_LOCAL_REGULAR,
                vec![],
            ),
        ] {
            let mut section = section;
            if section.name == "__const" {
                section.segment = "__DATA".into();
            }
            let object = parsed(
                vec![text_section(&[RET], vec![]), section],
                vec![defined_symbol("_main", 1, 0, true)],
            );
            assert!(matches!(
                link(&[object]),
                Err(LinkerError::MalformedInput { ref detail, .. })
                    if detail.contains("read-only after fixups")
            ));
        }
    }

    fn signed_ret_executable() -> Vec<u8> {
        let mut writer = MachOWriter::new();
        writer.add_text_section(&0xD65F03C0u32.to_le_bytes());
        writer.add_symbol("_main", 1, 0, true).unwrap();
        let obj = MachOParser::parse(&writer.write().unwrap()).unwrap();
        link(&[obj]).unwrap()
    }

    #[test]
    fn signature_self_check_refuses_tampered_or_off_contract_images() {
        let exe = signed_ret_executable();
        let text_size = crate::macho::codesign::verify_ad_hoc_signature(&exe)
            .unwrap()
            .code_directory
            .exec_segment
            .unwrap()
            .limit;
        assert_eq!(text_size % PAGE_SIZE, 0);
        self_check_code_signature(&exe, text_size, CS_EXECSEG_MAIN_BINARY).unwrap();

        // A changed byte after signing fails the independent verifier.
        let mut tampered = exe.clone();
        let last_text_page = 0x4000 - 1;
        tampered[last_text_page] ^= 0xFF;
        assert!(matches!(
            self_check_code_signature(&tampered, text_size, CS_EXECSEG_MAIN_BINARY),
            Err(LinkerError::CodeSignatureSelfCheck(
                crate::macho::codesign::CodeSignatureError::CodePageHashMismatch {
                    slot: 0,
                    page: 3
                }
            ))
        ));

        // A valid signature with the wrong main-binary marking, or an
        // executable segment other than the whole __TEXT range, departs from
        // the contract.
        for (size, flags) in [(text_size, 0), (8, CS_EXECSEG_MAIN_BINARY)] {
            let error = self_check_code_signature(&exe, size, flags).unwrap_err();
            assert!(
                matches!(error, LinkerError::CodeSignatureContract(ref detail) if detail.contains("executable segment")),
                "{error}"
            );
        }
    }

    #[test]
    fn code_signature_sizes_refuse_images_beyond_the_32_bit_code_limit() {
        assert_eq!(code_signature_block_count(0).unwrap(), 0);
        assert_eq!(code_signature_block_count(1).unwrap(), 1);
        assert_eq!(code_signature_block_count(4096).unwrap(), 1);
        assert_eq!(code_signature_block_count(4097).unwrap(), 2);
        let largest = u64::from(u32::MAX);
        assert_eq!(
            code_signature_block_count(largest).unwrap(),
            largest.div_ceil(4096) as u32
        );
        for over in [largest + 1, u64::MAX] {
            assert!(matches!(
                code_signature_block_count(over),
                Err(LinkerError::LayoutOverflow(_))
            ));
            assert!(matches!(
                code_signature_size(over),
                Err(LinkerError::LayoutOverflow(_))
            ));
        }
    }

    #[test]
    fn signature_contract_names_each_departure_from_the_linker_signature() {
        use crate::macho::codesign::test_support::{CodeDirectorySpec, resign};
        let exe = signed_ret_executable();
        let text_size = crate::macho::codesign::verify_ad_hoc_signature(&exe)
            .unwrap()
            .code_directory
            .exec_segment
            .unwrap()
            .limit;
        let own = CodeDirectorySpec::linker_like();
        self_check_code_signature(
            &resign(&exe, std::slice::from_ref(&own)),
            text_size,
            CS_EXECSEG_MAIN_BINARY,
        )
        .unwrap();
        let variant = |edit: &dyn Fn(&mut CodeDirectorySpec)| {
            let mut spec = own.clone();
            edit(&mut spec);
            vec![spec]
        };
        let alternate = CodeDirectorySpec {
            slot: crate::macho::codesign::CSSLOT_ALTERNATE_CODEDIRECTORIES,
            ..own.clone()
        };
        // Each signature verifies independently; only the contract refuses it.
        for (directories, field) in [
            (variant(&|cd| cd.flags = CS_ADHOC), "flags"),
            (
                variant(&|cd| cd.flags = CS_ADHOC | CS_LINKER_SIGNED | 0x0001_0000),
                "flags",
            ),
            (variant(&|cd| cd.page_shift = 14), "page size"),
            (variant(&|cd| cd.identifier = "trust-cG"), "identifier"),
            (vec![own.clone(), alternate], "alternate CodeDirectories"),
        ] {
            let image = resign(&exe, &directories);
            crate::macho::codesign::verify_ad_hoc_signature(&image).unwrap();
            let error =
                self_check_code_signature(&image, text_size, CS_EXECSEG_MAIN_BINARY).unwrap_err();
            assert!(
                matches!(error, LinkerError::CodeSignatureContract(ref detail) if detail.starts_with(&format!("unexpected {field} "))),
                "{field}: {error}"
            );
        }
    }
}
