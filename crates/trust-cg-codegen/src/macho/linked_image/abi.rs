// trust-cg-codegen/macho/linked_image/abi.rs - Mach-O ABI constants for the linked-image replay
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Mach-O ABI values the linked-image readers use, declared here from
//! `<mach-o/loader.h>`, `<mach-o/nlist.h>`, `<mach-o/reloc.h>`,
//! `<mach-o/arm64/reloc.h>` and `<mach-o/fixup-chains.h>` so that neither
//! reader imports the object writer's or the standalone linker's constants.

pub(super) const MH_MAGIC_64: u32 = 0xFEED_FACF;
pub(super) const FAT_MAGIC: u32 = 0xCAFE_BABE;
pub(super) const FAT_CIGAM: u32 = 0xBEBA_FECA;
pub(super) const CPU_TYPE_ARM64: u32 = 0x0100_000C;

pub(super) const MH_OBJECT: u32 = 0x1;
pub(super) const MH_EXECUTE: u32 = 0x2;
pub(super) const MH_DYLIB: u32 = 0x6;

pub(super) const MH_TWOLEVEL: u32 = 0x80;
pub(super) const MH_WEAK_DEFINES: u32 = 0x8000;
pub(super) const MH_BINDS_TO_WEAK: u32 = 0x1_0000;
pub(super) const MH_PIE: u32 = 0x20_0000;
pub(super) const MH_HAS_TLV_DESCRIPTORS: u32 = 0x80_0000;
pub(super) const MH_SUBSECTIONS_VIA_SYMBOLS: u32 = 0x2000;

pub(super) const LC_REQ_DYLD: u32 = 0x8000_0000;
pub(super) const LC_SYMTAB: u32 = 0x2;
pub(super) const LC_DYSYMTAB: u32 = 0xB;
pub(super) const LC_LOAD_DYLIB: u32 = 0xC;
pub(super) const LC_ID_DYLIB: u32 = 0xD;
pub(super) const LC_LOAD_DYLINKER: u32 = 0xE;
pub(super) const LC_LOAD_WEAK_DYLIB: u32 = 0x18 | LC_REQ_DYLD;
pub(super) const LC_SEGMENT_64: u32 = 0x19;
pub(super) const LC_UUID: u32 = 0x1B;
pub(super) const LC_RPATH: u32 = 0x1C | LC_REQ_DYLD;
pub(super) const LC_CODE_SIGNATURE: u32 = 0x1D;
pub(super) const LC_REEXPORT_DYLIB: u32 = 0x1F | LC_REQ_DYLD;
pub(super) const LC_LAZY_LOAD_DYLIB: u32 = 0x20;
pub(super) const LC_DYLD_INFO: u32 = 0x22;
pub(super) const LC_DYLD_INFO_ONLY: u32 = 0x22 | LC_REQ_DYLD;
pub(super) const LC_LOAD_UPWARD_DYLIB: u32 = 0x23 | LC_REQ_DYLD;
pub(super) const LC_VERSION_MIN_MACOSX: u32 = 0x24;
pub(super) const LC_FUNCTION_STARTS: u32 = 0x26;
pub(super) const LC_MAIN: u32 = 0x28 | LC_REQ_DYLD;
pub(super) const LC_DATA_IN_CODE: u32 = 0x29;
pub(super) const LC_SOURCE_VERSION: u32 = 0x2A;
pub(super) const LC_LINKER_OPTION: u32 = 0x2D;
pub(super) const LC_LINKER_OPTIMIZATION_HINT: u32 = 0x2E;
pub(super) const LC_NOTE: u32 = 0x31;
pub(super) const LC_BUILD_VERSION: u32 = 0x32;
pub(super) const LC_DYLD_EXPORTS_TRIE: u32 = 0x33 | LC_REQ_DYLD;
pub(super) const LC_DYLD_CHAINED_FIXUPS: u32 = 0x34 | LC_REQ_DYLD;
pub(super) const LC_ATOM_INFO: u32 = 0x36;

/// The install name of libSystem, which every image links.
pub(super) const LIBSYSTEM_INSTALL_NAME: &str = "/usr/lib/libSystem.B.dylib";

pub(super) const SG_READ_ONLY: u32 = 0x10;
pub(super) const VM_PROT_READ: u32 = 0x1;
pub(super) const VM_PROT_WRITE: u32 = 0x2;
pub(super) const VM_PROT_EXECUTE: u32 = 0x4;

pub(super) const SECTION_TYPE: u32 = 0xFF;
pub(super) const S_ZEROFILL: u32 = 0x1;
pub(super) const S_CSTRING_LITERALS: u32 = 0x2;
pub(super) const S_4BYTE_LITERALS: u32 = 0x3;
pub(super) const S_8BYTE_LITERALS: u32 = 0x4;
pub(super) const S_LITERAL_POINTERS: u32 = 0x5;
pub(super) const S_NON_LAZY_SYMBOL_POINTERS: u32 = 0x6;
pub(super) const S_LAZY_SYMBOL_POINTERS: u32 = 0x7;
pub(super) const S_SYMBOL_STUBS: u32 = 0x8;
pub(super) const S_MOD_INIT_FUNC_POINTERS: u32 = 0x9;
pub(super) const S_MOD_TERM_FUNC_POINTERS: u32 = 0xA;
pub(super) const S_GB_ZEROFILL: u32 = 0xC;
pub(super) const S_INTERPOSING: u32 = 0xD;
pub(super) const S_16BYTE_LITERALS: u32 = 0xE;
pub(super) const S_DTRACE_DOF: u32 = 0xF;
pub(super) const S_LAZY_DYLIB_SYMBOL_POINTERS: u32 = 0x10;
pub(super) const S_THREAD_LOCAL_REGULAR: u32 = 0x11;
pub(super) const S_THREAD_LOCAL_ZEROFILL: u32 = 0x12;
pub(super) const S_THREAD_LOCAL_VARIABLES: u32 = 0x13;
pub(super) const S_THREAD_LOCAL_VARIABLE_POINTERS: u32 = 0x14;
pub(super) const S_THREAD_LOCAL_INIT_FUNCTION_POINTERS: u32 = 0x15;
pub(super) const S_INIT_FUNC_OFFSETS: u32 = 0x16;
pub(super) const S_ATTR_PURE_INSTRUCTIONS: u32 = 0x8000_0000;
pub(super) const S_ATTR_NO_DEAD_STRIP: u32 = 0x1000_0000;
pub(super) const S_ATTR_DEBUG: u32 = 0x0200_0000;
pub(super) const S_ATTR_SOME_INSTRUCTIONS: u32 = 0x0000_0400;

pub(super) const N_STAB: u8 = 0xE0;
pub(super) const N_PEXT: u8 = 0x10;
pub(super) const N_TYPE: u8 = 0x0E;
pub(super) const N_EXT: u8 = 0x01;
pub(super) const N_UNDF: u8 = 0x0;
pub(super) const N_SECT: u8 = 0xE;
pub(super) const N_NO_DEAD_STRIP: u16 = 0x0020;
pub(super) const N_WEAK_REF: u16 = 0x0040;
pub(super) const N_WEAK_DEF: u16 = 0x0080;

pub(super) const ARM64_RELOC_UNSIGNED: u8 = 0;
pub(super) const ARM64_RELOC_SUBTRACTOR: u8 = 1;
pub(super) const ARM64_RELOC_BRANCH26: u8 = 2;
pub(super) const ARM64_RELOC_PAGE21: u8 = 3;
pub(super) const ARM64_RELOC_PAGEOFF12: u8 = 4;
pub(super) const ARM64_RELOC_GOT_LOAD_PAGE21: u8 = 5;
pub(super) const ARM64_RELOC_GOT_LOAD_PAGEOFF12: u8 = 6;
pub(super) const ARM64_RELOC_POINTER_TO_GOT: u8 = 7;
pub(super) const ARM64_RELOC_TLVP_LOAD_PAGE21: u8 = 8;
pub(super) const ARM64_RELOC_TLVP_LOAD_PAGEOFF12: u8 = 9;
pub(super) const ARM64_RELOC_ADDEND: u8 = 10;

/// `<mach-o/arm64/reloc.h>` spelling of an ARM64 relocation type.
pub(super) fn arm64_reloc_name(kind: u8) -> &'static str {
    match kind {
        ARM64_RELOC_UNSIGNED => "ARM64_RELOC_UNSIGNED",
        ARM64_RELOC_SUBTRACTOR => "ARM64_RELOC_SUBTRACTOR",
        ARM64_RELOC_BRANCH26 => "ARM64_RELOC_BRANCH26",
        ARM64_RELOC_PAGE21 => "ARM64_RELOC_PAGE21",
        ARM64_RELOC_PAGEOFF12 => "ARM64_RELOC_PAGEOFF12",
        ARM64_RELOC_GOT_LOAD_PAGE21 => "ARM64_RELOC_GOT_LOAD_PAGE21",
        ARM64_RELOC_GOT_LOAD_PAGEOFF12 => "ARM64_RELOC_GOT_LOAD_PAGEOFF12",
        ARM64_RELOC_POINTER_TO_GOT => "ARM64_RELOC_POINTER_TO_GOT",
        ARM64_RELOC_TLVP_LOAD_PAGE21 => "ARM64_RELOC_TLVP_LOAD_PAGE21",
        ARM64_RELOC_TLVP_LOAD_PAGEOFF12 => "ARM64_RELOC_TLVP_LOAD_PAGEOFF12",
        ARM64_RELOC_ADDEND => "ARM64_RELOC_ADDEND",
        11 => "ARM64_RELOC_AUTHENTICATED_POINTER",
        _ => "ARM64_RELOC_<unknown>",
    }
}

/// `<mach-o/fixup-chains.h>` pointer formats this replay decodes.
pub(super) const DYLD_CHAINED_PTR_64: u16 = 2;
pub(super) const DYLD_CHAINED_PTR_64_OFFSET: u16 = 6;
pub(super) const DYLD_CHAINED_PTR_START_NONE: u16 = 0xFFFF;
pub(super) const DYLD_CHAINED_PTR_START_MULTI: u16 = 0x8000;
pub(super) const DYLD_CHAINED_IMPORT: u32 = 1;
pub(super) const DYLD_CHAINED_IMPORT_ADDEND: u32 = 2;
pub(super) const DYLD_CHAINED_IMPORT_ADDEND64: u32 = 3;

/// `BIND_SPECIAL_DYLIB_WEAK_LOOKUP`: dyld's weak-definition lookup.
pub(super) const BIND_SPECIAL_DYLIB_WEAK_LOOKUP: i32 = -3;

/// Exports-trie terminal flags.
pub(super) const EXPORT_SYMBOL_FLAGS_KIND_MASK: u64 = 0x03;
pub(super) const EXPORT_SYMBOL_FLAGS_KIND_THREAD_LOCAL: u64 = 0x01;
pub(super) const EXPORT_SYMBOL_FLAGS_KIND_ABSOLUTE: u64 = 0x02;
pub(super) const EXPORT_SYMBOL_FLAGS_WEAK_DEFINITION: u64 = 0x04;
pub(super) const EXPORT_SYMBOL_FLAGS_REEXPORT: u64 = 0x08;
pub(super) const EXPORT_SYMBOL_FLAGS_STUB_AND_RESOLVER: u64 = 0x10;

/// LC_BUILD_VERSION tool identifiers.
pub(super) fn build_tool_name(tool: u32) -> &'static str {
    match tool {
        1 => "clang",
        2 => "swift",
        3 => "ld",
        4 => "lld",
        _ => "tool",
    }
}

/// `xxxx.yy.zz` nibble-encoded version (`LC_BUILD_VERSION`, dylib versions).
pub(super) fn version_string(version: u32) -> String {
    format!(
        "{}.{}.{}",
        version >> 16,
        (version >> 8) & 0xFF,
        version & 0xFF
    )
}

pub(super) fn read_u16(bytes: &[u8], at: usize) -> Option<u16> {
    let end = at.checked_add(2)?;
    Some(u16::from_le_bytes(bytes.get(at..end)?.try_into().ok()?))
}

pub(super) fn read_u32(bytes: &[u8], at: usize) -> Option<u32> {
    let end = at.checked_add(4)?;
    Some(u32::from_le_bytes(bytes.get(at..end)?.try_into().ok()?))
}

pub(super) fn read_u64(bytes: &[u8], at: usize) -> Option<u64> {
    let end = at.checked_add(8)?;
    Some(u64::from_le_bytes(bytes.get(at..end)?.try_into().ok()?))
}

/// A NUL-padded 16-byte segment or section name.
pub(super) fn fixed_name(bytes: &[u8], at: usize) -> Option<String> {
    let raw = bytes.get(at..at.checked_add(16)?)?;
    let end = raw.iter().position(|&b| b == 0).unwrap_or(raw.len());
    Some(String::from_utf8_lossy(&raw[..end]).into_owned())
}

/// A NUL-terminated string starting at `at` and ending before `limit`.
pub(super) fn c_string(bytes: &[u8], at: usize, limit: usize) -> Option<String> {
    let limit = limit.min(bytes.len());
    let raw = bytes.get(at..limit)?;
    let end = raw.iter().position(|&b| b == 0)?;
    Some(String::from_utf8_lossy(&raw[..end]).into_owned())
}

/// ULEB128 at `*at`, advancing it; `None` past `limit` or beyond 64 bits.
pub(super) fn read_uleb(bytes: &[u8], at: &mut usize, limit: usize) -> Option<u64> {
    let mut value = 0u64;
    let mut shift = 0u32;
    loop {
        if *at >= limit {
            return None;
        }
        let byte = *bytes.get(*at)?;
        *at += 1;
        let low = u64::from(byte & 0x7F);
        if shift >= 64 || (shift == 63 && low > 1) {
            return None;
        }
        value |= low << shift;
        if byte & 0x80 == 0 {
            return Some(value);
        }
        shift += 7;
    }
}

/// SLEB128 at `*at`, advancing it.
pub(super) fn read_sleb(bytes: &[u8], at: &mut usize, limit: usize) -> Option<i64> {
    let mut value = 0i64;
    let mut shift = 0u32;
    loop {
        if *at >= limit || shift >= 64 {
            return None;
        }
        let byte = *bytes.get(*at)?;
        *at += 1;
        value |= i64::from(byte & 0x7F) << shift;
        shift += 7;
        if byte & 0x80 == 0 {
            if shift < 64 && byte & 0x40 != 0 {
                value |= -1i64 << shift;
            }
            return Some(value);
        }
    }
}

/// Lowercase hexadecimal spelling of `bytes`.
pub(super) fn hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push_str(&format!("{byte:02x}"));
    }
    out
}
