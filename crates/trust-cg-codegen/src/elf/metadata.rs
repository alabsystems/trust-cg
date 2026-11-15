// trust-cg-codegen/elf/metadata.rs - ELF metadata sections and headers
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: System V ABI, ELF-64 Object File Format (section groups, program headers)
// Reference: GNU Binutils (note.GNU-stack convention)

//! ELF metadata support.
//!
//! DWARF debug sections are not produced here: [`super::dwarf`] attaches the
//! full DWARF 4 image from [`crate::dwarf_info`].
//!
//! This module provides:
//! - **`.note.GNU-stack`**: Marks the object as not requiring an executable stack.
//! - **Section groups**: ELF COMDAT `.group` sections for deduplication.
//! - **Program header stubs**: `PT_LOAD` segment structures for future linking support.
//!
//! All helpers are self-contained and depend only on [`super::constants`].

#[allow(unused_imports)]
use super::constants::*;

// ---------------------------------------------------------------------------
// Additional ELF constants (not in constants.rs)
// ---------------------------------------------------------------------------

/// ELF section type for section groups.
pub const SHT_GROUP: u32 = 17;

/// ELF section type for notes.
pub const SHT_NOTE: u32 = 7;

/// Section flag: member of a section group.
pub const SHF_GROUP: u64 = 0x200;

/// COMDAT section group flag (first word of `.group` data).
pub const GRP_COMDAT: u32 = 1;

/// Loadable segment type.
pub const PT_LOAD: u32 = 1;

/// Unused program header entry type.
pub const PT_NULL: u32 = 0;

/// Segment permission: readable.
pub const PF_R: u32 = 4;

/// Segment permission: writable.
pub const PF_W: u32 = 2;

/// Segment permission: executable.
pub const PF_X: u32 = 1;

/// Size of an ELF64 program header entry in bytes.
pub const ELF64_PHDR_SIZE: usize = 56;

// ---------------------------------------------------------------------------
// Internal serialization helpers
// ---------------------------------------------------------------------------

fn push_u32(buf: &mut Vec<u8>, value: u32) {
    buf.extend_from_slice(&value.to_le_bytes());
}

fn push_u64(buf: &mut Vec<u8>, value: u64) {
    buf.extend_from_slice(&value.to_le_bytes());
}

// ---------------------------------------------------------------------------
// NoteGnuStack
// ---------------------------------------------------------------------------

/// `.note.GNU-stack` section marker.
///
/// An empty section of type `SHT_PROGBITS` with no `SHF_EXECINSTR` flag.
/// Its presence tells the linker that this object does not require an
/// executable stack. Without it, the GNU linker may assume the worst and
/// mark the stack executable.
///
/// Despite the ".note" prefix in the name, the conventional section type
/// is `SHT_PROGBITS` (not `SHT_NOTE`).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct NoteGnuStack;

impl NoteGnuStack {
    /// Section name.
    pub const NAME: &'static str = ".note.GNU-stack";
    /// Standard alignment for this section.
    pub const ALIGN: u64 = 1;

    /// Create a new `.note.GNU-stack` marker.
    pub fn new() -> Self {
        Self
    }

    /// ELF section type for this section.
    pub fn section_type(&self) -> u32 {
        SHT_PROGBITS
    }

    /// ELF section flags (no SHF_EXECINSTR = non-executable stack).
    pub fn section_flags(&self) -> u64 {
        0
    }

    /// Section alignment.
    pub fn section_align(&self) -> u64 {
        Self::ALIGN
    }

    /// Generate section contents (empty for this marker section).
    pub fn section_bytes(&self) -> Vec<u8> {
        Vec::new()
    }
}

// ---------------------------------------------------------------------------
// SectionGroup
// ---------------------------------------------------------------------------

/// ELF COMDAT section group (`.group` section).
///
/// A section group allows the linker to discard duplicate copies of a set of
/// sections across translation units. The section data is a sequence of
/// little-endian `u32` values: the group flag word (`GRP_COMDAT`) followed
/// by the section header indices of member sections.
///
/// The `.group` section header uses:
/// - `sh_type = SHT_GROUP`
/// - `sh_link = <.symtab section index>`
/// - `sh_info = <signature symbol index>`
/// - `sh_flags = 0` (the group section itself does NOT have SHF_GROUP;
///    member sections carry that flag)
/// - `sh_entsize = 4` (each entry is a u32)
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SectionGroup {
    /// Section header index of the associated symbol table (.symtab).
    pub symtab_section_index: u32,
    /// Symbol table index of the group signature symbol.
    pub signature_symbol_index: u32,
    /// Section header indices of the member sections.
    pub member_indices: Vec<u32>,
}

impl SectionGroup {
    /// Section name.
    pub const NAME: &'static str = ".group";
    /// Alignment for the group section.
    pub const ALIGN: u64 = 4;
    /// Entry size (each member index is a u32).
    pub const ENTRY_SIZE: u64 = 4;

    /// Create a new COMDAT section group.
    pub fn new(
        symtab_section_index: u32,
        signature_symbol_index: u32,
        member_indices: Vec<u32>,
    ) -> Self {
        Self {
            symtab_section_index,
            signature_symbol_index,
            member_indices,
        }
    }

    /// ELF section type for this section.
    pub fn section_type(&self) -> u32 {
        SHT_GROUP
    }

    /// ELF section flags.
    ///
    /// The `.group` section itself has flags = 0. Member sections carry
    /// `SHF_GROUP`.
    pub fn section_flags(&self) -> u64 {
        0
    }

    /// Section alignment.
    pub fn section_align(&self) -> u64 {
        Self::ALIGN
    }

    /// Group flag word (first u32 in the section data).
    pub fn group_flag(&self) -> u32 {
        GRP_COMDAT
    }

    /// Generate section contents: flag word followed by member section indices.
    pub fn section_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity((1 + self.member_indices.len()) * 4);
        push_u32(&mut bytes, self.group_flag());
        for &idx in &self.member_indices {
            push_u32(&mut bytes, idx);
        }
        bytes
    }
}

// ---------------------------------------------------------------------------
// ProgramHeaderStub
// ---------------------------------------------------------------------------

/// Minimal ELF64 program header entry for future linking support.
///
/// Program headers describe segments for the runtime loader. While
/// relocatable object files (.o) typically have no program headers,
/// this stub supports generating them for when Trust Codegen produces
/// executable or shared library output.
///
/// Layout (Elf64_Phdr, 56 bytes):
/// ```text
/// Offset  Size  Field
/// 0        4    p_type
/// 4        4    p_flags
/// 8        8    p_offset
/// 16       8    p_vaddr
/// 24       8    p_paddr
/// 32       8    p_filesz
/// 40       8    p_memsz
/// 48       8    p_align
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProgramHeaderStub {
    /// Segment type (PT_LOAD, PT_NULL, etc.).
    pub p_type: u32,
    /// Segment permission flags (PF_R | PF_W | PF_X).
    pub p_flags: u32,
    /// File offset of the segment.
    pub p_offset: u64,
    /// Virtual address of the segment.
    pub p_vaddr: u64,
    /// Physical address of the segment.
    pub p_paddr: u64,
    /// Size of the segment in the file.
    pub p_filesz: u64,
    /// Size of the segment in memory.
    pub p_memsz: u64,
    /// Alignment (must be power of 2; 0 or 1 means no alignment).
    pub p_align: u64,
}

impl ProgramHeaderStub {
    /// Create a minimal read-only `PT_LOAD` program header.
    pub fn load() -> Self {
        Self {
            p_type: PT_LOAD,
            p_flags: PF_R,
            p_offset: 0,
            p_vaddr: 0,
            p_paddr: 0,
            p_filesz: 0,
            p_memsz: 0,
            p_align: 0,
        }
    }

    /// Create a null program header entry (PT_NULL, all zeros).
    pub fn null() -> Self {
        Self {
            p_type: PT_NULL,
            p_flags: 0,
            p_offset: 0,
            p_vaddr: 0,
            p_paddr: 0,
            p_filesz: 0,
            p_memsz: 0,
            p_align: 0,
        }
    }

    /// Size of the serialized program header entry in bytes.
    pub fn size() -> usize {
        ELF64_PHDR_SIZE
    }

    /// Serialize the program header to little-endian bytes (56 bytes).
    pub fn write(&self, buf: &mut Vec<u8>) {
        push_u32(buf, self.p_type);
        push_u32(buf, self.p_flags);
        push_u64(buf, self.p_offset);
        push_u64(buf, self.p_vaddr);
        push_u64(buf, self.p_paddr);
        push_u64(buf, self.p_filesz);
        push_u64(buf, self.p_memsz);
        push_u64(buf, self.p_align);
    }

    /// Serialize to a standalone byte vector.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(ELF64_PHDR_SIZE);
        self.write(&mut buf);
        buf
    }
}

impl Default for ProgramHeaderStub {
    fn default() -> Self {
        Self::load()
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn read_u32_le(bytes: &[u8], offset: usize) -> u32 {
        u32::from_le_bytes([
            bytes[offset],
            bytes[offset + 1],
            bytes[offset + 2],
            bytes[offset + 3],
        ])
    }

    fn read_u64_le(bytes: &[u8], offset: usize) -> u64 {
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

    // --- Constants ---

    #[test]
    fn test_elf_constants_values() {
        assert_eq!(SHT_GROUP, 17);
        assert_eq!(SHT_NOTE, 7);
        assert_eq!(SHF_GROUP, 0x200);
        assert_eq!(GRP_COMDAT, 1);
        assert_eq!(PT_LOAD, 1);
        assert_eq!(PT_NULL, 0);
        assert_eq!(PF_R, 4);
        assert_eq!(PF_W, 2);
        assert_eq!(PF_X, 1);
        assert_eq!(ELF64_PHDR_SIZE, 56);
    }

    // --- NoteGnuStack ---

    #[test]
    fn test_note_gnu_stack_metadata() {
        let note = NoteGnuStack::new();
        assert_eq!(NoteGnuStack::NAME, ".note.GNU-stack");
        assert_eq!(note.section_type(), SHT_PROGBITS);
        assert_eq!(note.section_flags(), 0);
        assert_eq!(
            note.section_flags() & SHF_EXECINSTR,
            0,
            "must not be executable"
        );
        assert_eq!(note.section_align(), 1);
        assert!(
            note.section_bytes().is_empty(),
            "marker section has no data"
        );
    }

    #[test]
    fn test_note_gnu_stack_default() {
        let note = NoteGnuStack;
        assert_eq!(note, NoteGnuStack::new());
    }

    // --- SectionGroup ---

    #[test]
    fn test_section_group_encoding() {
        let group = SectionGroup::new(6, 2, vec![1, 3, 7]);
        let bytes = group.section_bytes();

        assert_eq!(SectionGroup::NAME, ".group");
        assert_eq!(group.section_type(), SHT_GROUP);
        // Group section itself has flags=0 (members have SHF_GROUP)
        assert_eq!(group.section_flags(), 0);
        assert_eq!(group.section_align(), 4);
        assert_eq!(group.group_flag(), GRP_COMDAT);

        // 4 bytes flag + 3 * 4 bytes members = 16 bytes
        assert_eq!(bytes.len(), 16);
        assert_eq!(read_u32_le(&bytes, 0), GRP_COMDAT);
        assert_eq!(read_u32_le(&bytes, 4), 1);
        assert_eq!(read_u32_le(&bytes, 8), 3);
        assert_eq!(read_u32_le(&bytes, 12), 7);
    }

    #[test]
    fn test_section_group_empty() {
        let group = SectionGroup::new(4, 1, Vec::new());
        let bytes = group.section_bytes();
        // Still has the flag word
        assert_eq!(bytes.len(), 4);
        assert_eq!(read_u32_le(&bytes, 0), GRP_COMDAT);
    }

    #[test]
    fn test_section_group_fields() {
        let group = SectionGroup::new(5, 3, vec![2, 4]);
        assert_eq!(group.symtab_section_index, 5);
        assert_eq!(group.signature_symbol_index, 3);
        assert_eq!(group.member_indices, vec![2, 4]);
    }

    #[test]
    fn test_section_group_entry_size() {
        assert_eq!(SectionGroup::ENTRY_SIZE, 4);
    }

    // --- ProgramHeaderStub ---

    #[test]
    fn test_program_header_load_encoding() {
        let phdr = ProgramHeaderStub::load();
        let bytes = phdr.to_bytes();

        assert_eq!(ProgramHeaderStub::size(), ELF64_PHDR_SIZE);
        assert_eq!(bytes.len(), ELF64_PHDR_SIZE);
        assert_eq!(read_u32_le(&bytes, 0), PT_LOAD);
        assert_eq!(read_u32_le(&bytes, 4), PF_R);
        assert_eq!(read_u64_le(&bytes, 8), 0); // p_offset
        assert_eq!(read_u64_le(&bytes, 16), 0); // p_vaddr
        assert_eq!(read_u64_le(&bytes, 24), 0); // p_paddr
        assert_eq!(read_u64_le(&bytes, 32), 0); // p_filesz
        assert_eq!(read_u64_le(&bytes, 40), 0); // p_memsz
        assert_eq!(read_u64_le(&bytes, 48), 0); // p_align
    }

    #[test]
    fn test_program_header_null() {
        let phdr = ProgramHeaderStub::null();
        let bytes = phdr.to_bytes();
        assert_eq!(bytes.len(), ELF64_PHDR_SIZE);
        assert_eq!(read_u32_le(&bytes, 0), PT_NULL);
        // All remaining fields should be zero
        assert!(
            bytes[4..].iter().all(|&b| b == 0),
            "null phdr should be zeros after type"
        );
    }

    #[test]
    fn test_program_header_custom() {
        let phdr = ProgramHeaderStub {
            p_type: PT_LOAD,
            p_flags: PF_R | PF_X,
            p_offset: 0x40,
            p_vaddr: 0x400000,
            p_paddr: 0x400000,
            p_filesz: 0x120,
            p_memsz: 0x180,
            p_align: 0x1000,
        };
        let bytes = phdr.to_bytes();

        assert_eq!(read_u32_le(&bytes, 0), PT_LOAD);
        assert_eq!(read_u32_le(&bytes, 4), PF_R | PF_X);
        assert_eq!(read_u64_le(&bytes, 8), 0x40);
        assert_eq!(read_u64_le(&bytes, 16), 0x400000);
        assert_eq!(read_u64_le(&bytes, 24), 0x400000);
        assert_eq!(read_u64_le(&bytes, 32), 0x120);
        assert_eq!(read_u64_le(&bytes, 40), 0x180);
        assert_eq!(read_u64_le(&bytes, 48), 0x1000);
    }

    #[test]
    fn test_program_header_default_is_load() {
        let phdr = ProgramHeaderStub::default();
        assert_eq!(phdr, ProgramHeaderStub::load());
    }

    #[test]
    fn test_program_header_write_method() {
        let phdr = ProgramHeaderStub::load();
        let mut buf = Vec::new();
        phdr.write(&mut buf);
        assert_eq!(buf, phdr.to_bytes());
    }

    #[test]
    fn test_rwx_flag_combinations() {
        assert_eq!(PF_R | PF_W | PF_X, 7);
        assert_eq!(PF_R | PF_W, 6);
        assert_eq!(PF_R | PF_X, 5);
    }
}
