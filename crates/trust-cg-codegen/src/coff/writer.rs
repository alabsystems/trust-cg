// trust-cg-codegen/coff/writer.rs - COFF object file writer
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Assembles a minimal x86-64 COFF relocatable object file.

pub const IMAGE_FILE_MACHINE_AMD64: u16 = 0x8664;

pub const IMAGE_SCN_CNT_CODE: u32 = 0x0000_0020;
pub const IMAGE_SCN_CNT_INITIALIZED_DATA: u32 = 0x0000_0040;
pub const IMAGE_SCN_ALIGN_4BYTES: u32 = 0x0030_0000;
pub const IMAGE_SCN_ALIGN_8BYTES: u32 = 0x0040_0000;
pub const IMAGE_SCN_ALIGN_16BYTES: u32 = 0x0050_0000;
/// PE/COFF encodes section alignment as `(log2(bytes) + 1) << 20`, so 32 bytes
/// is `6 << 20`. Needed by the x86 JCC-erratum padding, which is only sound if
/// the linker honours the 32-byte grid the padding was computed against.
pub const IMAGE_SCN_ALIGN_32BYTES: u32 = 0x0060_0000;
pub const IMAGE_SCN_MEM_EXECUTE: u32 = 0x2000_0000;
pub const IMAGE_SCN_MEM_READ: u32 = 0x4000_0000;

/// Section is a COMDAT (linker-dedupable / selectable) section.
pub const IMAGE_SCN_LNK_COMDAT: u32 = 0x0000_1000;

pub const IMAGE_SYM_TYPE_NULL: u16 = 0x0000;
pub const IMAGE_SYM_DTYPE_FUNCTION: u16 = 0x0020;
pub const IMAGE_SYM_CLASS_EXTERNAL: u8 = 2;
pub const IMAGE_SYM_CLASS_STATIC: u8 = 3;

/// The reference's 64-bit virtual address (absolute).
pub const IMAGE_REL_AMD64_ADDR64: u16 = 0x0001;
/// The reference's 32-bit virtual address (absolute).
pub const IMAGE_REL_AMD64_ADDR32: u16 = 0x0002;
/// The reference's 32-bit address without an image base (RVA).
pub const IMAGE_REL_AMD64_ADDR32NB: u16 = 0x0003;
/// The 32-bit relative address from the byte following the relocation.
pub const IMAGE_REL_AMD64_REL32: u16 = 0x0004;
/// The 16-bit section index of the section containing the target.
pub const IMAGE_REL_AMD64_SECTION: u16 = 0x000A;
/// The 32-bit offset of the target from the beginning of its section.
pub const IMAGE_REL_AMD64_SECREL: u16 = 0x000B;
/// A 7-bit unsigned offset from the base of the section containing the target.
pub const IMAGE_REL_AMD64_SECREL7: u16 = 0x000C;
/// CLR token.
pub const IMAGE_REL_AMD64_TOKEN: u16 = 0x000E;

const COFF_FILE_HEADER_SIZE: usize = 20;
const COFF_SECTION_HEADER_SIZE: usize = 40;
const COFF_SYMBOL_SIZE: usize = 18;
const COFF_RELOCATION_SIZE: usize = 10;
const COFF_SHORT_NAME_MAX_LEN: usize = 8;

pub type CoffResult<T> = Result<T, CoffError>;

/// Recoverable COFF writer limit errors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CoffError {
    /// The object has more sections than the 16-bit COFF file header can encode.
    SectionCountOverflow { count: usize, max: usize },
    /// The object has more symbols than the 32-bit COFF file header can encode.
    SymbolCountOverflow { count: usize, max: usize },
    /// Section string-table names are not supported by this writer slice.
    LongSectionName { name: String, max_len: usize },
    /// A section has more relocations than the 16-bit section header can encode.
    RelocationCountOverflow {
        section_name: String,
        count: usize,
        max: usize,
    },
}

impl core::fmt::Display for CoffError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::SectionCountOverflow { count, max } => {
                write!(f, "COFF section count {count} exceeds maximum {max}")
            }
            Self::SymbolCountOverflow { count, max } => {
                write!(f, "COFF symbol count {count} exceeds maximum {max}")
            }
            Self::LongSectionName { name, max_len } => write!(
                f,
                "COFF section name `{name}` is longer than the supported {max_len} byte limit"
            ),
            Self::RelocationCountOverflow {
                section_name,
                count,
                max,
            } => write!(
                f,
                "COFF section `{section_name}` relocation count {count} exceeds maximum {max}"
            ),
        }
    }
}

impl std::error::Error for CoffError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoffRelocation {
    pub virtual_address: u32,
    pub symbol_table_index: u32,
    pub typ: u16,
}

impl CoffRelocation {
    /// Construct a relocation with an explicit AMD64 relocation type.
    pub fn new(virtual_address: u32, symbol_table_index: u32, typ: u16) -> Self {
        Self {
            virtual_address,
            symbol_table_index,
            typ,
        }
    }

    /// `IMAGE_REL_AMD64_ADDR64` — 64-bit absolute virtual address.
    pub fn amd64_addr64(virtual_address: u32, symbol_table_index: u32) -> Self {
        Self::new(virtual_address, symbol_table_index, IMAGE_REL_AMD64_ADDR64)
    }

    /// `IMAGE_REL_AMD64_ADDR32` — 32-bit absolute virtual address.
    pub fn amd64_addr32(virtual_address: u32, symbol_table_index: u32) -> Self {
        Self::new(virtual_address, symbol_table_index, IMAGE_REL_AMD64_ADDR32)
    }

    pub fn amd64_addr32nb(virtual_address: u32, symbol_table_index: u32) -> Self {
        Self {
            virtual_address,
            symbol_table_index,
            typ: IMAGE_REL_AMD64_ADDR32NB,
        }
    }

    pub fn amd64_rel32(virtual_address: u32, symbol_table_index: u32) -> Self {
        Self {
            virtual_address,
            symbol_table_index,
            typ: IMAGE_REL_AMD64_REL32,
        }
    }

    /// `IMAGE_REL_AMD64_SECTION` — 16-bit section index of the target.
    pub fn amd64_section(virtual_address: u32, symbol_table_index: u32) -> Self {
        Self::new(virtual_address, symbol_table_index, IMAGE_REL_AMD64_SECTION)
    }

    /// `IMAGE_REL_AMD64_SECREL` — 32-bit offset from the start of the section.
    pub fn amd64_secrel(virtual_address: u32, symbol_table_index: u32) -> Self {
        Self::new(virtual_address, symbol_table_index, IMAGE_REL_AMD64_SECREL)
    }

    /// `IMAGE_REL_AMD64_SECREL7` — 7-bit offset from the start of the section.
    pub fn amd64_secrel7(virtual_address: u32, symbol_table_index: u32) -> Self {
        Self::new(virtual_address, symbol_table_index, IMAGE_REL_AMD64_SECREL7)
    }

    /// `IMAGE_REL_AMD64_TOKEN` — CLR token.
    pub fn amd64_token(virtual_address: u32, symbol_table_index: u32) -> Self {
        Self::new(virtual_address, symbol_table_index, IMAGE_REL_AMD64_TOKEN)
    }
}

/// COMDAT section-selection kinds (`IMAGE_COMDAT_SELECT_*`).
///
/// Stored in the `Selection` field of the COMDAT-defining symbol's auxiliary
/// record. Recorded here as a capability stub so later linking work can mark a
/// section as dedupable and emit the appropriate auxiliary record.
pub const IMAGE_COMDAT_SELECT_NODUPLICATES: u8 = 1;
pub const IMAGE_COMDAT_SELECT_ANY: u8 = 2;
pub const IMAGE_COMDAT_SELECT_SAME_SIZE: u8 = 3;
pub const IMAGE_COMDAT_SELECT_EXACT_MATCH: u8 = 4;
pub const IMAGE_COMDAT_SELECT_ASSOCIATIVE: u8 = 5;
pub const IMAGE_COMDAT_SELECT_LARGEST: u8 = 6;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoffSection {
    pub name: String,
    pub data: Vec<u8>,
    pub characteristics: u32,
    pub relocations: Vec<CoffRelocation>,
    /// COMDAT selection kind (`IMAGE_COMDAT_SELECT_*`) when this section is a
    /// linker-dedupable COMDAT group, or `None` for a normal section.
    ///
    /// This is a capability stub: the writer records the intent and sets the
    /// `IMAGE_SCN_LNK_COMDAT` characteristic so later linking work can emit the
    /// matching COMDAT auxiliary symbol record.
    pub comdat_selection: Option<u8>,
}

impl CoffSection {
    /// Mark this section as a COMDAT group with the given selection kind.
    ///
    /// Sets the `IMAGE_SCN_LNK_COMDAT` characteristic and records the selection
    /// so a later linking pass can emit the COMDAT auxiliary record.
    pub fn mark_comdat(&mut self, selection: u8) {
        self.comdat_selection = Some(selection);
        self.characteristics |= IMAGE_SCN_LNK_COMDAT;
    }

    /// Returns `true` if this section is flagged as a COMDAT group.
    pub fn is_comdat(&self) -> bool {
        self.comdat_selection.is_some()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoffSymbol {
    pub name: String,
    pub value: u32,
    pub section_number: i16,
    pub typ: u16,
    pub storage_class: u8,
}

#[derive(Debug, Clone)]
pub struct CoffWriter {
    machine: u16,
    sections: Vec<CoffSection>,
    symbols: Vec<CoffSymbol>,
}

impl CoffWriter {
    pub fn new_x86_64() -> Self {
        Self {
            machine: IMAGE_FILE_MACHINE_AMD64,
            sections: Vec::new(),
            symbols: Vec::new(),
        }
    }

    pub fn add_text_section(&mut self, code: &[u8]) -> u16 {
        self.add_text_section_with_align(code, 4)
    }

    /// Like [`add_text_section`](Self::add_text_section) with an explicit
    /// alignment exponent (log2 bytes), matching the Mach-O writer's spelling.
    ///
    /// ⚑ The exponent, NOT a byte count — the ELF writer's equivalent takes
    /// BYTES, and mixing the two silently requests 2^16 or 4-byte alignment.
    /// Used when the emitted code carries function-relative alignment padding:
    /// the section must be at least as aligned as the grid that padding assumed,
    /// or the linker places it so every padded boundary lands off-by-16 in the
    /// final image.
    pub fn add_text_section_with_align(&mut self, code: &[u8], align_log2: u32) -> u16 {
        let align_bits = match align_log2 {
            2 => IMAGE_SCN_ALIGN_4BYTES,
            3 => IMAGE_SCN_ALIGN_8BYTES,
            4 => IMAGE_SCN_ALIGN_16BYTES,
            5 => IMAGE_SCN_ALIGN_32BYTES,
            // PE encodes alignment as (log2 + 1) << 20 and tops out at 8192.
            // Anything outside the range this writer has constants for is a
            // caller bug; fall back to the 16-byte convention rather than
            // encoding a wrong exponent.
            _ => IMAGE_SCN_ALIGN_16BYTES,
        };
        self.add_section(
            ".text",
            code,
            IMAGE_SCN_CNT_CODE | align_bits | IMAGE_SCN_MEM_EXECUTE | IMAGE_SCN_MEM_READ,
        )
    }

    pub fn add_readonly_data_section(&mut self, data: &[u8]) -> u16 {
        self.add_section(
            ".rdata",
            data,
            IMAGE_SCN_CNT_INITIALIZED_DATA | IMAGE_SCN_ALIGN_8BYTES | IMAGE_SCN_MEM_READ,
        )
    }

    pub fn add_exception_data_section(&mut self, data: &[u8]) -> u16 {
        self.add_section(
            ".pdata",
            data,
            IMAGE_SCN_CNT_INITIALIZED_DATA | IMAGE_SCN_ALIGN_4BYTES | IMAGE_SCN_MEM_READ,
        )
    }

    pub fn add_unwind_data_section(&mut self, data: &[u8]) -> u16 {
        self.add_section(
            ".xdata",
            data,
            IMAGE_SCN_CNT_INITIALIZED_DATA | IMAGE_SCN_ALIGN_4BYTES | IMAGE_SCN_MEM_READ,
        )
    }

    pub fn add_section(&mut self, name: &str, data: &[u8], characteristics: u32) -> u16 {
        self.sections.push(CoffSection {
            name: name.to_string(),
            data: data.to_vec(),
            characteristics,
            relocations: Vec::new(),
            comdat_selection: None,
        });
        self.sections.len() as u16
    }

    /// Mark a section (1-based section number, as returned by `add_section`) as a
    /// COMDAT group with the given `IMAGE_COMDAT_SELECT_*` selection kind.
    ///
    /// Returns `true` if the section number was valid. This records intent and
    /// sets `IMAGE_SCN_LNK_COMDAT`; emitting the COMDAT auxiliary symbol record
    /// is deferred to later linking work.
    pub fn mark_section_comdat(&mut self, section_number: u16, selection: u8) -> bool {
        if section_number == 0 {
            return false;
        }
        if let Some(section) = self.sections.get_mut((section_number - 1) as usize) {
            section.mark_comdat(selection);
            true
        } else {
            false
        }
    }

    pub fn add_function_symbol(&mut self, name: &str, section_number: u16, value: u32) -> u32 {
        self.add_symbol(
            name,
            section_number as i16,
            value,
            IMAGE_SYM_DTYPE_FUNCTION,
            IMAGE_SYM_CLASS_EXTERNAL,
        )
    }

    pub fn add_static_section_symbol(&mut self, name: &str, section_number: u16) -> u32 {
        self.add_symbol(
            name,
            section_number as i16,
            0,
            IMAGE_SYM_TYPE_NULL,
            IMAGE_SYM_CLASS_STATIC,
        )
    }

    pub fn add_symbol(
        &mut self,
        name: &str,
        section_number: i16,
        value: u32,
        typ: u16,
        storage_class: u8,
    ) -> u32 {
        let index = self.symbols.len() as u32;
        self.symbols.push(CoffSymbol {
            name: name.to_string(),
            value,
            section_number,
            typ,
            storage_class,
        });
        index
    }

    pub fn add_relocation(&mut self, section_idx: usize, relocation: CoffRelocation) {
        assert!(
            section_idx < self.sections.len(),
            "COFF relocation section index {section_idx} out of range for {} section(s)",
            self.sections.len()
        );
        self.sections[section_idx].relocations.push(relocation);
    }

    pub fn write(&self) -> CoffResult<Vec<u8>> {
        let section_count = self.sections.len();
        if section_count > u16::MAX as usize {
            return Err(CoffError::SectionCountOverflow {
                count: section_count,
                max: u16::MAX as usize,
            });
        }
        if self.symbols.len() > u32::MAX as usize {
            return Err(CoffError::SymbolCountOverflow {
                count: self.symbols.len(),
                max: u32::MAX as usize,
            });
        }
        for section in &self.sections {
            if section.name.len() > COFF_SHORT_NAME_MAX_LEN {
                return Err(CoffError::LongSectionName {
                    name: section.name.clone(),
                    max_len: COFF_SHORT_NAME_MAX_LEN,
                });
            }
            if section.relocations.len() > u16::MAX as usize {
                return Err(CoffError::RelocationCountOverflow {
                    section_name: section.name.clone(),
                    count: section.relocations.len(),
                    max: u16::MAX as usize,
                });
            }
        }

        let mut string_table = vec![0u8; 4];
        let section_names: Vec<[u8; 8]> = self
            .sections
            .iter()
            .map(|section| encode_coff_name(&section.name, &mut string_table))
            .collect();
        let symbol_names: Vec<[u8; 8]> = self
            .symbols
            .iter()
            .map(|symbol| encode_coff_name(&symbol.name, &mut string_table))
            .collect();
        let string_table_len = string_table.len() as u32;
        string_table[0..4].copy_from_slice(&string_table_len.to_le_bytes());

        let mut cursor = COFF_FILE_HEADER_SIZE + section_count * COFF_SECTION_HEADER_SIZE;
        cursor = align_to(cursor, 4);

        let mut section_layouts = Vec::with_capacity(section_count);
        for section in &self.sections {
            cursor = align_to(cursor, 4);
            let raw_data_ptr = if section.data.is_empty() {
                0
            } else {
                let ptr = cursor as u32;
                cursor += section.data.len();
                ptr
            };
            section_layouts.push((raw_data_ptr, 0u32));
        }

        for (idx, section) in self.sections.iter().enumerate() {
            cursor = align_to(cursor, 4);
            if !section.relocations.is_empty() {
                section_layouts[idx].1 = cursor as u32;
                cursor += section.relocations.len() * COFF_RELOCATION_SIZE;
            }
        }

        cursor = align_to(cursor, 4);
        let symbol_table_ptr = cursor as u32;
        cursor += self.symbols.len() * COFF_SYMBOL_SIZE;

        let mut buf = Vec::with_capacity(cursor + string_table.len());
        write_u16(&mut buf, self.machine);
        write_u16(&mut buf, section_count as u16);
        write_u32(&mut buf, 0);
        write_u32(&mut buf, symbol_table_ptr);
        write_u32(&mut buf, self.symbols.len() as u32);
        write_u16(&mut buf, 0);
        write_u16(&mut buf, 0);

        for (idx, section) in self.sections.iter().enumerate() {
            let (raw_data_ptr, relocation_ptr) = section_layouts[idx];
            buf.extend_from_slice(&section_names[idx]);
            write_u32(&mut buf, 0);
            write_u32(&mut buf, 0);
            write_u32(&mut buf, section.data.len() as u32);
            write_u32(&mut buf, raw_data_ptr);
            write_u32(&mut buf, relocation_ptr);
            write_u32(&mut buf, 0);
            write_u16(&mut buf, section.relocations.len() as u16);
            write_u16(&mut buf, 0);
            write_u32(&mut buf, section.characteristics);
        }

        pad_to(
            &mut buf,
            COFF_FILE_HEADER_SIZE + section_count * COFF_SECTION_HEADER_SIZE,
        );
        let aligned_after_headers = align_to(buf.len(), 4);
        pad_to(&mut buf, aligned_after_headers);

        for (idx, section) in self.sections.iter().enumerate() {
            let (raw_data_ptr, _) = section_layouts[idx];
            if raw_data_ptr != 0 {
                pad_to(&mut buf, raw_data_ptr as usize);
                buf.extend_from_slice(&section.data);
            }
        }

        for (idx, section) in self.sections.iter().enumerate() {
            let (_, relocation_ptr) = section_layouts[idx];
            if relocation_ptr != 0 {
                pad_to(&mut buf, relocation_ptr as usize);
                for relocation in &section.relocations {
                    write_u32(&mut buf, relocation.virtual_address);
                    write_u32(&mut buf, relocation.symbol_table_index);
                    write_u16(&mut buf, relocation.typ);
                }
            }
        }

        pad_to(&mut buf, symbol_table_ptr as usize);
        for (idx, symbol) in self.symbols.iter().enumerate() {
            buf.extend_from_slice(&symbol_names[idx]);
            write_u32(&mut buf, symbol.value);
            write_i16(&mut buf, symbol.section_number);
            write_u16(&mut buf, symbol.typ);
            buf.push(symbol.storage_class);
            buf.push(0);
        }

        buf.extend_from_slice(&string_table);
        Ok(buf)
    }
}

impl Default for CoffWriter {
    fn default() -> Self {
        Self::new_x86_64()
    }
}

fn encode_coff_name(name: &str, string_table: &mut Vec<u8>) -> [u8; 8] {
    let bytes = name.as_bytes();
    let mut encoded = [0u8; 8];
    if bytes.len() <= 8 {
        encoded[..bytes.len()].copy_from_slice(bytes);
        return encoded;
    }

    let offset = string_table.len() as u32;
    string_table.extend_from_slice(bytes);
    string_table.push(0);
    encoded[4..8].copy_from_slice(&offset.to_le_bytes());
    encoded
}

fn align_to(value: usize, alignment: usize) -> usize {
    debug_assert!(alignment.is_power_of_two());
    (value + alignment - 1) & !(alignment - 1)
}

fn pad_to(buf: &mut Vec<u8>, len: usize) {
    if buf.len() < len {
        buf.resize(len, 0);
    }
}

fn write_u16(buf: &mut Vec<u8>, value: u16) {
    buf.extend_from_slice(&value.to_le_bytes());
}

fn write_i16(buf: &mut Vec<u8>, value: i16) {
    buf.extend_from_slice(&value.to_le_bytes());
}

fn write_u32(buf: &mut Vec<u8>, value: u32) {
    buf.extend_from_slice(&value.to_le_bytes());
}

#[cfg(test)]
mod tests {
    use super::*;

    fn read_u16(bytes: &[u8], offset: usize) -> u16 {
        u16::from_le_bytes([bytes[offset], bytes[offset + 1]])
    }

    fn read_i16(bytes: &[u8], offset: usize) -> i16 {
        i16::from_le_bytes([bytes[offset], bytes[offset + 1]])
    }

    fn read_u32(bytes: &[u8], offset: usize) -> u32 {
        u32::from_le_bytes([
            bytes[offset],
            bytes[offset + 1],
            bytes[offset + 2],
            bytes[offset + 3],
        ])
    }

    #[test]
    fn empty_x86_64_coff_object_has_file_header_and_string_table() {
        let bytes = CoffWriter::new_x86_64().write().unwrap();

        assert_eq!(read_u16(&bytes, 0), IMAGE_FILE_MACHINE_AMD64);
        assert_eq!(read_u16(&bytes, 2), 0);
        assert_eq!(read_u32(&bytes, 8), COFF_FILE_HEADER_SIZE as u32);
        assert_eq!(read_u32(&bytes, 12), 0);
        assert_eq!(read_u32(&bytes, COFF_FILE_HEADER_SIZE), 4);
    }

    #[test]
    fn text_function_symbol_object_is_parseable() {
        let mut writer = CoffWriter::new_x86_64();
        let text = writer.add_text_section(&[0xC3]);
        writer.add_function_symbol("add", text, 0);

        let bytes = writer.write().unwrap();
        assert_eq!(read_u16(&bytes, 0), IMAGE_FILE_MACHINE_AMD64);
        assert_eq!(read_u16(&bytes, 2), 1);
        assert_eq!(read_u32(&bytes, 12), 1);

        let section = COFF_FILE_HEADER_SIZE;
        assert_eq!(&bytes[section..section + 5], b".text");
        assert_eq!(
            read_u32(&bytes, section + 36),
            IMAGE_SCN_CNT_CODE
                | IMAGE_SCN_ALIGN_16BYTES
                | IMAGE_SCN_MEM_EXECUTE
                | IMAGE_SCN_MEM_READ
        );
        let raw_ptr = read_u32(&bytes, section + 20) as usize;
        assert_eq!(bytes[raw_ptr], 0xC3);

        let symtab = read_u32(&bytes, 8) as usize;
        assert_eq!(&bytes[symtab..symtab + 3], b"add");
        assert_eq!(read_u32(&bytes, symtab + 8), 0);
        assert_eq!(read_i16(&bytes, symtab + 12), 1);
        assert_eq!(read_u16(&bytes, symtab + 14), IMAGE_SYM_DTYPE_FUNCTION);
        assert_eq!(bytes[symtab + 16], IMAGE_SYM_CLASS_EXTERNAL);
    }

    #[test]
    fn long_symbol_names_use_coff_string_table() {
        let mut writer = CoffWriter::new_x86_64();
        let text = writer.add_text_section(&[0xC3]);
        writer.add_function_symbol("very_long_function_name", text, 0);

        let bytes = writer.write().unwrap();
        let symtab = read_u32(&bytes, 8) as usize;
        assert_eq!(read_u32(&bytes, symtab), 0);
        let name_offset = read_u32(&bytes, symtab + 4) as usize;

        let strtab = symtab + COFF_SYMBOL_SIZE;
        let strtab_len = read_u32(&bytes, strtab) as usize;
        assert!(strtab_len > 4);
        let name_start = strtab + name_offset;
        assert_eq!(
            &bytes[name_start..name_start + "very_long_function_name".len()],
            b"very_long_function_name"
        );
    }

    #[test]
    fn amd64_rel32_relocation_is_written_after_section_data() {
        let mut writer = CoffWriter::new_x86_64();
        let text = writer.add_text_section(&[0xE8, 0, 0, 0, 0, 0xC3]);
        let callee = writer.add_function_symbol("callee", text, 5);
        writer.add_relocation(0, CoffRelocation::amd64_rel32(1, callee));

        let bytes = writer.write().unwrap();
        let section = COFF_FILE_HEADER_SIZE;
        assert_eq!(read_u16(&bytes, section + 32), 1);
        let reloc_ptr = read_u32(&bytes, section + 24) as usize;
        assert_eq!(read_u32(&bytes, reloc_ptr), 1);
        assert_eq!(read_u32(&bytes, reloc_ptr + 4), callee);
        assert_eq!(read_u16(&bytes, reloc_ptr + 8), IMAGE_REL_AMD64_REL32);
    }

    #[test]
    #[should_panic(expected = "COFF relocation section index 99 out of range")]
    fn relocation_to_out_of_range_section_panics() {
        let mut writer = CoffWriter::new_x86_64();
        writer.add_text_section(&[0xC3]);
        writer.add_relocation(99, CoffRelocation::amd64_rel32(0, 0));
    }

    #[test]
    fn amd64_addr32nb_relocation_and_unwind_sections_are_written() {
        let mut writer = CoffWriter::new_x86_64();
        let text = writer.add_text_section(&[0x55, 0x5D, 0xC3]);
        let xdata = writer.add_unwind_data_section(&[0x01, 0x04, 0x02, 0x05]);
        let pdata = writer.add_exception_data_section(&[0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0]);
        let text_symbol = writer.add_static_section_symbol(".text", text);
        let xdata_symbol = writer.add_static_section_symbol(".xdata", xdata);
        writer.add_relocation(
            (pdata - 1) as usize,
            CoffRelocation::amd64_addr32nb(0, text_symbol),
        );
        writer.add_relocation(
            (pdata - 1) as usize,
            CoffRelocation::amd64_addr32nb(8, xdata_symbol),
        );

        let bytes = writer.write().unwrap();
        assert_eq!(read_u16(&bytes, 2), 3);
        let xdata_section = COFF_FILE_HEADER_SIZE + COFF_SECTION_HEADER_SIZE;
        let pdata_section = xdata_section + COFF_SECTION_HEADER_SIZE;
        assert_eq!(&bytes[xdata_section..xdata_section + 6], b".xdata");
        assert_eq!(&bytes[pdata_section..pdata_section + 6], b".pdata");
        assert_eq!(read_u16(&bytes, pdata_section + 32), 2);
        let reloc_ptr = read_u32(&bytes, pdata_section + 24) as usize;
        assert_eq!(read_u32(&bytes, reloc_ptr), 0);
        assert_eq!(read_u16(&bytes, reloc_ptr + 8), IMAGE_REL_AMD64_ADDR32NB);
        assert_eq!(read_u32(&bytes, reloc_ptr + 10), 8);
        assert_eq!(
            read_u16(&bytes, reloc_ptr + COFF_RELOCATION_SIZE + 8),
            IMAGE_REL_AMD64_ADDR32NB
        );
    }

    #[test]
    fn write_rejects_too_many_sections_without_panicking() {
        let mut writer = CoffWriter::new_x86_64();
        for _ in 0..=u16::MAX {
            writer.add_section(".x", &[], IMAGE_SCN_CNT_INITIALIZED_DATA);
        }

        let err = writer.write().unwrap_err();
        assert_eq!(
            err,
            CoffError::SectionCountOverflow {
                count: u16::MAX as usize + 1,
                max: u16::MAX as usize,
            }
        );
    }

    #[test]
    fn write_rejects_long_section_names_without_panicking() {
        let mut writer = CoffWriter::new_x86_64();
        writer.add_section(
            ".debug_long_name",
            &[],
            IMAGE_SCN_CNT_INITIALIZED_DATA | IMAGE_SCN_MEM_READ,
        );

        let err = writer.write().unwrap_err();
        assert_eq!(
            err,
            CoffError::LongSectionName {
                name: ".debug_long_name".to_string(),
                max_len: COFF_SHORT_NAME_MAX_LEN,
            }
        );
    }

    #[test]
    fn write_rejects_too_many_relocations_without_panicking() {
        let mut writer = CoffWriter::new_x86_64();
        writer.add_text_section(&[0xC3]);
        for _ in 0..=u16::MAX {
            writer.add_relocation(0, CoffRelocation::amd64_rel32(0, 0));
        }

        let err = writer.write().unwrap_err();
        assert_eq!(
            err,
            CoffError::RelocationCountOverflow {
                section_name: ".text".to_string(),
                count: u16::MAX as usize + 1,
                max: u16::MAX as usize,
            }
        );
    }

    /// The AMD64 relocation type constants must match the published PE/COFF
    /// values, and the constructor helpers must select the right type.
    #[test]
    fn amd64_relocation_type_codes_match_pe_coff_abi() {
        assert_eq!(IMAGE_REL_AMD64_ADDR64, 0x0001);
        assert_eq!(IMAGE_REL_AMD64_ADDR32, 0x0002);
        assert_eq!(IMAGE_REL_AMD64_ADDR32NB, 0x0003);
        assert_eq!(IMAGE_REL_AMD64_REL32, 0x0004);
        assert_eq!(IMAGE_REL_AMD64_SECTION, 0x000A);
        assert_eq!(IMAGE_REL_AMD64_SECREL, 0x000B);
        assert_eq!(IMAGE_REL_AMD64_SECREL7, 0x000C);
        assert_eq!(IMAGE_REL_AMD64_TOKEN, 0x000E);

        assert_eq!(
            CoffRelocation::amd64_addr64(0, 0).typ,
            IMAGE_REL_AMD64_ADDR64
        );
        assert_eq!(
            CoffRelocation::amd64_addr32(0, 0).typ,
            IMAGE_REL_AMD64_ADDR32
        );
        assert_eq!(
            CoffRelocation::amd64_addr32nb(0, 0).typ,
            IMAGE_REL_AMD64_ADDR32NB
        );
        assert_eq!(CoffRelocation::amd64_rel32(0, 0).typ, IMAGE_REL_AMD64_REL32);
        assert_eq!(
            CoffRelocation::amd64_section(0, 0).typ,
            IMAGE_REL_AMD64_SECTION
        );
        assert_eq!(
            CoffRelocation::amd64_secrel(0, 0).typ,
            IMAGE_REL_AMD64_SECREL
        );
        assert_eq!(
            CoffRelocation::amd64_secrel7(0, 0).typ,
            IMAGE_REL_AMD64_SECREL7
        );
        assert_eq!(CoffRelocation::amd64_token(0, 0).typ, IMAGE_REL_AMD64_TOKEN);
    }

    /// Each new relocation kind must encode to the 10-byte COFF relocation
    /// record layout: u32 virtual_address, u32 symbol_table_index, u16 type.
    #[test]
    fn new_amd64_relocations_encode_to_coff_records() {
        let kinds: [(CoffRelocation, u16); 6] = [
            (
                CoffRelocation::amd64_addr64(0x10, 3),
                IMAGE_REL_AMD64_ADDR64,
            ),
            (
                CoffRelocation::amd64_addr32(0x14, 4),
                IMAGE_REL_AMD64_ADDR32,
            ),
            (
                CoffRelocation::amd64_section(0x18, 5),
                IMAGE_REL_AMD64_SECTION,
            ),
            (
                CoffRelocation::amd64_secrel(0x1C, 6),
                IMAGE_REL_AMD64_SECREL,
            ),
            (
                CoffRelocation::amd64_secrel7(0x20, 7),
                IMAGE_REL_AMD64_SECREL7,
            ),
            (CoffRelocation::amd64_token(0x24, 8), IMAGE_REL_AMD64_TOKEN),
        ];

        let mut writer = CoffWriter::new_x86_64();
        writer.add_section(".data", &[0u8; 64], IMAGE_SCN_CNT_INITIALIZED_DATA);
        for (reloc, _) in &kinds {
            writer.add_relocation(0, reloc.clone());
        }

        let bytes = writer.write().unwrap();
        let section = COFF_FILE_HEADER_SIZE;
        assert_eq!(read_u16(&bytes, section + 32), kinds.len() as u16);
        let reloc_ptr = read_u32(&bytes, section + 24) as usize;

        for (i, (reloc, expected_typ)) in kinds.iter().enumerate() {
            let off = reloc_ptr + i * COFF_RELOCATION_SIZE;
            assert_eq!(read_u32(&bytes, off), reloc.virtual_address, "vaddr {i}");
            assert_eq!(
                read_u32(&bytes, off + 4),
                reloc.symbol_table_index,
                "sym {i}"
            );
            assert_eq!(read_u16(&bytes, off + 8), *expected_typ, "type {i}");
        }
    }

    /// The COMDAT capability stub sets the section selection and the
    /// IMAGE_SCN_LNK_COMDAT characteristic, which must reach the written
    /// section header.
    #[test]
    fn mark_section_comdat_sets_lnk_comdat_characteristic() {
        assert_eq!(IMAGE_SCN_LNK_COMDAT, 0x0000_1000);

        let mut writer = CoffWriter::new_x86_64();
        let sect = writer.add_section(
            ".text$x",
            &[0xC3],
            IMAGE_SCN_CNT_CODE | IMAGE_SCN_MEM_EXECUTE | IMAGE_SCN_MEM_READ,
        );
        assert!(writer.mark_section_comdat(sect, IMAGE_COMDAT_SELECT_ANY));
        // Out-of-range section numbers are rejected without panicking.
        assert!(!writer.mark_section_comdat(0, IMAGE_COMDAT_SELECT_ANY));
        assert!(!writer.mark_section_comdat(99, IMAGE_COMDAT_SELECT_ANY));

        let bytes = writer.write().unwrap();
        let section = COFF_FILE_HEADER_SIZE;
        let characteristics = read_u32(&bytes, section + 36);
        assert_ne!(
            characteristics & IMAGE_SCN_LNK_COMDAT,
            0,
            "section header must carry IMAGE_SCN_LNK_COMDAT"
        );
        // The pre-existing characteristics must be preserved (additive only).
        assert_ne!(characteristics & IMAGE_SCN_CNT_CODE, 0);
        assert_ne!(characteristics & IMAGE_SCN_MEM_EXECUTE, 0);
    }

    /// The CoffSection COMDAT field tracks the selection kind directly.
    #[test]
    fn coff_section_comdat_selection_is_recorded() {
        let mut section = CoffSection {
            name: ".rdata$z".to_string(),
            data: vec![0u8; 8],
            characteristics: IMAGE_SCN_CNT_INITIALIZED_DATA | IMAGE_SCN_MEM_READ,
            relocations: Vec::new(),
            comdat_selection: None,
        };
        assert!(!section.is_comdat());

        section.mark_comdat(IMAGE_COMDAT_SELECT_LARGEST);
        assert!(section.is_comdat());
        assert_eq!(section.comdat_selection, Some(IMAGE_COMDAT_SELECT_LARGEST));
        assert_ne!(section.characteristics & IMAGE_SCN_LNK_COMDAT, 0);
    }
}
