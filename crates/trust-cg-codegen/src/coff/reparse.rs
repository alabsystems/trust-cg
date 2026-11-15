// trust-cg-codegen/coff/reparse.rs - Independent COFF symbol-table reader
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! An independent reader of a COFF relocatable object's symbol table, for the
//! post-emission binding check (`Compiler::compile`'s
//! `check_object_function_bindings`). It reads the object bytes, not writer
//! state, so it also covers an object taken from the artifact cache.
//!
//! It reads the file header (`PointerToSymbolTable`, `NumberOfSymbols`), each
//! 18-byte symbol record (short names inline, long names through the string
//! table that follows the symbol table) and skips each record's auxiliary
//! records. Every read is bounds-checked; a truncated or inconsistent table is
//! an error, never a shorter list.

/// One primary COFF symbol record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoffSymbolRecord {
    /// The symbol's name (inline short name, or the string-table entry).
    pub name: String,
    /// `Value`: the offset in its section for a section symbol.
    pub value: u32,
    /// `SectionNumber`: 1-based section number, 0 (undefined), -1
    /// (absolute) or -2 (debug).
    pub section_number: i16,
    /// `Type` (`IMAGE_SYM_DTYPE_FUNCTION << 4`-style complex type in the high
    /// byte; trust-cg writes `0x20` for a function).
    pub typ: u16,
    /// `StorageClass` (`IMAGE_SYM_CLASS_EXTERNAL` = 2, `IMAGE_SYM_CLASS_STATIC`
    /// = 3, `IMAGE_SYM_CLASS_WEAK_EXTERNAL` = 105, ...).
    pub storage_class: u8,
}

const FILE_HEADER_SIZE: usize = 20;
const SYMBOL_SIZE: usize = 18;

/// Every primary symbol record of the COFF relocatable object `bytes`, in
/// table order (auxiliary records skipped).
pub fn read_symbols(bytes: &[u8]) -> Result<Vec<CoffSymbolRecord>, String> {
    let field = |at: usize, width: usize| {
        at.checked_add(width)
            .and_then(|end| bytes.get(at..end))
            .ok_or_else(|| format!("COFF object truncated at byte {at} (+{width})"))
    };
    let u16_at = |at: usize| field(at, 2).map(|b| u16::from_le_bytes([b[0], b[1]]));
    let u32_at = |at: usize| field(at, 4).map(|b| u32::from_le_bytes([b[0], b[1], b[2], b[3]]));
    if bytes.len() < FILE_HEADER_SIZE {
        return Err(format!(
            "COFF object of {} bytes has no file header",
            bytes.len()
        ));
    }
    let table = usize::try_from(u32_at(8)?).map_err(|error| error.to_string())?;
    let count = usize::try_from(u32_at(12)?).map_err(|error| error.to_string())?;
    let strings = count
        .checked_mul(SYMBOL_SIZE)
        .and_then(|size| table.checked_add(size))
        .ok_or_else(|| "COFF symbol table size overflows".to_string())?;
    let string_table_size = if count == 0 {
        0
    } else {
        usize::try_from(u32_at(strings)?).map_err(|error| error.to_string())?
    };
    if count != 0 && string_table_size < 4 {
        return Err(format!(
            "COFF string table size {string_table_size} is smaller than its own size field"
        ));
    }
    let string = |offset: usize| -> Result<String, String> {
        if offset < 4 || offset >= string_table_size {
            return Err(format!(
                "COFF long name offset {offset} is outside the {string_table_size}-byte string table"
            ));
        }
        let start = strings
            .checked_add(offset)
            .ok_or_else(|| "COFF string offset overflows".to_string())?;
        let end = strings
            .checked_add(string_table_size)
            .ok_or_else(|| "COFF string table end overflows".to_string())?;
        let tail = bytes
            .get(start..end)
            .ok_or_else(|| format!("COFF string table runs past the object at byte {start}"))?;
        let length = tail
            .iter()
            .position(|&byte| byte == 0)
            .ok_or_else(|| format!("COFF long name at offset {offset} is not NUL-terminated"))?;
        String::from_utf8(tail[..length].to_vec())
            .map_err(|_| format!("COFF long name at offset {offset} is not UTF-8"))
    };
    let mut symbols = Vec::new();
    let mut index = 0usize;
    while index < count {
        let at = table + index * SYMBOL_SIZE;
        let raw_name = field(at, 8)?;
        let name = if raw_name[..4] == [0, 0, 0, 0] {
            string(usize::try_from(u32_at(at + 4)?).map_err(|error| error.to_string())?)?
        } else {
            let length = raw_name.iter().position(|&byte| byte == 0).unwrap_or(8);
            String::from_utf8(raw_name[..length].to_vec())
                .map_err(|_| format!("COFF short name of symbol #{index} is not UTF-8"))?
        };
        let auxiliary = usize::from(field(at + 17, 1)?[0]);
        symbols.push(CoffSymbolRecord {
            name,
            value: u32_at(at + 8)?,
            section_number: u16_at(at + 12)? as i16,
            typ: u16_at(at + 14)?,
            storage_class: field(at + 16, 1)?[0],
        });
        index = index
            .checked_add(1 + auxiliary)
            .filter(|next| *next <= count)
            .ok_or_else(|| {
                format!(
                    "COFF symbol #{index} claims {auxiliary} auxiliary record(s) past the \
                     {count}-entry table"
                )
            })?;
    }
    Ok(symbols)
}

#[cfg(test)]
mod tests {
    use super::read_symbols;
    use crate::coff::{CoffWriter, IMAGE_SYM_CLASS_EXTERNAL, IMAGE_SYM_CLASS_STATIC};

    #[test]
    fn reads_back_what_the_writer_wrote() {
        let mut writer = CoffWriter::new_x86_64();
        let text = writer.add_text_section_with_align(&[0xc3, 0xc3], 4);
        writer.add_function_symbol("exported", text, 0);
        writer.add_static_function_symbol("a_module_local_function_with_a_long_name", text, 1);
        writer.add_static_section_symbol(".text", text);
        let bytes = writer.write().expect("COFF object");
        let symbols = read_symbols(&bytes).expect("symbol table");
        let summary: Vec<(&str, u32, i16, u16, u8)> = symbols
            .iter()
            .map(|symbol| {
                (
                    symbol.name.as_str(),
                    symbol.value,
                    symbol.section_number,
                    symbol.typ,
                    symbol.storage_class,
                )
            })
            .collect();
        assert_eq!(
            summary,
            [
                ("exported", 0, 1, 0x20, IMAGE_SYM_CLASS_EXTERNAL),
                (
                    "a_module_local_function_with_a_long_name",
                    1,
                    1,
                    0x20,
                    IMAGE_SYM_CLASS_STATIC
                ),
                (".text", 0, 1, 0, IMAGE_SYM_CLASS_STATIC),
            ]
        );
    }

    #[test]
    fn a_truncated_table_is_an_error() {
        let mut writer = CoffWriter::new_x86_64();
        let text = writer.add_text_section_with_align(&[0xc3], 4);
        writer.add_function_symbol("f", text, 0);
        let bytes = writer.write().expect("COFF object");
        for length in [0, 10, bytes.len() - 5] {
            assert!(read_symbols(&bytes[..length]).is_err(), "length {length}");
        }
    }
}
