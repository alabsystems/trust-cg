// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Bounded independent ELF64 reader for one ordinary scalar-cell caller.
//! Read all text relocations from the immutable object, including symbol
//! binding and the complete st_other byte. No producer inventory is authority.
//! Reference: https://github.com/ARM-software/abi-aa/blob/main/aaelf64/aaelf64.rst

use super::*;

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ScalarCellElfError {
    #[error("invalid or unsupported scalar-cell ELF object: {0}")]
    Object(&'static str),
    #[error(transparent)]
    Bytes(#[from] ScalarCellByteError),
}

type Result<T> = std::result::Result<T, ScalarCellElfError>;
fn invalid(reason: &'static str) -> ScalarCellElfError {
    ScalarCellElfError::Object(reason)
}

/// An original source caller bound to the exact code, symbol and CALL26 records
/// in one immutable relocatable ELF object. This is diagnostic correspondence;
/// linking, unwind metadata, callback semantics and proof admission remain
/// separate. Other non-executable sections are not semantic proof endpoints.
pub struct CheckedAarch64ScalarCellElf<'a> {
    source: CheckedAarch64ScalarCellSource<'a>,
    object: &'a [u8],
    code: &'a [u8],
    relocations: Vec<ScalarCellRelocation<'a>>,
}

impl<'a> CheckedAarch64ScalarCellElf<'a> {
    pub fn source(&self) -> &CheckedAarch64ScalarCellSource<'a> {
        &self.source
    }
    pub fn object(&self) -> &'a [u8] {
        self.object
    }
    pub fn code(&self) -> &'a [u8] {
        self.code
    }
    pub fn relocations(&self) -> &[ScalarCellRelocation<'a>] {
        &self.relocations
    }
}

fn range(bytes: &[u8], offset: u64, size: u64) -> Result<&[u8]> {
    let start = usize::try_from(offset).map_err(|_| invalid("file offset overflow"))?;
    let count = usize::try_from(size).map_err(|_| invalid("file size overflow"))?;
    bytes
        .get(
            start
                ..start
                    .checked_add(count)
                    .ok_or_else(|| invalid("file range overflow"))?,
        )
        .ok_or_else(|| invalid("file range out of bounds"))
}
fn number(bytes: &[u8], offset: usize, size: usize) -> Result<u64> {
    let data = range(bytes, offset as u64, size as u64)?;
    Ok(data
        .iter()
        .enumerate()
        .fold(0, |n, (i, byte)| n | (u64::from(*byte) << (8 * i))))
}
fn string(bytes: &[u8], offset: u64) -> Result<&str> {
    let offset = usize::try_from(offset).map_err(|_| invalid("string offset overflow"))?;
    let tail = bytes
        .get(offset..)
        .ok_or_else(|| invalid("string offset out of bounds"))?;
    let end = tail
        .iter()
        .position(|b| *b == 0)
        .ok_or_else(|| invalid("unterminated string"))?;
    std::str::from_utf8(&tail[..end]).map_err(|_| invalid("non-UTF8 symbol or section name"))
}

struct Section<'a> {
    header: &'a [u8],
    kind: u64,
    flags: u64,
    size: u64,
    link: usize,
    info: usize,
    data: &'a [u8],
}

fn sections(object: &[u8]) -> Result<Vec<Section<'_>>> {
    if !(64..=1_048_576).contains(&object.len())
        || object.get(..7) != Some(b"\x7fELF\x02\x01\x01")
        || !matches!(object[7], 0 | 3)
        || object[8..16].iter().any(|b| *b != 0)
        || number(object, 16, 2)? != 1
        || number(object, 18, 2)? != 183
        || number(object, 20, 4)? != 1
        || number(object, 24, 8)? != 0
        || number(object, 32, 8)? != 0
        || number(object, 48, 4)? != 0
        || number(object, 52, 2)? != 64
        || number(object, 56, 2)? != 0
        || number(object, 58, 2)? != 64
    {
        return Err(invalid("requires bounded little-endian AArch64 ET_REL"));
    }
    let table = number(object, 40, 8)?;
    let count = number(object, 60, 2)?;
    if table < 64 || table % 8 != 0 || !(2..=64).contains(&count) {
        return Err(invalid("section table shape"));
    }
    let headers = range(object, table, count * 64)?;
    if headers[..64].iter().any(|b| *b != 0) {
        return Err(invalid("nonzero null section"));
    }
    let mut result = Vec::new();
    let mut occupied = vec![(0, 64), (table, table + count * 64)];
    for header in headers.chunks_exact(64) {
        let kind = number(header, 4, 4)?;
        let offset = number(header, 24, 8)?;
        let size = number(header, 32, 8)?;
        let align = number(header, 48, 8)?;
        if !matches!(kind, 0 | 1 | 2 | 3 | 4 | 8)
            || align != 0 && !align.is_power_of_two()
            || size > 1_048_576
            || align > 1 && offset % align != 0
        {
            return Err(invalid("section type, alignment or size"));
        }
        let data = if kind == 8 {
            &[][..]
        } else {
            range(object, offset, size)?
        };
        if kind != 8 && size != 0 {
            let end = offset
                .checked_add(size)
                .ok_or_else(|| invalid("section range overflow"))?;
            if occupied.iter().any(|(a, b)| offset < *b && *a < end) {
                return Err(invalid("overlapping file sections"));
            }
            occupied.push((offset, end));
        }
        if kind == 3 && (data.first() != Some(&0) || data.last() != Some(&0)) {
            return Err(invalid("string table boundaries"));
        }
        result.push(Section {
            header,
            kind,
            flags: number(header, 8, 8)?,
            size,
            link: number(header, 40, 4)? as usize,
            info: number(header, 44, 4)? as usize,
            data,
        });
    }
    let names = result
        .get(number(object, 62, 2)? as usize)
        .filter(|s| s.kind == 3)
        .ok_or_else(|| invalid("section name table"))?;
    for section in &result {
        string(names.data, number(section.header, 0, 4)?)?;
    }
    Ok(result)
}

struct Symbol<'a> {
    name: &'a str,
    info: u8,
    other: u8,
    section: usize,
    value: u64,
    size: u64,
}

fn symbols<'a>(sections: &[Section<'a>]) -> Result<(usize, Vec<Symbol<'a>>)> {
    let mut tables = sections.iter().enumerate().filter(|(_, s)| s.kind == 2);
    let (index, table) = tables
        .next()
        .ok_or_else(|| invalid("missing symbol table"))?;
    if tables.next().is_some()
        || number(table.header, 56, 8)? != 24
        || table.size % 24 != 0
        || !(2..=128).contains(&(table.size / 24))
    {
        return Err(invalid("symbol table shape"));
    }
    let names = sections
        .get(table.link)
        .filter(|s| s.kind == 3)
        .ok_or_else(|| invalid("symbol string table"))?;
    if table.data[..24].iter().any(|b| *b != 0) {
        return Err(invalid("nonzero null symbol"));
    }
    let mut result = Vec::new();
    for raw in table.data.chunks_exact(24) {
        result.push(Symbol {
            name: string(names.data, number(raw, 0, 4)?)?,
            info: raw[4],
            other: raw[5],
            section: number(raw, 6, 2)? as usize,
            value: number(raw, 8, 8)?,
            size: number(raw, 16, 8)?,
        });
    }
    if table.info > result.len()
        || table.info == 0
        || result
            .iter()
            .enumerate()
            .any(|(i, s)| (s.info >> 4 == 0) != (i < table.info))
    {
        return Err(invalid("symbol binding order"));
    }
    Ok((index, result))
}

/// Independently parse the original caller's complete executable section and
/// every relocation which targets it. The narrow format accepts one ordinary
/// global function spanning its section; it rejects alternate PCS flags,
/// weak/defined callbacks, non-RELA relocation formats and ambiguous symbols.
pub fn check_aarch64_scalar_cell_elf<'a>(
    module: &'a trust_ir::Module,
    lir: &'a Function,
    object: &'a [u8],
) -> Result<CheckedAarch64ScalarCellElf<'a>> {
    let source = super::super::check_aarch64_scalar_cell_source(module, lir)
        .map_err(ScalarCellByteError::Source)?;
    let sections = sections(object)?;
    let (symtab, symbols) = symbols(&sections)?;
    let mut callers = symbols.iter().filter(|s| s.name == lir.name);
    let caller = callers
        .next()
        .ok_or_else(|| invalid("missing source caller symbol"))?;
    if callers.next().is_some()
        || caller.info != 0x12
        || caller.other != 0
        || caller.value != 0
        || caller.section == 0
    {
        return Err(invalid("caller symbol or calling convention"));
    }
    let text = sections
        .get(caller.section)
        .ok_or_else(|| invalid("caller section index"))?;
    if text.kind != 1
        || text.flags != 6
        || text.size != caller.size
        || text.size == 0
        || number(text.header, 48, 8)? < 4
        || sections
            .iter()
            .enumerate()
            .any(|(i, s)| i != caller.section && s.flags & 4 != 0 && s.size != 0)
        || symbols.iter().any(|s| {
            s.section == caller.section
                && !std::ptr::eq(s, caller)
                && (s.info & 15 != 0 || s.info >> 4 != 0)
                && s.info & 15 != 3
        })
    {
        return Err(invalid("requires one complete executable caller section"));
    }
    let mut relocations = Vec::new();
    for section in sections.iter().filter(|s| s.kind == 4) {
        if section.link != symtab
            || section.info == 0
            || section.info >= sections.len()
            || number(section.header, 56, 8)? != 24
            || section.size % 24 != 0
            || section.size / 24 > 128
        {
            return Err(invalid("relocation table links or extent"));
        }
        for raw in section.data.chunks_exact(24) {
            let offset = number(raw, 0, 8)?;
            let info = number(raw, 8, 8)?;
            let symbol = symbols
                .get((info >> 32) as usize)
                .ok_or_else(|| invalid("relocation symbol index"))?;
            if offset >= sections[section.info].size {
                return Err(invalid("relocation patch outside section"));
            }
            if section.info != caller.section {
                continue;
            }
            if symbol.info >> 4 != 1
                || !matches!(symbol.info & 15, 0 | 2)
                || symbol.other != 0
                || symbol.section != 0
                || symbol.value != 0
                || symbol.size != 0
                || symbol.name.is_empty()
                || symbols.iter().filter(|s| s.name == symbol.name).count() != 1
            {
                return Err(invalid("callback symbol or calling convention"));
            }
            relocations.push(ScalarCellRelocation {
                offset,
                kind: info as u32,
                symbol: symbol.name,
                addend: number(raw, 16, 8)? as i64,
            });
        }
    }
    check_aarch64_scalar_cell_bytes(module, lir, text.data, &relocations)?;
    Ok(CheckedAarch64ScalarCellElf {
        source,
        object,
        code: text.data,
        relocations,
    })
}
