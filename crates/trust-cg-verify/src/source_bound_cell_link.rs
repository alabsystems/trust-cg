// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Bind a checked relocatable scalar-cell caller to an ELF64 executable.
//! This independently checks load mappings, unchanged non-call words and every
//! resolved CALL26. Callback bodies are immutable endpoints, not proved code.
//! No instruction credit, loader theorem or callback contract is manufactured.

use super::CheckedAarch64ScalarCellElf;

#[path = "source_bound_cell_dynamic.rs"]
mod dynamic;

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("invalid or unsupported linked scalar-cell image: {0}")]
pub struct ScalarCellLinkError(&'static str);
type Result<T> = std::result::Result<T, ScalarCellLinkError>;
fn error(why: &'static str) -> ScalarCellLinkError {
    ScalarCellLinkError(why)
}

/// One uniquely defined callback's exact linked bytes and ELF virtual address.
/// A PIE address is relative to the executable's runtime load bias.
/// Establishing its ABI, memory effects and control behavior is separate work.
pub struct ScalarCellLinkedCallback<'a> {
    name: &'a str,
    address: u64,
    code: &'a [u8],
}
impl<'a> ScalarCellLinkedCallback<'a> {
    pub fn name(&self) -> &'a str {
        self.name
    }
    pub fn address(&self) -> u64 {
        self.address
    }
    pub fn code(&self) -> &'a [u8] {
        self.code
    }
}

/// Source/object/image correspondence with no public unchecked constructor.
/// Every endpoint remains borrowed immutably for this value's entire lifetime.
pub struct CheckedAarch64ScalarCellLink<'a> {
    object: &'a CheckedAarch64ScalarCellElf<'a>,
    image: &'a [u8],
    address: u64,
    code: &'a [u8],
    callbacks: Vec<ScalarCellLinkedCallback<'a>>,
}
impl<'a> CheckedAarch64ScalarCellLink<'a> {
    /// PIE addresses need the same aligned, non-wrapping load bias at runtime.
    /// The file's supported dynamic relocations write only non-executable
    /// mappings. This does not prove loader, initializer or dependency behavior.
    pub fn is_position_independent(&self) -> bool {
        self.image[16] == 3
    }
    pub fn object(&self) -> &CheckedAarch64ScalarCellElf<'a> {
        self.object
    }
    pub fn image(&self) -> &'a [u8] {
        self.image
    }
    pub fn address(&self) -> u64 {
        self.address
    }
    pub fn code(&self) -> &'a [u8] {
        self.code
    }
    pub fn callbacks(&self) -> &[ScalarCellLinkedCallback<'a>] {
        &self.callbacks
    }
}

fn bytes(image: &[u8], offset: u64, size: u64) -> Result<&[u8]> {
    let a = usize::try_from(offset).map_err(|_| error("file offset overflow"))?;
    let n = usize::try_from(size).map_err(|_| error("file size overflow"))?;
    image
        .get(
            a..a.checked_add(n)
                .ok_or_else(|| error("file extent overflow"))?,
        )
        .ok_or_else(|| error("file extent out of bounds"))
}
fn number(image: &[u8], offset: u64, size: u64) -> Result<u64> {
    Ok(bytes(image, offset, size)?
        .iter()
        .enumerate()
        .fold(0, |v, (i, b)| v | (u64::from(*b) << (8 * i))))
}
fn string(table: &[u8], offset: u64) -> Result<&str> {
    let tail = bytes(
        table,
        offset,
        (table.len() as u64)
            .checked_sub(offset)
            .ok_or_else(|| error("string offset out of bounds"))?,
    )?;
    let n = tail
        .iter()
        .position(|b| *b == 0)
        .ok_or_else(|| error("unterminated symbol"))?;
    std::str::from_utf8(&tail[..n]).map_err(|_| error("non-UTF8 symbol"))
}

struct Load {
    offset: u64,
    address: u64,
    file_size: u64,
    memory_size: u64,
    flags: u64,
}
struct Section {
    offset: u64,
    address: u64,
    size: u64,
    kind: u64,
    flags: u64,
    link: usize,
    info: usize,
    entry_size: u64,
}
struct Symbol<'a> {
    name: &'a str,
    address: u64,
    size: u64,
    section: usize,
    info: u8,
    other: u8,
}
struct Image<'a> {
    bytes: &'a [u8],
    loads: Vec<Load>,
    sections: Vec<Section>,
    symbols: Vec<Symbol<'a>>,
}

fn overlap(a: u64, a_end: u64, b: u64, b_end: u64) -> bool {
    a < b_end && b < a_end
}

impl<'a> Image<'a> {
    fn read(image: &'a [u8]) -> Result<Self> {
        if !(64..=16_777_216).contains(&image.len())
            || image.get(..7) != Some(b"\x7fELF\x02\x01\x01")
            || !matches!(image[7], 0 | 3)
            || image[8..16].iter().any(|b| *b != 0)
            || !matches!(number(image, 16, 2)?, 2 | 3)
            || number(image, 18, 2)? != 183
            || number(image, 20, 4)? != 1
            || number(image, 48, 4)? != 0
            || number(image, 52, 2)? != 64
            || number(image, 54, 2)? != 56
            || number(image, 58, 2)? != 64
        {
            return Err(error("requires bounded little-endian AArch64 executable"));
        }
        let phoff = number(image, 32, 8)?;
        let pie = number(image, 16, 2)? == 3;
        let shoff = number(image, 40, 8)?;
        let phnum = number(image, 56, 2)?;
        let shnum = number(image, 60, 2)?;
        if phoff < 64
            || shoff < 64
            || phoff % 8 != 0
            || shoff % 8 != 0
            || !(1..=128).contains(&phnum)
            || !(2..=4096).contains(&shnum)
        {
            return Err(error("header table shape"));
        }
        let ph = bytes(image, phoff, phnum * 56)?;
        let sh = bytes(image, shoff, shnum * 64)?;
        if overlap(phoff, phoff + phnum * 56, shoff, shoff + shnum * 64)
            || sh[..64].iter().any(|b| *b != 0)
        {
            return Err(error("overlapping or malformed header tables"));
        }
        let mut loads: Vec<Load> = Vec::new();
        for h in ph.as_chunks::<56>().0 {
            let kind = number(h, 0, 4)?;
            let flags = number(h, 4, 4)?;
            // A PIE's loader metadata receives a separate relocation write-range
            // check; a static image may not smuggle in dynamic loading.
            if !matches!(
                kind,
                0 | 1 | 4 | 6 | 0x6474_e550 | 0x6474_e551 | 0x6474_e552
            ) && !(pie && matches!(kind, 2 | 3))
            {
                return Err(error("dynamic or unsupported program header"));
            }
            if kind != 1 {
                continue;
            }
            let offset = number(h, 8, 8)?;
            let address = number(h, 16, 8)?;
            let file_size = number(h, 32, 8)?;
            let memory_size = number(h, 40, 8)?;
            let align = number(h, 48, 8)?;
            if flags & !7 != 0
                || file_size > memory_size
                || memory_size == 0
                || align < 65536
                || !align.is_power_of_two()
                || offset % align != address % align
            {
                return Err(error("load flags, extent or alignment"));
            }
            bytes(image, offset, file_size)?;
            let end = address
                .checked_add(memory_size)
                .ok_or_else(|| error("load address overflow"))?;
            // Keep even 64 KiB loader pages disjoint. This also covers 4/16 KiB
            // pages and prevents a later writable LOAD from shadowing code.
            let page_start = address & !65535;
            let page_end = end
                .checked_add(65535)
                .ok_or_else(|| error("load page overflow"))?
                & !65535;
            if loads.iter().any(|old| {
                overlap(
                    page_start,
                    page_end,
                    old.address & !65535,
                    (old.address + old.memory_size + 65535) & !65535,
                )
            }) {
                return Err(error("overlapping load pages"));
            }
            loads.push(Load {
                offset,
                address,
                file_size,
                memory_size,
                flags,
            });
        }
        if loads.is_empty() {
            return Err(error("missing load mappings"));
        }
        let mut sections = Vec::new();
        for h in sh.as_chunks::<64>().0 {
            let kind = number(h, 4, 4)?;
            let offset = number(h, 24, 8)?;
            let size = number(h, 32, 8)?;
            // PIE loader sections receive separate dynamic checks. Other
            // images allow only inert tables/data and initialization arrays;
            // unknown section kinds and REL/RELR remain unsupported.
            if !matches!(kind, 0 | 1 | 2 | 3 | 7 | 8 | 14 | 15 | 16)
                && !(pie && dynamic::section_kind(kind))
            {
                return Err(error("relocation, dynamic or unsupported section"));
            }
            if kind != 8 {
                bytes(image, offset, size)?;
            }
            let alignment = number(h, 48, 8)?;
            if alignment != 0 && !alignment.is_power_of_two() {
                return Err(error("section alignment"));
            }
            sections.push(Section {
                kind,
                offset,
                size,
                address: number(h, 16, 8)?,
                flags: number(h, 8, 8)?,
                link: number(h, 40, 4)? as usize,
                info: number(h, 44, 4)? as usize,
                entry_size: number(h, 56, 8)?,
            });
        }
        let names = sections
            .get(number(image, 62, 2)? as usize)
            .filter(|s| s.kind == 3)
            .ok_or_else(|| error("section name table"))?;
        let names = bytes(image, names.offset, names.size)?;
        for h in sh.as_chunks::<64>().0 {
            string(names, number(h, 0, 4)?)?;
        }
        let mut tables = sections.iter().filter(|s| s.kind == 2);
        let table = tables.next().ok_or_else(|| error("missing symbols"))?;
        if tables.next().is_some()
            || table.entry_size != 24
            || table.size % 24 != 0
            || !(24..=24 * 65536).contains(&table.size)
        {
            return Err(error("symbol table shape"));
        }
        let data = bytes(image, table.offset, table.size)?;
        if data[..24].iter().any(|b| *b != 0) {
            return Err(error("null symbol"));
        }
        let names = sections
            .get(table.link)
            .filter(|s| s.kind == 3)
            .ok_or_else(|| error("symbol strings"))?;
        let names = bytes(image, names.offset, names.size)?;
        if names.first() != Some(&0) || names.last() != Some(&0) {
            return Err(error("symbol string boundaries"));
        }
        let mut symbols = Vec::new();
        for raw in data.as_chunks::<24>().0 {
            symbols.push(Symbol {
                name: string(names, number(raw, 0, 4)?)?,
                info: raw[4],
                other: raw[5],
                section: number(raw, 6, 2)? as usize,
                address: number(raw, 8, 8)?,
                size: number(raw, 16, 8)?,
            });
        }
        if table.info == 0
            || table.info > symbols.len()
            || symbols
                .iter()
                .enumerate()
                .any(|(i, s)| (s.info >> 4 == 0) != (i < table.info))
        {
            return Err(error("symbol binding order"));
        }
        let parsed = Self {
            bytes: image,
            loads,
            sections,
            symbols,
        };
        if pie {
            dynamic::check(&parsed, ph)?;
        }
        Ok(parsed)
    }

    fn function(&self, name: &str) -> Result<&Symbol<'a>> {
        let mut found = self.symbols.iter().filter(|s| s.name == name);
        let symbol = found.next().ok_or_else(|| error("missing function"))?;
        if found.next().is_some()
            || symbol.info != 0x12
            || symbol.other != 0
            || symbol.size == 0
            || symbol.size % 4 != 0
            || symbol.address % 4 != 0
            || symbol.section == 0
        {
            return Err(error("ambiguous or non-ordinary function"));
        }
        Ok(symbol)
    }

    fn code(&self, symbol: &Symbol<'a>) -> Result<&'a [u8]> {
        let section = self
            .sections
            .get(symbol.section)
            .ok_or_else(|| error("function section index"))?;
        let relative = symbol
            .address
            .checked_sub(section.address)
            .ok_or_else(|| error("function before section"))?;
        if section.kind != 1
            || section.flags != 6
            || relative
                .checked_add(symbol.size)
                .is_none_or(|end| end > section.size)
        {
            return Err(error("function outside executable section"));
        }
        let offset = section
            .offset
            .checked_add(relative)
            .ok_or_else(|| error("function file offset overflow"))?;
        let end = symbol
            .address
            .checked_add(symbol.size)
            .ok_or_else(|| error("function address overflow"))?;
        let mut mappings = self
            .loads
            .iter()
            .filter(|load| symbol.address >= load.address && end <= load.address + load.file_size);
        let load = mappings
            .next()
            .ok_or_else(|| error("function has no file-backed load mapping"))?;
        if mappings.next().is_some()
            || load.flags != 5
            || load.offset.checked_add(symbol.address - load.address) != Some(offset)
        {
            return Err(error(
                "function mapping disagrees with section or is writable",
            ));
        }
        bytes(self.bytes, offset, symbol.size)
    }
}

/// Compare every caller word and resolve every call directly to the unique
/// ordinary function definition in a static executable or supported Linux PIE.
/// PIE dynamic relocations must stay entirely within non-executable writable
/// mappings. Direct caller BLs cannot be replaced by PLT calls or thunks.
/// Weak/IFUNC callback symbols and alternate PCS are not supported.
/// The returned callback bodies still need independent semantic/ABI checks.
pub fn check_aarch64_scalar_cell_link<'a>(
    object: &'a CheckedAarch64ScalarCellElf<'a>,
    image: &'a [u8],
) -> Result<CheckedAarch64ScalarCellLink<'a>> {
    let parsed = Image::read(image)?;
    let caller = parsed.function(&object.source().lir().name)?;
    let code = parsed.code(caller)?;
    if code.len() != object.code().len() {
        return Err(error("caller size changed"));
    }
    let mut callbacks: Vec<ScalarCellLinkedCallback<'a>> = Vec::new();
    for (offset, (before, after)) in object
        .code()
        .as_chunks::<4>()
        .0
        .iter()
        .zip(code.as_chunks::<4>().0)
        .enumerate()
    {
        let offset = (offset * 4) as u64;
        if let Some(reloc) = object.relocations().iter().find(|r| r.offset == offset) {
            let target = parsed.function(reloc.symbol)?;
            let target_code = parsed.code(target)?;
            if overlap(
                caller.address,
                caller.address + caller.size,
                target.address,
                target.address + target.size,
            ) {
                return Err(error("callback overlaps caller"));
            }
            let word = u32::from_le_bytes(*after);
            let displacement = i64::from(((word & 0x03ff_ffff) << 6) as i32 >> 6) * 4;
            let destination =
                i128::from(caller.address) + i128::from(offset) + i128::from(displacement);
            if word & 0xfc00_0000 != 0x9400_0000 || destination != i128::from(target.address) {
                return Err(error("CALL26 target does not match callback definition"));
            }
            if !callbacks.iter().any(|c| c.name == target.name) {
                if callbacks.iter().any(|c| {
                    overlap(
                        c.address,
                        c.address + c.code.len() as u64,
                        target.address,
                        target.address + target.size,
                    )
                }) {
                    return Err(error("overlapping callback definitions"));
                }
                callbacks.push(ScalarCellLinkedCallback {
                    name: target.name,
                    address: target.address,
                    code: target_code,
                });
            }
        } else if before != after {
            return Err(error("non-call instruction changed"));
        }
    }
    Ok(CheckedAarch64ScalarCellLink {
        object,
        image,
        address: caller.address,
        code,
        callbacks,
    })
}
