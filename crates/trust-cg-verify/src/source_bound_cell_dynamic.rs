// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Inspect the loader's relocation tables, not just section-header summaries.
//! This proves no loader theorem: it checks that every supported relocation
//! destination and the loader's DEBUG/GOT slots avoid executable LOAD pages.
//! Initializers, dependencies, IFUNCs in those dependencies and subsequent
//! program effects still need their own semantics and authority.

use std::collections::BTreeMap;

use super::{Image, Result, bytes, error, number, overlap, string};

pub(super) fn section_kind(kind: u64) -> bool {
    // RELA, DYNAMIC, DYNSYM, GNU_HASH, VERDEF, VERNEED, VERSYM.
    matches!(kind, 4 | 6 | 11 | 0x6fff_fff6 | 0x6fff_fffd..=0x6fff_ffff)
}

fn mapped<'a>(image: &Image<'a>, address: u64, size: u64, writable: bool) -> Result<&'a [u8]> {
    let end = address
        .checked_add(size)
        .ok_or_else(|| error("dynamic range overflow"))?;
    let load = image
        .loads
        .iter()
        .find(|l| address >= l.address && end <= l.address + l.file_size)
        .ok_or_else(|| error("dynamic table outside file-backed LOAD"))?;
    if if writable {
        load.flags != 6
    } else {
        load.flags != 4 && load.flags != 5
    } {
        return Err(error("dynamic table LOAD permissions"));
    }
    bytes(image.bytes, load.offset + (address - load.address), size)
}

fn writable(image: &Image<'_>, address: u64, size: u64) -> Result<()> {
    let end = address
        .checked_add(size)
        .ok_or_else(|| error("relocation destination overflow"))?;
    if size == 0
        || !image
            .loads
            .iter()
            .any(|l| l.flags == 6 && address >= l.address && end <= l.address + l.memory_size)
    {
        return Err(error(
            "relocation destination is not wholly writable non-executable memory",
        ));
    }
    Ok(())
}

fn header(ph: &[u8], kind: u64) -> Result<&[u8]> {
    let mut found = ph
        .as_chunks::<56>()
        .0
        .iter()
        .filter(|h| number(&h[..], 0, 4) == Ok(kind));
    let h = found
        .next()
        .ok_or_else(|| error("PIE missing loader header"))?;
    if found.next().is_some() {
        return Err(error("duplicate loader header"));
    }
    Ok(h)
}

pub(super) fn check(image: &Image<'_>, ph: &[u8]) -> Result<()> {
    let interp = header(ph, 3)?;
    let interpreter = bytes(image.bytes, number(interp, 8, 8)?, number(interp, 32, 8)?)?;
    if interpreter != b"/lib/ld-linux-aarch64.so.1\0"
        || mapped(
            image,
            number(interp, 16, 8)?,
            interpreter.len() as u64,
            false,
        )? != interpreter
    {
        return Err(error("unsupported or unmapped PIE interpreter"));
    }
    let dynamic = header(ph, 2)?;
    let address = number(dynamic, 16, 8)?;
    let size = number(dynamic, 32, 8)?;
    if size == 0 || size > 16 * 4096 || size % 16 != 0 || number(dynamic, 40, 8)? != size {
        return Err(error("dynamic table extent"));
    }
    let data = mapped(image, address, size, true)?;
    if data.as_ptr() != bytes(image.bytes, number(dynamic, 8, 8)?, size)?.as_ptr() {
        return Err(error("dynamic header file mapping disagreement"));
    }
    let mut sections = image.sections.iter().filter(|s| s.kind == 6);
    let section = sections
        .next()
        .ok_or_else(|| error("missing dynamic section"))?;
    if sections.next().is_some()
        || section.address != address
        || section.size != size
        || section.offset != number(dynamic, 8, 8)?
        || section.entry_size != 16
        || section.flags != 3
    {
        return Err(error("dynamic section/header disagreement"));
    }
    let mut tags = BTreeMap::new();
    let mut needed = Vec::new();
    let mut ended = false;
    for (i, raw) in data.as_chunks::<16>().0.iter().enumerate() {
        let tag = number(raw, 0, 8)?;
        let value = number(raw, 8, 8)?;
        if ended || tag == 0 {
            if tag != 0 || value != 0 {
                return Err(error("nonzero data after dynamic terminator"));
            }
            ended = true;
            continue;
        }
        if tag == 1 {
            needed.push(value);
            continue;
        }
        // No TEXTREL, REL/RELR, TLS descriptors, filters, audit hooks or
        // processor-specific loader extensions are silently ignored.
        if !matches!(tag, 2..=15 | 20 | 21 | 23..=30 | 32 | 33 |
            0x6fff_fef5 | 0x6fff_fff0 | 0x6fff_fff9 | 0x6fff_fffb | 0x6fff_fffc..=0x6fff_ffff)
            || tags.insert(tag, value).is_some()
        {
            return Err(error("duplicate or unsupported dynamic tag"));
        }
        if tag == 21 {
            if value != 0 {
                return Err(error("pre-populated loader DEBUG slot"));
            }
            writable(image, address + i as u64 * 16 + 8, 8)?;
        }
    }
    let required = |tag| {
        tags.get(&tag)
            .copied()
            .ok_or_else(|| error("missing dynamic tag"))
    };
    if !ended
        || required(0x6fff_fffb)? & 0x0800_0000 == 0
        || required(0x6fff_fffb)? & !(0x0800_0000 | 1) != 0
        || tags.get(&30).copied().unwrap_or(0) & !8 != 0
    {
        return Err(error("not an ordinary PIE or unsupported loader flags"));
    }
    // DT_BIND_NOW has no payload. Lazy binding is supported only through the
    // same checked GOT/JUMP_SLOT write extents as eager binding.
    if tags.get(&24).is_some_and(|v| *v != 0) {
        return Err(error("BIND_NOW payload"));
    }
    let str_address = required(5)?;
    let strings = mapped(image, str_address, required(10)?, false)?;
    if strings.first() != Some(&0) || strings.last() != Some(&0) {
        return Err(error("dynamic string boundaries"));
    }
    for offset in needed.into_iter().chain(
        [14, 15, 29]
            .into_iter()
            .filter_map(|t| tags.get(&t).copied()),
    ) {
        string(strings, offset)?;
    }
    let mut dynsyms = image
        .sections
        .iter()
        .enumerate()
        .filter(|(_, s)| s.kind == 11);
    let (symbol_index, symbols) = dynsyms
        .next()
        .ok_or_else(|| error("missing dynamic symbols"))?;
    if dynsyms.next().is_some()
        || required(11)? != 24
        || symbols.entry_size != 24
        || symbols.address != required(6)?
        || symbols.size == 0
        || symbols.size % 24 != 0
        || symbols.size > 24 * 65536
        || symbols.flags != 2
    {
        return Err(error("dynamic symbol table shape"));
    }
    let strings_section = image
        .sections
        .get(symbols.link)
        .ok_or_else(|| error("dynamic string section index"))?;
    if strings_section.kind != 3
        || strings_section.address != str_address
        || strings_section.size != strings.len() as u64
        || section.link != symbols.link
        || bytes(image.bytes, strings_section.offset, strings_section.size)?.as_ptr()
            != strings.as_ptr()
    {
        return Err(error("dynamic string mapping disagreement"));
    }
    let symbols_data = mapped(image, symbols.address, symbols.size, false)?;
    if symbols_data.as_ptr() != bytes(image.bytes, symbols.offset, symbols.size)?.as_ptr()
        || symbols_data[..24].iter().any(|b| *b != 0)
    {
        return Err(error("dynamic symbols mapping or null symbol"));
    }
    for symbol in symbols_data.as_chunks::<24>().0 {
        string(strings, number(symbol, 0, 4)?)?;
        if symbol[4] & 15 == 10 {
            return Err(error("image-defined IFUNC resolver unsupported"));
        }
    }
    let mut protected = vec![(address, address + size)];
    if let Some(got) = tags.get(&3) {
        writable(image, *got, 24)?;
        protected.push((*got, *got + 24));
    }
    if tags.contains_key(&0x6fff_fff9) && !tags.contains_key(&7) {
        return Err(error("relative count without RELA table"));
    }
    let mut tables = Vec::new();
    if tags.contains_key(&7) || tags.contains_key(&8) || tags.contains_key(&9) {
        if required(9)? != 24 {
            return Err(error("dynamic RELA entry size"));
        }
        tables.push((required(7)?, required(8)?, false));
    }
    if tags.contains_key(&23) || tags.contains_key(&2) || tags.contains_key(&20) {
        if required(20)? != 7 || !tags.contains_key(&3) {
            return Err(error("unsupported PLT relocation table"));
        }
        tables.push((required(23)?, required(2)?, true));
    }
    let reloc_sections: Vec<_> = image.sections.iter().filter(|s| s.kind == 4).collect();
    if reloc_sections.len() != tables.len() {
        return Err(error("unaccounted relocation section"));
    }
    let mut written = BTreeMap::new();
    let mut matched_sections = Vec::new();
    for (table_address, table_size, plt) in tables {
        if table_size == 0 || table_size % 24 != 0 || table_size > 24 * 65536 {
            return Err(error("dynamic relocation table bounds"));
        }
        let data = mapped(image, table_address, table_size, false)?;
        let mut matching = reloc_sections
            .iter()
            .enumerate()
            .filter(|(_, s)| s.address == table_address && s.size == table_size);
        let (index, section) = matching
            .next()
            .ok_or_else(|| error("loader relocation table not in sections"))?;
        if matching.next().is_some()
            || matched_sections.contains(&index)
            || section.entry_size != 24
            || section.link != symbol_index
            || section.flags & !0x42 != 0
            || section.flags & 2 == 0
            || data.as_ptr() != bytes(image.bytes, section.offset, section.size)?.as_ptr()
        {
            return Err(error("relocation section/table disagreement"));
        }
        matched_sections.push(index);
        let relative_count = if plt {
            0
        } else {
            tags.get(&0x6fff_fff9).copied().unwrap_or(0)
        };
        if relative_count > table_size / 24 {
            return Err(error("relative relocation count overflow"));
        }
        for (i, raw) in data.as_chunks::<24>().0.iter().enumerate() {
            let destination = number(raw, 0, 8)?;
            let info = number(raw, 8, 8)?;
            let kind = info as u32;
            let symbol = info >> 32;
            if (plt && kind != 1026)
                || (!plt && !matches!(kind, 257 | 1025 | 1027))
                || symbol >= symbols.size / 24
                || (kind == 1027 && symbol != 0)
                || (kind != 1027 && symbol == 0)
                || ((i as u64) < relative_count && kind != 1027)
                || destination % 8 != 0
            {
                return Err(error("unsupported dynamic relocation or symbol"));
            }
            writable(image, destination, 8)?;
            let end = destination + 8; // writable checked the addition.
            if protected
                .iter()
                .any(|(a, b)| overlap(*a, *b, destination, end))
            {
                return Err(error("relocation can rewrite loader metadata"));
            }
            if written
                .range(..end)
                .next_back()
                .is_some_and(|(_, old_end)| *old_end > destination)
            {
                return Err(error("overlapping dynamic relocation writes"));
            }
            written.insert(destination, end);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::super::Load;
    use super::*;

    #[test]
    fn high_virtual_address_maps_without_intermediate_overflow() {
        // The file and virtual extents both satisfy the parent parser's LOAD
        // invariants. Adding the file offset before subtracting the virtual
        // base would nevertheless overflow for this valid relative range.
        let offset = 2 * 65536;
        let address = u64::MAX - 131_071;
        let mut data = vec![0; offset as usize];
        data.extend_from_slice(&[11, 22, 33, 44, 55, 66, 77, 88]);
        let image = Image {
            bytes: &data,
            loads: vec![Load {
                offset,
                address,
                file_size: 8,
                memory_size: 8,
                flags: 4,
            }],
            sections: Vec::new(),
            symbols: Vec::new(),
        };
        assert_eq!(
            mapped(&image, address + 2, 4, false).unwrap(),
            [33, 44, 55, 66]
        );
        assert!(mapped(&image, address + 5, 4, false).is_err());
        assert!(mapped(&image, address + 2, 4, true).is_err());
    }
}
