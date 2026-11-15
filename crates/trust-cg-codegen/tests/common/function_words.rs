// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//! The code of every function a relocatable AArch64 object defines, read from
//! the object's own symbol table by this parser rather than the emitter: ELF
//! `STT_FUNC` extents, or Mach-O external `__TEXT,__text` symbols, each
//! extending to the next `__text` symbol.

// Declared unconditionally; a target whose callers are all cfg'd out for this
// host must not trip the workspace's `warnings = "deny"`.
#![allow(dead_code)]

use std::collections::BTreeMap;

fn le16(bytes: &[u8], at: usize) -> u16 {
    u16::from_le_bytes(bytes[at..at + 2].try_into().unwrap())
}

fn le32(bytes: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap())
}

fn le64(bytes: &[u8], at: usize) -> usize {
    usize::try_from(u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap())).unwrap()
}

/// The NUL-terminated string at `at`, or the rest of `bytes` (a full-width
/// Mach-O segment or section name has no NUL).
fn cstr(bytes: &[u8], at: usize) -> &str {
    let len = bytes[at..]
        .iter()
        .position(|&b| b == 0)
        .unwrap_or(bytes.len() - at);
    std::str::from_utf8(&bytes[at..at + len]).unwrap()
}

fn code_words(code: &[u8]) -> Vec<u32> {
    assert_eq!(code.len() % 4, 0, "function extent is not word sized");
    code.as_chunks::<4>()
        .0
        .iter()
        .map(|word| u32::from_le_bytes(*word))
        .collect()
}

/// Every defined function's words, keyed by its C-level name (the Mach-O
/// leading underscore removed).
pub fn function_words(object: &[u8]) -> BTreeMap<String, Vec<u32>> {
    let mut functions = BTreeMap::new();
    if object.starts_with(b"\x7fELF") {
        let (shoff, shentsize, shnum) = (
            le64(object, 40),
            usize::from(le16(object, 58)),
            usize::from(le16(object, 60)),
        );
        let header = |index: usize| {
            assert!(index < shnum, "section index {index} out of range");
            shoff + index * shentsize
        };
        for index in 0..shnum {
            let symtab = header(index);
            if le32(object, symtab + 4) != 2 {
                continue; // not SHT_SYMTAB
            }
            let strtab = le64(object, header(le32(object, symtab + 40) as usize) + 24);
            let (offset, size, entsize) = (
                le64(object, symtab + 24),
                le64(object, symtab + 32),
                le64(object, symtab + 56),
            );
            for entry in (offset..offset + size).step_by(entsize) {
                if object[entry + 4] & 0xF != 2 {
                    continue; // not STT_FUNC
                }
                let section = header(usize::from(le16(object, entry + 6)));
                let start = le64(object, section + 24) + le64(object, entry + 8);
                let name = cstr(object, strtab + le32(object, entry) as usize).to_string();
                let code = code_words(&object[start..start + le64(object, entry + 16)]);
                assert!(
                    functions.insert(name, code).is_none(),
                    "duplicate ELF function"
                );
            }
        }
        return functions;
    }
    assert_eq!(le32(object, 0), 0xFEED_FACF, "MH_MAGIC_64");
    let (mut text, mut symtab, mut ordinal, mut at) = (None, None, 0u8, 32);
    for _ in 0..le32(object, 16) {
        match le32(object, at) {
            0x19 => {
                for index in 0..le32(object, at + 64) as usize {
                    let section = at + 72 + index * 80;
                    ordinal += 1;
                    if cstr(&object[section..section + 16], 0) == "__text"
                        && cstr(&object[section + 16..section + 32], 0) == "__TEXT"
                    {
                        text = Some((
                            ordinal,
                            le64(object, section + 32),
                            le64(object, section + 40),
                            le32(object, section + 48) as usize,
                        ));
                    }
                }
            }
            0x2 => {
                symtab = Some((
                    le32(object, at + 8) as usize,
                    le32(object, at + 12) as usize,
                    le32(object, at + 16) as usize,
                ));
            }
            _ => {}
        }
        at += le32(object, at + 4) as usize;
    }
    let (text_ordinal, text_addr, text_size, text_offset) = text.expect("__TEXT,__text");
    let (symoff, nsyms, stroff) = symtab.expect("LC_SYMTAB");
    // Every N_SECT symbol in __text (no stabs) bounds an extent; only the
    // external ones name a function.
    let mut starts: Vec<(usize, bool, String)> = (0..nsyms)
        .filter_map(|index| {
            let entry = symoff + index * 16;
            let n_type = object[entry + 4];
            (n_type & 0xE0 == 0 && n_type & 0x0E == 0x0E && object[entry + 5] == text_ordinal).then(
                || {
                    let name = cstr(object, stroff + le32(object, entry) as usize);
                    (
                        le64(object, entry + 8) - text_addr,
                        n_type & 0x01 != 0,
                        name.strip_prefix('_').unwrap_or(name).to_string(),
                    )
                },
            )
        })
        .collect();
    starts.sort();
    for (index, (start, external, name)) in starts.iter().enumerate() {
        if !external {
            continue;
        }
        let end = starts.get(index + 1).map_or(text_size, |(next, ..)| *next);
        let code = code_words(&object[text_offset + start..text_offset + end]);
        assert!(
            functions.insert(name.clone(), code).is_none(),
            "duplicate Mach-O function"
        );
    }
    functions
}
