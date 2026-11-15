#![allow(dead_code)]
// trust-cg-codegen/tests/common/x86_64_object.rs - link-facing checks of emitted x86-64 objects
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The link-facing contract of an emitted x86-64 relocatable object, checked
//! without a linker: the container is the host's x86-64 object format (ELF
//! `ET_REL`/`EM_X86_64` off macOS, Mach-O `MH_OBJECT`/`CPU_TYPE_X86_64` on
//! macOS, matching what the x86-64 link/run tests emit), every function a C
//! driver calls is a defined global symbol, and every function the object calls
//! out to is an undefined reference. These are the object-inspection legs the
//! x86-64 link/run tests keep on hosts where
//! `common::rosetta::x86_64_link_run` finds no x86-64 driver.

use std::collections::BTreeSet;

const EM_X86_64: u16 = 62;
const ET_REL: u16 = 1;
const SHT_SYMTAB: u32 = 2;
const STB_GLOBAL: u8 = 1;
const STB_WEAK: u8 = 2;
const MH_MAGIC_64: u32 = 0xfeed_facf;
const CPU_TYPE_X86_64: u32 = 0x0100_0007;
const MH_OBJECT: u32 = 1;
const LC_SYMTAB: u32 = 0x2;
const N_STAB: u8 = 0xe0;
const N_TYPE: u8 = 0x0e;
const N_EXT: u8 = 0x01;
const N_UNDF: u8 = 0x0;
const N_SECT: u8 = 0xe;

/// The host's x86-64 relocatable format: Mach-O on macOS, ELF elsewhere.
pub const HOST_IS_MACHO: bool = cfg!(target_os = "macos");

/// The object-file spelling of the C function `name` in the host's x86-64
/// object format (Mach-O prefixes `_`; ELF uses the bare name).
pub fn host_c_symbol(name: &str) -> String {
    if HOST_IS_MACHO {
        format!("_{name}")
    } else {
        name.to_owned()
    }
}

/// The external symbols of an x86-64 relocatable object.
#[derive(Debug, Default)]
pub struct X86_64ObjectSymbols {
    /// Defined symbols with global (or weak) binding.
    pub defined_globals: BTreeSet<String>,
    /// Undefined references.
    pub undefined: BTreeSet<String>,
}

fn u16_at(bytes: &[u8], offset: usize) -> u16 {
    u16::from_le_bytes(bytes[offset..offset + 2].try_into().unwrap())
}

fn u32_at(bytes: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes(bytes[offset..offset + 4].try_into().unwrap())
}

fn u64_at(bytes: &[u8], offset: usize) -> usize {
    u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap()) as usize
}

fn c_string(bytes: &[u8], offset: usize) -> String {
    let end = bytes[offset..]
        .iter()
        .position(|&b| b == 0)
        .map(|len| offset + len)
        .expect("unterminated symbol name");
    String::from_utf8_lossy(&bytes[offset..end]).into_owned()
}

fn elf_symbols(label: &str, object: &[u8]) -> X86_64ObjectSymbols {
    assert!(object.len() >= 64, "{label}: ELF header truncated");
    assert_eq!(&object[..4], b"\x7fELF", "{label}: ELF magic");
    assert_eq!(
        &object[4..6],
        b"\x02\x01",
        "{label}: ELFCLASS64/ELFDATA2LSB"
    );
    assert_eq!(u16_at(object, 16), ET_REL, "{label}: ET_REL");
    assert_eq!(u16_at(object, 18), EM_X86_64, "{label}: EM_X86_64");
    let shoff = u64_at(object, 0x28);
    let shentsize = u16_at(object, 0x3a) as usize;
    let shnum = u16_at(object, 0x3c) as usize;
    assert!(shentsize >= 64, "{label}: ELF section header size");
    let section = |index: usize| shoff + index * shentsize;
    let mut symbols = X86_64ObjectSymbols::default();
    let mut symtabs = 0;
    for index in 0..shnum {
        let header = section(index);
        if u32_at(object, header + 4) != SHT_SYMTAB {
            continue;
        }
        symtabs += 1;
        let (offset, size, entsize) = (
            u64_at(object, header + 24),
            u64_at(object, header + 32),
            u64_at(object, header + 56),
        );
        assert_eq!(entsize, 24, "{label}: Elf64_Sym size");
        let strtab = u64_at(object, section(u32_at(object, header + 40) as usize) + 24);
        for sym in (offset..offset + size).step_by(entsize).skip(1) {
            let name = c_string(object, strtab + u32_at(object, sym) as usize);
            let binding = object[sym + 4] >> 4;
            let defined = u16_at(object, sym + 6) != 0;
            if name.is_empty() {
                continue;
            }
            if !defined {
                symbols.undefined.insert(name);
            } else if matches!(binding, STB_GLOBAL | STB_WEAK) {
                symbols.defined_globals.insert(name);
            }
        }
    }
    assert_eq!(symtabs, 1, "{label}: exactly one SHT_SYMTAB section");
    symbols
}

fn macho_symbols(label: &str, object: &[u8]) -> X86_64ObjectSymbols {
    assert!(object.len() >= 32, "{label}: Mach-O header truncated");
    assert_eq!(u32_at(object, 0), MH_MAGIC_64, "{label}: MH_MAGIC_64");
    assert_eq!(
        u32_at(object, 4),
        CPU_TYPE_X86_64,
        "{label}: CPU_TYPE_X86_64"
    );
    assert_eq!(u32_at(object, 12), MH_OBJECT, "{label}: MH_OBJECT");
    let ncmds = u32_at(object, 16) as usize;
    let mut command = 32;
    let mut symbols = X86_64ObjectSymbols::default();
    let mut symtabs = 0;
    for _ in 0..ncmds {
        let (cmd, cmdsize) = (
            u32_at(object, command),
            u32_at(object, command + 4) as usize,
        );
        assert!(cmdsize >= 8, "{label}: Mach-O load command size");
        if cmd == LC_SYMTAB {
            symtabs += 1;
            let symoff = u32_at(object, command + 8) as usize;
            let nsyms = u32_at(object, command + 12) as usize;
            let stroff = u32_at(object, command + 16) as usize;
            for index in 0..nsyms {
                let entry = symoff + index * 16;
                let n_type = object[entry + 4];
                if n_type & N_STAB != 0 || n_type & N_EXT == 0 {
                    continue;
                }
                let name = c_string(object, stroff + u32_at(object, entry) as usize);
                match n_type & N_TYPE {
                    N_UNDF => {
                        symbols.undefined.insert(name);
                    }
                    N_SECT => {
                        symbols.defined_globals.insert(name);
                    }
                    _ => {}
                }
            }
        }
        command += cmdsize;
    }
    assert_eq!(symtabs, 1, "{label}: exactly one LC_SYMTAB");
    symbols
}

/// Parse `object` as an x86-64 relocatable object in the given container
/// (Mach-O when `macho`, ELF otherwise), asserting its header, and return its
/// external symbols. Both arms are callable on every host.
pub fn x86_64_object_symbols(label: &str, object: &[u8], macho: bool) -> X86_64ObjectSymbols {
    if macho {
        macho_symbols(label, object)
    } else {
        elf_symbols(label, object)
    }
}

/// Parse `object` as the host's x86-64 relocatable object, asserting its
/// container, and return its external symbols.
pub fn host_x86_64_object_symbols(label: &str, object: &[u8]) -> X86_64ObjectSymbols {
    x86_64_object_symbols(label, object, HOST_IS_MACHO)
}

/// Assert the link-facing contract of an emitted object: it is the host's
/// x86-64 relocatable format, every C function in `defines` is a defined
/// global symbol, and every C function in `imports` is an undefined reference
/// (names are C-level; [`host_c_symbol`] spells them for the host format).
pub fn assert_host_x86_64_object(label: &str, object: &[u8], defines: &[&str], imports: &[&str]) {
    let symbols = host_x86_64_object_symbols(label, object);
    for name in defines {
        let symbol = host_c_symbol(name);
        assert!(
            symbols.defined_globals.contains(&symbol),
            "{label}: the emitted x86-64 object must define global `{symbol}` for the C driver; \
             defined globals: {:?}",
            symbols.defined_globals
        );
    }
    for name in imports {
        let symbol = host_c_symbol(name);
        assert!(
            symbols.undefined.contains(&symbol),
            "{label}: the emitted x86-64 object must reference `{symbol}` as undefined; \
             undefined: {:?}",
            symbols.undefined
        );
    }
}
