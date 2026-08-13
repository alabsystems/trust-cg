// trust-cg-codegen/tests/e2e_x86_64_windows_host_objects.rs
//
// Windows-host x86-64 cross-object proof tests. These tests intentionally use
// no external linker, objdump, otool, readelf, nm, or platform SDK tools.

use trust_cg_codegen::elf::constants::*;
use trust_cg_codegen::macho::constants::*;
use trust_cg_codegen::x86_64::{
    build_x86_add_test_function, build_x86_const_test_function, x86_compile_to_elf,
    x86_compile_to_macho,
};

fn windows_x86_64_host() -> bool {
    cfg!(all(target_os = "windows", target_arch = "x86_64"))
}

fn read_u16(bytes: &[u8], offset: usize) -> u16 {
    u16::from_le_bytes([bytes[offset], bytes[offset + 1]])
}

fn read_u32(bytes: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes([
        bytes[offset],
        bytes[offset + 1],
        bytes[offset + 2],
        bytes[offset + 3],
    ])
}

fn read_u64(bytes: &[u8], offset: usize) -> u64 {
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

#[derive(Debug)]
struct ElfSection {
    name: String,
    sh_type: u32,
    flags: u64,
    offset: usize,
    size: usize,
    link: u32,
    entsize: u64,
}

#[derive(Debug)]
struct ElfSymbol {
    name: String,
    info: u8,
    section_index: u16,
    value: u64,
    size: u64,
}

fn c_string(bytes: &[u8], start: usize) -> String {
    if start >= bytes.len() {
        return String::new();
    }
    let end = bytes[start..]
        .iter()
        .position(|&b| b == 0)
        .map(|pos| start + pos)
        .unwrap_or(bytes.len());
    String::from_utf8_lossy(&bytes[start..end]).into_owned()
}

fn elf_sections(bytes: &[u8]) -> Vec<ElfSection> {
    assert!(
        bytes.len() >= ELF64_EHDR_SIZE,
        "ELF object too small: {} bytes",
        bytes.len()
    );
    let sh_offset = read_u64(bytes, 40) as usize;
    let sh_entsize = read_u16(bytes, 58) as usize;
    let sh_num = read_u16(bytes, 60) as usize;
    let sh_str_index = read_u16(bytes, 62) as usize;

    assert_eq!(sh_entsize, ELF64_SHDR_SIZE, "ELF section entry size");
    assert!(sh_num > sh_str_index, "ELF shstrndx must name a section");
    assert!(
        sh_offset + sh_num * sh_entsize <= bytes.len(),
        "ELF section headers must fit in object"
    );

    let shstr = sh_offset + sh_str_index * sh_entsize;
    let shstr_offset = read_u64(bytes, shstr + 24) as usize;
    let shstr_size = read_u64(bytes, shstr + 32) as usize;
    assert!(
        shstr_offset + shstr_size <= bytes.len(),
        "ELF section-name table must fit in object"
    );

    let mut sections = Vec::with_capacity(sh_num);
    for index in 0..sh_num {
        let section = sh_offset + index * sh_entsize;
        let name_offset = read_u32(bytes, section) as usize;
        let name = if name_offset < shstr_size {
            c_string(bytes, shstr_offset + name_offset)
        } else {
            String::new()
        };
        sections.push(ElfSection {
            name,
            sh_type: read_u32(bytes, section + 4),
            flags: read_u64(bytes, section + 8),
            offset: read_u64(bytes, section + 24) as usize,
            size: read_u64(bytes, section + 32) as usize,
            link: read_u32(bytes, section + 40),
            entsize: read_u64(bytes, section + 56),
        });
    }
    sections
}

fn elf_symbols(bytes: &[u8], sections: &[ElfSection]) -> Vec<ElfSymbol> {
    let symtab = sections
        .iter()
        .find(|section| section.sh_type == SHT_SYMTAB)
        .expect("ELF .symtab section must exist");
    assert_eq!(symtab.entsize, ELF64_SYM_SIZE as u64, "ELF symbol size");
    assert!(
        symtab.offset + symtab.size <= bytes.len(),
        "ELF .symtab must fit in object"
    );

    let strtab = sections
        .get(symtab.link as usize)
        .expect("ELF .symtab link must point at string table");
    assert_eq!(strtab.sh_type, SHT_STRTAB, "ELF symbol strings type");
    assert!(
        strtab.offset + strtab.size <= bytes.len(),
        "ELF symbol string table must fit in object"
    );

    let mut symbols = Vec::new();
    for symbol_offset in (symtab.offset..symtab.offset + symtab.size).step_by(ELF64_SYM_SIZE) {
        let name_offset = read_u32(bytes, symbol_offset) as usize;
        if name_offset == 0 {
            continue;
        }
        symbols.push(ElfSymbol {
            name: c_string(bytes, strtab.offset + name_offset),
            info: bytes[symbol_offset + 4],
            section_index: read_u16(bytes, symbol_offset + 6),
            value: read_u64(bytes, symbol_offset + 8),
            size: read_u64(bytes, symbol_offset + 16),
        });
    }
    symbols
}

fn assert_linux_elf_x86_64_object(bytes: &[u8], symbol: &str) {
    assert_eq!(&bytes[0..4], &[ELFMAG0, ELFMAG1, ELFMAG2, ELFMAG3]);
    assert_eq!(bytes[4], ELFCLASS64, "ELF class");
    assert_eq!(bytes[5], ELFDATA2LSB, "ELF endianness");
    assert_eq!(bytes[6], EV_CURRENT, "ELF ident version");
    assert_eq!(read_u16(bytes, 16), ET_REL, "ELF file type");
    assert_eq!(read_u16(bytes, 18), EM_X86_64, "ELF machine");
    assert_eq!(
        read_u16(bytes, 52),
        ELF64_EHDR_SIZE as u16,
        "ELF header size"
    );

    let sections = elf_sections(bytes);
    let text = sections
        .iter()
        .find(|section| section.name == ".text")
        .expect("ELF .text section must exist");
    assert_eq!(text.sh_type, SHT_PROGBITS, "ELF .text type");
    assert_ne!(text.flags & SHF_ALLOC, 0, "ELF .text must be allocatable");
    assert_ne!(
        text.flags & SHF_EXECINSTR,
        0,
        "ELF .text must be executable"
    );
    assert!(text.size > 0, "ELF .text must contain machine code");
    assert!(
        text.offset + text.size <= bytes.len(),
        "ELF .text must fit in object"
    );
    assert!(
        bytes[text.offset..text.offset + text.size].contains(&0xC3),
        "ELF .text should contain x86-64 RET"
    );

    let found = elf_symbols(bytes, &sections)
        .into_iter()
        .find(|entry| entry.name == symbol)
        .unwrap_or_else(|| panic!("ELF symbol table must contain {symbol}"));
    assert_eq!(found.info >> 4, STB_GLOBAL, "ELF symbol binding");
    assert_eq!(found.info & 0x0F, STT_FUNC, "ELF symbol type");
    assert_ne!(
        found.section_index, SHN_UNDEF,
        "ELF function symbol must be defined"
    );
    assert!(
        found.size > 0,
        "ELF function symbol should cover emitted machine code"
    );
    assert_eq!(found.value, 0, "single-function ELF symbol starts at .text");
}

#[derive(Debug)]
struct MachOSection {
    sectname: String,
    segname: String,
    offset: usize,
    size: usize,
    align: u32,
    flags: u32,
}

#[derive(Debug)]
struct MachOSymbol {
    name: String,
    n_type: u8,
    n_sect: u8,
    value: u64,
}

fn fixed_string(bytes: &[u8]) -> String {
    let end = bytes.iter().position(|&b| b == 0).unwrap_or(bytes.len());
    String::from_utf8_lossy(&bytes[..end]).into_owned()
}

fn macho_sections(bytes: &[u8]) -> Vec<MachOSection> {
    let sizeofcmds = read_u32(bytes, 20) as usize;
    let mut offset = MACH_HEADER_64_SIZE as usize;
    let end = MACH_HEADER_64_SIZE as usize + sizeofcmds;
    assert!(
        end <= bytes.len(),
        "Mach-O load commands must fit in object"
    );

    let mut sections = Vec::new();
    while offset < end {
        assert!(offset + 8 <= end, "Mach-O load command header fits");
        let cmd = read_u32(bytes, offset);
        let cmdsize = read_u32(bytes, offset + 4) as usize;
        assert!(cmdsize >= 8, "Mach-O load command size is sane");
        assert!(offset + cmdsize <= end, "Mach-O load command fits");

        if cmd == LC_SEGMENT_64 {
            let nsects = read_u32(bytes, offset + 64) as usize;
            assert!(
                cmdsize >= SEGMENT_COMMAND_64_SIZE as usize + nsects * SECTION_64_SIZE as usize,
                "Mach-O segment command must include all section records"
            );
            let mut section_offset = offset + SEGMENT_COMMAND_64_SIZE as usize;
            for _ in 0..nsects {
                sections.push(MachOSection {
                    sectname: fixed_string(&bytes[section_offset..section_offset + 16]),
                    segname: fixed_string(&bytes[section_offset + 16..section_offset + 32]),
                    size: read_u64(bytes, section_offset + 40) as usize,
                    offset: read_u32(bytes, section_offset + 48) as usize,
                    align: read_u32(bytes, section_offset + 52),
                    flags: read_u32(bytes, section_offset + 64),
                });
                section_offset += SECTION_64_SIZE as usize;
            }
        }

        offset += cmdsize;
    }
    sections
}

fn macho_symbols(bytes: &[u8]) -> Vec<MachOSymbol> {
    let sizeofcmds = read_u32(bytes, 20) as usize;
    let mut offset = MACH_HEADER_64_SIZE as usize;
    let end = MACH_HEADER_64_SIZE as usize + sizeofcmds;

    while offset < end {
        let cmd = read_u32(bytes, offset);
        let cmdsize = read_u32(bytes, offset + 4) as usize;
        assert!(
            cmdsize >= 8 && offset + cmdsize <= end,
            "Mach-O load command fits"
        );
        if cmd == LC_SYMTAB {
            let symoff = read_u32(bytes, offset + 8) as usize;
            let nsyms = read_u32(bytes, offset + 12) as usize;
            let stroff = read_u32(bytes, offset + 16) as usize;
            let strsize = read_u32(bytes, offset + 20) as usize;
            assert!(
                symoff + nsyms * NLIST_64_SIZE as usize <= bytes.len(),
                "Mach-O symbol table must fit in object"
            );
            assert!(
                stroff + strsize <= bytes.len(),
                "Mach-O string table must fit in object"
            );

            let mut symbols = Vec::with_capacity(nsyms);
            for index in 0..nsyms {
                let symbol_offset = symoff + index * NLIST_64_SIZE as usize;
                let name_offset = read_u32(bytes, symbol_offset) as usize;
                symbols.push(MachOSymbol {
                    name: c_string(bytes, stroff + name_offset),
                    n_type: bytes[symbol_offset + 4],
                    n_sect: bytes[symbol_offset + 5],
                    value: read_u64(bytes, symbol_offset + 8),
                });
            }
            return symbols;
        }
        offset += cmdsize;
    }

    panic!("Mach-O LC_SYMTAB command must exist");
}

fn assert_macos_macho_x86_64_object(bytes: &[u8], symbol: &str) {
    assert!(
        bytes.len() >= MACH_HEADER_64_SIZE as usize,
        "Mach-O object too small: {} bytes",
        bytes.len()
    );
    assert_eq!(read_u32(bytes, 0), MH_MAGIC_64, "Mach-O magic");
    assert_eq!(read_u32(bytes, 4), CPU_TYPE_X86_64, "Mach-O CPU type");
    assert_eq!(
        read_u32(bytes, 8),
        CPU_SUBTYPE_X86_64_ALL,
        "Mach-O CPU subtype"
    );
    assert_eq!(read_u32(bytes, 12), MH_OBJECT, "Mach-O file type");
    assert!(read_u32(bytes, 16) >= 3, "Mach-O load command count");
    assert_ne!(
        read_u32(bytes, 24) & MH_SUBSECTIONS_VIA_SYMBOLS,
        0,
        "Mach-O subsection flag"
    );

    let text = macho_sections(bytes)
        .into_iter()
        .find(|section| section.segname == "__TEXT" && section.sectname == "__text")
        .expect("Mach-O __TEXT,__text section must exist");
    assert_eq!(text.align, 4, "Mach-O x86-64 text alignment");
    assert_ne!(
        text.flags & S_ATTR_PURE_INSTRUCTIONS,
        0,
        "Mach-O text must be pure instructions"
    );
    assert_ne!(
        text.flags & S_ATTR_SOME_INSTRUCTIONS,
        0,
        "Mach-O text must contain instructions"
    );
    assert!(text.size > 0, "Mach-O __text must contain machine code");
    assert!(
        text.offset + text.size <= bytes.len(),
        "Mach-O __text must fit in object"
    );
    assert!(
        bytes[text.offset..text.offset + text.size].contains(&0xC3),
        "Mach-O __text should contain x86-64 RET"
    );

    let found = macho_symbols(bytes)
        .into_iter()
        .find(|entry| entry.name == symbol)
        .unwrap_or_else(|| panic!("Mach-O symbol table must contain {symbol}"));
    assert_eq!(
        found.n_type,
        N_SECT | N_EXT,
        "Mach-O symbol must be external defined"
    );
    assert_eq!(found.n_sect, 1, "Mach-O function symbol section");
    assert_eq!(
        found.value, 0,
        "single-function Mach-O symbol starts at __text"
    );
}

#[test]
fn windows_x86_64_no_toolchain_emits_parseable_linux_elf_objects() {
    if !windows_x86_64_host() {
        eprintln!("SKIP: Windows x86-64 host proof test");
        return;
    }

    let cases = [
        ("const42", build_x86_const_test_function()),
        ("add", build_x86_add_test_function()),
    ];
    for (symbol, func) in cases {
        let bytes = x86_compile_to_elf(&func)
            .unwrap_or_else(|error| panic!("x86-64 ELF AOT compile failed for {symbol}: {error}"));
        assert_linux_elf_x86_64_object(&bytes, symbol);
    }
}

#[test]
fn windows_x86_64_no_toolchain_emits_parseable_macos_macho_objects() {
    if !windows_x86_64_host() {
        eprintln!("SKIP: Windows x86-64 host proof test");
        return;
    }

    let cases = [
        ("_const42", build_x86_const_test_function()),
        ("_add", build_x86_add_test_function()),
    ];
    for (symbol, func) in cases {
        let bytes = x86_compile_to_macho(&func).unwrap_or_else(|error| {
            panic!("x86-64 Mach-O AOT compile failed for {symbol}: {error}")
        });
        assert_macos_macho_x86_64_object(&bytes, symbol);
    }
}
