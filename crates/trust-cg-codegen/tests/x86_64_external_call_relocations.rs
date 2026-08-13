// Regression tests for x86-64 ELF/Mach-O module CALL relocations.
//
// Part of #L36.

use trust_cg_codegen::elf::constants::{
    ELF64_RELA_SIZE, ELF64_SHDR_SIZE, ELF64_SYM_SIZE, R_X86_64_GOTPCREL, R_X86_64_PC32,
    R_X86_64_PLT32, SHN_UNDEF, SHT_RELA, SHT_SYMTAB, STB_GLOBAL, STT_FUNC, STT_NOTYPE, elf64_r_sym,
    elf64_r_type, elf64_st_bind, elf64_st_type,
};
use trust_cg_codegen::macho::constants as macho;
use trust_cg_codegen::macho::{X86_64RelocKind, decode_x86_64_relocation};
use trust_cg_codegen::x86_64::pipeline::X86RegAllocMode;
use trust_cg_codegen::x86_64::{X86OutputFormat, X86Pipeline, X86PipelineConfig, X86PipelineError};
use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_lower::function::Signature;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst, X86ISelOperand};

#[derive(Debug)]
struct ElfSection {
    name: String,
    sh_type: u32,
    offset: usize,
    size: usize,
    link: usize,
}

#[derive(Debug)]
struct ElfSymbolRecord {
    name: String,
    info: u8,
    section: u16,
}

#[derive(Debug)]
struct ElfRelaRecord {
    offset: u64,
    symbol_index: u32,
    reloc_type: u32,
    addend: i64,
}

#[derive(Debug)]
struct ParsedElf {
    symbols: Vec<ElfSymbolRecord>,
    text_relocations: Vec<ElfRelaRecord>,
}

#[derive(Debug)]
struct MachSymbolRecord {
    name: String,
    n_type: u8,
    section: u8,
}

#[derive(Debug)]
struct ParsedMachO {
    symbols: Vec<MachSymbolRecord>,
    text_relocations: Vec<trust_cg_codegen::macho::X86_64Relocation>,
}

fn module_pipeline(output_format: X86OutputFormat) -> X86Pipeline {
    X86Pipeline::new(X86PipelineConfig {
        output_format,
        opt_level: trust_cg_opt::OptLevel::O0,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Simplified,
        ..X86PipelineConfig::default()
    })
}

fn minimal_function(name: &str) -> X86ISelFunction {
    let mut func = X86ISelFunction::new(
        name.to_string(),
        Signature {
            params: vec![],
            returns: vec![],
        },
    );
    func.ensure_block(Block(0));
    func
}

fn caller_function(callee: &str) -> X86ISelFunction {
    let mut func = minimal_function("caller");
    func.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::Call,
            vec![X86ISelOperand::Symbol(callee.to_string())],
        ),
    );
    func.push_inst(Block(0), X86ISelInst::new(X86Opcode::Ret, vec![]));
    func
}

fn global_ref_function(symbol: &str) -> X86ISelFunction {
    let mut func = minimal_function("materialize");
    let dst = VReg::new(0, RegClass::Gpr64);
    func.next_vreg = 1;
    func.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::LeaRip,
            vec![
                X86ISelOperand::VReg(dst),
                X86ISelOperand::Symbol(symbol.to_string()),
            ],
        ),
    );
    func.push_inst(Block(0), X86ISelInst::new(X86Opcode::Ret, vec![]));
    func
}

fn extern_ref_function(symbol: &str) -> X86ISelFunction {
    let mut func = minimal_function("materialize_extern");
    let dst = VReg::new(0, RegClass::Gpr64);
    func.next_vreg = 1;
    func.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::MovRipRel,
            vec![
                X86ISelOperand::VReg(dst),
                X86ISelOperand::Symbol(symbol.to_string()),
            ],
        ),
    );
    func.push_inst(Block(0), X86ISelInst::new(X86Opcode::Ret, vec![]));
    func
}

fn return_function(name: &str) -> X86ISelFunction {
    let mut func = minimal_function(name);
    func.push_inst(Block(0), X86ISelInst::new(X86Opcode::Ret, vec![]));
    func
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

fn read_i64(bytes: &[u8], offset: usize) -> i64 {
    i64::from_le_bytes([
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

fn cstring(bytes: &[u8], offset: usize) -> String {
    let end = bytes[offset..]
        .iter()
        .position(|&byte| byte == 0)
        .map(|delta| offset + delta)
        .unwrap_or(bytes.len());
    String::from_utf8_lossy(&bytes[offset..end]).into_owned()
}

fn name16(bytes: &[u8], offset: usize) -> String {
    let raw = &bytes[offset..offset + 16];
    let end = raw.iter().position(|&byte| byte == 0).unwrap_or(16);
    String::from_utf8_lossy(&raw[..end]).into_owned()
}

fn parse_elf(bytes: &[u8]) -> ParsedElf {
    assert_eq!(&bytes[0..4], &[0x7f, b'E', b'L', b'F']);

    let shoff = read_u64(bytes, 40) as usize;
    let shnum = read_u16(bytes, 60) as usize;
    let shstrndx = read_u16(bytes, 62) as usize;
    let shstr = shoff + shstrndx * ELF64_SHDR_SIZE;
    let shstr_offset = read_u64(bytes, shstr + 24) as usize;

    let mut sections = Vec::new();
    for index in 0..shnum {
        let sh = shoff + index * ELF64_SHDR_SIZE;
        let name_offset = shstr_offset + read_u32(bytes, sh) as usize;
        sections.push(ElfSection {
            name: cstring(bytes, name_offset),
            sh_type: read_u32(bytes, sh + 4),
            offset: read_u64(bytes, sh + 24) as usize,
            size: read_u64(bytes, sh + 32) as usize,
            link: read_u32(bytes, sh + 40) as usize,
        });
    }

    let symtab = sections
        .iter()
        .find(|section| section.sh_type == SHT_SYMTAB)
        .expect("ELF object should contain .symtab");
    let strtab = &sections[symtab.link];
    let mut symbols = Vec::new();
    for index in 0..symtab.size / ELF64_SYM_SIZE {
        let sym = symtab.offset + index * ELF64_SYM_SIZE;
        let name_offset = read_u32(bytes, sym) as usize;
        symbols.push(ElfSymbolRecord {
            name: if name_offset == 0 {
                String::new()
            } else {
                cstring(bytes, strtab.offset + name_offset)
            },
            info: bytes[sym + 4],
            section: read_u16(bytes, sym + 6),
        });
    }

    let rela_text = sections
        .iter()
        .find(|section| section.name == ".rela.text" && section.sh_type == SHT_RELA)
        .expect("ELF object should contain .rela.text");
    let mut text_relocations = Vec::new();
    for index in 0..rela_text.size / ELF64_RELA_SIZE {
        let rela = rela_text.offset + index * ELF64_RELA_SIZE;
        let info = read_u64(bytes, rela + 8);
        text_relocations.push(ElfRelaRecord {
            offset: read_u64(bytes, rela),
            symbol_index: elf64_r_sym(info),
            reloc_type: elf64_r_type(info),
            addend: read_i64(bytes, rela + 16),
        });
    }

    ParsedElf {
        symbols,
        text_relocations,
    }
}

fn parse_macho(bytes: &[u8]) -> ParsedMachO {
    assert_eq!(read_u32(bytes, 0), macho::MH_MAGIC_64);
    assert_eq!(read_u32(bytes, 4), macho::CPU_TYPE_X86_64);

    let ncmds = read_u32(bytes, 16) as usize;
    let mut offset = macho::MACH_HEADER_64_SIZE as usize;
    let mut symoff = 0usize;
    let mut nsyms = 0usize;
    let mut stroff = 0usize;
    let mut text_reloff = 0usize;
    let mut text_nreloc = 0usize;

    for _ in 0..ncmds {
        let cmd = read_u32(bytes, offset);
        let cmdsize = read_u32(bytes, offset + 4) as usize;
        match cmd {
            macho::LC_SEGMENT_64 => {
                let nsects = read_u32(bytes, offset + 64) as usize;
                let mut section_offset = offset + macho::SEGMENT_COMMAND_64_SIZE as usize;
                for _ in 0..nsects {
                    if name16(bytes, section_offset) == "__text" {
                        text_reloff = read_u32(bytes, section_offset + 56) as usize;
                        text_nreloc = read_u32(bytes, section_offset + 60) as usize;
                    }
                    section_offset += macho::SECTION_64_SIZE as usize;
                }
            }
            macho::LC_SYMTAB => {
                symoff = read_u32(bytes, offset + 8) as usize;
                nsyms = read_u32(bytes, offset + 12) as usize;
                stroff = read_u32(bytes, offset + 16) as usize;
            }
            _ => {}
        }
        offset += cmdsize;
    }

    let mut symbols = Vec::new();
    for index in 0..nsyms {
        let sym = symoff + index * macho::NLIST_64_SIZE as usize;
        let name_offset = read_u32(bytes, sym) as usize;
        symbols.push(MachSymbolRecord {
            name: if name_offset == 0 {
                String::new()
            } else {
                cstring(bytes, stroff + name_offset)
            },
            n_type: bytes[sym + 4],
            section: bytes[sym + 5],
        });
    }

    let mut text_relocations = Vec::new();
    for index in 0..text_nreloc {
        let reloc = text_reloff + index * macho::RELOCATION_INFO_SIZE as usize;
        let reloc_bytes: [u8; 8] = bytes[reloc..reloc + 8]
            .try_into()
            .expect("relocation entry should be 8 bytes");
        text_relocations
            .push(decode_x86_64_relocation(&reloc_bytes).expect("decode x86-64 Mach-O relocation"));
    }

    ParsedMachO {
        symbols,
        text_relocations,
    }
}

fn symbol_index_elf(parsed: &ParsedElf, name: &str) -> usize {
    parsed
        .symbols
        .iter()
        .position(|symbol| symbol.name == name)
        .unwrap_or_else(|| panic!("missing ELF symbol {name}; symbols={:?}", parsed.symbols))
}

fn symbol_index_macho(parsed: &ParsedMachO, name: &str) -> usize {
    parsed
        .symbols
        .iter()
        .position(|symbol| symbol.name == name)
        .unwrap_or_else(|| panic!("missing Mach-O symbol {name}; symbols={:?}", parsed.symbols))
}

#[test]
fn elf_module_external_direct_call_emits_undefined_plt32_relocation() {
    let caller = caller_function("external_callee");
    let bytes = module_pipeline(X86OutputFormat::Elf)
        .compile_module(&[caller])
        .expect("ELF module should compile with undefined external call relocation");
    let parsed = parse_elf(&bytes);

    let external_index = symbol_index_elf(&parsed, "external_callee");
    let external = &parsed.symbols[external_index];
    assert_eq!(external.section, SHN_UNDEF);
    assert_eq!(elf64_st_bind(external.info), STB_GLOBAL);
    assert_eq!(elf64_st_type(external.info), STT_FUNC);

    assert!(
        parsed.text_relocations.iter().any(|reloc| {
            reloc.offset == 1
                && reloc.symbol_index as usize == external_index
                && reloc.reloc_type == R_X86_64_PLT32
                && reloc.addend == -4
        }),
        "expected .rela.text PLT32 relocation to external_callee, got {:?}",
        parsed.text_relocations
    );
}

#[test]
fn elf_module_intra_module_direct_call_targets_defined_callee() {
    let caller = caller_function("callee");
    let callee = return_function("callee");
    let bytes = module_pipeline(X86OutputFormat::Elf)
        .compile_module(&[caller, callee])
        .expect("ELF module should compile with in-module call relocation");
    let parsed = parse_elf(&bytes);

    let callee_index = symbol_index_elf(&parsed, "callee");
    assert_ne!(parsed.symbols[callee_index].section, SHN_UNDEF);
    assert!(
        parsed.text_relocations.iter().any(|reloc| {
            reloc.symbol_index as usize == callee_index
                && reloc.reloc_type == R_X86_64_PLT32
                && reloc.addend == -4
        }),
        "expected .rela.text PLT32 relocation to defined callee, got {:?}",
        parsed.text_relocations
    );
}

#[test]
fn elf_module_global_ref_to_defined_symbol_emits_pc32_relocation() {
    let materialize = global_ref_function("callee");
    let callee = return_function("callee");
    let bytes = module_pipeline(X86OutputFormat::Elf)
        .compile_module(&[materialize, callee])
        .expect("ELF module should compile with in-module GlobalRef relocation");
    let parsed = parse_elf(&bytes);

    let callee_index = symbol_index_elf(&parsed, "callee");
    assert!(
        parsed.text_relocations.iter().any(|reloc| {
            reloc.offset == 3
                && reloc.symbol_index as usize == callee_index
                && reloc.reloc_type == R_X86_64_PC32
                && reloc.addend == -4
        }),
        "expected .rela.text PC32 relocation to defined callee, got {:?}",
        parsed.text_relocations
    );
}

#[test]
fn elf_module_global_ref_to_missing_symbol_fails_closed() {
    let materialize = global_ref_function("missing");
    let err = module_pipeline(X86OutputFormat::Elf)
        .compile_module(&[materialize])
        .expect_err("ELF GlobalRef to an undefined symbol must fail closed");

    match err {
        X86PipelineError::GlobalRefUnsupported {
            function, symbol, ..
        } => {
            assert_eq!(function, "materialize");
            assert_eq!(symbol, "missing");
        }
        other => panic!("expected GlobalRefUnsupported, got {other:?}"),
    }
}

#[test]
fn elf_module_extern_ref_emits_gotpcrel_relocation_to_undefined_symbol() {
    let materialize = extern_ref_function("external_data");
    let bytes = module_pipeline(X86OutputFormat::Elf)
        .compile_module(&[materialize])
        .expect("ELF module should compile ExternRef GOTPCREL relocation");
    let parsed = parse_elf(&bytes);

    let external_index = symbol_index_elf(&parsed, "external_data");
    let external = &parsed.symbols[external_index];
    assert_eq!(external.section, SHN_UNDEF);
    assert_eq!(elf64_st_bind(external.info), STB_GLOBAL);
    assert_eq!(elf64_st_type(external.info), STT_NOTYPE);

    assert!(
        parsed.text_relocations.iter().any(|reloc| {
            reloc.offset == 3
                && reloc.symbol_index as usize == external_index
                && reloc.reloc_type == R_X86_64_GOTPCREL
                && reloc.addend == -4
        }),
        "expected .rela.text GOTPCREL relocation to external_data, got {:?}",
        parsed.text_relocations
    );
}

#[test]
fn raw_module_symbol_address_leaves_zero_disp32_placeholder() {
    // RawBytes is non-linkable output (used by tests and by the x86-64
    // code-size probe in `Compiler::compile_x86_64`). It now tolerates
    // symbol-address (`GlobalRef` / `ExternRef`) RIP-relative sites exactly
    // like it already tolerates CALL `rel32`: the 4-byte displacement is left
    // as a zero placeholder rather than rejected. The real relocations are
    // emitted only by the linkable MachO / ELF / COFF module paths.
    for materialize in [
        global_ref_function("external_data"),
        extern_ref_function("external_data"),
    ] {
        let bytes = module_pipeline(X86OutputFormat::RawBytes)
            .compile_module(&[materialize])
            .expect("raw x86 module emission tolerates symbol-address placeholders");
        assert!(
            !bytes.is_empty(),
            "raw module should still emit the encoded code bytes"
        );
        // The RIP-relative disp32 occupies the last 4 bytes of the
        // materialization instruction, followed by the RET (0xC3). The disp32
        // must be a zero placeholder (no in-place relocation in RawBytes).
        let ret_pos = bytes
            .iter()
            .rposition(|&b| b == 0xC3)
            .expect("encoded function should end with RET");
        assert!(ret_pos >= 4, "instruction stream too short for a disp32");
        assert_eq!(
            &bytes[ret_pos - 4..ret_pos],
            &[0u8; 4],
            "symbol-address disp32 should be a zero placeholder in RawBytes"
        );
    }
}

#[test]
fn macho_module_external_direct_call_emits_undefined_branch_relocation() {
    let caller = caller_function("external_callee");
    let bytes = module_pipeline(X86OutputFormat::MachO)
        .compile_module(&[caller])
        .expect("Mach-O module should compile with undefined external call relocation");
    let parsed = parse_macho(&bytes);

    let external_index = symbol_index_macho(&parsed, "_external_callee");
    let external = &parsed.symbols[external_index];
    assert_eq!(external.n_type, macho::N_UNDF | macho::N_EXT);
    assert_eq!(external.section, 0);

    assert!(
        parsed.text_relocations.iter().any(|reloc| {
            reloc.offset == 1
                && reloc.symbol_index as usize == external_index
                && reloc.kind == X86_64RelocKind::Branch
                && reloc.is_extern
                && reloc.pc_relative
                && reloc.length == 2
        }),
        "expected __text BRANCH relocation to _external_callee, got {:?}",
        parsed.text_relocations
    );
}

#[test]
fn macho_module_global_ref_to_defined_symbol_emits_signed_relocation() {
    let materialize = global_ref_function("callee");
    let callee = return_function("callee");
    let bytes = module_pipeline(X86OutputFormat::MachO)
        .compile_module(&[materialize, callee])
        .expect("Mach-O module should compile with in-module GlobalRef relocation");
    let parsed = parse_macho(&bytes);

    let callee_index = symbol_index_macho(&parsed, "_callee");
    assert!(
        parsed.text_relocations.iter().any(|reloc| {
            reloc.offset == 3
                && reloc.symbol_index as usize == callee_index
                && reloc.kind == X86_64RelocKind::Signed
                && reloc.is_extern
                && reloc.pc_relative
                && reloc.length == 2
        }),
        "expected __text SIGNED relocation to defined _callee, got {:?}",
        parsed.text_relocations
    );
}

#[test]
fn macho_module_extern_ref_emits_got_load_relocation_to_undefined_symbol() {
    let materialize = extern_ref_function("external_data");
    let bytes = module_pipeline(X86OutputFormat::MachO)
        .compile_module(&[materialize])
        .expect("Mach-O module should compile ExternRef GOT_LOAD relocation");
    let parsed = parse_macho(&bytes);

    let external_index = symbol_index_macho(&parsed, "_external_data");
    let external = &parsed.symbols[external_index];
    assert_eq!(external.n_type, macho::N_UNDF | macho::N_EXT);
    assert_eq!(external.section, 0);

    assert!(
        parsed.text_relocations.iter().any(|reloc| {
            reloc.offset == 3
                && reloc.symbol_index as usize == external_index
                && reloc.kind == X86_64RelocKind::GotLoad
                && reloc.is_extern
                && reloc.pc_relative
                && reloc.length == 2
        }),
        "expected __text GOT_LOAD relocation to _external_data, got {:?}",
        parsed.text_relocations
    );
}

#[test]
fn macho_module_intra_module_direct_call_targets_defined_callee() {
    let caller = caller_function("callee");
    let callee = return_function("callee");
    let bytes = module_pipeline(X86OutputFormat::MachO)
        .compile_module(&[caller, callee])
        .expect("Mach-O module should compile with in-module call relocation");
    let parsed = parse_macho(&bytes);

    let callee_index = symbol_index_macho(&parsed, "_callee");
    let callee = &parsed.symbols[callee_index];
    assert_eq!(callee.n_type, macho::N_SECT | macho::N_EXT);
    assert_ne!(callee.section, 0);
    assert!(
        parsed.text_relocations.iter().any(|reloc| {
            reloc.symbol_index as usize == callee_index
                && reloc.kind == X86_64RelocKind::Branch
                && reloc.is_extern
                && reloc.pc_relative
                && reloc.length == 2
        }),
        "expected __text BRANCH relocation to defined _callee, got {:?}",
        parsed.text_relocations
    );
}
