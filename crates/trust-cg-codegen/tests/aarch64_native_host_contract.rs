// Copyright 2026 Andrew Yates | Apache-2.0
//! Contract for `common/native_host.rs`, the host facts every AArch64 native
//! link-and-run control shares: the Darwin assembly translation, the object
//! container checks and the independent code-section reader. Pure object and
//! text checks; they run on every host and grant no native-execution credit.

#[path = "common/native_host.rs"]
mod native_host;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::{
    BinOp, Block, BlockId, Endianness, FuncId, FuncTy, Function, Inst, InstrNode, Module,
    StructPassingPolicy, TargetInfo, Ty, ValueId,
};

#[test]
fn darwin_translation_prefixes_globals_and_drops_elf_only_directives() {
    let source = ".text\n.p2align 2\n.global f1\n.type f1,%function\nf1:\nmov x9,x1; bl f1\n\
                  .global f1_word\nf1_word:\n.inst 0x8b010000\nadd x0,x0,#f1_word\nret\n\
                  .size f1,.-f1\n.section .note.GNU-stack,\"\",%progbits\n";
    assert_eq!(
        native_host::darwin_assembly(source),
        ".text\n.p2align 2\n.globl _f1\n_f1:\nmov x9,x1\nbl _f1\n.globl _f1_word\n\
         _f1_word:\n.inst 0x8b010000\nadd x0,x0,#f1_word\nret\n"
    );
}

#[test]
fn darwin_translation_leaves_local_labels_and_comments_intact() {
    let source = ".global g\ng:\nloop:\nb loop // g stays a comment; not split\nret\n";
    assert_eq!(
        native_host::darwin_assembly(source),
        ".globl _g\n_g:\nloop:\nb loop // g stays a comment; not split\nret\n"
    );
}

#[test]
fn host_arm_is_identity_on_linux_and_the_darwin_translation_on_macos() {
    let source = ".global h\n.type h,%function\nh:\nret\n.size h,.-h\n";
    let host = native_host::assembly(source);
    if native_host::DARWIN {
        assert_eq!(host, native_host::darwin_assembly(source));
    } else {
        assert_eq!(host, source);
    }
    assert_eq!(
        native_host::NATIVE,
        native_host::LINUX_GNU || native_host::DARWIN
    );
    assert_eq!(
        native_host::c_symbol("h"),
        if native_host::DARWIN { "_h" } else { "h" }
    );
}

#[test]
#[should_panic(expected = "spelled like a register")]
fn darwin_translation_rejects_register_spelled_globals() {
    native_host::darwin_assembly(".global x9\nx9:\nret\n");
}

#[test]
#[should_panic(expected = "ELF-only operator")]
fn darwin_translation_rejects_elf_relocation_operators() {
    native_host::darwin_assembly(".global f\nf:\nadd x0,x0,:lo12:f\nret\n");
}

#[test]
#[should_panic(expected = "no mapping for ELF section")]
fn darwin_translation_rejects_unknown_sections() {
    native_host::darwin_assembly(".section .init_array,\"aw\"\n");
}

#[test]
#[should_panic(expected = "ambiguous")]
fn darwin_translation_rejects_separators_inside_quoted_operands() {
    native_host::darwin_assembly(".ascii \"a;b\"\n");
}

fn add_module(triple: &str) -> Module {
    let mut module = Module::new("native_host_contract");
    module.target_info = Some(TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    let ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "native_host_add", ty, BlockId::new(0));
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn compile(triple: &str) -> Vec<u8> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O2,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple).unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&add_module(triple))
    .unwrap()
    .object_code
}

/// `add x0, x0, x1` then `ret`, located by the independent section readers
/// in both containers regardless of host.
#[test]
fn independent_code_readers_find_the_same_words_in_elf_and_macho() {
    const ADD_X0_X0_X1: u32 = 0x8b01_0000;
    const RET: u32 = 0xd65f_03c0;
    let elf = compile("aarch64-unknown-linux-gnu");
    let macho = compile("aarch64-apple-darwin");
    native_host::assert_elf_aarch64_object(&elf);
    native_host::assert_macho_arm64_object(&macho);
    for object in [&elf, &macho] {
        let words = native_host::text_words(object);
        assert!(words.contains(&ADD_X0_X0_X1), "{words:08x?}");
        assert!(words.contains(&RET), "{words:08x?}");
    }
    native_host::assert_native_object(&compile(native_host::TRIPLE));
}

fn u16_at(bytes: &[u8], at: usize) -> usize {
    usize::from(u16::from_le_bytes(bytes[at..at + 2].try_into().unwrap()))
}

fn u32_at(bytes: &[u8], at: usize) -> usize {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap()) as usize
}

fn u64_at(bytes: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap())
}

fn c_string(bytes: &[u8], at: usize) -> &str {
    let tail = &bytes[at..];
    std::str::from_utf8(&tail[..tail.iter().position(|b| *b == 0).unwrap()]).unwrap()
}

/// `(st_info, st_shndx, st_value, st_size)` of ELF64 symbol `name` and the
/// section-header index of `.text`, read from the raw section/symbol tables.
fn elf_symbol(object: &[u8], name: &str) -> ((u8, usize, u64, u64), usize) {
    let table = usize::try_from(u64_at(object, 40)).unwrap();
    let (entry_size, count) = (u16_at(object, 58), u16_at(object, 60));
    let header = |index: usize| table + index * entry_size;
    let offset = |index: usize| usize::try_from(u64_at(object, header(index) + 24)).unwrap();
    let names = offset(u16_at(object, 62));
    let text = (0..count)
        .find(|index| c_string(object, names + u32_at(object, header(*index))) == ".text")
        .expect("ELF .text");
    // SHT_SYMTAB = 2; sh_link names its string table.
    let symtab = (0..count)
        .find(|index| u32_at(object, header(*index) + 4) == 2)
        .expect("ELF .symtab");
    let strings = offset(u32_at(object, header(symtab) + 40));
    let size = usize::try_from(u64_at(object, header(symtab) + 32)).unwrap();
    let mut found = None;
    for symbol in (offset(symtab)..offset(symtab) + size).step_by(24) {
        if c_string(object, strings + u32_at(object, symbol)) == name {
            assert!(found.is_none(), "duplicate ELF symbol {name}");
            found = Some((
                object[symbol + 4],
                u16_at(object, symbol + 6),
                u64_at(object, symbol + 8),
                u64_at(object, symbol + 16),
            ));
        }
    }
    (found.expect("ELF symbol missing"), text)
}

/// `(n_type, n_sect, n_value)` of Mach-O symbol `name` from LC_SYMTAB.
fn macho_symbol(object: &[u8], name: &str) -> (u8, u8, u64) {
    let mut cursor = 32;
    for _ in 0..u32_at(object, 16) {
        if u32_at(object, cursor) == 0x2 {
            let (symbols, count) = (u32_at(object, cursor + 8), u32_at(object, cursor + 12));
            let strings = u32_at(object, cursor + 16);
            let mut found = None;
            for symbol in (symbols..symbols + count * 16).step_by(16) {
                if c_string(object, strings + u32_at(object, symbol)) == name {
                    assert!(found.is_none(), "duplicate Mach-O symbol {name}");
                    found = Some((
                        object[symbol + 4],
                        object[symbol + 5],
                        u64_at(object, symbol + 8),
                    ));
                }
            }
            return found.expect("Mach-O symbol missing");
        }
        cursor += u32_at(object, cursor + 4);
    }
    panic!("Mach-O LC_SYMTAB missing")
}

/// The fixup-free function container used by the overflow link-run pins.
/// Its ELF arm executes only on Linux GNU, so both containers are checked
/// here, on every host, through the raw section and symbol tables: the exact
/// code words, and one defined, exported function symbol at offset zero
/// (ELF: STB_GLOBAL/STT_FUNC in `.text` with the code size; Mach-O: an
/// external N_SECT `_` symbol in section 1).
#[test]
fn naked_function_objects_export_the_exact_code_in_both_containers() {
    const CODE: [u32; 3] = [0x8b01_0000, 0xd503_201f, 0xd65f_03c0];
    let code: Vec<u8> = CODE.iter().flat_map(|word| word.to_le_bytes()).collect();
    let elf = native_host::naked_function_object_for("aarch64-unknown-linux-gnu", "naked", &code);
    native_host::assert_elf_aarch64_object(&elf);
    assert_eq!(native_host::text_words(&elf), CODE);
    let ((info, section, value, size), text) = elf_symbol(&elf, "naked");
    // (STB_GLOBAL << 4) | STT_FUNC.
    assert_eq!(info, 0x12, "ELF binding/type");
    assert_eq!((section, value, size), (text, 0, code.len() as u64));

    let macho = native_host::naked_function_object_for("aarch64-apple-darwin", "naked", &code);
    native_host::assert_macho_arm64_object(&macho);
    assert_eq!(native_host::text_words(&macho), CODE);
    // N_SECT (0x0e) | N_EXT (0x01), first section, offset zero.
    assert_eq!(macho_symbol(&macho, "_naked"), (0x0f, 1, 0));

    assert_eq!(
        native_host::naked_function_object("naked", &code),
        native_host::naked_function_object_for(native_host::TRIPLE, "naked", &code)
    );
}

#[test]
#[should_panic(expected = "no naked-function container")]
fn naked_function_object_refuses_an_unknown_triple() {
    native_host::naked_function_object_for("aarch64-unknown-linux-musl", "naked", &[0; 4]);
}

#[test]
#[should_panic(expected = "MH_MAGIC_64")]
fn macho_check_rejects_an_elf_object() {
    native_host::assert_macho_arm64_object(&compile("aarch64-unknown-linux-gnu"));
}

#[test]
#[should_panic(expected = "ELF magic")]
fn elf_check_rejects_a_macho_object() {
    native_host::assert_elf_aarch64_object(&compile("aarch64-apple-darwin"));
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
