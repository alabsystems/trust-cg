// trust-cg-codegen/tests/e2e_aarch64_elf_stack_zero_fill.rs - AArch64 ELF
// non-executable-stack marker and SHT_NOBITS zero-fill placement.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Every AArch64 ELF emission route must carry one empty `.note.GNU-stack`
//! (GNU convention: `SHT_PROGBITS`, flags 0) and no BTI/PAC property note,
//! and writable all-zero definitions must occupy SHT_NOBITS `.bss` / `.tbss`
//! instead of file bytes. A zero-initialized COMDAT definition
//! (`LinkOnce`/`LinkOnceOdr`/`WeakOdr`) must occupy an SHT_NOBITS
//! `.bss.<sym>` / `.tbss.<sym>` member of its own `GRP_COMDAT` group.
//!
//! The object tests run on every host. An ELF64 reader written in this file
//! (independent of the writer and of the reparse gate) checks section headers,
//! symbols, relocation records and COMDAT group payloads; `llvm-readelf` or
//! `readelf` cross-checks the section and group tables when one is
//! installed. A mutation control shows the link-once oracle catches a
//! zero-fill member's type, `SHF_GROUP`/`SHF_TLS` flag, group payload or
//! binding flipped. On Linux AArch64 the native controls link WITHOUT
//! `-z noexecstack` and require `PT_GNU_STACK` RW (with an `-z execstack`
//! control proving the check detects RWE), dlopen a generated shared object,
//! and read/write a large zero global and zero TLS templates in three live
//! threads at O0-O3. Two objects that each define the same zero link-once
//! data and thread-local link into one executable that shares one instance
//! (one per thread for TLS) with the second copy's groups discarded; strong
//! twins fail to link. On glibc 2.41 or later the RWE control must also fail
//! to dlopen; an older glibc's load is recorded.
//!
//! trust-cg emits no BTI landing pads and no property note, and the link
//! driver refuses `-z force-bti` (`[TCG-LINK-BTI-PAC]`). The Linux controls
//! show why: GNU `readelf -n` finds no `NT_GNU_PROPERTY_TYPE_0` in any route
//! object (a compiler-made BTI/PAC object shows the check detects one), while
//! a direct `-z force-bti` link of a CG object succeeds with only a linker
//! warning naming it and marks the output BTI-compatible. The default link
//! runs the CG function through an indirect call; on a `bti` host the forced
//! executable's outcome (SIGILL or not) is recorded, not asserted. This is
//! object and execution evidence, not a proof.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use trust_cg_codegen::pipeline::{
    GlobalSymbolRef, ObjectGlobal, OptLevel, Pipeline, PipelineConfig,
};
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::value::GlobalId;
use trust_ir::{
    BinOp, Block, BlockId, Constant, Endianness, FuncId, FuncTy, Function, Global, Inst, InstrNode,
    Linkage, Module, StructPassingPolicy, TargetInfo, TlsModel, Ty, ValueId,
};

const TRIPLE: &str = "aarch64-unknown-linux-gnu";
const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
/// Size of the large zero-initialized global. Its file footprint must be 0.
const BIG: usize = 8 << 20;

const SHT_PROGBITS: u32 = 1;
const SHT_SYMTAB: u32 = 2;
const SHT_RELA: u32 = 4;
const SHT_NOTE: u32 = 7;
const SHT_NOBITS: u32 = 8;
const SHF_WRITE: u64 = 0x1;
const SHF_ALLOC: u64 = 0x2;
const SHF_EXECINSTR: u64 = 0x4;
const SHF_TLS: u64 = 0x400;
const STT_OBJECT: u8 = 1;
const STT_TLS: u8 = 6;

// --- independent little-endian ELF64 reader (fixed trusted test input) -----

fn u16le(b: &[u8], off: usize) -> u16 {
    u16::from_le_bytes(b[off..off + 2].try_into().unwrap())
}
fn u32le(b: &[u8], off: usize) -> u32 {
    u32::from_le_bytes(b[off..off + 4].try_into().unwrap())
}
fn u64le(b: &[u8], off: usize) -> u64 {
    u64::from_le_bytes(b[off..off + 8].try_into().unwrap())
}
fn cstr(b: &[u8], off: usize) -> String {
    let end = b[off..].iter().position(|&c| c == 0).unwrap() + off;
    String::from_utf8_lossy(&b[off..end]).into_owned()
}

#[derive(Clone, Debug)]
struct Section {
    name: String,
    sh_type: u32,
    flags: u64,
    offset: usize,
    size: u64,
    link: u32,
    info: u32,
    align: u64,
}

#[derive(Clone, Debug)]
struct Symbol {
    name: String,
    kind: u8,
    shndx: u16,
    value: u64,
    size: u64,
}

/// One relocation record, resolved to its target section and symbol names.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Reloc {
    section: String,
    offset: u64,
    kind: u32,
    symbol: String,
    addend: i64,
}

struct Elf {
    machine: u16,
    sections: Vec<Section>,
    symbols: Vec<Symbol>,
    relocs: Vec<Reloc>,
}

impl Elf {
    fn parse(obj: &[u8]) -> Elf {
        assert_eq!(&obj[..4], b"\x7fELF", "not an ELF object");
        assert_eq!((obj[4], obj[5]), (2, 1), "ELF64 little-endian");
        assert_eq!(u16le(obj, 16), 1, "ET_REL");
        let shoff = u64le(obj, 0x28) as usize;
        let shentsize = u16le(obj, 0x3a) as usize;
        let shnum = u16le(obj, 0x3c) as usize;
        let shstrndx = u16le(obj, 0x3e) as usize;
        assert_eq!(shentsize, 64);
        assert!(shoff + shnum * 64 <= obj.len(), "section headers in bounds");
        let shstr = u64le(obj, shoff + shstrndx * 64 + 0x18) as usize;
        let sections: Vec<Section> = (0..shnum)
            .map(|i| {
                let h = shoff + i * 64;
                Section {
                    name: cstr(obj, shstr + u32le(obj, h) as usize),
                    sh_type: u32le(obj, h + 4),
                    flags: u64le(obj, h + 8),
                    offset: u64le(obj, h + 0x18) as usize,
                    size: u64le(obj, h + 0x20),
                    link: u32le(obj, h + 0x28),
                    info: u32le(obj, h + 0x2c),
                    align: u64le(obj, h + 0x30),
                }
            })
            .collect();
        for section in &sections {
            if section.sh_type != SHT_NOBITS {
                assert!(
                    section.offset as u64 + section.size <= obj.len() as u64,
                    "{} file range in bounds",
                    section.name
                );
            }
        }
        let symtab = sections
            .iter()
            .find(|s| s.sh_type == SHT_SYMTAB)
            .expect("symbol table");
        let strtab = &sections[symtab.link as usize];
        let symbols: Vec<Symbol> = (0..symtab.size as usize / 24)
            .map(|k| {
                let e = symtab.offset + k * 24;
                Symbol {
                    name: cstr(obj, strtab.offset + u32le(obj, e) as usize),
                    kind: obj[e + 4] & 0xf,
                    shndx: u16le(obj, e + 6),
                    value: u64le(obj, e + 8),
                    size: u64le(obj, e + 16),
                }
            })
            .collect();
        let mut relocs = Vec::new();
        for rela in sections.iter().filter(|s| s.sh_type == SHT_RELA) {
            for k in 0..rela.size as usize / 24 {
                let e = rela.offset + k * 24;
                let info = u64le(obj, e + 8);
                relocs.push(Reloc {
                    section: sections[rela.info as usize].name.clone(),
                    offset: u64le(obj, e),
                    kind: info as u32,
                    symbol: symbols[(info >> 32) as usize].name.clone(),
                    addend: u64le(obj, e + 16) as i64,
                });
            }
        }
        relocs.sort();
        Elf {
            machine: u16le(obj, 18),
            sections,
            symbols,
            relocs,
        }
    }

    fn section(&self, name: &str) -> &Section {
        self.sections
            .iter()
            .find(|s| s.name == name)
            .unwrap_or_else(|| panic!("section {name} missing"))
    }

    fn section_index(&self, name: &str) -> u16 {
        self.sections.iter().position(|s| s.name == name).unwrap() as u16
    }

    fn symbol(&self, name: &str) -> &Symbol {
        self.symbols
            .iter()
            .find(|s| s.name == name)
            .unwrap_or_else(|| panic!("symbol {name} missing"))
    }
}

// --- external section-table cross-check -----------------------------------

/// An installed ELF reader: `llvm-readelf` (PATH or Homebrew LLVM) or GNU
/// `readelf`. `None` leaves the in-file reader as the only object evidence.
fn readelf_tool() -> Option<PathBuf> {
    [
        "llvm-readelf",
        "/opt/homebrew/opt/llvm/bin/llvm-readelf",
        "/usr/local/opt/llvm/bin/llvm-readelf",
        "readelf",
    ]
    .into_iter()
    .map(PathBuf::from)
    .find(|tool| {
        Command::new(tool)
            .arg("--version")
            .output()
            .is_ok_and(|output| output.status.success())
    })
}

fn readelf(tool: &Path, args: &[&str], file: &Path) -> String {
    let output = Command::new(tool)
        .args(args)
        .arg(file)
        .output()
        .unwrap_or_else(|error| panic!("{tool:?} {args:?} {file:?}: {error}"));
    assert!(
        output.status.success(),
        "{tool:?} {args:?} {file:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).into_owned()
}

/// `readelf -S -W` row for `name`: (type, size, flags, align) with the flag
/// letters column empty when the section has no flags.
fn readelf_section_row(listing: &str, name: &str) -> (String, u64, String, u64) {
    let row = listing
        .lines()
        .filter_map(|line| line.split_once(']').map(|(_, rest)| rest))
        .find(|rest| rest.split_whitespace().next() == Some(name))
        .unwrap_or_else(|| panic!("readelf section row for {name} missing:\n{listing}"));
    let fields: Vec<&str> = row.split_whitespace().collect();
    // name type address offset size entsize [flags] link info align
    let (flags, tail) = match fields.len() {
        9 => (String::new(), &fields[6..]),
        10 => (fields[6].to_owned(), &fields[7..]),
        _ => panic!("unexpected readelf section row {row:?}"),
    };
    (
        fields[1].to_owned(),
        u64::from_str_radix(fields[4], 16).unwrap(),
        flags,
        tail[2].parse().unwrap(),
    )
}

static SEQUENCE: AtomicU64 = AtomicU64::new(0);

/// A new directory owned by this test process; never another test's files.
fn scratch_dir(label: &str) -> PathBuf {
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "trust-cg-elf-stack-zero-{label}-{}-{stamp}-{}",
        std::process::id(),
        SEQUENCE.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&dir).unwrap();
    dir
}

// --- the object-level non-executable-stack contract --------------------------

/// Structural shape that identifies which ELF emitter produced an object.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Emitter {
    /// `emit_elf_with_function_symbols`: no relocations, no unwind tables.
    FunctionSymbols,
    /// `emit_aarch64_elf_with_supported_fixups`: relocations, no unwind tables.
    SupportedFixups,
    /// `emit_aarch64_elf_module_with_unwind`: `.eh_frame` present.
    ModuleWithUnwind,
}

fn emitter_of(elf: &Elf) -> Emitter {
    let has_unwind = elf.sections.iter().any(|s| s.name == ".eh_frame");
    let has_relocs = elf.sections.iter().any(|s| s.sh_type == SHT_RELA);
    match (has_unwind, has_relocs) {
        (true, _) => Emitter::ModuleWithUnwind,
        (false, true) => Emitter::SupportedFixups,
        (false, false) => Emitter::FunctionSymbols,
    }
}

/// Why `obj` violates the non-executable-stack contract, if it does.
fn stack_note_violation(obj: &[u8]) -> Option<String> {
    let elf = Elf::parse(obj);
    if elf.machine != 183 {
        return Some(format!("e_machine {} is not EM_AARCH64", elf.machine));
    }
    let notes: Vec<&Section> = elf
        .sections
        .iter()
        .filter(|s| s.name == ".note.GNU-stack")
        .collect();
    let [note] = notes.as_slice() else {
        return Some(format!("{} .note.GNU-stack sections", notes.len()));
    };
    if (note.sh_type, note.flags, note.size) != (SHT_PROGBITS, 0, 0) {
        return Some(format!(
            ".note.GNU-stack is type {} flags {:#x} size {}",
            note.sh_type, note.flags, note.size
        ));
    }
    // No BTI landing pads or PAC are emitted, so no property note may claim
    // them (or anything else).
    if let Some(note) = elf
        .sections
        .iter()
        .find(|s| s.sh_type == SHT_NOTE || s.name.starts_with(".note.gnu.property"))
    {
        return Some(format!("unexpected note section {}", note.name));
    }
    if let Some(exec) = elf
        .sections
        .iter()
        .find(|s| s.flags & SHF_EXECINSTR != 0 && s.name != ".text")
    {
        return Some(format!("non-text executable section {}", exec.name));
    }
    None
}

/// The first line of a `readelf -n` listing that shows a GNU note (a BTI/PAC
/// property note is `NT_GNU_PROPERTY_TYPE_0`), if any. The Linux native
/// control runs this predicate on a compiler-made BTI/PAC object to show it
/// detects a real property note.
fn readelf_notes_violation(listing: &str) -> Option<&str> {
    listing
        .lines()
        .find(|line| line.contains("GNU_PROPERTY") || line.contains("NT_GNU"))
}

fn assert_stack_note(route: &str, obj: &[u8], dir: &Path) {
    if let Some(violation) = stack_note_violation(obj) {
        panic!("{route}: {violation}");
    }
    if let Some(tool) = readelf_tool() {
        let path = dir.join(format!("{}.o", route.replace(['/', ' '], "_")));
        std::fs::write(&path, obj).unwrap();
        let listing = readelf(&tool, &["-S", "-W"], &path);
        let (kind, size, flags, _) = readelf_section_row(&listing, ".note.GNU-stack");
        assert_eq!(
            (kind.as_str(), size, flags.as_str()),
            ("PROGBITS", 0, ""),
            "{route}: {tool:?} row"
        );
        let notes = readelf(&tool, &["-n"], &path);
        assert_eq!(
            readelf_notes_violation(&notes),
            None,
            "{route}: unexpected ELF notes:\n{notes}"
        );
    }
}

fn pipeline(opt_level: OptLevel) -> Pipeline {
    Pipeline::new(PipelineConfig {
        target_triple: TRIPLE.to_owned(),
        opt_level,
        ..PipelineConfig::default()
    })
}

fn machine_function(name: &str, call: Option<&str>) -> trust_cg_ir::function::MachFunction {
    use trust_cg_ir::function::{MachFunction, Signature};
    use trust_cg_ir::inst::{AArch64Opcode, MachInst};
    use trust_cg_ir::operand::MachOperand;

    let mut function = MachFunction::new(name.to_owned(), Signature::new(vec![], vec![]));
    if let Some(callee) = call {
        // Save and restore the frame record around the call, as frame
        // lowering does: the final-stream frame net rejects a return through
        // the link register the BL clobbered.
        let frame_record = |opcode: AArch64Opcode, offset: i64| {
            MachInst::new(
                opcode,
                vec![
                    MachOperand::PReg(trust_cg_ir::aarch64_regs::X29),
                    MachOperand::PReg(trust_cg_ir::aarch64_regs::X30),
                    MachOperand::Special(trust_cg_ir::SpecialReg::SP),
                    MachOperand::Imm(offset),
                ],
            )
        };
        for inst in [
            frame_record(AArch64Opcode::StpPreIndex, -16),
            MachInst::new(
                AArch64Opcode::Bl,
                vec![MachOperand::Symbol(callee.to_owned())],
            ),
            frame_record(AArch64Opcode::LdpPostIndex, 16),
        ] {
            let id = function.push_inst(inst);
            function.append_inst(function.entry, id);
        }
    }
    let ret = function.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    function.append_inst(function.entry, ret);
    function
}

/// `fn name(x: i64) -> i64 { x + 1 }` in the lowering IR.
fn lower_function(name: &str) -> trust_cg_lower::function::Function {
    use trust_cg_lower::function::{BasicBlock, Function as LowerFunction, Signature};
    use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
    use trust_cg_lower::types::Type;

    let mut function = LowerFunction::new(
        name.to_owned(),
        Signature {
            params: vec![Type::I64],
            returns: vec![Type::I64],
        },
    );
    function.entry_block = Block(0);
    function.block_order = vec![Block(0)];
    function.blocks.insert(
        Block(0),
        BasicBlock {
            params: vec![(Value(0), Type::I64)],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Iconst {
                        ty: Type::I64,
                        imm: 1,
                    },
                    args: vec![],
                    results: vec![Value(1)],
                },
                Instruction {
                    opcode: Opcode::Iadd,
                    args: vec![Value(0), Value(1)],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(2)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    function
}

fn object_global(name: &str, data: Vec<u8>, align: u32) -> ObjectGlobal {
    ObjectGlobal {
        name: name.to_owned(),
        data,
        mutable: true,
        is_external: true,
        symbol_refs: vec![],
        is_thread_local: false,
        is_import: false,
        is_weak: false,
        align,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        section: None,
        comdat: false,
    }
}

/// One object from every public AArch64 ELF entry point, labeled with the
/// emitter its structure must show.
fn route_objects(opt: OptLevel) -> Vec<(String, Emitter, Vec<u8>)> {
    let p = pipeline(opt);
    let zero = object_global("route_zero", vec![0; 64], 16);
    let slot = ObjectGlobal {
        name: "route_slot".to_owned(),
        symbol_refs: vec![GlobalSymbolRef {
            offset: 0,
            symbol: "route_plain".to_owned(),
            addend: 0,
        }],
        ..object_global("route_slot", vec![0; 8], 8)
    };
    let (prepared, metrics) = p
        .prepare_function_with_metrics(&lower_function("route_prepared"), None)
        .unwrap();
    let layouts = [metrics.frame_layout.clone()];
    assert!(
        layouts[0].is_some(),
        "prepared functions carry a frame layout"
    );
    let mut objects = vec![
        (
            "compile_module".to_owned(),
            Emitter::FunctionSymbols,
            p.compile_module(&[machine_function("route_plain", None)])
                .unwrap(),
        ),
        (
            "compile_module_with_globals/zero".to_owned(),
            Emitter::FunctionSymbols,
            p.compile_module_with_globals(
                &[machine_function("route_plain", None)],
                std::slice::from_ref(&zero),
            )
            .unwrap(),
        ),
        (
            "compile_module_parallel_with_globals".to_owned(),
            Emitter::FunctionSymbols,
            p.compile_module_parallel_with_globals(
                &[
                    machine_function("route_plain", None),
                    machine_function("route_other", None),
                ],
                std::slice::from_ref(&zero),
            )
            .unwrap(),
        ),
        (
            "compile_module/text-fixup".to_owned(),
            Emitter::SupportedFixups,
            p.compile_module(&[machine_function("route_call", Some("printf"))])
                .unwrap(),
        ),
        (
            "compile_module_with_globals/data-fixup".to_owned(),
            Emitter::SupportedFixups,
            p.compile_module_with_globals(&[machine_function("route_plain", None)], &[slot, zero])
                .unwrap(),
        ),
        (
            "compile_module_with_globals_and_layouts".to_owned(),
            Emitter::ModuleWithUnwind,
            p.compile_module_with_globals_and_layouts(
                std::slice::from_ref(&prepared),
                &[],
                &layouts,
            )
            .unwrap(),
        ),
        (
            "compile_module_parallel_with_globals_and_layouts".to_owned(),
            Emitter::ModuleWithUnwind,
            p.compile_module_parallel_with_globals_and_layouts(&[prepared], &[], &layouts)
                .unwrap(),
        ),
        (
            "compile_function".to_owned(),
            Emitter::ModuleWithUnwind,
            p.compile_function(&lower_function("route_single")).unwrap(),
        ),
        (
            "encode_and_emit".to_owned(),
            Emitter::ModuleWithUnwind,
            p.encode_and_emit(&mut machine_function("route_encoded", None))
                .unwrap(),
        ),
        (
            "compile_ir_function".to_owned(),
            Emitter::ModuleWithUnwind,
            p.compile_ir_function(&mut machine_function("route_ir", None))
                .unwrap(),
        ),
    ];
    for tls in [false, true] {
        objects.push((
            format!("Compiler::compile/tls={tls}"),
            Emitter::ModuleWithUnwind,
            compile_zero_fill_module(opt, true, tls),
        ));
    }
    objects
}

#[test]
fn every_aarch64_elf_route_emits_one_nonexecutable_stack_note_and_no_property_note() {
    let dir = scratch_dir("routes");
    let mut emitters = Vec::new();
    for opt in OPT_LEVELS {
        for (route, expected, object) in route_objects(opt) {
            let route = format!("{route}/{opt:?}");
            let elf = Elf::parse(&object);
            assert_eq!(emitter_of(&elf), expected, "{route}: emitter shape");
            assert_stack_note(&route, &object, &dir);
            emitters.push(expected);
        }
    }
    for emitter in [
        Emitter::FunctionSymbols,
        Emitter::SupportedFixups,
        Emitter::ModuleWithUnwind,
    ] {
        assert!(emitters.contains(&emitter), "{emitter:?} route exercised");
    }
    std::fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn stack_note_oracle_rejects_missing_duplicate_flagged_and_property_mutations() {
    let object = pipeline(OptLevel::O0)
        .compile_module(&[machine_function("oracle_plain", None)])
        .unwrap();
    assert_eq!(stack_note_violation(&object), None);
    let elf = Elf::parse(&object);
    let shoff = u64le(&object, 0x28) as usize;
    let note = shoff + elf.section_index(".note.GNU-stack") as usize * 64;
    let text_name = u32le(&object, shoff + elf.section_index(".text") as usize * 64);
    let mutate = |edit: &dyn Fn(&mut Vec<u8>)| {
        let mut corrupt = object.clone();
        edit(&mut corrupt);
        stack_note_violation(&corrupt)
    };
    for (label, violation) in [
        // Renaming the marker to `.text` removes it.
        (
            "missing",
            mutate(&|b| b[note..note + 4].copy_from_slice(&text_name.to_le_bytes())),
        ),
        ("executable", mutate(&|b| b[note + 8] = SHF_EXECINSTR as u8)),
        ("note type", mutate(&|b| b[note + 4] = SHT_NOTE as u8)),
        ("nonempty", mutate(&|b| b[note + 0x20] = 1)),
    ] {
        assert!(violation.is_some(), "{label} mutation accepted");
    }

    // Structural mutations built through the writer: a second marker, a
    // property note (which would claim BTI/PAC), any other note, and an
    // executable non-text section must each be refused.
    let with_sections = |extra: &dyn Fn(&mut trust_cg_codegen::elf::ElfWriter)| {
        let mut writer =
            trust_cg_codegen::elf::ElfWriter::new(trust_cg_codegen::elf::ElfMachine::AArch64);
        writer.add_text_section(&0xd65f_03c0u32.to_le_bytes());
        writer.add_note_gnu_stack();
        extra(&mut writer);
        stack_note_violation(&writer.write_checked().unwrap())
    };
    assert_eq!(with_sections(&|_| {}), None, "writer-built control");
    for (label, violation) in [
        (
            "duplicate",
            with_sections(&|w| {
                w.add_note_gnu_stack();
            }),
        ),
        (
            "property note",
            with_sections(&|w| {
                w.add_section(".note.gnu.property", &[0; 32], SHT_NOTE, SHF_ALLOC, 8)
                    .unwrap();
            }),
        ),
        (
            "other note",
            with_sections(&|w| {
                w.add_section(".note.ABI-tag", &[0; 16], SHT_NOTE, SHF_ALLOC, 4)
                    .unwrap();
            }),
        ),
        (
            "executable data",
            with_sections(&|w| {
                w.add_section(
                    ".data",
                    &[0; 8],
                    SHT_PROGBITS,
                    SHF_ALLOC | SHF_WRITE | SHF_EXECINSTR,
                    8,
                )
                .unwrap();
            }),
        ),
    ] {
        assert!(violation.is_some(), "{label} mutation accepted");
    }
}

// --- zero-fill placement ---------------------------------------------------------

fn global_addr(global: u32, result: u32) -> InstrNode {
    InstrNode::new(Inst::GlobalAddr {
        global: GlobalId::new(global),
    })
    .with_result(ValueId::new(result))
}

fn ret(value: u32) -> InstrNode {
    InstrNode::new(Inst::Return {
        values: vec![ValueId::new(value)],
    })
}

/// `p = &global; v = *p + x; *p = v; return v` — CG's own load/store.
fn bump_body(global: u32) -> Vec<InstrNode> {
    vec![
        global_addr(global, 1),
        InstrNode::new(Inst::Load {
            ty: Ty::U64,
            ptr: ValueId::new(1),
            volatile: false,
            align: Some(8),
        })
        .with_result(ValueId::new(2)),
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U64,
            lhs: ValueId::new(2),
            rhs: ValueId::new(0),
        })
        .with_result(ValueId::new(3)),
        InstrNode::new(Inst::Store {
            ty: Ty::U64,
            ptr: ValueId::new(1),
            value: ValueId::new(3),
            volatile: false,
            align: Some(8),
        }),
        ret(3),
    ]
}

/// A `[u64; n]` initializer in trust-ir's one canonical array spelling
/// (SPEC_RATIFICATIONS §3.1): two or more equal elements are a splat.
fn u64_array(values: &[u64]) -> Constant {
    Constant::array(values.iter().map(|&v| Constant::Int(v.into())).collect())
}

/// The zero-fill fixture. With `zero == false` every zero initializer becomes
/// a nonzero one and the code is otherwise identical: the relocation and text
/// control for the placement change. `tls == false` drops the thread-locals
/// (local-exec TLS cannot be linked into a shared object).
///
/// Globals, in order: 0 `zf_big` (Internal, initializer-less, 8 MiB);
/// 1 `zf_counter` (Internal, initializer-less u64); 2 `zf_public_zero`
/// (External `[u64; 4]`, explicit zeros, align 64); 3 `zf_seed` (External,
/// initialized); 4 `zf_ro_zero` (External immutable zeros); 5 `zf_tls_zero`
/// (TLS `[u64; 4]`, zeros, align 128); 6 `zf_tls_init` (TLS, initialized).
fn zero_fill_module(zero: bool, tls: bool) -> Module {
    let mut module = Module::new("zero_fill");
    module.target_info = Some(TargetInfo {
        triple: TRIPLE.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    let byte = module
        .add_type(Ty::U8)
        .expect("Module::add_type: test fixture");
    let word = module
        .add_type(Ty::U64)
        .expect("Module::add_type: test fixture");
    let global = |name: &str, ty: Ty, initializer: Option<Constant>, linkage, align| Global {
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        name: name.into(),
        ty,
        mutable: true,
        initializer,
        linkage,
        tls: None,
        align,
    };
    let filled = |value: u64, count: usize| -> Constant {
        u64_array(&vec![if zero { 0 } else { value }; count])
    };
    module.globals = vec![
        global(
            "zf_big",
            Ty::Array(byte, BIG as u64),
            (!zero).then(|| Constant::splat(Constant::Int(0x5a), BIG as u64)),
            Linkage::Internal,
            None,
        ),
        global(
            "zf_counter",
            Ty::U64,
            (!zero).then_some(Constant::Int(0x77)),
            Linkage::Internal,
            None,
        ),
        global(
            "zf_public_zero",
            Ty::Array(word, 4),
            Some(filled(0x33, 4)),
            Linkage::External,
            Some(64),
        ),
        global(
            "zf_seed",
            Ty::U64,
            Some(Constant::Int(0x1234_5678)),
            Linkage::External,
            None,
        ),
        Global {
            mutable: false,
            ..global(
                "zf_ro_zero",
                Ty::Array(word, 2),
                Some(u64_array(&[0, 0])),
                Linkage::External,
                None,
            )
        },
    ];
    if tls {
        module.globals.push(Global {
            tls: Some(TlsModel::LocalExec),
            ..global(
                "zf_tls_zero",
                Ty::Array(word, 4),
                Some(filled(0x44, 4)),
                Linkage::External,
                Some(128),
            )
        });
        module.globals.push(Global {
            tls: Some(TlsModel::LocalExec),
            ..global(
                "zf_tls_init",
                Ty::Array(word, 2),
                Some(u64_array(&[0x1111_2222_3333_4444, 0x5555_6666_7777_8888])),
                Linkage::External,
                Some(64),
            )
        });
    }

    let address_signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let bump_signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut functions = vec![
        (
            "zf_big_addr",
            address_signature,
            vec![global_addr(0, 0), ret(0)],
        ),
        ("zf_counter_bump", bump_signature, bump_body(1)),
    ];
    if tls {
        // A public (preemptible) data symbol is addressed only from the
        // executable variant; shared objects need GOT access for it.
        functions.push((
            "zf_public_zero_addr",
            address_signature,
            vec![global_addr(2, 0), ret(0)],
        ));
        functions.push((
            "zf_tls_zero_addr",
            address_signature,
            vec![global_addr(5, 0), ret(0)],
        ));
        functions.push((
            "zf_tls_init_addr",
            address_signature,
            vec![global_addr(6, 0), ret(0)],
        ));
        functions.push(("zf_tls_bump", bump_signature, bump_body(5)));
    }
    for (index, (name, signature, body)) in functions.into_iter().enumerate() {
        let mut function =
            Function::new(FuncId::new(index as u32), name, signature, BlockId::new(0));
        function.linkage = Linkage::External;
        let params = if signature == bump_signature {
            vec![(ValueId::new(0), Ty::U64)]
        } else {
            vec![]
        };
        function.blocks = vec![Block {
            id: BlockId::new(0),
            params,
            body,
        }];
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
    }
    module
}

fn compile_zero_fill_module(opt: OptLevel, zero: bool, tls: bool) -> Vec<u8> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: opt,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(TRIPLE).unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&zero_fill_module(zero, tls))
    .unwrap_or_else(|error| panic!("zero-fill fixture must compile at {opt:?}: {error}"))
    .object_code
}

/// Expected (section, st_value, st_size, symbol type) for every data symbol.
const PLACEMENT: [(&str, &str, u64, u64, u8); 7] = [
    ("zf_big", ".bss", 0, BIG as u64, STT_OBJECT),
    ("zf_counter", ".bss", BIG as u64, 8, STT_OBJECT),
    ("zf_public_zero", ".bss", BIG as u64 + 64, 32, STT_OBJECT),
    ("zf_seed", ".data", 0, 8, STT_OBJECT),
    ("zf_ro_zero", ".rodata", 0, 16, STT_OBJECT),
    ("zf_tls_zero", ".tbss", 0, 32, STT_TLS),
    ("zf_tls_init", ".tdata", 0, 16, STT_TLS),
];

#[test]
fn zero_initialized_globals_and_tls_templates_use_nobits_without_file_bytes() {
    let dir = scratch_dir("nobits");
    let tool = readelf_tool();
    for opt in OPT_LEVELS {
        let object = compile_zero_fill_module(opt, true, true);
        let elf = Elf::parse(&object);
        assert!(
            object.len() < 64 << 10,
            "{opt:?}: an {BIG}-byte zero global inflated the object to {} bytes",
            object.len()
        );
        for (name, sh_type, flags, size, align) in [
            (
                ".bss",
                SHT_NOBITS,
                SHF_ALLOC | SHF_WRITE,
                BIG as u64 + 96,
                64,
            ),
            (
                ".tbss",
                SHT_NOBITS,
                SHF_ALLOC | SHF_WRITE | SHF_TLS,
                32,
                128,
            ),
            (
                ".tdata",
                SHT_PROGBITS,
                SHF_ALLOC | SHF_WRITE | SHF_TLS,
                16,
                64,
            ),
            (".data", SHT_PROGBITS, SHF_ALLOC | SHF_WRITE, 8, 8),
            (".rodata", SHT_PROGBITS, SHF_ALLOC, 16, 8),
        ] {
            let section = elf.section(name);
            assert_eq!(
                (section.sh_type, section.flags, section.size, section.align),
                (sh_type, flags, size, align),
                "{opt:?} {name}"
            );
        }
        for (symbol, section, value, size, kind) in PLACEMENT {
            let sym = elf.symbol(symbol);
            assert_eq!(
                (sym.shndx, sym.value, sym.size, sym.kind),
                (elf.section_index(section), value, size, kind),
                "{opt:?} {symbol}"
            );
        }
        let tdata = elf.section(".tdata");
        let template: Vec<u8> = [0x1111_2222_3333_4444u64, 0x5555_6666_7777_8888]
            .into_iter()
            .flat_map(u64::to_le_bytes)
            .collect();
        assert_eq!(&object[tdata.offset..tdata.offset + 16], template);
        let data = elf.section(".data");
        assert_eq!(
            &object[data.offset..data.offset + 8],
            0x1234_5678u64.to_le_bytes()
        );
        // No relocation may patch a zero-fill section.
        assert!(
            elf.relocs
                .iter()
                .all(|reloc| reloc.section != ".bss" && reloc.section != ".tbss"),
            "{opt:?}: {:?}",
            elf.relocs
        );

        // Control: the same code with nonzero initializers places the data in
        // PROGBITS, and the relocation records and text bytes are unchanged —
        // the placement moved bytes, not the relocation inventory.
        let control = compile_zero_fill_module(opt, false, true);
        let control_elf = Elf::parse(&control);
        assert!(control.len() > BIG, "control carries its initialized bytes");
        assert!(
            control_elf.sections.iter().all(|s| s.sh_type != SHT_NOBITS),
            "nonzero initializers must stay PROGBITS"
        );
        assert_eq!(control_elf.relocs, elf.relocs, "{opt:?} relocation records");
        let text = |bytes: &[u8], elf: &Elf| {
            let text = elf.section(".text");
            bytes[text.offset..text.offset + text.size as usize].to_vec()
        };
        assert_eq!(
            text(&control, &control_elf),
            text(&object, &elf),
            "{opt:?} text"
        );
        let zero_tls = control_elf.symbol("zf_tls_zero");
        assert_eq!(
            (zero_tls.shndx, zero_tls.kind),
            (control_elf.section_index(".tdata"), STT_TLS)
        );

        if let Some(tool) = &tool {
            let path = dir.join(format!("zero-fill-{opt:?}.o"));
            std::fs::write(&path, &object).unwrap();
            let listing = readelf(tool, &["-S", "-W"], &path);
            for (name, kind, size, flags, align) in [
                (".bss", "NOBITS", BIG as u64 + 96, "WA", 64),
                (".tbss", "NOBITS", 32, "WAT", 128),
                (".tdata", "PROGBITS", 16, "WAT", 64),
            ] {
                assert_eq!(
                    readelf_section_row(&listing, name),
                    (kind.to_owned(), size, flags.to_owned(), align),
                    "{opt:?} {tool:?} {name}"
                );
            }
        }
    }
    std::fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn zero_fill_placement_keeps_relocated_slots_and_constants_in_progbits() {
    let p = pipeline(OptLevel::O2);
    let slot = ObjectGlobal {
        symbol_refs: vec![GlobalSymbolRef {
            offset: 8,
            symbol: "slot_target".to_owned(),
            addend: 16,
        }],
        ..object_global("slot_table", vec![0; 16], 16)
    };
    let constant = ObjectGlobal {
        mutable: false,
        ..object_global("zero_constant", vec![0; 24], 8)
    };
    let retained = ObjectGlobal {
        retained: true,
        ..object_global("retained_zero", vec![0; 40], 8)
    };
    let object = p
        .compile_module_with_globals(
            &[machine_function("slot_target", None)],
            &[slot, constant, retained],
        )
        .unwrap();
    let elf = Elf::parse(&object);
    assert_eq!(emitter_of(&elf), Emitter::SupportedFixups);
    // The retained zero fill is alone in its own `.bss.retained_zero`, as
    // llc places an `@llvm.used` global, so `SHF_GNU_RETAIN` keeps nothing
    // else.
    for (name, section, size) in [
        ("slot_table", ".data", 16),
        ("zero_constant", ".rodata", 24),
        ("retained_zero", ".bss.retained_zero", 40),
    ] {
        let sym = elf.symbol(name);
        assert_eq!(
            (sym.shndx, sym.size),
            (elf.section_index(section), size),
            "{name}"
        );
    }
    let data = elf.section(".data");
    assert_eq!(data.sh_type, SHT_PROGBITS);
    assert_eq!(
        elf.relocs,
        [Reloc {
            section: ".data".to_owned(),
            offset: 8,
            kind: 257, // R_AARCH64_ABS64
            symbol: "slot_target".to_owned(),
            addend: 16,
        }]
    );
    let bss = elf.section(".bss.retained_zero");
    assert_eq!(bss.sh_type, SHT_NOBITS);
    assert_eq!(
        bss.flags,
        SHF_ALLOC | SHF_WRITE | 0x20_0000, // SHF_GNU_RETAIN on the retained zero-fill
    );
    assert_eq!(object[7], 3, "SHF_GNU_RETAIN selects ELFOSABI_GNU");
}

/// Adversarial control for the zero-fill planner's import exclusion. An
/// import has no bytes, so it is vacuously all-zero and has no pointer slot:
/// a planner that dropped the import check would give a mutable data or TLS
/// import a zero-size `.bss` / `.tbss` DEFINITION that shadows or collides
/// with the real provider at link time. Both object emitters must keep every
/// import undefined, and zero-fill must hold only real definitions.
#[test]
fn zero_fill_placement_never_turns_an_import_into_a_definition() {
    let import = |name: &str, is_thread_local: bool| ObjectGlobal {
        is_import: true,
        is_thread_local,
        ..object_global(name, vec![], 8)
    };
    let plain = vec![
        import("ext_counter", false),
        import("ext_tls", true),
        object_global("own_zero", vec![0; 24], 8),
    ];
    let mut with_slot = plain.clone();
    with_slot.push(ObjectGlobal {
        symbol_refs: vec![GlobalSymbolRef {
            offset: 0,
            symbol: "ext_counter".to_owned(),
            addend: 0,
        }],
        ..object_global("ext_slot", vec![0; 8], 8)
    });
    let p = pipeline(OptLevel::O0);
    for (label, globals, emitter) in [
        ("function-symbols", &plain, Emitter::FunctionSymbols),
        ("supported-fixups", &with_slot, Emitter::SupportedFixups),
    ] {
        let object = p
            .compile_module_with_globals(&[machine_function("import_user", None)], globals)
            .unwrap_or_else(|error| panic!("{label}: {error}"));
        let elf = Elf::parse(&object);
        assert_eq!(emitter_of(&elf), emitter, "{label}: emitter shape");
        let own = elf.symbol("own_zero");
        assert_eq!(
            (own.shndx, own.value, own.size),
            (elf.section_index(".bss"), 0, 24),
            "{label}: the real zero definition"
        );
        assert_eq!(elf.section(".bss").size, 24, "{label}: .bss contents");
        assert!(
            elf.sections.iter().all(|s| s.name != ".tbss"),
            "{label}: a TLS import must not define a .tbss template"
        );
        for name in ["ext_counter", "ext_tls"] {
            assert!(
                elf.symbols
                    .iter()
                    .filter(|symbol| symbol.name == name)
                    .all(|symbol| symbol.shndx == 0),
                "{label}: import {name} must stay undefined: {:?}",
                elf.symbols
            );
        }
        if emitter == Emitter::SupportedFixups {
            assert_eq!(elf.symbol("ext_counter").shndx, 0);
            assert_eq!(elf.symbol("ext_tls").kind, STT_TLS);
            assert_eq!(
                elf.relocs,
                [Reloc {
                    section: ".data".to_owned(),
                    offset: 0,
                    kind: 257, // R_AARCH64_ABS64
                    symbol: "ext_counter".to_owned(),
                    addend: 0,
                }]
            );
        }
    }
}

// --- COMDAT (link-once) zero-fill ------------------------------------------------

/// Size of the link-once zero global. Its file footprint must be 0.
const LO_BIG: usize = 4 << 20;
const SHT_GROUP: u32 = 17;
const SHF_GROUP: u64 = 0x200;
const GRP_COMDAT: u32 = 1;
const STB_WEAK: u8 = 2;
const LO_SEED: u64 = 0x5eed_0000_0000_1234;
const LO_TLS_SEED: [u64; 2] = [0x7157_0000_0000_0001, 0x7157_0000_0000_0002];
/// The three COMDAT linkages; each makes a `GRP_COMDAT` definition.
const COMDAT_LINKAGES: [Linkage; 3] = [Linkage::LinkOnce, Linkage::LinkOnceOdr, Linkage::WeakOdr];

/// Each COMDAT group of `obj`: (signature symbol, flag word, member section
/// names), read by the independent reader.
fn comdat_groups(obj: &[u8], elf: &Elf) -> Vec<(String, u32, Vec<String>)> {
    elf.sections
        .iter()
        .filter(|section| section.sh_type == SHT_GROUP)
        .map(|section| {
            let words: Vec<u32> = (0..section.size as usize / 4)
                .map(|word| u32le(obj, section.offset + word * 4))
                .collect();
            (
                elf.symbols[section.info as usize].name.clone(),
                words[0],
                words[1..]
                    .iter()
                    .map(|&member| {
                        elf.sections
                            .get(member as usize)
                            .map_or_else(|| format!("#{member}"), |s| s.name.clone())
                    })
                    .collect(),
            )
        })
        .collect()
}

/// One translation unit of the link-once zero-fill fixture, defining the
/// shared COMDAT data under `linkage` and its own `lo_<unit>_*` accessors.
/// With `zero == false` every zero initializer becomes nonzero and the code
/// is otherwise identical.
///
/// Globals, in order: 0 `lo_big` (`[u8; LO_BIG]`, zeros, align 4096);
/// 1 `lo_counter` (u64 zero); 2 `lo_tls` (TLS `[u64; 4]` zeros, align 64);
/// 3 `lo_seed` (u64 `LO_SEED`, the nonzero twin); 4 `lo_tls_seed` (TLS
/// `[u64; 2]` `LO_TLS_SEED`, the nonzero TLS twin).
fn link_once_unit(unit: &str, linkage: Linkage, zero: bool) -> Module {
    let mut module = Module::new(format!("link_once_{unit}"));
    module.target_info = Some(TargetInfo {
        triple: TRIPLE.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    let byte = module
        .add_type(Ty::U8)
        .expect("Module::add_type: test fixture");
    let word = module
        .add_type(Ty::U64)
        .expect("Module::add_type: test fixture");
    let global = |name: &str, ty: Ty, initializer: Constant, align| Global {
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        name: name.into(),
        ty,
        mutable: true,
        initializer: Some(initializer),
        linkage,
        tls: None,
        align,
    };
    let fill = |value: u64| if zero { 0 } else { value };
    module.globals = vec![
        global(
            "lo_big",
            Ty::Array(byte, LO_BIG as u64),
            Constant::splat(Constant::Int(fill(0x5a).into()), LO_BIG as u64),
            Some(4096),
        ),
        global(
            "lo_counter",
            Ty::U64,
            Constant::Int(fill(0x77).into()),
            None,
        ),
        Global {
            tls: Some(TlsModel::LocalExec),
            ..global(
                "lo_tls",
                Ty::Array(word, 4),
                u64_array(&[fill(0x44); 4]),
                Some(64),
            )
        },
        global("lo_seed", Ty::U64, Constant::Int(LO_SEED.into()), None),
        Global {
            tls: Some(TlsModel::LocalExec),
            ..global(
                "lo_tls_seed",
                Ty::Array(word, 2),
                u64_array(&LO_TLS_SEED),
                Some(16),
            )
        },
    ];
    let address_signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let bump_signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let load_signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let load_body = |global: u32| {
        vec![
            global_addr(global, 0),
            InstrNode::new(Inst::Load {
                ty: Ty::U64,
                ptr: ValueId::new(0),
                volatile: false,
                align: Some(8),
            })
            .with_result(ValueId::new(1)),
            ret(1),
        ]
    };
    let functions = [
        (
            "big_addr",
            address_signature,
            vec![global_addr(0, 0), ret(0)],
        ),
        (
            "counter_addr",
            address_signature,
            vec![global_addr(1, 0), ret(0)],
        ),
        ("counter_bump", bump_signature, bump_body(1)),
        (
            "tls_addr",
            address_signature,
            vec![global_addr(2, 0), ret(0)],
        ),
        ("tls_bump", bump_signature, bump_body(2)),
        ("seed", load_signature, load_body(3)),
        (
            "tls_seed_addr",
            address_signature,
            vec![global_addr(4, 0), ret(0)],
        ),
    ];
    for (index, (name, signature, body)) in functions.into_iter().enumerate() {
        let mut function = Function::new(
            FuncId::new(index as u32),
            format!("lo_{unit}_{name}"),
            signature,
            BlockId::new(0),
        );
        function.linkage = Linkage::External;
        let params = if signature == bump_signature {
            vec![(ValueId::new(0), Ty::U64)]
        } else {
            vec![]
        };
        function.blocks = vec![Block {
            id: BlockId::new(0),
            params,
            body,
        }];
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
    }
    module
}

fn compile_link_once_unit(opt: OptLevel, unit: &str, linkage: Linkage, zero: bool) -> Vec<u8> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: opt,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(TRIPLE).unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&link_once_unit(unit, linkage, zero))
    .unwrap_or_else(|error| {
        panic!("link-once fixture {unit} ({linkage:?}) must compile at {opt:?}: {error}")
    })
    .object_code
}

/// Expected (symbol, own section, sh_type, sh_flags, size, align, symbol
/// type) of every link-once definition in a zero-initialized unit.
const LINK_ONCE_PLACEMENT: [(&str, &str, u32, u64, u64, u64, u8); 5] = [
    (
        "lo_big",
        ".bss.lo_big",
        SHT_NOBITS,
        SHF_ALLOC | SHF_WRITE | SHF_GROUP,
        LO_BIG as u64,
        4096,
        STT_OBJECT,
    ),
    (
        "lo_counter",
        ".bss.lo_counter",
        SHT_NOBITS,
        SHF_ALLOC | SHF_WRITE | SHF_GROUP,
        8,
        8,
        STT_OBJECT,
    ),
    (
        "lo_tls",
        ".tbss.lo_tls",
        SHT_NOBITS,
        SHF_ALLOC | SHF_WRITE | SHF_TLS | SHF_GROUP,
        32,
        64,
        STT_TLS,
    ),
    (
        "lo_seed",
        ".data.lo_seed",
        SHT_PROGBITS,
        SHF_ALLOC | SHF_WRITE | SHF_GROUP,
        8,
        8,
        STT_OBJECT,
    ),
    (
        "lo_tls_seed",
        ".tdata.lo_tls_seed",
        SHT_PROGBITS,
        SHF_ALLOC | SHF_WRITE | SHF_TLS | SHF_GROUP,
        16,
        16,
        STT_TLS,
    ),
];

/// Every way a link-once unit's object departs from the COMDAT zero-fill
/// contract, read with the independent reader: each definition in its own
/// section of the expected type, flags, size and alignment; each section
/// the sole member of a `GRP_COMDAT` group signed by its `STB_WEAK` symbol;
/// no ungrouped section carrying `SHF_GROUP` and no relocation into
/// zero-fill; the nonzero twins holding their bytes; and no file bytes for
/// the zero fill. Empty for a faithful object.
fn link_once_violations(obj: &[u8]) -> Vec<String> {
    let elf = Elf::parse(obj);
    let mut violations = Vec::new();
    if obj.len() >= 64 << 10 {
        violations.push(format!("object is {} bytes", obj.len()));
    }
    let groups = comdat_groups(obj, &elf);
    for (symbol, section, sh_type, flags, size, align, kind) in LINK_ONCE_PLACEMENT {
        let Some(index) = elf.sections.iter().position(|s| s.name == section) else {
            violations.push(format!("{section} missing"));
            continue;
        };
        let header = &elf.sections[index];
        if (header.sh_type, header.flags, header.size, header.align)
            != (sh_type, flags, size, align)
        {
            violations.push(format!("{section} header {header:?}"));
        }
        let sym = elf.symbol(symbol);
        let bind = elf_symbol_bind(obj, &elf, symbol);
        if (sym.shndx as usize, sym.value, sym.size, sym.kind, bind)
            != (index, 0, size, kind, STB_WEAK)
        {
            violations.push(format!("{symbol} symbol {sym:?} bind {bind}"));
        }
        let signed: Vec<_> = groups.iter().filter(|(sig, ..)| sig == symbol).collect();
        if signed.len() != 1 || signed[0].1 != GRP_COMDAT || signed[0].2 != [section.to_owned()] {
            violations.push(format!("{symbol} group {signed:?}"));
        }
    }
    if groups.len() != LINK_ONCE_PLACEMENT.len() {
        violations.push(format!("groups {groups:?}"));
    }
    for section in &elf.sections {
        let member = groups
            .iter()
            .any(|(_, _, members)| members.contains(&section.name));
        if (section.flags & SHF_GROUP != 0) != member {
            violations.push(format!("{} SHF_GROUP vs membership {member}", section.name));
        }
    }
    for reloc in &elf.relocs {
        if elf.section(&reloc.section).sh_type == SHT_NOBITS {
            violations.push(format!("relocation into zero fill {reloc:?}"));
        }
    }
    if let Some(seed) = elf.sections.iter().find(|s| s.name == ".data.lo_seed")
        && seed.sh_type == SHT_PROGBITS
        && obj.get(seed.offset..seed.offset + 8) != Some(&LO_SEED.to_le_bytes()[..])
    {
        violations.push(".data.lo_seed bytes".to_owned());
    }
    if let Some(seed) = elf.sections.iter().find(|s| s.name == ".tdata.lo_tls_seed") {
        let want: Vec<u8> = LO_TLS_SEED.iter().flat_map(|v| v.to_le_bytes()).collect();
        if seed.sh_type == SHT_PROGBITS && obj.get(seed.offset..seed.offset + 16) != Some(&want[..])
        {
            violations.push(".tdata.lo_tls_seed bytes".to_owned());
        }
    }
    violations
}

/// `STB_*` binding of `name` (the reader keeps only the type nibble).
fn elf_symbol_bind(obj: &[u8], elf: &Elf, name: &str) -> u8 {
    let symtab = elf
        .sections
        .iter()
        .find(|s| s.sh_type == SHT_SYMTAB)
        .unwrap();
    let index = elf.symbols.iter().position(|s| s.name == name).unwrap();
    obj[symtab.offset + index * 24 + 4] >> 4
}

/// Zero-initialized link-once, link-once-ODR and weak-ODR definitions are
/// `SHT_NOBITS` `.bss.<sym>` / `.tbss.<sym>` members of their own COMDAT
/// group at O0-O3: an independent reader (and an installed readelf) sees no
/// file bytes, the type, flags, size and alignment, the `STB_WEAK`/`STT_TLS`
/// symbols, and each group's single member. The nonzero twins stay PROGBITS
/// with their bytes. Control: the same units with nonzero initializers put
/// every definition in a PROGBITS group member, with identical text and
/// relocation records.
#[test]
fn zero_link_once_globals_and_tls_templates_are_grouped_nobits_without_file_bytes() {
    let dir = scratch_dir("link-once-nobits");
    let tool = readelf_tool();
    for linkage in COMDAT_LINKAGES {
        for opt in OPT_LEVELS {
            let object = compile_link_once_unit(opt, "a", linkage, true);
            assert_eq!(
                link_once_violations(&object),
                Vec::<String>::new(),
                "{linkage:?} {opt:?}"
            );
            let elf = Elf::parse(&object);
            assert!(
                elf.sections
                    .iter()
                    .all(|s| s.name != ".bss" && s.name != ".tbss" && s.name != ".data"),
                "{linkage:?} {opt:?}: COMDAT data leaves the shared sections empty"
            );

            let control = compile_link_once_unit(opt, "a", linkage, false);
            let control_elf = Elf::parse(&control);
            assert!(
                control.len() > LO_BIG,
                "control carries its initialized bytes"
            );
            for (symbol, section, ..) in LINK_ONCE_PLACEMENT {
                let progbits = section
                    .replacen(".bss.", ".data.", 1)
                    .replacen(".tbss.", ".tdata.", 1);
                let header = control_elf.section(&progbits);
                assert_eq!(
                    header.sh_type, SHT_PROGBITS,
                    "{linkage:?} {opt:?} {progbits}"
                );
                assert_ne!(header.flags & SHF_GROUP, 0, "{progbits}");
                assert_eq!(
                    control_elf.symbol(symbol).shndx,
                    control_elf.section_index(&progbits),
                    "{symbol}"
                );
            }
            assert!(
                control_elf.sections.iter().all(|s| s.sh_type != SHT_NOBITS),
                "nonzero initializers must stay PROGBITS"
            );
            assert_eq!(
                control_elf.relocs, elf.relocs,
                "{linkage:?} {opt:?} relocations"
            );
            let text = |bytes: &[u8], elf: &Elf| {
                let text = elf.section(".text");
                bytes[text.offset..text.offset + text.size as usize].to_vec()
            };
            assert_eq!(
                text(&control, &control_elf),
                text(&object, &elf),
                "{opt:?} text"
            );

            if let Some(tool) = &tool {
                let path = dir.join(format!("link-once-{linkage:?}-{opt:?}.o"));
                std::fs::write(&path, &object).unwrap();
                let listing = readelf(tool, &["-S", "-W"], &path);
                for (name, kind, size, flags, align) in [
                    (".bss.lo_big", "NOBITS", LO_BIG as u64, "WAG", 4096),
                    (".bss.lo_counter", "NOBITS", 8, "WAG", 8),
                    (".tbss.lo_tls", "NOBITS", 32, "WAGT", 64),
                    (".data.lo_seed", "PROGBITS", 8, "WAG", 8),
                    (".tdata.lo_tls_seed", "PROGBITS", 16, "WAGT", 16),
                ] {
                    assert_eq!(
                        readelf_section_row(&listing, name),
                        (kind.to_owned(), size, flags.to_owned(), align),
                        "{linkage:?} {opt:?} {tool:?} {name}"
                    );
                }
                let groups = readelf(tool, &["-g", "-W"], &path);
                for signature in ["lo_big", "lo_counter", "lo_tls", "lo_seed", "lo_tls_seed"] {
                    assert!(
                        groups.contains(&format!("[{signature}]")),
                        "{linkage:?} {opt:?} {tool:?} group {signature}:\n{groups}"
                    );
                }
                assert_eq!(
                    groups.matches("COMDAT group section").count(),
                    5,
                    "{linkage:?} {opt:?}:\n{groups}"
                );
            }
        }
    }
    std::fs::remove_dir_all(&dir).unwrap();
}

/// Mutation control for [`link_once_violations`]: a faithful object has no
/// violation, and flipping a zero-fill member's type to PROGBITS, clearing
/// its `SHF_GROUP` or `SHF_TLS`, retargeting its group's member word at
/// another section, flagging an ungrouped section `SHF_GROUP`, or turning
/// its `STB_WEAK` symbol global is each caught.
#[test]
fn link_once_oracle_catches_type_group_flag_and_membership_mutations() {
    let object = compile_link_once_unit(OptLevel::O2, "a", Linkage::LinkOnceOdr, true);
    assert_eq!(link_once_violations(&object), Vec::<String>::new());
    let elf = Elf::parse(&object);
    let shoff = u64le(&object, 0x28) as usize;
    let header = |name: &str| shoff + elf.section_index(name) as usize * 64;
    let patch = |at: usize, value: &[u8]| {
        let mut copy = object.clone();
        copy[at..at + value.len()].copy_from_slice(value);
        copy
    };
    let rw = SHF_ALLOC | SHF_WRITE;
    let group_of = |signature: &str| {
        elf.sections
            .iter()
            .find(|s| s.sh_type == SHT_GROUP && elf.symbols[s.info as usize].name == signature)
            .unwrap()
            .offset
    };
    let symtab = elf
        .sections
        .iter()
        .find(|s| s.sh_type == SHT_SYMTAB)
        .unwrap();
    let counter_symbol = elf
        .symbols
        .iter()
        .position(|s| s.name == "lo_counter")
        .unwrap();
    for (label, mutated) in [
        (
            ".bss.lo_counter type PROGBITS",
            patch(header(".bss.lo_counter") + 4, &SHT_PROGBITS.to_le_bytes()),
        ),
        (
            ".tbss.lo_tls type PROGBITS",
            patch(header(".tbss.lo_tls") + 4, &SHT_PROGBITS.to_le_bytes()),
        ),
        (
            ".bss.lo_big without SHF_GROUP",
            patch(header(".bss.lo_big") + 8, &rw.to_le_bytes()),
        ),
        (
            ".tbss.lo_tls without SHF_TLS",
            patch(header(".tbss.lo_tls") + 8, &(rw | SHF_GROUP).to_le_bytes()),
        ),
        (
            "lo_counter group names .bss.lo_big",
            patch(
                group_of("lo_counter") + 4,
                &u32::from(elf.section_index(".bss.lo_big")).to_le_bytes(),
            ),
        ),
        (
            ".text claims SHF_GROUP",
            patch(
                header(".text") + 8,
                &(SHF_ALLOC | SHF_EXECINSTR | SHF_GROUP).to_le_bytes(),
            ),
        ),
        (
            "lo_counter bound STB_GLOBAL",
            patch(
                symtab.offset + counter_symbol * 24 + 4,
                &[(1 << 4) | STT_OBJECT],
            ),
        ),
    ] {
        assert!(
            !link_once_violations(&mutated).is_empty(),
            "{label} must be caught"
        );
    }
}

// --- Linux AArch64 native controls ---------------------------------------------

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[path = "common/rosetta.rs"]
mod native_process;

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
mod native {
    use super::*;
    use std::time::Duration;

    /// Run a required native command (compiler, linker, readelf or the
    /// linked program) and return its stdout.
    fn checked(cmd: &mut Command, timeout: Duration) -> String {
        let result = native_process::command_output_with_timeout(cmd, timeout)
            .unwrap_or_else(|error| panic!("required native command {cmd:?}: {error}"));
        assert!(
            !result.timed_out && result.output.status.success(),
            "{cmd:?}: {}\nstdout={}\nstderr={}",
            result.output.status,
            String::from_utf8_lossy(&result.output.stdout),
            String::from_utf8_lossy(&result.output.stderr),
        );
        String::from_utf8_lossy(&result.output.stdout).into_owned()
    }

    fn link(args: &[&str], inputs: &[&Path], output: &Path) {
        let mut cc = Command::new("cc");
        cc.args(args).args(inputs).arg("-o").arg(output);
        checked(&mut cc, native_process::codegen_link_timeout());
    }

    fn program_headers(image: &Path) -> String {
        checked(
            Command::new("readelf").args(["-l", "-W"]).arg(image),
            native_process::codegen_link_timeout(),
        )
    }

    /// (FileSiz, MemSiz, flag letters, Align) of the first `kind` segment.
    fn segment(listing: &str, kind: &str) -> Option<(u64, u64, String, u64)> {
        let fields: Vec<&str> = listing
            .lines()
            .map(str::split_whitespace)
            .map(Iterator::collect::<Vec<_>>)
            .find(|fields| fields.first() == Some(&kind))?;
        let hex = |field: &str| u64::from_str_radix(field.trim_start_matches("0x"), 16).unwrap();
        let last = fields.len() - 1;
        Some((
            hex(fields[4]),
            hex(fields[5]),
            fields[6..last].concat(),
            hex(fields[last]),
        ))
    }

    fn assert_nonexecutable_stack(image: &Path) {
        let listing = program_headers(image);
        let (_, _, flags, _) = segment(&listing, "GNU_STACK")
            .unwrap_or_else(|| panic!("{image:?} has no PT_GNU_STACK:\n{listing}"));
        assert_eq!(
            flags, "RW",
            "{image:?} stack must be RW, not RWE:\n{listing}"
        );
    }

    /// GNU `readelf -n -W` listing of `file`.
    fn notes(file: &Path) -> String {
        checked(
            Command::new("readelf").args(["-n", "-W"]).arg(file),
            native_process::codegen_link_timeout(),
        )
    }

    /// Whether the listing carries an AArch64 feature property claiming BTI.
    fn claims_bti(listing: &str) -> bool {
        listing.contains("NT_GNU_PROPERTY_TYPE_0")
            && listing.lines().any(|line| {
                let line = line.to_ascii_lowercase();
                line.contains("aarch64 feature:") && line.contains("bti")
            })
    }

    /// A successful `cc` link; returns the linker's stderr (warnings).
    fn link_capturing(args: &[&str], inputs: &[&Path], output: &Path) -> String {
        let mut cc = Command::new("cc");
        cc.args(args).args(inputs).arg("-o").arg(output);
        let result = native_process::command_output_with_timeout(
            &mut cc,
            native_process::codegen_link_timeout(),
        )
        .unwrap_or_else(|error| panic!("required native command {cc:?}: {error}"));
        assert!(
            !result.timed_out && result.output.status.success(),
            "{cc:?}: {}\nstderr={}",
            result.output.status,
            String::from_utf8_lossy(&result.output.stderr),
        );
        String::from_utf8_lossy(&result.output.stderr).into_owned()
    }

    /// GNU ld's per-input `-z force-bti` warning text.
    const GNU_LD_FORCE_BTI_WARNING: &str =
        "warning: BTI turned on by -z force-bti when all inputs do not have BTI in NOTE section";
    /// lld's per-input `-z force-bti` warning text.
    const LLD_FORCE_BTI_WARNING: &str =
        "-z force-bti: file does not have GNU_PROPERTY_AARCH64_FEATURE_1_BTI property";

    /// The linker's `-z force-bti` warning lines, matched by the message text
    /// itself, not by a path or option spelling that may contain `force-bti`.
    fn force_bti_warnings(stderr: &str) -> Vec<&str> {
        stderr
            .lines()
            .filter(|line| {
                line.contains(GNU_LD_FORCE_BTI_WARNING) || line.contains(LLD_FORCE_BTI_WARNING)
            })
            .collect()
    }

    /// `/proc/cpuinfo` lists the `bti` feature (FEAT_BTI, HWCAP2_BTI).
    fn cpu_reports_bti() -> bool {
        std::fs::read_to_string("/proc/cpuinfo")
            .expect("read /proc/cpuinfo")
            .lines()
            .filter(|line| line.starts_with("Features"))
            .filter_map(|line| line.split_once(':'))
            .any(|(_, features)| features.split_whitespace().any(|feature| feature == "bti"))
    }

    /// `getconf GNU_LIBC_VERSION` text and its (major, minor) version.
    fn glibc_version() -> (String, (u32, u32)) {
        let text = checked(
            Command::new("getconf").arg("GNU_LIBC_VERSION"),
            native_process::codegen_link_timeout(),
        )
        .trim()
        .to_owned();
        let number = text
            .strip_prefix("glibc ")
            .unwrap_or_else(|| panic!("unexpected GNU_LIBC_VERSION {text:?}"));
        let mut parts = number.split('.').map(|part| part.parse::<u32>().unwrap());
        let version = (parts.next().unwrap(), parts.next().unwrap());
        (text, version)
    }

    const EXECUTABLE_DRIVER: &str = r#"
#define _GNU_SOURCE
#include <pthread.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#define BIG ((size_t)8 << 20)
extern uint8_t *zf_big_addr(void);
extern uint64_t zf_counter_bump(uint64_t);
extern uint64_t zf_public_zero[4], zf_seed;
extern uint64_t *zf_public_zero_addr(void);
extern __thread uint64_t zf_tls_zero[4], zf_tls_init[2];
extern uint64_t *zf_tls_zero_addr(void), *zf_tls_init_addr(void);
extern uint64_t zf_tls_bump(uint64_t);
static pthread_barrier_t barrier;
static uintptr_t tls_addresses[3];

static int check_thread(int id) {
    uint64_t *z = zf_tls_zero_addr(), *t = zf_tls_init_addr();
    if (z != zf_tls_zero || t != zf_tls_init) return 10;
    if ((uintptr_t)z % 128 || (uintptr_t)t % 64) return 11;
    for (int j = 0; j < 4; ++j) if (z[j] != 0) return 12;
    if (t[0] != UINT64_C(0x1111222233334444) || t[1] != UINT64_C(0x5555666677778888)) return 13;
    tls_addresses[id] = (uintptr_t)z;
    uint64_t total = 0;
    for (uint64_t k = 1; k <= 100; ++k) {
        total += k * (uint64_t)(id + 1);
        if (zf_tls_bump(k * (uint64_t)(id + 1)) != total || zf_tls_zero[0] != total) return 14;
    }
    if (z[1] || z[2] || z[3]) return 15;
    return 0;
}

static void *worker(void *arg) {
    int failed = check_thread((int)(intptr_t)arg);
    // Both workers hold live TLS blocks at the same time.
    pthread_barrier_wait(&barrier);
    return (void *)(intptr_t)failed;
}

int main(void) {
    uint8_t *big = zf_big_addr();
    for (size_t k = 0; k < BIG; ++k) if (big[k]) return 1;
    for (size_t k = 0; k < BIG; k += 4093) big[k] = (uint8_t)(k * 7 + 1);
    big[BIG - 1] = 0xa5;
    for (size_t k = 0; k < BIG; k += 4093) if (big[k] != (uint8_t)(k * 7 + 1)) return 2;
    if (big[BIG - 1] != 0xa5) return 2;
    if (zf_counter_bump(0) != 0 || zf_counter_bump(5) != 5 || zf_counter_bump(7) != 12) return 3;
    if (zf_public_zero_addr() != zf_public_zero || (uintptr_t)zf_public_zero % 64) return 4;
    for (int j = 0; j < 4; ++j) if (zf_public_zero[j]) return 4;
    zf_public_zero[3] = 99;
    if (zf_public_zero_addr()[3] != 99 || zf_seed != UINT64_C(0x12345678)) return 5;
    if ((uintptr_t)zf_public_zero >= (uintptr_t)big && (uintptr_t)zf_public_zero < (uintptr_t)big + BIG) return 6;
    int status = check_thread(0);
    if (status) return status;
    if (pthread_barrier_init(&barrier, 0, 2)) return 20;
    pthread_t threads[2];
    for (intptr_t k = 0; k < 2; ++k)
        if (pthread_create(&threads[k], 0, worker, (void *)(k + 1))) return 21;
    for (int k = 0; k < 2; ++k) {
        void *result;
        if (pthread_join(threads[k], &result) || result) return 22;
    }
    if (zf_tls_zero[0] != 5050) return 23;
    for (int a = 0; a < 3; ++a)
        for (int b = a + 1; b < 3; ++b)
            if (tls_addresses[a] == tls_addresses[b]) return 24;
    if (pthread_barrier_destroy(&barrier)) return 25;
    puts("zero-fill globals and TLS templates matched in three threads");
    return 0;
}
"#;

    const DLOPEN_DRIVER: &str = r#"
#include <dlfcn.h>
#include <stdint.h>
#include <stdio.h>
int main(int argc, char **argv) {
    if (argc != 2) return 1;
    void *library = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
    if (!library) { fprintf(stderr, "dlopen: %s\n", dlerror()); return 2; }
    uint64_t (*bump)(uint64_t) = (uint64_t (*)(uint64_t))dlsym(library, "zf_counter_bump");
    uint8_t *(*big)(void) = (uint8_t *(*)(void))dlsym(library, "zf_big_addr");
    uint64_t *zero = (uint64_t *)dlsym(library, "zf_public_zero");
    if (!bump || !big || !zero) return 3;
    if (bump(0) != 0 || bump(9) != 9) return 4;
    uint8_t *bytes = big();
    for (size_t k = 0; k < ((size_t)8 << 20); k += 4096) if (bytes[k]) return 5;
    for (int j = 0; j < 4; ++j) if (zero[j]) return 6;
    puts("dlopen of the generated shared object passed");
    return dlclose(library) ? 7 : 0;
}
"#;

    #[test]
    fn linux_images_linked_without_noexecstack_have_nonexecutable_stack() {
        let dir = scratch_dir("gnu-stack");
        // Every emitter route, linked as a shared object without
        // `-z noexecstack`: the CG object alone decides the stack flags.
        let mut libraries = 0;
        for (route, _, object) in route_objects(OptLevel::O2) {
            if route.contains("tls=true") {
                // Local-exec TLS belongs in an executable; the executable
                // test below checks that image's PT_GNU_STACK.
                continue;
            }
            let stem = route.replace(['/', ' ', ':', '='], "_");
            let input = dir.join(format!("{stem}.o"));
            let library = dir.join(format!("lib{stem}.so"));
            std::fs::write(&input, object).unwrap();
            link(&["-shared"], &[&input], &library);
            assert_nonexecutable_stack(&library);
            libraries += 1;
        }
        assert_eq!(libraries, 11, "every non-TLS route linked");

        let driver = dir.join("dlopen.c");
        std::fs::write(&driver, DLOPEN_DRIVER).unwrap();
        let loader = dir.join("dlopen");
        link(&["-O2"], &[&driver, Path::new("-ldl")], &loader);
        for opt in OPT_LEVELS {
            let input = dir.join(format!("shared-{opt:?}.o"));
            let library = dir.join(format!("libzf-{opt:?}.so"));
            std::fs::write(&input, compile_zero_fill_module(opt, true, false)).unwrap();
            link(&["-shared"], &[&input], &library);
            assert_nonexecutable_stack(&library);
            // glibc 2.41+ refuses to dlopen an object that needs an
            // executable stack; this load must succeed on every glibc.
            let output = checked(
                Command::new(&loader).arg(&library),
                native_process::codegen_run_timeout(),
            );
            assert_eq!(
                output.trim(),
                "dlopen of the generated shared object passed",
                "{opt:?}"
            );
        }

        // Negative control: the same check must see RWE when the link asks
        // for an executable stack, so the RW result above is not vacuous.
        let input = dir.join("control.o");
        std::fs::write(&input, compile_zero_fill_module(OptLevel::O0, true, false)).unwrap();
        let library = dir.join("libexecstack.so");
        link(&["-shared", "-Wl,-z,execstack"], &[&input], &library);
        let listing = program_headers(&library);
        let (_, _, flags, _) = segment(&listing, "GNU_STACK").unwrap();
        assert_eq!(flags, "RWE", "execstack control:\n{listing}");

        // glibc 2.41 made dlopen refuse an object that needs an executable
        // stack. From 2.41 this RWE control must fail to load; an older
        // glibc loads it, which is recorded, not asserted, and leaves the
        // 2.41 refusal to a newer-glibc host.
        let (glibc, version) = glibc_version();
        let load = native_process::command_output_with_timeout(
            Command::new(&loader)
                .arg(&library)
                .env_remove("GLIBC_TUNABLES"),
            native_process::codegen_run_timeout(),
        )
        .expect("run the dlopen loader on the RWE control");
        let outcome = format!(
            "{} (timed out: {}), stderr {:?}",
            load.output.status,
            load.timed_out,
            String::from_utf8_lossy(&load.output.stderr).trim()
        );
        if version >= (2, 41) {
            assert!(
                !load.timed_out && load.output.status.code() == Some(2),
                "{glibc} must refuse to dlopen the RWE control: {outcome}"
            );
            println!("{glibc}: dlopen refused the RWE control: {outcome}");
        } else {
            println!(
                "{glibc}: dlopen of the RWE control gave {outcome}; the glibc 2.41 \
                 executable-stack dlopen refusal needs a newer-glibc host and was not exercised"
            );
        }

        // Host-linker sensitivity record (not an assertion: a linker whose
        // default is a non-executable stack reports RW here too): the same
        // writer WITHOUT the marker, as every emitter produced before.
        let mut writer =
            trust_cg_codegen::elf::ElfWriter::new(trust_cg_codegen::elf::ElfMachine::AArch64);
        writer.add_text_section(&0xd65f_03c0u32.to_le_bytes());
        writer.add_symbol("noteless_ret", 1, 0, 4, true, 2);
        let input = dir.join("noteless.o");
        std::fs::write(&input, writer.write_checked().unwrap()).unwrap();
        let library = dir.join("libnoteless.so");
        let linked = native_process::command_output_with_timeout(
            Command::new("cc")
                .arg("-shared")
                .arg(&input)
                .arg("-o")
                .arg(&library),
            native_process::codegen_link_timeout(),
        )
        .is_ok_and(|result| !result.timed_out && result.output.status.success());
        let record = if linked {
            segment(&program_headers(&library), "GNU_STACK")
                .map_or("no PT_GNU_STACK".to_owned(), |(_, _, flags, _)| flags)
        } else {
            "a refused link".to_owned()
        };
        println!("host linker gives a note-less object {record}");
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn linux_large_zero_global_and_zero_tls_templates_execute_at_o0_o3() {
        let dir = scratch_dir("native-zero-fill");
        let driver = dir.join("driver.c");
        std::fs::write(&driver, EXECUTABLE_DRIVER).unwrap();
        let mut executions = 0;
        for opt in OPT_LEVELS {
            let object = dir.join(format!("zero-fill-{opt:?}.o"));
            let binary = dir.join(format!("zero-fill-{opt:?}"));
            std::fs::write(&object, compile_zero_fill_module(opt, true, true)).unwrap();
            // Deliberately no `-z noexecstack`.
            link(&["-O2", "-pthread"], &[&driver, &object], &binary);
            assert_nonexecutable_stack(&binary);
            let size = std::fs::metadata(&binary).unwrap().len();
            assert!(
                size < (1 << 20),
                "{opt:?}: {BIG}-byte zero global inflated the executable to {size} bytes"
            );
            let listing = program_headers(&binary);
            let (file_size, memory_size, _, align) = segment(&listing, "TLS")
                .unwrap_or_else(|| panic!("{opt:?}: no PT_TLS:\n{listing}"));
            assert!(
                memory_size >= file_size + 32 && align >= 128,
                "{opt:?}: PT_TLS must carry the zero-filled .tbss tail:\n{listing}"
            );
            let sections = checked(
                Command::new("readelf").args(["-S", "-W"]).arg(&binary),
                native_process::codegen_link_timeout(),
            );
            let (kind, bss_size, _, _) = readelf_section_row(&sections, ".bss");
            assert!(
                kind == "NOBITS" && bss_size >= BIG as u64,
                "{opt:?}: {sections}"
            );
            let run = native_process::run_executable_with_timeout(
                &binary,
                native_process::codegen_run_timeout(),
            )
            .expect("linked zero-fill driver must execute");
            assert!(
                !run.timed_out && run.output.status.success(),
                "{opt:?}: {}\nstdout={}\nstderr={}",
                run.output.status,
                String::from_utf8_lossy(&run.output.stdout),
                String::from_utf8_lossy(&run.output.stderr)
            );
            assert_eq!(
                String::from_utf8_lossy(&run.output.stdout).trim(),
                "zero-fill globals and TLS templates matched in three threads",
                "{opt:?}"
            );
            executions += 1;
        }
        assert_eq!(executions, 4);
        std::fs::remove_dir_all(&dir).unwrap();
    }

    /// The C side of the link-once control: units `a` and `b` each define
    /// the same zero link-once data; the program checks that both units
    /// address ONE instance (writes through either are seen by the other),
    /// that the thread-local is one zero-filled instance per thread shared
    /// by both units in three live threads, and that the nonzero twins keep
    /// their values.
    const LINK_ONCE_DRIVER: &str = r#"
#define _GNU_SOURCE
#include <pthread.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#define LO_BIG ((size_t)4 << 20)
extern uint8_t lo_big[];
extern uint64_t lo_counter, lo_seed;
extern __thread uint64_t lo_tls[4], lo_tls_seed[2];
extern uint8_t *lo_a_big_addr(void), *lo_b_big_addr(void);
extern uint64_t *lo_a_counter_addr(void), *lo_b_counter_addr(void);
extern uint64_t lo_a_counter_bump(uint64_t), lo_b_counter_bump(uint64_t);
extern uint64_t *lo_a_tls_addr(void), *lo_b_tls_addr(void);
extern uint64_t lo_a_tls_bump(uint64_t), lo_b_tls_bump(uint64_t);
extern uint64_t lo_a_seed(void), lo_b_seed(void);
extern uint64_t *lo_a_tls_seed_addr(void), *lo_b_tls_seed_addr(void);
static pthread_barrier_t barrier;
static uintptr_t tls_addresses[3];

static int check_thread(int id) {
    uint64_t *a = lo_a_tls_addr(), *b = lo_b_tls_addr();
    if (a != b || a != lo_tls) return 10;
    if ((uintptr_t)a % 64) return 11;
    for (int j = 0; j < 4; ++j) if (a[j]) return 12;
    uint64_t *seed = lo_a_tls_seed_addr();
    if (seed != lo_b_tls_seed_addr() || seed != lo_tls_seed) return 13;
    if (seed[0] != UINT64_C(0x7157000000000001) || seed[1] != UINT64_C(0x7157000000000002)) return 13;
    tls_addresses[id] = (uintptr_t)a;
    uint64_t total = 0;
    for (uint64_t k = 1; k <= 50; ++k) {
        uint64_t add = k * (uint64_t)(id + 1);
        total += add;
        uint64_t got = (k & 1) ? lo_a_tls_bump(add) : lo_b_tls_bump(add);
        if (got != total || lo_tls[0] != total) return 14;
    }
    if (a[1] || a[2] || a[3]) return 15;
    return 0;
}

static void *worker(void *arg) {
    int failed = check_thread((int)(intptr_t)arg);
    // Every thread holds its live TLS block at the same time.
    pthread_barrier_wait(&barrier);
    return (void *)(intptr_t)failed;
}

int main(void) {
    uint8_t *big = lo_a_big_addr();
    if (big != lo_b_big_addr() || big != lo_big || (uintptr_t)big % 4096) return 1;
    for (size_t k = 0; k < LO_BIG; ++k) if (big[k]) return 2;
    big[LO_BIG - 1] = 0xa5;
    lo_b_big_addr()[12345] = 7;
    if (lo_b_big_addr()[LO_BIG - 1] != 0xa5 || lo_a_big_addr()[12345] != 7) return 3;
    if (lo_a_counter_addr() != lo_b_counter_addr() || lo_a_counter_addr() != &lo_counter) return 4;
    if (lo_counter != 0) return 5;
    if (lo_a_counter_bump(5) != 5 || lo_b_counter_bump(7) != 12 || lo_counter != 12) return 6;
    if (lo_a_seed() != UINT64_C(0x5eed000000001234) || lo_b_seed() != lo_seed) return 7;
    if (pthread_barrier_init(&barrier, 0, 3)) return 20;
    pthread_t threads[2];
    for (intptr_t k = 0; k < 2; ++k)
        if (pthread_create(&threads[k], 0, worker, (void *)(k + 1))) return 21;
    int status = check_thread(0);
    pthread_barrier_wait(&barrier);
    for (int k = 0; k < 2; ++k) {
        void *result;
        if (pthread_join(threads[k], &result) || result) return 22;
    }
    if (status) return status;
    if (lo_tls[0] != 1275) return 23;
    for (int a = 0; a < 3; ++a)
        for (int b = a + 1; b < 3; ++b)
            if (tls_addresses[a] == tls_addresses[b]) return 24;
    if (pthread_barrier_destroy(&barrier)) return 25;
    puts("link-once zero-fill data and TLS shared one instance in three threads");
    return 0;
}
"#;

    /// Remove a native test's scratch directory unless
    /// `TCG_RETAIN_TEST_EVIDENCE` is set, which keeps its objects, maps,
    /// readelf listings and run output for an evidence archive.
    fn finish_scratch(dir: &Path) {
        if std::env::var_os("TCG_RETAIN_TEST_EVIDENCE").is_some() {
            println!("evidence retained in {}", dir.display());
        } else {
            std::fs::remove_dir_all(dir).unwrap();
        }
    }

    /// Defined (non-`U`) `nm` rows of `image` naming `symbol`.
    fn defined_count(image: &Path, symbol: &str) -> usize {
        checked(
            Command::new("nm").arg(image),
            native_process::codegen_link_timeout(),
        )
        .lines()
        .filter(|line| line.split_whitespace().last() == Some(symbol) && !line.contains(" U "))
        .count()
    }

    /// Two objects that each define the same zero-initialized link-once
    /// global, zero link-once thread-local and their nonzero twins (every
    /// pairing of `LinkOnce`, `LinkOnceOdr` and `WeakOdr`) link with `cc`
    /// into one executable at O0-O3 without `-z noexecstack`. GNU ld's map
    /// discards the second object's five groups, `nm` finds one definition
    /// of each symbol, the 4 MiB zero global leaves the executable under
    /// 1 MiB, PT_TLS carries the zero `.tbss` tail, and the program sees one
    /// instance across both units and one per thread for TLS in three live
    /// threads. Control: the same units with strong `External` linkage fail
    /// to link with "multiple definition".
    #[test]
    fn linux_link_once_zero_data_and_tls_share_one_instance_across_objects() {
        let dir = scratch_dir("link-once-native");
        let driver = dir.join("driver.c");
        std::fs::write(&driver, LINK_ONCE_DRIVER).unwrap();
        let pairs = [
            (Linkage::LinkOnce, Linkage::LinkOnceOdr),
            (Linkage::LinkOnceOdr, Linkage::WeakOdr),
            (Linkage::WeakOdr, Linkage::LinkOnce),
        ];
        let mut executions = 0;
        for (a_linkage, b_linkage) in pairs {
            for opt in OPT_LEVELS {
                let label = format!("{a_linkage:?}+{b_linkage:?} {opt:?}");
                let stem = format!("{a_linkage:?}-{b_linkage:?}-{opt:?}");
                let a = dir.join(format!("a-{stem}.o"));
                let b = dir.join(format!("b-{stem}.o"));
                for (path, unit, linkage) in [(&a, "a", a_linkage), (&b, "b", b_linkage)] {
                    let object = compile_link_once_unit(opt, unit, linkage, true);
                    assert_eq!(
                        link_once_violations(&object),
                        Vec::<String>::new(),
                        "{label} unit {unit}"
                    );
                    std::fs::write(path, object).unwrap();
                    let listing = checked(
                        Command::new("readelf")
                            .args(["-S", "-g", "-s", "-W"])
                            .arg(path),
                        native_process::codegen_link_timeout(),
                    );
                    std::fs::write(path.with_extension("readelf.txt"), listing).unwrap();
                }
                let binary = dir.join(format!("link-once-{stem}"));
                let map = dir.join(format!("link-once-{stem}.map"));
                let map_flag = format!("-Wl,-Map,{}", map.display());
                link(&["-O2", "-pthread", &map_flag], &[&driver, &a, &b], &binary);
                assert_nonexecutable_stack(&binary);
                let size = std::fs::metadata(&binary).unwrap().len();
                assert!(
                    size < (1 << 20),
                    "{label}: the {LO_BIG}-byte zero link-once global inflated the executable to {size} bytes"
                );
                let map_text = std::fs::read_to_string(&map).unwrap();
                let discarded = map_text
                    .split("Discarded input sections")
                    .nth(1)
                    .and_then(|rest| rest.split("Memory Configuration").next())
                    .expect("GNU ld map lists discarded input sections");
                // GNU ld lists a discarded input section as `name addr size
                // file`, wrapping a long name onto its own line.
                let lines: Vec<&str> = discarded.lines().collect();
                let dropped = |section: &str, object: &Path| {
                    let file = object.to_str().unwrap();
                    lines.iter().enumerate().any(|(index, line)| {
                        line.split_whitespace().next() == Some(section)
                            && (line.ends_with(file)
                                || lines
                                    .get(index + 1)
                                    .is_some_and(|next| next.ends_with(file)))
                    })
                };
                for section in [
                    ".bss.lo_big",
                    ".bss.lo_counter",
                    ".tbss.lo_tls",
                    ".data.lo_seed",
                    ".tdata.lo_tls_seed",
                ] {
                    assert!(
                        dropped(section, &b) && !dropped(section, &a),
                        "{label}: only the second object's {section} group is discarded:\n{discarded}"
                    );
                }
                for symbol in ["lo_big", "lo_counter", "lo_tls", "lo_seed", "lo_tls_seed"] {
                    assert_eq!(defined_count(&binary, symbol), 1, "{label}: {symbol}");
                }
                let listing = program_headers(&binary);
                let (file_size, memory_size, _, align) = segment(&listing, "TLS")
                    .unwrap_or_else(|| panic!("{label}: no PT_TLS:\n{listing}"));
                assert!(
                    memory_size >= file_size + 32 && align >= 64,
                    "{label}: PT_TLS must carry the zero-filled .tbss tail:\n{listing}"
                );
                let sections = checked(
                    Command::new("readelf").args(["-S", "-W"]).arg(&binary),
                    native_process::codegen_link_timeout(),
                );
                std::fs::write(
                    dir.join(format!("link-once-{stem}.readelf.txt")),
                    format!("{sections}\n{listing}"),
                )
                .unwrap();
                let (kind, bss_size, _, _) = readelf_section_row(&sections, ".bss");
                assert!(
                    kind == "NOBITS" && bss_size >= LO_BIG as u64,
                    "{label}: {sections}"
                );
                let run = native_process::run_executable_with_timeout(
                    &binary,
                    native_process::codegen_run_timeout(),
                )
                .expect("linked link-once driver must execute");
                std::fs::write(
                    dir.join(format!("link-once-{stem}.run.txt")),
                    format!(
                        "{}\nsize {size}\n{}",
                        run.output.status,
                        String::from_utf8_lossy(&run.output.stdout)
                    ),
                )
                .unwrap();
                assert!(
                    !run.timed_out && run.output.status.success(),
                    "{label}: {}\nstdout={}\nstderr={}",
                    run.output.status,
                    String::from_utf8_lossy(&run.output.stdout),
                    String::from_utf8_lossy(&run.output.stderr)
                );
                assert_eq!(
                    String::from_utf8_lossy(&run.output.stdout).trim(),
                    "link-once zero-fill data and TLS shared one instance in three threads",
                    "{label}"
                );
                executions += 1;
            }
        }
        assert_eq!(executions, 12);

        // Control: strong definitions of the same zero data in both objects
        // are a duplicate-definition link error, so the link above succeeds
        // because of the COMDAT groups, not in spite of them.
        for opt in [OptLevel::O0, OptLevel::O2] {
            let a = dir.join(format!("strong-a-{opt:?}.o"));
            let b = dir.join(format!("strong-b-{opt:?}.o"));
            std::fs::write(
                &a,
                compile_link_once_unit(opt, "a", Linkage::External, true),
            )
            .unwrap();
            std::fs::write(
                &b,
                compile_link_once_unit(opt, "b", Linkage::External, true),
            )
            .unwrap();
            let binary = dir.join(format!("strong-{opt:?}"));
            let result = native_process::command_output_with_timeout(
                Command::new("cc")
                    .args(["-O2", "-pthread"])
                    .arg(&driver)
                    .arg(&a)
                    .arg(&b)
                    .arg("-o")
                    .arg(&binary),
                native_process::codegen_link_timeout(),
            )
            .expect("run cc for the strong-definition control");
            let stderr = String::from_utf8_lossy(&result.output.stderr);
            std::fs::write(
                dir.join(format!("strong-{opt:?}.link.txt")),
                stderr.as_bytes(),
            )
            .unwrap();
            assert!(
                !result.timed_out
                    && !result.output.status.success()
                    && stderr.contains("multiple definition of `lo_counter'"),
                "{opt:?}: strong zero definitions must not link: {stderr}"
            );
        }
        finish_scratch(&dir);
    }

    // --- BTI/PAC: trust-cg emits no landing pads and no property note ------

    /// `long cg_bti_bump(long x) { return x + 1; }`, the C twin of the CG
    /// function `lower_function` builds; compiled with branch protection it
    /// starts with a BTI landing pad and carries the BTI/PAC property note.
    const BTI_MARKED_CALLEE: &str = "long cg_bti_bump(long x) { return x + 1; }\n";

    /// A startfile-free executable whose only code besides the callee has BTI
    /// landing pads: the entry accepts any indirect branch (`BTI JC`,
    /// `hint #38`), and with `-mbranch-protection=standard` each C function
    /// starts with a landing pad. It prints a marker, calls `cg_bti_bump`
    /// through a pointer (`BLR`, which a BTI-guarded page requires to land on
    /// a landing pad) and prints the result, so a fault between the two lines
    /// is the indirect call into the callee.
    const BTI_DRIVER: &str = r#"
#include <unistd.h>
extern long cg_bti_bump(long);
long (*volatile cg_target)(long) = cg_bti_bump;
__asm__(".text\n"
        ".globl bti_entry\n"
        ".type bti_entry, %function\n"
        "bti_entry:\n"
        "  hint #38\n"
        "  mov x29, #0\n"
        "  mov x30, #0\n"
        "  bl bti_main\n"
        "  brk #0\n"
        ".size bti_entry, .-bti_entry\n");
static void say(const char *text, unsigned long length) { (void)!write(1, text, length); }
void bti_main(void) {
    say("indirect call\n", 14);
    long value = cg_target(41);
    if (value != 42) { say("wrong value\n", 12); _exit(1); }
    say("returned 42\n", 12);
    _exit(0);
}
"#;

    /// The same indirect call from an ordinary `main`, linked with the
    /// host's startfiles.
    const STARTFILE_DRIVER: &str = r#"
#include <unistd.h>
extern long cg_bti_bump(long);
long (*volatile cg_target)(long) = cg_bti_bump;
int main(void) {
    (void)!write(1, "main\n", 5);
    return cg_target(41) == 42 ? 0 : 1;
}
"#;

    const BTI_DRIVER_OUTPUT: &str = "indirect call\nreturned 42\n";

    /// Compile C `source` with `-mbranch-protection=standard`; the object
    /// must carry the BTI property.
    fn compile_marked_c(dir: &Path, name: &str, source: &str) -> PathBuf {
        let c = dir.join(format!("{name}.c"));
        let object = dir.join(format!("{name}.o"));
        std::fs::write(&c, source).unwrap();
        checked(
            Command::new("cc")
                .args(["-c", "-O2", "-mbranch-protection=standard"])
                .arg(&c)
                .arg("-o")
                .arg(&object),
            native_process::codegen_link_timeout(),
        );
        let listing = notes(&object);
        assert!(claims_bti(&listing), "{name}: no BTI property:\n{listing}");
        object
    }

    fn run(image: &Path) -> native_process::TimedCommandOutput {
        native_process::run_executable_with_timeout(image, native_process::codegen_run_timeout())
            .unwrap_or_else(|error| panic!("run {image:?}: {error}"))
    }

    fn stdout_of(run: &native_process::TimedCommandOutput) -> String {
        String::from_utf8_lossy(&run.output.stdout).into_owned()
    }

    /// The recorded outcome of a run whose result is not asserted. The
    /// runner reports a signal-killed program as exit status 128 + signal.
    fn outcome(run: &native_process::TimedCommandOutput) -> String {
        let status = match (run.timed_out, run.output.status.code()) {
            (true, _) => "timed out".to_owned(),
            (false, Some(132)) => "SIGILL (exit status 132)".to_owned(),
            (false, Some(code)) => format!("exit status {code}"),
            (false, None) => format!("{}", run.output.status),
        };
        format!("{status}, stdout {:?}", stdout_of(run))
    }

    fn assert_driver_ran(image: &Path) {
        let run = run(image);
        assert!(
            !run.timed_out && run.output.status.success() && stdout_of(&run) == BTI_DRIVER_OUTPUT,
            "{image:?}: {}\nstderr={}",
            outcome(&run),
            String::from_utf8_lossy(&run.output.stderr)
        );
    }

    /// Every route object at O0-O3 under GNU `readelf -n` shows no
    /// `NT_GNU_PROPERTY_TYPE_0`; a compiler-made BTI/PAC object shows that
    /// the same predicate detects a real property note.
    #[test]
    fn linux_gnu_readelf_finds_no_property_note_in_any_route_object() {
        let dir = scratch_dir("property-notes");
        let version = checked(
            Command::new("readelf").arg("--version"),
            native_process::codegen_link_timeout(),
        );
        let control = notes(&compile_marked_c(&dir, "marked", BTI_MARKED_CALLEE));
        let detected = readelf_notes_violation(&control)
            .unwrap_or_else(|| panic!("the note predicate missed a property note:\n{control}"))
            .trim()
            .to_owned();
        let mut objects = 0;
        for opt in OPT_LEVELS {
            for (route, _, object) in route_objects(opt) {
                let stem = route.replace(['/', ' ', ':', '='], "_");
                let path = dir.join(format!("{stem}-{opt:?}.o"));
                std::fs::write(&path, object).unwrap();
                let listing = notes(&path);
                assert_eq!(
                    readelf_notes_violation(&listing),
                    None,
                    "{route}/{opt:?}: unexpected note:\n{listing}"
                );
                assert!(!claims_bti(&listing), "{route}/{opt:?}");
                objects += 1;
            }
        }
        assert_eq!(objects, 48, "12 routes at O0-O3");
        println!(
            "record: {}: no NT_GNU_PROPERTY_TYPE_0 in {objects} route objects; \
             the -mbranch-protection=standard control shows {detected:?}",
            version.lines().next().unwrap_or_default()
        );
        std::fs::remove_dir_all(&dir).unwrap();
    }

    /// A forced BTI link of a CG object succeeds with only a linker warning
    /// and marks the output BTI-compatible, which the CG code (no landing
    /// pads) is not: the reason the link driver refuses `-z force-bti`.
    /// The default link runs the CG function through an indirect call. On a
    /// host whose `/proc/cpuinfo` reports `bti` the forced executable is run
    /// too and its outcome is recorded, not asserted: whether the loader
    /// guards the mapping is the host's choice.
    #[test]
    fn linux_forced_bti_links_claim_a_property_the_cg_code_lacks() {
        let dir = scratch_dir("bti-link");
        let bti_host = cpu_reports_bti();
        // The warning matcher is pinned to the linker message: a line that
        // names a CG object under a path spelled with `force-bti`, but is
        // not the BTI warning, is not one.
        assert_eq!(
            force_bti_warnings(
                "/usr/bin/ld: /tmp/x-force-bti-1/cg-O0.o: warning: relocation in read-only section\n\
                 /usr/bin/ld: /tmp/x/cg-force-bti-O0: warning: -z force-bti ignored"
            ),
            Vec::<&str>::new()
        );
        let gnu = format!("/usr/bin/ld: /tmp/x/cg-O0.o: {GNU_LD_FORCE_BTI_WARNING}.");
        let lld = format!("ld.lld: warning: /tmp/x/cg-O0.o: {LLD_FORCE_BTI_WARNING}");
        assert_eq!(
            force_bti_warnings(&format!("{gnu}\n{lld}")),
            [gnu.as_str(), lld.as_str()]
        );
        println!("record: /proc/cpuinfo reports bti: {bti_host}");
        let driver = compile_marked_c(&dir, "bti-driver", BTI_DRIVER);
        let marked = compile_marked_c(&dir, "bti-marked-callee", BTI_MARKED_CALLEE);
        let startfile_driver = compile_marked_c(&dir, "startfile-driver", STARTFILE_DRIVER);
        let entry = ["-nostartfiles", "-Wl,-e,bti_entry"];
        let forced = ["-nostartfiles", "-Wl,-e,bti_entry", "-Wl,-z,force-bti"];

        // Harness control: every input carries BTI, so the forced link warns
        // about nothing, and the guarded image runs where BTI is enforced.
        // A fault of the CG variant below is then the CG callee's.
        let control = dir.join("bti-control");
        let stderr = link_capturing(&forced, &[&driver, &marked], &control);
        assert_eq!(force_bti_warnings(&stderr), Vec::<&str>::new(), "{stderr}");
        assert_eq!(stderr.trim(), "", "the harness control link prints nothing");
        assert!(claims_bti(&notes(&control)));
        if bti_host {
            assert_driver_ran(&control);
        }

        for opt in OPT_LEVELS {
            let object = dir.join(format!("cg-{opt:?}.o"));
            let bytes = pipeline(opt)
                .compile_function(&lower_function("cg_bti_bump"))
                .unwrap();
            std::fs::write(&object, bytes).unwrap();
            let name = object.file_name().unwrap().to_str().unwrap();
            assert_eq!(readelf_notes_violation(&notes(&object)), None, "{name}");

            // Direct shared link: the default output makes no BTI claim; the
            // forced one names the CG object in ld's warning and claims BTI.
            let shared = dir.join(format!("libcg-{opt:?}.so"));
            link(&["-shared"], &[&object], &shared);
            assert!(!claims_bti(&notes(&shared)), "{opt:?}: default shared link");
            let forced_shared = dir.join(format!("libcg-force-bti-{opt:?}.so"));
            let stderr =
                link_capturing(&["-shared", "-Wl,-z,force-bti"], &[&object], &forced_shared);
            let warning = force_bti_warnings(&stderr)
                .into_iter()
                .find(|line| line.contains(name))
                .unwrap_or_else(|| panic!("{opt:?}: no force-bti warning names {name}:\n{stderr}"));
            println!("record: {opt:?} cc -shared -Wl,-z,force-bti: {warning}");
            let listing = notes(&forced_shared);
            assert!(
                claims_bti(&listing),
                "{opt:?}: forced shared object:\n{listing}"
            );

            // Default executable: the indirect call runs and returns 42.
            let default_image = dir.join(format!("cg-default-{opt:?}"));
            link(&entry, &[&driver, &object], &default_image);
            assert!(!claims_bti(&notes(&default_image)), "{opt:?}");
            assert_driver_ran(&default_image);

            // Forced executable: the CG object is the only input ld warns
            // about, every stderr line is that BTI warning, and the image
            // claims BTI.
            let forced_image = dir.join(format!("cg-force-bti-{opt:?}"));
            let stderr = link_capturing(&forced, &[&driver, &object], &forced_image);
            let warnings = force_bti_warnings(&stderr);
            assert!(
                !warnings.is_empty() && warnings.iter().all(|line| line.contains(name)),
                "{opt:?}: only the CG object may lack BTI:\n{stderr}"
            );
            assert_eq!(
                warnings.len(),
                stderr
                    .lines()
                    .filter(|line| !line.trim().is_empty())
                    .count(),
                "{opt:?}: the forced link prints only BTI warnings:\n{stderr}"
            );
            assert!(claims_bti(&notes(&forced_image)), "{opt:?}");
            if bti_host {
                println!(
                    "record: {opt:?} force-bti executable indirect-calling the CG function: {}",
                    outcome(&run(&forced_image))
                );
            } else {
                println!("record: {opt:?} force-bti executable not run: no bti in /proc/cpuinfo");
            }
        }

        // Host startfiles: an ordinary forced link also warns about the
        // host's own inputs; its run shows whether they reach `main`.
        let image = dir.join("startfile-force-bti");
        let stderr = link_capturing(
            &["-Wl,-z,force-bti"],
            &[&startfile_driver, &dir.join("cg-O2.o")],
            &image,
        );
        let scratch = dir.to_str().unwrap();
        let host_inputs: Vec<&str> = force_bti_warnings(&stderr)
            .into_iter()
            .filter(|line| !line.contains(scratch))
            .collect();
        println!(
            "record: a startfile force-bti link warns about {} host input(s): {host_inputs:?}",
            host_inputs.len()
        );
        if bti_host {
            println!(
                "record: startfile force-bti executable: {}",
                outcome(&run(&image))
            );
        }
        std::fs::remove_dir_all(&dir).unwrap();
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
