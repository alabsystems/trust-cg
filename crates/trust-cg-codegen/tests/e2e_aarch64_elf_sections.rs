// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Explicit section placement, constructor tables, function sections and
//! COMDAT groups on AArch64 objects (trust-ir v41 `Global.section`, trust-ir
//! v45 `Function.section`, trust-ir linkage,
//! `CompilerConfig::function_sections`).
//!
//! Object-level tests run on every host: each object is reparsed by the
//! independent parser below AND cross-checked with an external `readelf`
//! (`llvm-readelf` or GNU `readelf`); the explicit function-section checker
//! is itself shown to refuse mutated objects. Explicit zero-fill names
//! (`.bss*`, `.tbss*`, `.sbss*`, `.lbss*`) holding all-zero,
//! relocation-free globals are `SHT_NOBITS`; a nonzero or relocated
//! initializer in one stays refused by name (`[TCG-SECTION-NOBITS]`). Every
//! name GNU ld 2.42's or LLD 22.1.6's default link places outside plain
//! data (object_sections::ELF_NAME_RULES) is refused by name for a data
//! global, and so is an implicit COMDAT `<base>.<symbol>` that would leave
//! its base's rule; names one character past a family keep the global's
//! flags unless BFD matches them by a raw name prefix (every
//! `.eh_frame_entry*` spelling is refused). Native execution controls run
//! only where a matching linker
//! exists: the Linux controls (constructor before `main`, destructor after
//! it, also with the constructor state in a NOBITS `.bss.tcg`; explicit
//! zero-fill sections read and written in three threads; `--gc-sections` at
//! function granularity and over named function sections, COMDAT
//! deduplication across objects; trust-cg's own bytes under each refused
//! name faulting, failing to link or landing in a special output under GNU
//! ld and LLD; C globals under the `.eh_frame_entry` prefix failing the GNU
//! link; the honoured writable names surviving a store under both) and
//! a Darwin `__mod_init_func` constructor control. This is object and
//! execution evidence for these linker versions, not a proof.

#[path = "common/fresh_dir.rs"]
mod fresh_dir;
#[path = "common/llvm_tools.rs"]
mod llvm_tools;

#[path = "common/pinned_target.rs"]
mod pinned_target;

#[path = "common/admission_expect.rs"]
mod admission_expect;

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{CompilationResult, Compiler, CompilerConfig, CompilerTraceLevel};
use trust_ir::value::GlobalId;
use trust_ir::{
    BinOp, Block, BlockId, Constant, FuncId, FuncTy, Function, Global, Inst, InstrNode, Linkage,
    Module, Ty, ValueId, Visibility,
};

const LINUX: &str = "aarch64-unknown-linux-gnu";
const DARWIN: &str = "aarch64-apple-darwin";

// ELF constants (gABI / AArch64 psABI).
const SHT_PROGBITS: u32 = 1;
const SHT_RELA: u32 = 4;
const SHT_INIT_ARRAY: u32 = 14;
const SHT_FINI_ARRAY: u32 = 15;
const SHT_PREINIT_ARRAY: u32 = 16;
const SHT_GROUP: u32 = 17;
const SHF_WRITE: u64 = 0x1;
const SHF_ALLOC: u64 = 0x2;
const SHF_EXECINSTR: u64 = 0x4;
const SHF_GROUP: u64 = 0x200;
const SHF_TLS: u64 = 0x400;
const SHF_GNU_RETAIN: u64 = 0x20_0000;
const GRP_COMDAT: u32 = 1;
const STB_LOCAL: u8 = 0;
const STB_GLOBAL: u8 = 1;
const STB_WEAK: u8 = 2;
const STT_SECTION: u8 = 3;
const R_AARCH64_ABS64: u32 = 257;
const R_AARCH64_PREL32: u32 = 261;
const R_AARCH64_CALL26: u32 = 283;

// =============================================================================
// Module builders
// =============================================================================

fn node(inst: Inst, result: u32) -> InstrNode {
    InstrNode::new(inst).with_result(ValueId::new(result))
}

fn const_u64(value: i128, result: u32) -> InstrNode {
    node(
        Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(value),
        },
        result,
    )
}

fn ret(values: &[u32]) -> InstrNode {
    InstrNode::new(Inst::Return {
        values: values.iter().map(|value| ValueId::new(*value)).collect(),
    })
}

/// Define `name(params) -> returns` with a single block.
fn define(
    module: &mut Module,
    name: &str,
    returns: Vec<Ty>,
    linkage: Linkage,
    body: Vec<InstrNode>,
) -> FuncId {
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, sig, BlockId::new(0));
    function.linkage = linkage;
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![],
        body,
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    id
}

/// Declare an external `name() -> returns` defined by another object.
fn declare(module: &mut Module, name: &str, returns: Vec<Ty>) -> FuncId {
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, sig, BlockId::new(0));
    function.linkage = Linkage::External;
    function.blocks.clear();
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    id
}

fn global(name: &str, ty: Ty, initializer: Constant, linkage: Linkage) -> Global {
    Global {
        name: name.to_string(),
        ty,
        mutable: false,
        initializer: Some(initializer),
        linkage,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

/// An 8-byte pointer global holding `&symbol` (a constructor-table entry).
fn pointer_entry(name: &str, symbol: &str, section: &str) -> Global {
    let mut entry = global(
        name,
        Ty::Ptr,
        Constant::SymbolAddr {
            symbol: symbol.to_string(),
            addend: 0,
        },
        Linkage::Internal,
    );
    entry.section = Some(section.to_string());
    entry
}

fn u64_value(value: u64) -> Constant {
    Constant::Int(value.into())
}

/// `state = state * 100 + add` on the u64 global at `state_index`.
fn scale_and_add(state_index: u32, add: i128) -> Vec<InstrNode> {
    vec![
        node(
            Inst::GlobalAddr {
                global: GlobalId::new(state_index),
            },
            0,
        ),
        node(
            Inst::Load {
                ty: Ty::U64,
                ptr: ValueId::new(0),
                volatile: true,
                align: Some(8),
            },
            1,
        ),
        const_u64(100, 2),
        node(
            Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::U64,
                lhs: ValueId::new(1),
                rhs: ValueId::new(2),
            },
            3,
        ),
        const_u64(add, 4),
        node(
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U64,
                lhs: ValueId::new(3),
                rhs: ValueId::new(4),
            },
            5,
        ),
        InstrNode::new(Inst::Store {
            ty: Ty::U64,
            ptr: ValueId::new(0),
            value: ValueId::new(5),
            volatile: true,
            align: Some(8),
        }),
        ret(&[]),
    ]
}

/// Constructors and a destructor registered through ELF pointer tables:
///
/// * `tcg_ctor_early` (priority `.init_array.00101`) makes `tcg_state` 1;
/// * `tcg_ctor` (plain `.init_array`, `#[used]`-retained) makes it
///   `1 * 100 + 42 = 142` — prioritized entries run first;
/// * `tcg_dtor` (`.fini_array`) calls the C `tcg_note_fini`.
fn constructor_module() -> Module {
    let mut module = Module::new("tcg_ctor_dtor");
    let mut state = global("tcg_state", Ty::U64, u64_value(0), Linkage::External);
    state.mutable = true;
    state.align = Some(8);
    module.globals.push(state);
    let mut init = pointer_entry("tcg_init_entry", "tcg_ctor", ".init_array");
    init.retained = true;
    module.globals.push(init);
    module.globals.push(pointer_entry(
        "tcg_init_early_entry",
        "tcg_ctor_early",
        ".init_array.00101",
    ));
    module
        .globals
        .push(pointer_entry("tcg_fini_entry", "tcg_dtor", ".fini_array"));

    define(
        &mut module,
        "tcg_ctor",
        vec![],
        Linkage::External,
        scale_and_add(0, 42),
    );
    define(
        &mut module,
        "tcg_ctor_early",
        vec![],
        Linkage::External,
        scale_and_add(0, 1),
    );
    let note = declare(&mut module, "tcg_note_fini", vec![]);
    define(
        &mut module,
        "tcg_dtor",
        vec![],
        Linkage::External,
        vec![
            InstrNode::new(Inst::Call {
                callee: note,
                args: vec![],
            }),
            ret(&[]),
        ],
    );
    module
}

/// `tcg_caller` calls `tcg_leaf`; `tcg_unused` is referenced by nothing.
fn three_function_module() -> Module {
    let mut module = Module::new("tcg_function_sections");
    let leaf = define(
        &mut module,
        "tcg_leaf",
        vec![Ty::U64],
        Linkage::External,
        vec![const_u64(7, 0), ret(&[0])],
    );
    define(
        &mut module,
        "tcg_caller",
        vec![Ty::U64],
        Linkage::External,
        vec![
            node(
                Inst::Call {
                    callee: leaf,
                    args: vec![],
                },
                0,
            ),
            const_u64(1, 1),
            node(
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::U64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                },
                2,
            ),
            ret(&[2]),
        ],
    );
    define(
        &mut module,
        "tcg_unused",
        vec![Ty::U64],
        Linkage::External,
        vec![const_u64(9, 0), ret(&[0])],
    );
    module
}

/// One translation unit of the COMDAT control: a link-once-ODR function
/// `tcg_shared` (7) and a link-once-ODR table `tcg_shared_table`, plus a
/// distinct exported `tcg_from_<unit>` returning `tcg_shared() + add`.
fn comdat_unit(unit: &str, add: i128, shared_linkage: Linkage) -> Module {
    let mut module = Module::new(format!("tcg_comdat_{unit}"));
    module.globals.push(global(
        "tcg_shared_table",
        Ty::U64,
        u64_value(0x5eed_5eed),
        shared_linkage,
    ));
    let shared = define(
        &mut module,
        "tcg_shared",
        vec![Ty::U64],
        shared_linkage,
        vec![const_u64(7, 0), ret(&[0])],
    );
    define(
        &mut module,
        &format!("tcg_from_{unit}"),
        vec![Ty::U64],
        Linkage::External,
        vec![
            node(
                Inst::Call {
                    callee: shared,
                    args: vec![],
                },
                0,
            ),
            const_u64(add, 1),
            node(
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::U64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                },
                2,
            ),
            ret(&[2]),
        ],
    );
    module
}

fn compile_with(
    module: &Module,
    triple: &str,
    opt_level: OptLevel,
    function_sections: bool,
) -> Result<Vec<u8>, String> {
    let config = CompilerConfig {
        opt_level,
        parallel: false,
        function_sections,
        ..CompilerConfig::default()
    };
    // The fixtures call C (`tcg_note_fini`, ...): an FFI boundary names the
    // target it is compiled for (`TargetInfoRequired`; WS7.3 admission).
    Compiler::new_for_target_spec(config, TargetSpec::parse(triple).expect("triple"))
        .with_codegen_license(permit_unlicensed())
        .compile(&pinned_target::pinned(module, triple))
        .map(|result| result.object_code)
        .map_err(|error| error.to_string())
}

fn compile(module: &Module, triple: &str, function_sections: bool) -> Vec<u8> {
    compile_with(module, triple, OptLevel::O0, function_sections)
        .unwrap_or_else(|error| panic!("{triple}: compilation must succeed: {error}"))
}

// =============================================================================
// Independent ELF64 reader
// =============================================================================

fn rd_u16(b: &[u8], off: usize) -> u16 {
    u16::from_le_bytes(b[off..off + 2].try_into().unwrap())
}
fn rd_u32(b: &[u8], off: usize) -> u32 {
    u32::from_le_bytes(b[off..off + 4].try_into().unwrap())
}
fn rd_u64(b: &[u8], off: usize) -> u64 {
    u64::from_le_bytes(b[off..off + 8].try_into().unwrap())
}
fn cstr(b: &[u8], start: usize) -> String {
    let end = start + b[start..].iter().position(|&c| c == 0).unwrap();
    String::from_utf8_lossy(&b[start..end]).into_owned()
}

#[derive(Debug, Clone)]
struct Section {
    name: String,
    sh_type: u32,
    flags: u64,
    offset: u64,
    size: u64,
    link: u32,
    info: u32,
    align: u64,
    entsize: u64,
}

#[derive(Debug, Clone)]
struct Symbol {
    name: String,
    bind: u8,
    sym_type: u8,
    shndx: u16,
    value: u64,
    size: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Rela {
    offset: u64,
    symbol: u32,
    rtype: u32,
    addend: i64,
}

struct Elf {
    bytes: Vec<u8>,
    osabi: u8,
    sections: Vec<Section>,
    symbols: Vec<Symbol>,
}

impl Elf {
    fn parse(bytes: &[u8]) -> Self {
        assert_eq!(&bytes[0..4], b"\x7fELF");
        assert_eq!(rd_u16(bytes, 18), 183, "EM_AARCH64");
        let shoff = rd_u64(bytes, 0x28) as usize;
        let shnum = rd_u16(bytes, 0x3c) as usize;
        let shstrndx = rd_u16(bytes, 0x3e) as usize;
        let header = |i: usize| shoff + i * 64;
        let shstr = rd_u64(bytes, header(shstrndx) + 0x18) as usize;
        let sections: Vec<Section> = (0..shnum)
            .map(|i| {
                let h = header(i);
                Section {
                    name: cstr(bytes, shstr + rd_u32(bytes, h) as usize),
                    sh_type: rd_u32(bytes, h + 4),
                    flags: rd_u64(bytes, h + 8),
                    offset: rd_u64(bytes, h + 0x18),
                    size: rd_u64(bytes, h + 0x20),
                    link: rd_u32(bytes, h + 0x28),
                    info: rd_u32(bytes, h + 0x2c),
                    align: rd_u64(bytes, h + 0x30),
                    entsize: rd_u64(bytes, h + 0x38),
                }
            })
            .collect();
        let symtab = sections.iter().find(|s| s.sh_type == 2).expect(".symtab");
        let strtab = sections[symtab.link as usize].offset as usize;
        let symbols = (0..(symtab.size / 24) as usize)
            .map(|i| {
                let e = symtab.offset as usize + i * 24;
                Symbol {
                    name: cstr(bytes, strtab + rd_u32(bytes, e) as usize),
                    bind: bytes[e + 4] >> 4,
                    sym_type: bytes[e + 4] & 0xf,
                    shndx: rd_u16(bytes, e + 6),
                    value: rd_u64(bytes, e + 8),
                    size: rd_u64(bytes, e + 16),
                }
            })
            .collect();
        Self {
            bytes: bytes.to_vec(),
            osabi: bytes[7],
            sections,
            symbols,
        }
    }

    fn index_of(&self, name: &str) -> usize {
        let hits: Vec<usize> = (0..self.sections.len())
            .filter(|&i| self.sections[i].name == name)
            .collect();
        assert_eq!(hits.len(), 1, "exactly one section named {name}");
        hits[0]
    }

    fn has(&self, name: &str) -> bool {
        self.sections.iter().any(|section| section.name == name)
    }

    fn section(&self, name: &str) -> &Section {
        &self.sections[self.index_of(name)]
    }

    fn data(&self, index: usize) -> &[u8] {
        let s = &self.sections[index];
        &self.bytes[s.offset as usize..(s.offset + s.size) as usize]
    }

    fn symbol(&self, name: &str) -> &Symbol {
        let hits: Vec<&Symbol> = self.symbols.iter().filter(|s| s.name == name).collect();
        assert_eq!(hits.len(), 1, "exactly one symbol named {name}");
        hits[0]
    }

    fn section_of(&self, symbol: &str) -> &Section {
        &self.sections[self.symbol(symbol).shndx as usize]
    }

    /// Relocations applying to section `target`, in record order.
    fn relas(&self, target: usize) -> Vec<Rela> {
        self.sections
            .iter()
            .filter(|s| s.sh_type == SHT_RELA && s.info as usize == target)
            .flat_map(|s| {
                (0..(s.size / 24) as usize).map(move |i| {
                    let e = s.offset as usize + i * 24;
                    let info = rd_u64(&self.bytes, e + 8);
                    Rela {
                        offset: rd_u64(&self.bytes, e),
                        symbol: (info >> 32) as u32,
                        rtype: info as u32,
                        addend: rd_u64(&self.bytes, e + 16) as i64,
                    }
                })
            })
            .collect()
    }

    fn rela_section_for(&self, target: usize) -> Option<usize> {
        (0..self.sections.len()).find(|&i| {
            self.sections[i].sh_type == SHT_RELA && self.sections[i].info as usize == target
        })
    }

    fn symbol_name(&self, index: u32) -> &str {
        &self.symbols[index as usize].name
    }

    /// Every `SHT_GROUP`: (signature, member section indices).
    fn groups(&self) -> Vec<(String, Vec<u32>)> {
        (0..self.sections.len())
            .filter(|&i| self.sections[i].sh_type == SHT_GROUP)
            .map(|i| {
                let words: Vec<u32> = self
                    .data(i)
                    .chunks(4)
                    .map(|w| u32::from_le_bytes(w.try_into().unwrap()))
                    .collect();
                assert_eq!(words[0], GRP_COMDAT, "group flag word");
                let signature = self.symbol_name(self.sections[i].info).to_string();
                (signature, words[1..].to_vec())
            })
            .collect()
    }
}

// =============================================================================
// External readelf cross-check
// =============================================================================

/// The external ELF reader: `$TCG_READELF`, else `llvm-readelf` by the shared
/// LLVM tool discovery (`common/llvm_tools.rs`: `$TRUST_CG_LLVM_BIN`, install
/// directories, PATH, `llvm-config --bindir`, a sibling Trust build), else GNU
/// `readelf` on PATH. A missing reader fails the test.
fn readelf_tool() -> PathBuf {
    let mut candidates: Vec<PathBuf> = std::env::var_os("TCG_READELF")
        .map(PathBuf::from)
        .into_iter()
        .collect();
    candidates.extend(llvm_tools::find_llvm_tool("llvm-readelf"));
    candidates.push(PathBuf::from("readelf"));
    candidates
        .into_iter()
        .find(|tool| {
            Command::new(tool)
                .arg("--version")
                .output()
                .is_ok_and(|output| output.status.success())
        })
        .expect(
            "an llvm-readelf or GNU readelf is required for the object cross-check \
             (set TCG_READELF, or TRUST_CG_LLVM_BIN to an LLVM bin directory)",
        )
}

/// `readelf -W <flags>` over `bytes`; the text is shared by GNU readelf and
/// llvm-readelf's GNU output style for every fact asserted on it.
fn readelf(bytes: &[u8], flags: &[&str], tag: &str) -> String {
    let dir = scratch_dir(tag);
    let object = dir.join("object.o");
    std::fs::write(&object, bytes).unwrap();
    let output = Command::new(readelf_tool())
        .arg("-W")
        .args(flags)
        .arg(&object)
        .output()
        .expect("run readelf");
    assert!(
        output.status.success(),
        "readelf {flags:?} failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn scratch_dir(tag: &str) -> fresh_dir::ScratchDir {
    fresh_dir::create(&format!("tcg-elf-sections-{tag}-"))
}

// =============================================================================
// Object-level tests (every host)
// =============================================================================

/// `.init_array`, a priority `.init_array.N` and `.fini_array` become typed
/// pointer tables (writable+alloc, entsize 8, 8-aligned) whose single slot is
/// an `R_AARCH64_ABS64` against the constructor/destructor symbol; the
/// retained entry carries `SHF_GNU_RETAIN` with the GNU OSABI.
#[test]
fn constructor_tables_are_typed_pointer_arrays_with_abs64_slots() {
    let obj = compile(&constructor_module(), LINUX, false);
    let elf = Elf::parse(&obj);
    for (name, sh_type, target, retained) in [
        (".init_array", SHT_INIT_ARRAY, "tcg_ctor", true),
        (".init_array.00101", SHT_INIT_ARRAY, "tcg_ctor_early", false),
        (".fini_array", SHT_FINI_ARRAY, "tcg_dtor", false),
    ] {
        let index = elf.index_of(name);
        let section = &elf.sections[index];
        assert_eq!(section.sh_type, sh_type, "{name}");
        let want_flags = SHF_ALLOC | SHF_WRITE | if retained { SHF_GNU_RETAIN } else { 0 };
        assert_eq!(section.flags, want_flags, "{name}");
        assert_eq!(
            (section.size, section.entsize, section.align),
            (8, 8, 8),
            "{name}"
        );
        assert_eq!(elf.data(index), &[0u8; 8], "{name}: RELA slot placeholder");
        let relas = elf.relas(index);
        assert_eq!(relas.len(), 1, "{name}");
        assert_eq!(relas[0].rtype, R_AARCH64_ABS64, "{name}");
        assert_eq!((relas[0].offset, relas[0].addend), (0, 0), "{name}");
        assert_eq!(elf.symbol_name(relas[0].symbol), target, "{name}");
    }
    assert_eq!(elf.osabi, 3, "SHF_GNU_RETAIN requires ELFOSABI_GNU");

    let sections = readelf(&obj, &["-S"], "ctor-S");
    for needle in [".init_array ", ".init_array.00101", ".fini_array"] {
        let line = sections
            .lines()
            .find(|line| line.contains(needle))
            .unwrap_or_else(|| panic!("readelf -S lists {needle}:\n{sections}"));
        let kind = if needle.starts_with(".fini") {
            "FINI_ARRAY"
        } else {
            "INIT_ARRAY"
        };
        assert!(line.contains(kind), "{line}");
    }
    let relocations = readelf(&obj, &["-r"], "ctor-r");
    for target in ["tcg_ctor", "tcg_ctor_early", "tcg_dtor"] {
        assert!(
            relocations
                .lines()
                .any(|line| line.contains("R_AARCH64_ABS64") && line.contains(target)),
            "readelf -r: ABS64 against {target}:\n{relocations}"
        );
    }
}

/// `.preinit_array` is the third constructor-table type.
#[test]
fn preinit_array_is_a_typed_pointer_table() {
    let mut module = constructor_module();
    module.globals[3].section = Some(".preinit_array".to_string());
    let elf = Elf::parse(&compile(&module, LINUX, false));
    let section = elf.section(".preinit_array");
    assert_eq!(section.sh_type, SHT_PREINIT_ARRAY);
    assert_eq!(section.entsize, 8);
}

/// Named sections keep flags derived from the name's kind and the global,
/// the declared alignment, and a relocated slot's `R_AARCH64_ABS64` lands in
/// the named section's own `.rela` at the member's offset. Two globals
/// naming one section share it, packed in declaration order.
#[test]
fn named_sections_keep_flags_alignment_and_retarget_relocations() {
    let mut module = three_function_module();
    let mut mutable = global("tcg_rw", Ty::U64, u64_value(11), Linkage::External);
    mutable.mutable = true;
    mutable.section = Some("tcg_custom_rw".into());
    let mut constant = global("tcg_ro", Ty::U64, u64_value(22), Linkage::External);
    constant.section = Some(".rodata.tcg".into());
    let mut aligned = global("tcg_aligned", Ty::U64, u64_value(33), Linkage::External);
    aligned.align = Some(64);
    aligned.section = Some("tcg_shared_sec".into());
    let mut first = global("tcg_first", Ty::U64, u64_value(44), Linkage::External);
    first.section = Some("tcg_shared_sec".into());
    let mut table = global(
        "tcg_fn_table",
        Ty::Ptr,
        Constant::SymbolAddr {
            symbol: "tcg_leaf".into(),
            addend: 4,
        },
        Linkage::External,
    );
    table.section = Some(".data.rel.ro.tcg".into());
    let mut tls = global("tcg_tls", Ty::U64, u64_value(55), Linkage::External);
    tls.mutable = true;
    tls.tls = Some(trust_ir::TlsModel::LocalExec);
    tls.section = Some(".tdata.tcg".into());
    module.globals = vec![mutable, constant, first, aligned, table, tls];
    let obj = compile(&module, LINUX, false);
    let elf = Elf::parse(&obj);

    assert_eq!(elf.section_of("tcg_rw").name, "tcg_custom_rw");
    assert_eq!(elf.section_of("tcg_rw").flags, SHF_ALLOC | SHF_WRITE);
    assert_eq!(elf.section_of("tcg_ro").name, ".rodata.tcg");
    assert_eq!(elf.section_of("tcg_ro").flags, SHF_ALLOC);
    assert_eq!(
        elf.section_of("tcg_tls").flags,
        SHF_ALLOC | SHF_WRITE | SHF_TLS
    );
    assert_eq!(elf.symbol("tcg_tls").sym_type, 6, "STT_TLS");

    // Shared section: declaration order, over-alignment preserved.
    let shared = elf.index_of("tcg_shared_sec");
    assert_eq!(
        elf.sections[shared].flags, SHF_ALLOC,
        "immutable relocation-free"
    );
    assert_eq!(elf.sections[shared].align, 64);
    assert_eq!(elf.symbol("tcg_first").shndx as usize, shared);
    assert_eq!(elf.symbol("tcg_aligned").shndx as usize, shared);
    assert_eq!(elf.symbol("tcg_first").value, 0);
    assert_eq!(elf.symbol("tcg_aligned").value, 64);
    assert_eq!(&elf.data(shared)[64..72], &33u64.to_le_bytes());

    // The pointer slot's relocation is retargeted into its named section.
    let table_index = elf.index_of(".data.rel.ro.tcg");
    assert_eq!(elf.sections[table_index].flags, SHF_ALLOC | SHF_WRITE);
    let relas = elf.relas(table_index);
    assert_eq!(relas.len(), 1);
    assert_eq!(relas[0].rtype, R_AARCH64_ABS64);
    assert_eq!(relas[0].offset, elf.symbol("tcg_fn_table").value);
    assert_eq!(relas[0].addend, 4);
    assert_eq!(elf.symbol_name(relas[0].symbol), "tcg_leaf");
    assert!(
        !elf.has(".data") && !elf.has(".rodata"),
        "no implicit sections were needed"
    );

    let sections = readelf(&obj, &["-S"], "named-S");
    for (name, flags) in [
        ("tcg_custom_rw", " WA "),
        (".rodata.tcg", " A "),
        (".data.rel.ro.tcg", " WA "),
        (".tdata.tcg", " WAT "),
    ] {
        let line = sections
            .lines()
            .find(|line| line.contains(&format!(" {name} ")))
            .unwrap_or_else(|| panic!("readelf -S lists {name}:\n{sections}"));
        assert!(line.contains("PROGBITS") && line.contains(flags), "{line}");
    }
    let relocations = readelf(&obj, &["-r"], "named-r");
    assert!(
        relocations.contains(".rela.data.rel.ro.tcg"),
        "relocation section is named after the placed section:\n{relocations}"
    );
}

/// Every request the ELF emitter cannot honor is a NAMED refusal, never a
/// silent fallback to the default placement, at O0 and at O2.
#[test]
fn unhonorable_elf_sections_are_refused_by_name() {
    let refusal = |mutate: &dyn Fn(&mut Module), code: &str| {
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            let mut module = constructor_module();
            mutate(&mut module);
            let error = compile_with(&module, LINUX, opt_level, false)
                .expect_err("placement must be refused");
            assert!(
                error.contains(code),
                "{opt_level:?}: expected {code}: {error}"
            );
        }
    };
    refusal(
        &|m| m.globals[0].section = Some(".text.tcg".into()),
        "TCG-SECTION-EXEC",
    );
    // Zero-fill names: `tcg_state` is all-zero, so `.bss.tcg` alone is now
    // placed as SHT_NOBITS (`explicit_zero_fill_sections_are_nobits_without_
    // file_bytes`); a nonzero initializer or a relocated pointer slot in any
    // zero-fill family stays refused by name, and so does a TLS mismatch.
    refusal(
        &|m| {
            m.globals[0].initializer = Some(u64_value(1));
            m.globals[0].section = Some(".bss.tcg".into());
        },
        "TCG-SECTION-NOBITS",
    );
    for name in [".bss", ".sbss", ".sbss.tcg", ".lbss", ".lbss.tcg"] {
        refusal(
            &|m| {
                m.globals[0].initializer = Some(u64_value(0x100));
                m.globals[0].section = Some(name.into());
            },
            "TCG-SECTION-NOBITS",
        );
    }
    refusal(
        &|m| {
            m.globals[0].initializer = Some(u64_value(1));
            m.globals[0].tls = Some(trust_ir::TlsModel::LocalExec);
            m.globals[0].section = Some(".tbss.tcg".into());
        },
        "TCG-SECTION-NOBITS",
    );
    // All-zero bytes, but the slot is a relocated pointer to patch.
    refusal(
        &|m| m.globals[1].section = Some(".bss.tcg_table".into()),
        "TCG-SECTION-NOBITS",
    );
    refusal(
        &|m| m.globals[0].section = Some(".tbss.tcg".into()),
        "TCG-SECTION-TLS",
    );
    // lld folds `.bss.rel.ro[.*]` into PT_GNU_RELRO, so the mutable
    // all-zero `tcg_state` there would fault on its first store under lld.
    for name in [".bss.rel.ro", ".bss.rel.ro.tcg"] {
        refusal(
            &|m| m.globals[0].section = Some(name.into()),
            "TCG-SECTION-READONLY",
        );
    }
    refusal(
        &|m| {
            m.globals[0].tls = Some(trust_ir::TlsModel::LocalExec);
            m.globals[0].section = Some(".bss.tcg".into());
        },
        "TCG-SECTION-TLS",
    );
    refusal(
        &|m| m.globals[1].section = Some(".ctors".into()),
        "TCG-SECTION-CTORS",
    );
    refusal(
        &|m| m.globals[0].section = Some(".symtab".into()),
        "TCG-SECTION-RESERVED",
    );
    refusal(
        &|m| m.globals[0].section = Some("__DATA,__data".into()),
        "TCG-SECTION-NAME",
    );
    refusal(
        &|m| m.globals[0].section = Some(".rodata.state".into()),
        "TCG-SECTION-READONLY",
    );
    refusal(
        &|m| m.globals[0].section = Some(".tdata.state".into()),
        "TCG-SECTION-TLS",
    );
    // A raw constant is not a callable constructor entry.
    refusal(
        &|m| m.globals[0].section = Some(".init_array".into()),
        "TCG-SECTION-POINTER-TABLE",
    );
    // A mutable and an immutable global cannot share one custom section.
    refusal(
        &|m| {
            m.globals[0].section = Some("tcg_mixed".into());
            let mut constant = global("tcg_const", Ty::U64, u64_value(1), Linkage::External);
            constant.section = Some("tcg_mixed".into());
            m.globals.push(constant);
        },
        "TCG-SECTION-FLAGS",
    );
    // An import places no bytes here.
    refusal(
        &|m| {
            let mut import = global("tcg_import", Ty::U64, u64_value(0), Linkage::External);
            import.initializer = None;
            import.section = Some(".data.tcg".into());
            m.globals.push(import);
        },
        "TCG-SECTION-IMPORT",
    );
    // Names the default links of GNU ld 2.42 or LLD 22.1.6 put outside plain
    // writable data (object_sections::ELF_NAME_RULES), for the mutable
    // all-zero `tcg_state`: the independent verifier's list first (each was
    // a writable PROGBITS catch-all admission whose store faults under GNU
    // ld, `.jcr` under LLD too), then a sample of every derived class. The
    // Linux native control `refused_sections_fault_or_misplace_trust_cg_bytes`
    // links trust-cg's own bytes under each name to show the hazard.
    for (name, code) in [
        (".tcommon", "TCG-SECTION-TLS"),
        (".gnu_extab", "TCG-SECTION-RESERVED"),
        (".gcc_except_table.x", "TCG-SECTION-RESERVED"),
        (".exception_ranges", "TCG-SECTION-RESERVED"),
        (".sframe", "TCG-SECTION-RESERVED"),
        (".eh_frame.x", "TCG-SECTION-RESERVED"),
        (".jcr", "TCG-SECTION-RESERVED"),
        // Unwind and exception tables.
        (".gnu_extab.x", "TCG-SECTION-RESERVED"),
        (".exception_ranges.x", "TCG-SECTION-RESERVED"),
        (".sframe.x", "TCG-SECTION-RESERVED"),
        (".eh_frame_entry", "TCG-SECTION-RESERVED"),
        // BFD parses every input whose name STARTS with `.eh_frame_entry`
        // as compact unwind entries (no `.` boundary), and the GNU link then
        // fails; the verifier's sweep found these five spellings admitted.
        (".eh_frame_entryx", "TCG-SECTION-RESERVED"),
        (".eh_frame_entry1", "TCG-SECTION-RESERVED"),
        (".eh_frame_entry_x", "TCG-SECTION-RESERVED"),
        (".eh_frame_entry-x", "TCG-SECTION-RESERVED"),
        (".eh_frame_entry$x", "TCG-SECTION-RESERVED"),
        // Executable outputs.
        (".stub", "TCG-SECTION-EXEC"),
        (".iplt", "TCG-SECTION-EXEC"),
        // Read-only or PT_GNU_RELRO outputs under either linker.
        (".rodata1", "TCG-SECTION-READONLY"),
        (".toc", "TCG-SECTION-READONLY"),
        (".data.rel.ro.local", "TCG-SECTION-READONLY"),
        // Linker-owned, name-typed, unloaded and discarded outputs.
        (".igot", "TCG-SECTION-RESERVED"),
        (".igot.plt", "TCG-SECTION-RESERVED"),
        (".relro_padding", "TCG-SECTION-RESERVED"),
        ("COMMON", "TCG-SECTION-RESERVED"),
        (".rela_x", "TCG-SECTION-RESERVED"),
        (".relative", "TCG-SECTION-RESERVED"),
        (".relr.dyn", "TCG-SECTION-RESERVED"),
        (".stab", "TCG-SECTION-RESERVED"),
        (".stabstr", "TCG-SECTION-RESERVED"),
        (".stab.index", "TCG-SECTION-RESERVED"),
        (".line", "TCG-SECTION-RESERVED"),
        (".gnu_debuglink", "TCG-SECTION-RESERVED"),
        // A table crtbegin/crtend bracket.
        (".tm_clone_table", "TCG-SECTION-RESERVED"),
    ] {
        refusal(&|m| m.globals[0].section = Some(name.into()), code);
    }
    // Constructor tables are inside PT_GNU_RELRO under both linkers: a
    // MUTABLE table (every slot still a relocated pointer) is refused.
    for name in [".init_array", ".fini_array.00100", ".preinit_array"] {
        refusal(
            &|m| {
                m.globals[1].mutable = true;
                m.globals[1].section = Some(name.into());
            },
            "TCG-SECTION-READONLY",
        );
    }
}

/// A COMDAT definition's implicit section is `<base>.<symbol>`, which the
/// linkers place by name like any other input. A mutable link-once global
/// whose symbol is literally `rel.ro` (or starts `rel.ro.`) would get
/// `.data.rel.ro` (PT_GNU_RELRO under GNU ld and LLD) or, all-zero,
/// `.bss.rel.ro` (PT_GNU_RELRO under LLD): it is refused by name as
/// `[TCG-SECTION-READONLY]`, naming the implicit section. The same symbol
/// in every class that stays in its base's rule (immutable `.rodata.rel.ro`,
/// thread-local `.tdata.rel.ro`/`.tbss.rel.ro`) and a neighbouring
/// `rel.rox` keep their grouped sections.
#[test]
fn implicit_comdat_sections_leaving_their_placement_rule_are_refused_by_name() {
    let comdat = |name: &str, value: u64, mutable: bool, tls: bool| {
        let mut module = Module::new("tcg_comdat_name");
        let mut g = global(name, Ty::U64, u64_value(value), Linkage::LinkOnceOdr);
        g.mutable = mutable;
        if tls {
            g.tls = Some(trust_ir::TlsModel::LocalExec);
        }
        module.globals.push(g);
        define(
            &mut module,
            "tcg_comdat_addr",
            vec![Ty::Ptr],
            Linkage::External,
            vec![
                node(
                    Inst::GlobalAddr {
                        global: GlobalId::new(0),
                    },
                    0,
                ),
                ret(&[0]),
            ],
        );
        module
    };
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        for (name, value, section) in [
            ("rel.ro", 7, ".data.rel.ro"),
            ("rel.ro.local", 7, ".data.rel.ro.local"),
            ("rel.ro", 0, ".bss.rel.ro"),
            ("rel.ro.x", 0, ".bss.rel.ro.x"),
        ] {
            let error = compile_with(&comdat(name, value, true, false), LINUX, opt_level, false)
                .expect_err("the colliding implicit COMDAT section must be refused");
            assert!(
                error.contains("[TCG-SECTION-READONLY]")
                    && error.contains(&format!("implicit ELF COMDAT section `{section}`"))
                    && error.contains("PT_GNU_RELRO"),
                "{opt_level:?} {name}: {error}"
            );
        }
        for (name, value, mutable, tls, section, flags) in [
            (
                "rel.ro",
                7,
                false,
                false,
                ".rodata.rel.ro",
                SHF_ALLOC | SHF_GROUP,
            ),
            (
                "rel.ro",
                7,
                true,
                true,
                ".tdata.rel.ro",
                SHF_ALLOC | SHF_WRITE | SHF_TLS | SHF_GROUP,
            ),
            (
                "rel.ro",
                0,
                true,
                true,
                ".tbss.rel.ro",
                SHF_ALLOC | SHF_WRITE | SHF_TLS | SHF_GROUP,
            ),
            (
                "rel.rox",
                7,
                true,
                false,
                ".data.rel.rox",
                SHF_ALLOC | SHF_WRITE | SHF_GROUP,
            ),
        ] {
            let object = compile_with(&comdat(name, value, mutable, tls), LINUX, opt_level, false)
                .unwrap_or_else(|error| panic!("{opt_level:?} {section}: {error}"));
            let elf = Elf::parse(&object);
            let placed = elf.section_of(name);
            assert_eq!(
                (placed.name.as_str(), placed.flags),
                (section, flags),
                "{opt_level:?} {name}"
            );
            assert_eq!(
                elf.groups(),
                vec![(name.to_string(), vec![elf.index_of(section) as u32])],
                "{opt_level:?} {section}"
            );
        }
    }
}

/// Names one character past a linker family, or that neither default link
/// names, are orphans under GNU ld 2.42 and LLD 22.1.6 unless BFD matches
/// them by a raw name prefix (`.eh_frame_entry*`, `.rela*`: refused, see
/// `unhonorable_elf_sections_are_refused_by_name`); each of these keeps the
/// global's own flags (writable when mutable, `SHF_ALLOC` alone when
/// immutable), as do the immutable-only families (`.rodata1`, `.toc`,
/// `.data.rel.ro.*`) for an immutable global. Cross-checked with an
/// external readelf.
#[test]
fn boundary_section_names_keep_the_global_flags() {
    const WRITABLE: [&str; 16] = [
        ".data.tcg",
        ".data1",
        ".data.rel.rox",
        ".tcommon.x",
        ".jcrx",
        ".eh_framex",
        // One character short of BFD's `.eh_frame_entry` prefix.
        ".eh_frame_entq",
        ".sframex",
        ".rodata1.x",
        ".stabx",
        ".linex",
        ".relro",
        ".ldata.tcg",
        ".gnu_debugaltlink",
        "COMMONS",
        "tcg_custom_rw",
    ];
    const IMMUTABLE: [&str; 3] = [".rodata1", ".toc", ".data.rel.ro.tcg"];
    let mut module = Module::new("tcg_boundary_sections");
    for (index, name) in WRITABLE.iter().enumerate() {
        let mut g = global(
            &format!("tcg_rw_{index}"),
            Ty::U64,
            u64_value(index as u64 + 1),
            Linkage::External,
        );
        g.mutable = true;
        g.section = Some(name.to_string());
        module.globals.push(g);
    }
    for (index, name) in IMMUTABLE.iter().enumerate() {
        let mut g = global(
            &format!("tcg_ro_{index}"),
            Ty::U64,
            u64_value(index as u64 + 100),
            Linkage::External,
        );
        g.section = Some(name.to_string());
        module.globals.push(g);
    }
    // A module needs a function to compile.
    define(
        &mut module,
        "tcg_boundary_anchor",
        vec![Ty::U64],
        Linkage::External,
        vec![const_u64(1, 0), ret(&[0])],
    );
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let object = compile_with(&module, LINUX, opt_level, false)
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
        let elf = Elf::parse(&object);
        for (index, name) in WRITABLE.iter().enumerate() {
            let placed = elf.section_of(&format!("tcg_rw_{index}"));
            assert_eq!(
                (placed.name.as_str(), placed.sh_type, placed.flags),
                (*name, SHT_PROGBITS, SHF_ALLOC | SHF_WRITE),
                "{opt_level:?}"
            );
        }
        for (index, name) in IMMUTABLE.iter().enumerate() {
            let placed = elf.section_of(&format!("tcg_ro_{index}"));
            let flags = if name.starts_with(".data") {
                SHF_ALLOC | SHF_WRITE
            } else {
                SHF_ALLOC
            };
            assert_eq!(
                (placed.name.as_str(), placed.sh_type, placed.flags),
                (*name, SHT_PROGBITS, flags),
                "{opt_level:?}"
            );
        }
        let listing = readelf(&object, &["-S"], "boundary-S");
        for name in WRITABLE {
            let line = listing
                .lines()
                .find(|line| line.contains(&format!(" {name} ")))
                .unwrap_or_else(|| panic!("readelf -S lists {name}:\n{listing}"));
            assert!(line.contains("PROGBITS") && line.contains(" WA "), "{line}");
        }
    }
}

/// Size of the explicit `.bss.tcg_big` global. Its file footprint must be 0.
const ZF_BIG: usize = 2 << 20;
const SHT_NOBITS: u32 = 8;
const STT_OBJECT: u8 = 1;
const STT_TLS: u8 = 6;

/// `g += 3; return g` on the u64 global at `global_index`.
fn add_three(global_index: u32) -> Vec<InstrNode> {
    vec![
        node(
            Inst::GlobalAddr {
                global: GlobalId::new(global_index),
            },
            0,
        ),
        node(
            Inst::Load {
                ty: Ty::U64,
                ptr: ValueId::new(0),
                volatile: true,
                align: Some(8),
            },
            1,
        ),
        const_u64(3, 2),
        node(
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U64,
                lhs: ValueId::new(1),
                rhs: ValueId::new(2),
            },
            3,
        ),
        InstrNode::new(Inst::Store {
            ty: Ty::U64,
            ptr: ValueId::new(0),
            value: ValueId::new(3),
            volatile: true,
            align: Some(8),
        }),
        ret(&[3]),
    ]
}

/// All-zero, relocation-free globals placed by name in every zero-fill
/// family, each with a `<name>_addr` accessor, and `<name>_bump` (`+= 3`)
/// for the u64 ones:
///
/// | global | section | shape |
/// | --- | --- | --- |
/// | `tcg_zf_big` | `.bss.tcg_big` | mutable `[u8; ZF_BIG]`, align 256 |
/// | `tcg_zf_a` | `.bss.tcg_shared` | mutable u64 |
/// | `tcg_zf_b` | `.bss.tcg_shared` | immutable `[u64; 2]`, align 16 |
/// | `tcg_zf_sbss` | `.sbss` | mutable u32 |
/// | `tcg_zf_lbss` | `.lbss.tcg` | mutable `[u64; 64]`, align 64 |
/// | `tcg_zf_tls` | `.tbss.tcg` | thread-local `[u64; 4]`, align 64 |
/// | `tcg_zf_comdat` | `.bss.tcg_comdat` | link-once-ODR u64 (grouped) |
/// | `tcg_zf_local` | `.bss.tcg_shared` | internal u64 |
fn explicit_zero_fill_module() -> Module {
    let mut module = Module::new("tcg_explicit_zero_fill");
    let byte = module
        .add_type(Ty::U8)
        .expect("Module::add_type: test fixture");
    let word = module
        .add_type(Ty::U64)
        .expect("Module::add_type: test fixture");
    // An all-zero array is spelled as the splat of its zero element (trust-ir
    // SPEC_RATIFICATIONS §3.1 refuses uniform raw bytes at an array type); a
    // scalar is its typed zero (trust-ir types a global's initializer against
    // the global, so raw bytes are no constant of `u64`). Both spellings reach
    // the zero-fill.
    let zeros = |ty: &Ty| match ty {
        Ty::Array(_, len) => Constant::splat(Constant::Int(0), *len),
        _ => Constant::Int(0),
    };
    let placed = |name: &str, ty: Ty, section: &str, align: Option<u32>| {
        let initializer = zeros(&ty);
        let mut g = global(name, ty, initializer, Linkage::External);
        g.mutable = true;
        g.align = align;
        g.section = Some(section.into());
        g
    };
    let mut constant = placed("tcg_zf_b", Ty::Array(word, 2), ".bss.tcg_shared", Some(16));
    constant.mutable = false;
    let mut tls = placed("tcg_zf_tls", Ty::Array(word, 4), ".tbss.tcg", Some(64));
    tls.tls = Some(trust_ir::TlsModel::LocalExec);
    let mut comdat = placed("tcg_zf_comdat", Ty::U64, ".bss.tcg_comdat", None);
    comdat.linkage = Linkage::LinkOnceOdr;
    let mut local = placed("tcg_zf_local", Ty::U64, ".bss.tcg_shared", None);
    local.linkage = Linkage::Internal;
    module.globals = vec![
        placed(
            "tcg_zf_big",
            Ty::Array(byte, ZF_BIG as u64),
            ".bss.tcg_big",
            Some(256),
        ),
        placed("tcg_zf_a", Ty::U64, ".bss.tcg_shared", None),
        constant,
        placed("tcg_zf_sbss", Ty::U32, ".sbss", None),
        placed("tcg_zf_lbss", Ty::Array(word, 64), ".lbss.tcg", Some(64)),
        tls,
        comdat,
        local,
    ];
    let names: Vec<String> = module.globals.iter().map(|g| g.name.clone()).collect();
    for (index, name) in names.iter().enumerate() {
        define(
            &mut module,
            &format!("{name}_addr"),
            vec![Ty::Ptr],
            Linkage::External,
            vec![
                node(
                    Inst::GlobalAddr {
                        global: GlobalId::new(index as u32),
                    },
                    0,
                ),
                ret(&[0]),
            ],
        );
    }
    for (name, index) in [
        ("tcg_zf_a", 1),
        ("tcg_zf_tls", 5),
        ("tcg_zf_comdat", 6),
        ("tcg_zf_local", 7),
    ] {
        define(
            &mut module,
            &format!("{name}_bump"),
            vec![Ty::U64],
            Linkage::External,
            add_three(index),
        );
    }
    module
}

/// One row of [`EXPLICIT_ZERO_FILL`], in the column order its doc names.
type ZeroFillRow = (&'static str, &'static str, u64, u64, u64, u64, u64, u8, u8);

/// Expected (symbol, section, sh_flags, section size, section align, symbol
/// value, symbol size, STB_*, STT_*) of [`explicit_zero_fill_module`].
const EXPLICIT_ZERO_FILL: [ZeroFillRow; 8] = [
    (
        "tcg_zf_big",
        ".bss.tcg_big",
        SHF_ALLOC | SHF_WRITE,
        ZF_BIG as u64,
        256,
        0,
        ZF_BIG as u64,
        STB_GLOBAL,
        STT_OBJECT,
    ),
    (
        "tcg_zf_a",
        ".bss.tcg_shared",
        SHF_ALLOC | SHF_WRITE,
        40,
        16,
        0,
        8,
        STB_GLOBAL,
        STT_OBJECT,
    ),
    (
        "tcg_zf_b",
        ".bss.tcg_shared",
        SHF_ALLOC | SHF_WRITE,
        40,
        16,
        16,
        16,
        STB_GLOBAL,
        STT_OBJECT,
    ),
    // Without an explicit `align`, a global's alignment is floored at 8.
    (
        "tcg_zf_sbss",
        ".sbss",
        SHF_ALLOC | SHF_WRITE,
        4,
        8,
        0,
        4,
        STB_GLOBAL,
        STT_OBJECT,
    ),
    (
        "tcg_zf_lbss",
        ".lbss.tcg",
        SHF_ALLOC | SHF_WRITE,
        512,
        64,
        0,
        512,
        STB_GLOBAL,
        STT_OBJECT,
    ),
    (
        "tcg_zf_tls",
        ".tbss.tcg",
        SHF_ALLOC | SHF_WRITE | SHF_TLS,
        32,
        64,
        0,
        32,
        STB_GLOBAL,
        STT_TLS,
    ),
    (
        "tcg_zf_comdat",
        ".bss.tcg_comdat",
        SHF_ALLOC | SHF_WRITE | SHF_GROUP,
        8,
        8,
        0,
        8,
        STB_WEAK,
        STT_OBJECT,
    ),
    (
        "tcg_zf_local",
        ".bss.tcg_shared",
        SHF_ALLOC | SHF_WRITE,
        40,
        16,
        32,
        8,
        STB_LOCAL,
        STT_OBJECT,
    ),
];

/// Explicit zero-fill names (`.bss*`, `.tbss*`, `.sbss`, `.lbss*`) holding
/// all-zero, relocation-free globals are `SHT_NOBITS` at O0-O3, with the
/// family's flags (`SHF_TLS` on `.tbss`), each member's alignment and
/// offset, `STT_TLS` for the template and no file bytes; members naming one
/// section share it, and a COMDAT definition naming `.bss.*` is that
/// section alone inside its group. No relocation patches a zero-fill
/// section. The constructor module's all-zero `tcg_state`, whose `.bss.tcg`
/// request the refusal test used to pin, now lands in a NOBITS `.bss.tcg`.
/// Cross-checked with an external readelf.
#[test]
fn explicit_zero_fill_sections_are_nobits_without_file_bytes() {
    let module = explicit_zero_fill_module();
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let obj = compile_with(&module, LINUX, opt_level, false)
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
        let elf = Elf::parse(&obj);
        assert!(
            obj.len() < 64 << 10,
            "{opt_level:?}: {ZF_BIG} zero bytes inflated the object to {} bytes",
            obj.len()
        );
        for (symbol, section, flags, size, align, value, symbol_size, bind, kind) in
            EXPLICIT_ZERO_FILL
        {
            let index = elf.index_of(section);
            let header = &elf.sections[index];
            assert_eq!(
                (header.sh_type, header.flags, header.size, header.align),
                (SHT_NOBITS, flags, size, align),
                "{opt_level:?} {section}"
            );
            assert!(elf.relas(index).is_empty(), "{opt_level:?} {section}");
            let sym = elf.symbol(symbol);
            assert_eq!(
                (
                    sym.shndx as usize,
                    sym.value,
                    sym.size,
                    sym.bind,
                    sym.sym_type
                ),
                (index, value, symbol_size, bind, kind),
                "{opt_level:?} {symbol}"
            );
        }
        assert_eq!(
            elf.groups(),
            vec![(
                "tcg_zf_comdat".to_string(),
                vec![elf.index_of(".bss.tcg_comdat") as u32]
            )],
            "{opt_level:?}"
        );
        assert!(
            !elf.has(".bss") && !elf.has(".data") && !elf.has(".tbss"),
            "{opt_level:?}: every global kept its explicit name"
        );
    }

    let listing = readelf(
        &compile(&module, LINUX, false),
        &["-S"],
        "explicit-zero-fill-S",
    );
    for (name, flags) in [
        (".bss.tcg_big", " WA "),
        (".bss.tcg_shared", " WA "),
        (".sbss", " WA "),
        (".lbss.tcg", " WA "),
        (".tbss.tcg", " WAT "),
        (".bss.tcg_comdat", " WAG "),
    ] {
        let line = listing
            .lines()
            .find(|line| line.contains(&format!(" {name} ")))
            .unwrap_or_else(|| panic!("readelf -S lists {name}:\n{listing}"));
        assert!(line.contains("NOBITS") && line.contains(flags), "{line}");
    }

    // The refusal test's former `.bss.tcg` pin on the all-zero `tcg_state`.
    let mut constructors = constructor_module();
    constructors.globals[0].section = Some(".bss.tcg".into());
    let elf = Elf::parse(&compile(&constructors, LINUX, false));
    let state = elf.section_of("tcg_state");
    assert_eq!(
        (
            state.name.as_str(),
            state.sh_type,
            state.flags,
            state.size,
            state.align
        ),
        (".bss.tcg", SHT_NOBITS, SHF_ALLOC | SHF_WRITE, 8, 8)
    );
}

/// Function sections split every function into `.text.<symbol>`: each body
/// is byte-identical to its bytes in the one-`.text` object, the call
/// relocation lands in the caller's own `.rela` at a `BL`, and every FDE is
/// anchored at its own section's local `STT_SECTION` symbol with addend 0.
#[test]
fn function_sections_split_bodies_and_anchor_relocations_per_section() {
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let module = three_function_module();
        let packed =
            Elf::parse(&compile_with(&module, LINUX, opt_level, false).expect("one .text object"));
        let split_bytes = compile_with(&module, LINUX, opt_level, true).expect("split object");
        let split = Elf::parse(&split_bytes);
        assert!(packed.has(".text"));
        assert!(
            !split.has(".text"),
            "{opt_level:?}: no function stays packed"
        );

        let text = packed.index_of(".text");
        for name in ["tcg_leaf", "tcg_caller", "tcg_unused"] {
            let section_name = format!(".text.{name}");
            let index = split.index_of(&section_name);
            let section = &split.sections[index];
            assert_eq!(section.sh_type, SHT_PROGBITS);
            assert_eq!(section.flags, SHF_ALLOC | SHF_EXECINSTR, "{section_name}");
            assert_eq!(section.flags & SHF_GROUP, 0, "not a COMDAT");
            let symbol = split.symbol(name);
            assert_eq!(symbol.shndx as usize, index);
            assert_eq!((symbol.value, symbol.bind), (0, STB_GLOBAL));
            assert_eq!(symbol.size, section.size);
            let packed_symbol = packed.symbol(name);
            let start = packed_symbol.value as usize;
            assert_eq!(
                split.data(index),
                &packed.data(text)[start..start + section.size as usize],
                "{opt_level:?} {name}: body bytes are unchanged by the split"
            );
        }

        // Every packed `.text` relocation moved into the section of the
        // function containing it, at the same function-relative offset, with
        // the same type, target and addend (and nothing else was added).
        let mut moved = BTreeSet::new();
        for rela in packed.relas(text) {
            let function = packed
                .symbols
                .iter()
                .find(|symbol| {
                    symbol.shndx as usize == text
                        && symbol.sym_type == 2
                        && (symbol.value..symbol.value + symbol.size).contains(&rela.offset)
                })
                .expect("text relocation inside a function");
            moved.insert((
                format!(".text.{}", function.name),
                rela.offset - function.value,
                rela.rtype,
                packed.symbol_name(rela.symbol).to_string(),
                rela.addend,
            ));
        }
        let mut placed = BTreeSet::new();
        for name in ["tcg_leaf", "tcg_caller", "tcg_unused"] {
            let section = format!(".text.{name}");
            for rela in split.relas(split.index_of(&section)) {
                placed.insert((
                    section.clone(),
                    rela.offset,
                    rela.rtype,
                    split.symbol_name(rela.symbol).to_string(),
                    rela.addend,
                ));
            }
        }
        assert_eq!(moved, placed, "{opt_level:?}");
        if opt_level == OptLevel::O0 {
            // Unoptimized, the caller really calls the leaf through a BL.
            let caller = split.index_of(".text.tcg_caller");
            let calls = split.relas(caller);
            assert_eq!(calls.len(), 1);
            assert_eq!(calls[0].rtype, R_AARCH64_CALL26);
            assert_eq!(split.symbol_name(calls[0].symbol), "tcg_leaf");
            let word = rd_u32(split.data(caller), calls[0].offset as usize);
            assert_eq!(word & 0xfc00_0000, 0x9400_0000, "relocation sits on a BL");
            let leaf = split.index_of(".text.tcg_leaf");
            assert!(split.rela_section_for(leaf).is_none());
        }

        // FDE pc-begin: local section anchors, one per text section.
        let eh = split.index_of(".eh_frame");
        let mut anchored = BTreeSet::new();
        for rela in split.relas(eh) {
            assert_eq!(rela.rtype, R_AARCH64_PREL32);
            assert_eq!(rela.addend, 0);
            let symbol = &split.symbols[rela.symbol as usize];
            assert_eq!((symbol.bind, symbol.sym_type), (STB_LOCAL, STT_SECTION));
            anchored.insert(split.sections[symbol.shndx as usize].name.clone());
        }
        assert_eq!(
            anchored,
            BTreeSet::from([
                ".text.tcg_caller".to_string(),
                ".text.tcg_leaf".to_string(),
                ".text.tcg_unused".to_string()
            ])
        );
    }
    let sections = readelf(
        &compile(&three_function_module(), LINUX, true),
        &["-S"],
        "fsec-S",
    );
    for name in [".text.tcg_leaf", ".text.tcg_caller", ".text.tcg_unused"] {
        assert!(
            sections.lines().any(|line| line.contains(name)
                && line.contains("PROGBITS")
                && line.contains(" AX ")),
            "readelf -S: {name} AX\n{sections}"
        );
    }
}

/// Function sections are an ELF policy: the Mach-O object is unchanged.
#[test]
fn function_sections_leave_macho_objects_unchanged() {
    let module = three_function_module();
    assert_eq!(
        compile(&module, DARWIN, false),
        compile(&module, DARWIN, true)
    );
}

/// Link-once/ODR definitions form COMDAT groups signed by their symbol: the
/// function's `.text.<symbol>` and its `.rela` join the group, the table's
/// `.rodata.<symbol>` forms its own, both symbols are `STB_WEAK`, and the
/// strong external caller stays in the ungrouped `.text`.
#[test]
fn comdat_definitions_form_groups_with_their_relocations() {
    let mut module = comdat_unit("a", 1, Linkage::LinkOnceOdr);
    // Give the COMDAT function (`functions[0]`) a relocation of its own: a
    // call to `tcg_seven`, defined next.
    let seven = FuncId::new(module.functions.len() as u32);
    module.functions[0].blocks[0].body = vec![
        node(
            Inst::Call {
                callee: seven,
                args: vec![],
            },
            0,
        ),
        ret(&[0]),
    ];
    define(
        &mut module,
        "tcg_seven",
        vec![Ty::U64],
        Linkage::External,
        vec![const_u64(7, 0), ret(&[0])],
    );
    let obj = compile(&module, LINUX, false);
    let elf = Elf::parse(&obj);

    let text = elf.index_of(".text.tcg_shared");
    let rela = elf.rela_section_for(text).expect(".rela.text.tcg_shared");
    let table = elf.index_of(".rodata.tcg_shared_table");
    let groups = elf.groups();
    assert_eq!(groups.len(), 2, "{groups:?}");
    assert!(groups.contains(&("tcg_shared".to_string(), vec![text as u32, rela as u32])));
    assert!(groups.contains(&("tcg_shared_table".to_string(), vec![table as u32])));
    for index in [text, rela, table] {
        assert_ne!(
            elf.sections[index].flags & SHF_GROUP,
            0,
            "{}",
            elf.sections[index].name
        );
    }
    assert_eq!(elf.section(".text").flags & SHF_GROUP, 0);
    assert_eq!(elf.symbol("tcg_shared").bind, STB_WEAK);
    assert_eq!(elf.symbol("tcg_shared_table").bind, STB_WEAK);
    assert_eq!(elf.symbol("tcg_from_a").bind, STB_GLOBAL);
    assert_eq!(elf.section_of("tcg_from_a").name, ".text");
    // Every group precedes its members.
    for (index, section) in elf.sections.iter().enumerate() {
        if section.sh_type == SHT_GROUP {
            let members = &groups
                .iter()
                .find(|(sig, _)| *sig == elf.symbol_name(section.info))
                .unwrap()
                .1;
            assert!(members.iter().all(|&member| member as usize > index));
        }
    }

    let listing = readelf(&obj, &["-g"], "comdat-g");
    for needle in [
        "[tcg_shared]",
        "[tcg_shared_table]",
        ".text.tcg_shared",
        ".rela.text.tcg_shared",
        ".rodata.tcg_shared_table",
    ] {
        assert!(listing.contains(needle), "readelf -g: {needle}\n{listing}");
    }
    assert_eq!(
        listing.matches("COMDAT group section").count(),
        2,
        "{listing}"
    );
}

/// `tcg_hook` (linkage under test) returns 7; the strong `tcg_hook_caller`
/// returns `tcg_hook() + 1`.
fn hook_module(hook_linkage: Linkage) -> Module {
    let mut module = Module::new("tcg_interposable_hook");
    let hook = define(
        &mut module,
        "tcg_hook",
        vec![Ty::U64],
        hook_linkage,
        vec![const_u64(7, 0), ret(&[0])],
    );
    define(
        &mut module,
        "tcg_hook_caller",
        vec![Ty::U64],
        Linkage::External,
        vec![
            node(
                Inst::Call {
                    callee: hook,
                    args: vec![],
                },
                0,
            ),
            const_u64(1, 1),
            node(
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::U64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                },
                2,
            ),
            ret(&[2]),
        ],
    );
    module
}

/// Adversarial control for the function-linkage mapping. An interposable
/// (`Weak`, `LinkOnce`) hook is a plain `STB_WEAK` definition in the shared
/// `.text`: another object's definition may replace it at link time, so the
/// O2 caller must keep a relocated call to the symbol instead of absorbing
/// this body (the compiler keeps interposable bodies out of the module inliner
/// and the structural purity inference). The ODR forms are safe to coalesce
/// (every copy is equivalent) and get `STB_WEAK` in a COMDAT group.
#[test]
fn interposable_functions_are_weak_and_never_inlined() {
    for linkage in [Linkage::Weak, Linkage::LinkOnce] {
        let elf = Elf::parse(
            &compile_with(&hook_module(linkage), LINUX, OptLevel::O2, false).expect("compile"),
        );
        let caller = elf.symbol("tcg_hook_caller");
        let caller_text = elf.sections[caller.shndx as usize].name.clone();
        assert!(
            elf.relas(caller.shndx as usize).iter().any(|rela| {
                elf.symbol_name(rela.symbol) == "tcg_hook"
                    && (caller.value..caller.value + caller.size).contains(&rela.offset)
            }),
            "{linkage}: the O2 caller must still call the interposable hook (in {caller_text})"
        );
        let hook = elf.symbol("tcg_hook");
        assert_eq!(hook.bind, STB_WEAK, "{linkage}: interposable definition");
        assert_eq!(elf.sections[hook.shndx as usize].name, ".text", "{linkage}");
        assert!(elf.groups().is_empty(), "{linkage}: no COMDAT group");
    }
    for linkage in [Linkage::LinkOnceOdr, Linkage::WeakOdr] {
        let elf = Elf::parse(
            &compile_with(&hook_module(linkage), LINUX, OptLevel::O2, false).expect("compile"),
        );
        let hook = elf.symbol("tcg_hook");
        assert_eq!(hook.bind, STB_WEAK, "{linkage}");
        assert_eq!(
            elf.sections[hook.shndx as usize].name, ".text.tcg_hook",
            "{linkage}"
        );
        assert_eq!(
            elf.groups()
                .iter()
                .map(|(signature, _)| signature.as_str())
                .collect::<Vec<_>>(),
            vec!["tcg_hook"],
            "{linkage}"
        );
    }
}

/// The JIT installs no object sections: a module carrying an explicit
/// section (here a constructor table) is refused by name, never installed
/// with the placement — and the constructor's run-first semantics — dropped.
/// The same module without the section is JIT-compiled.
#[cfg(target_arch = "aarch64")]
#[test]
fn jit_refuses_explicit_sections_by_name() {
    let mut module = Module::new("tcg_jit_ctor");
    define(
        &mut module,
        "tcg_ctor",
        vec![Ty::U64],
        Linkage::External,
        vec![const_u64(7, 0), ret(&[0])],
    );
    module
        .globals
        .push(pointer_entry("tcg_init_entry", "tcg_ctor", ".init_array"));
    let compiler =
        Compiler::new(CompilerConfig::default()).with_codegen_license(permit_unlicensed());
    let externs = std::collections::HashMap::new();
    let error = match compiler.compile_module_to_jit(&module, &externs) {
        Ok(_) => panic!("a sectioned JIT module must be refused"),
        Err(error) => error.to_string(),
    };
    assert!(
        error.contains("TCG-SECTION-TARGET") && error.contains("JIT"),
        "{error}"
    );
    module.globals[0].section = None;
    compiler
        .compile_module_to_jit(&module, &externs)
        .unwrap_or_else(|error| panic!("the unsectioned control must JIT-compile: {error}"));
}

// =============================================================================
// trust-ir v45 explicit function sections (every host)
// =============================================================================

/// `tcg_value() -> u64` returning `callee() + add`.
fn calls_plus(callee: FuncId, add: i128) -> Vec<InstrNode> {
    vec![
        node(
            Inst::Call {
                callee,
                args: vec![],
            },
            0,
        ),
        const_u64(add, 1),
        node(
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            },
            2,
        ),
        ret(&[2]),
    ]
}

/// The explicit function section of each function in
/// [`sectioned_function_module`]; `None` is the default placement.
const FUNCTION_SECTIONS: [(&str, Option<&str>); 6] = [
    ("tcg_leaf", None),
    ("tcg_hot", Some(".text.hot")),
    ("tcg_cold_a", Some("tcg_cold_code")),
    ("tcg_cold_b", Some("tcg_cold_code")),
    ("tcg_in_text", Some(".text")),
    ("tcg_plain", None),
];

/// `tcg_leaf` (7, weak, so no caller absorbs it at any level) in the default
/// section; `tcg_hot` (`.text.hot`) returns `tcg_leaf() + 1`; `tcg_cold_a` (3)
/// and `tcg_cold_b` (`tcg_leaf() + 2`) share `tcg_cold_code`; `tcg_in_text`
/// (4) names `.text` itself; `tcg_plain` (5) has no section. With `sections`
/// false the same module carries none.
fn sectioned_function_module(sections: bool) -> Module {
    let mut module = Module::new("tcg_function_sections_v45");
    let leaf = define(
        &mut module,
        "tcg_leaf",
        vec![Ty::U64],
        Linkage::Weak,
        vec![const_u64(7, 0), ret(&[0])],
    );
    define(
        &mut module,
        "tcg_hot",
        vec![Ty::U64],
        Linkage::External,
        calls_plus(leaf, 1),
    );
    define(
        &mut module,
        "tcg_cold_a",
        vec![Ty::U64],
        Linkage::External,
        vec![const_u64(3, 0), ret(&[0])],
    );
    define(
        &mut module,
        "tcg_cold_b",
        vec![Ty::U64],
        Linkage::External,
        calls_plus(leaf, 2),
    );
    define(
        &mut module,
        "tcg_in_text",
        vec![Ty::U64],
        Linkage::External,
        vec![const_u64(4, 0), ret(&[0])],
    );
    define(
        &mut module,
        "tcg_plain",
        vec![Ty::U64],
        Linkage::External,
        vec![const_u64(5, 0), ret(&[0])],
    );
    if sections {
        for (function, (name, section)) in module.functions.iter_mut().zip(FUNCTION_SECTIONS) {
            assert_eq!(function.name, name);
            function.section = section.map(str::to_string);
        }
    }
    module
}

/// Where `name` must land, given each function's explicit section in `rows`
/// ([`FUNCTION_SECTIONS`] for [`sectioned_function_module`]).
fn expected_function_section_in(
    rows: &[(&str, Option<&str>)],
    name: &str,
    function_sections: bool,
) -> String {
    match rows
        .iter()
        .find(|(function, _)| *function == name)
        .and_then(|(_, section)| *section)
    {
        Some(section) => section.to_string(),
        None if function_sections => format!(".text.{name}"),
        None => ".text".to_string(),
    }
}

/// A text relocation as `(function, function-relative offset, type, target,
/// addend)`.
type FunctionRelocation = (String, u64, u32, String, i64);

/// Every relocation that patches a function body of [`FUNCTION_SECTIONS`],
/// keyed by the function containing it, wherever that body lives.
fn function_relocations(elf: &Elf) -> BTreeSet<FunctionRelocation> {
    let mut rows = BTreeSet::new();
    for (index, section) in elf.sections.iter().enumerate() {
        if section.sh_type != SHT_RELA || section.name.contains("eh_frame") {
            continue;
        }
        let target = section.info as usize;
        for rela in elf.relas(target) {
            let function = elf
                .symbols
                .iter()
                .find(|symbol| {
                    symbol.shndx as usize == target
                        && symbol.sym_type == 2
                        && (symbol.value..symbol.value + symbol.size).contains(&rela.offset)
                })
                .map_or_else(
                    || format!("<outside a function in section {index}>"),
                    |f| f.name.clone(),
                );
            let base = elf
                .symbols
                .iter()
                .find(|symbol| symbol.name == function)
                .map_or(0, |symbol| symbol.value);
            rows.insert((
                function,
                rela.offset - base,
                rela.rtype,
                elf.symbol_name(rela.symbol).to_string(),
                rela.addend,
            ));
        }
    }
    rows
}

/// Every way `bytes` departs from the explicit-section contract, read by the
/// independent parser: each function's symbol sits in its expected section;
/// every text section is `SHT_PROGBITS` `SHF_ALLOC|SHF_EXECINSTR`, ungrouped
/// and 4-aligned; every `.eh_frame` pc-begin is an `R_AARCH64_PREL32` against
/// the local section symbol of its function's section with the function's
/// offset in it as addend; and the text relocations, keyed by the function
/// containing them, are exactly `expected` (the unsectioned object's).
/// Empty for a faithful object.
fn function_section_mismatches(
    bytes: &[u8],
    function_sections: bool,
    expected: &BTreeSet<FunctionRelocation>,
) -> Vec<String> {
    function_section_mismatches_in(&FUNCTION_SECTIONS, bytes, function_sections, expected)
}

/// [`function_section_mismatches`] for a module whose functions, and their
/// explicit sections, are exactly `rows`.
fn function_section_mismatches_in(
    rows: &[(&str, Option<&str>)],
    bytes: &[u8],
    function_sections: bool,
    expected: &BTreeSet<FunctionRelocation>,
) -> Vec<String> {
    let elf = Elf::parse(bytes);
    let mut mismatches = Vec::new();
    let mut expected_fdes = BTreeSet::new();
    for &(name, _) in rows {
        let want = expected_function_section_in(rows, name, function_sections);
        let symbol = elf.symbol(name);
        let section = &elf.sections[symbol.shndx as usize];
        if section.name != want {
            mismatches.push(format!("{name} is in {} not {want}", section.name));
        }
        if (section.sh_type, section.flags, section.align)
            != (SHT_PROGBITS, SHF_ALLOC | SHF_EXECINSTR, 4)
        {
            mismatches.push(format!("{want}: {section:?}"));
        }
        expected_fdes.insert((section.name.clone(), symbol.value as i64));
    }
    let mut fdes = BTreeSet::new();
    for rela in elf.relas(elf.index_of(".eh_frame")) {
        let symbol = &elf.symbols[rela.symbol as usize];
        if rela.rtype != R_AARCH64_PREL32
            || (symbol.bind, symbol.sym_type) != (STB_LOCAL, STT_SECTION)
        {
            mismatches.push(format!("FDE relocation {rela:?} against {symbol:?}"));
        }
        fdes.insert((
            elf.sections[symbol.shndx as usize].name.clone(),
            rela.addend,
        ));
    }
    if fdes != expected_fdes {
        mismatches.push(format!("FDE anchors {fdes:?} != {expected_fdes:?}"));
    }
    let relocations = function_relocations(&elf);
    if relocations != *expected {
        mismatches.push(format!("text relocations {relocations:?} != {expected:?}"));
    }
    mismatches
}

/// trust-ir v45 `Function.section` through `Compiler::compile` (O0-O3): each
/// named function lands in its section (`.text.hot`; the shared
/// `tcg_cold_code`; `.text` itself), bodies are byte-identical to the
/// unsectioned object's, every call relocation moves into its caller's
/// section at the same function-relative offset, and each FDE is anchored at
/// its function's section. `-ffunction-sections` splits only the unnamed
/// functions. The independent checker refuses four object mutations, and an
/// external readelf agrees on names and flags.
#[test]
fn explicit_function_sections_place_bodies_relocations_and_fdes() {
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let packed_bytes = compile_with(&sectioned_function_module(false), LINUX, opt_level, false)
            .expect("unsectioned object");
        let packed = Elf::parse(&packed_bytes);
        let expected = function_relocations(&packed);
        // The weak leaf is never absorbed: both callers keep their `CALL26`.
        for caller in ["tcg_hot", "tcg_cold_b"] {
            assert!(
                expected
                    .iter()
                    .any(|(function, _, kind, target, _)| function == caller
                        && *kind == R_AARCH64_CALL26
                        && target == "tcg_leaf"),
                "{opt_level:?}: {caller} calls tcg_leaf: {expected:?}"
            );
        }
        for function_sections in [false, true] {
            let label = format!("{opt_level:?} function_sections={function_sections}");
            let bytes = compile_with(
                &sectioned_function_module(true),
                LINUX,
                opt_level,
                function_sections,
            )
            .unwrap_or_else(|error| panic!("{label}: {error}"));
            assert_eq!(
                function_section_mismatches(&bytes, function_sections, &expected),
                Vec::<String>::new(),
                "{label}"
            );
            let elf = Elf::parse(&bytes);
            for section in [".text.hot", "tcg_cold_code"] {
                assert_eq!(
                    elf.section(section).flags & SHF_GROUP,
                    0,
                    "{label}: {section}"
                );
            }
            // The shared section holds both cold bodies, `tcg_cold_a` first.
            let (a, b) = (elf.symbol("tcg_cold_a"), elf.symbol("tcg_cold_b"));
            assert_eq!(a.value, 0, "{label}");
            assert!(
                b.value >= a.size && b.value % 4 == 0,
                "{label}: {a:?} {b:?}"
            );
            assert_eq!(
                elf.section("tcg_cold_code").size,
                b.value + b.size,
                "{label}"
            );

            // Bodies are unchanged by placement (the relocations moved with
            // them, checked above against the unsectioned object).
            for (name, _) in FUNCTION_SECTIONS {
                let symbol = elf.symbol(name);
                let before = packed.symbol(name);
                let len = symbol.size.min(before.size) as usize;
                let at = |elf: &Elf, symbol: &Symbol| {
                    let start = symbol.value as usize;
                    elf.data(symbol.shndx as usize)[start..start + len].to_vec()
                };
                assert_eq!(
                    at(&elf, symbol),
                    at(&packed, before),
                    "{label}: {name} body"
                );
            }

            // Mutation controls: the checker is load-bearing for each fact.
            let hot = elf.index_of(".text.hot");
            let header = |index: usize| rd_u64(&bytes, 0x28) as usize + index * 64;
            let mut not_exec = bytes.clone();
            let flags = header(hot) + 8;
            not_exec[flags] &= !(SHF_EXECINSTR as u8);
            let mut moved_symbol = bytes.clone();
            let symtab = elf.sections.iter().position(|s| s.sh_type == 2).unwrap();
            let hot_symbol = elf
                .symbols
                .iter()
                .position(|s| s.name == "tcg_hot")
                .unwrap();
            let shndx = elf.sections[symtab].offset as usize + hot_symbol * 24 + 6;
            let default_text = elf.index_of(".text") as u16;
            moved_symbol[shndx..shndx + 2].copy_from_slice(&default_text.to_le_bytes());
            let mut retargeted_rela = bytes.clone();
            let rela_hot = elf.rela_section_for(hot).expect(".rela.text.hot");
            let info = header(rela_hot) + 0x2c;
            retargeted_rela[info..info + 4].copy_from_slice(&u32::from(default_text).to_le_bytes());
            let mut fde_addend = bytes.clone();
            let eh_rela = elf.rela_section_for(elf.index_of(".eh_frame")).unwrap();
            let cold_b = elf.symbol("tcg_cold_b").value as i64;
            let entry = (0..(elf.sections[eh_rela].size / 24) as usize)
                .map(|i| elf.sections[eh_rela].offset as usize + i * 24)
                .find(|&entry| rd_u64(&bytes, entry + 16) as i64 == cold_b)
                .expect("the tcg_cold_b FDE");
            fde_addend[entry + 16..entry + 24].copy_from_slice(&0i64.to_le_bytes());
            for (mutation, mutated, needle) in [
                ("SHF_EXECINSTR cleared", not_exec, ".text.hot"),
                (
                    "tcg_hot moved to .text",
                    moved_symbol,
                    "tcg_hot is in .text",
                ),
                (
                    ".rela.text.hot retargeted",
                    retargeted_rela,
                    "text relocations",
                ),
                ("tcg_cold_b FDE addend zeroed", fde_addend, "FDE anchors"),
            ] {
                let mismatches =
                    function_section_mismatches(&mutated, function_sections, &expected);
                assert!(
                    mismatches.iter().any(|mismatch| mismatch.contains(needle)),
                    "{label}: {mutation} must be caught: {mismatches:?}"
                );
            }
        }
    }
    let listing = readelf(
        &compile(&sectioned_function_module(true), LINUX, false),
        &["-S"],
        "v45-fsec-S",
    );
    // Relocation sections are `.rela` + the name, the GNU as convention.
    for name in [
        ".text.hot",
        "tcg_cold_code",
        ".rela.text.hot",
        ".relatcg_cold_code",
    ] {
        assert!(
            listing
                .lines()
                .any(|line| line.contains(&format!(" {name} "))),
            "readelf -S: {name}\n{listing}"
        );
    }
    for name in [".text.hot", "tcg_cold_code"] {
        assert!(
            listing
                .lines()
                .any(|line| line.contains(&format!(" {name} "))
                    && line.contains("PROGBITS")
                    && line.contains(" AX ")),
            "readelf -S: {name} AX\n{listing}"
        );
    }
}

/// Unsectioned `() -> u64` leaves appended to [`sectioned_function_module`]
/// so that `Compiler::compile` takes its parallel preparation and emission
/// path (`resource_limits::worker_count_for_items` needs at least 32 items).
const PARALLEL_PADDING: usize = 34;

/// [`sectioned_function_module`] plus [`PARALLEL_PADDING`] default-placed
/// leaves `tcg_pad_NN` (40 definitions).
fn padded_sectioned_function_module(sections: bool) -> Module {
    let mut module = sectioned_function_module(sections);
    for index in 0..PARALLEL_PADDING {
        define(
            &mut module,
            &format!("tcg_pad_{index:02}"),
            vec![Ty::U64],
            Linkage::External,
            vec![const_u64(1000 + index as i128, 0), ret(&[0])],
        );
    }
    module
}

/// The `compile_module` trace entry's account of which preparation and
/// emission path `Compiler::compile` took (`CompilerTraceLevel::Full`).
fn emission_path(result: &CompilationResult) -> String {
    result
        .trace
        .as_ref()
        .expect("CompilerTraceLevel::Full records a trace")
        .entries
        .iter()
        .find(|entry| entry.phase == "compile_module")
        .and_then(|entry| entry.detail.clone())
        .expect("the compile_module trace entry names its emission path")
}

fn compile_traced(
    module: &Module,
    opt_level: OptLevel,
    function_sections: bool,
    parallel: bool,
) -> CompilationResult {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            parallel,
            function_sections,
            trace_level: CompilerTraceLevel::Full,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(LINUX).expect("triple"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .unwrap_or_else(|error| {
        panic!("{opt_level:?} function_sections={function_sections} parallel={parallel}: {error}")
    })
}

/// The explicit-section contract through the PARALLEL preparation and
/// emission path (`compile_module_parallel_emission_with_symbol_linkage`,
/// which wires the ELF text plan separately from the sequential emitter).
/// The 40-definition module crosses the parallel threshold; the compiler
/// trace shows which path each object came from. At O0-O3, with and without
/// `-ffunction-sections`, the parallel object passes the same placement,
/// flag, relocation and FDE checker as the sequential one (every function's
/// FDE included) and is byte-identical to it.
#[test]
fn explicit_function_sections_hold_on_the_parallel_emission_path() {
    let pads: Vec<String> = (0..PARALLEL_PADDING)
        .map(|index| format!("tcg_pad_{index:02}"))
        .collect();
    let rows: Vec<(&str, Option<&str>)> = FUNCTION_SECTIONS
        .iter()
        .copied()
        .chain(pads.iter().map(|pad| (pad.as_str(), None)))
        .collect();
    let functions = padded_sectioned_function_module(true).functions.len();
    assert_eq!(functions, rows.len());
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let packed = compile_traced(
            &padded_sectioned_function_module(false),
            opt_level,
            false,
            false,
        );
        let expected = function_relocations(&Elf::parse(&packed.object_code));
        for function_sections in [false, true] {
            let label = format!("{opt_level:?} function_sections={function_sections}");
            let module = padded_sectioned_function_module(true);
            let sequential = compile_traced(&module, opt_level, function_sections, false);
            let parallel = compile_traced(&module, opt_level, function_sections, true);
            let (sequential_path, parallel_path) =
                (emission_path(&sequential), emission_path(&parallel));
            assert_eq!(
                sequential_path,
                format!("{functions} functions, sequential preparation and emission"),
                "{label}"
            );
            assert!(
                parallel_path.starts_with(&format!(
                    "{functions} functions, parallel preparation and emission, "
                )),
                "{label}: the parallel row ran `{parallel_path}`; worker_count_for_items({functions}) \
                 = {:?} (it needs at least 32 items, TRUST_CG_MAX_PARALLELISM above 1 and two CPUs)",
                trust_cg_codegen::resource_limits::worker_count_for_items(functions)
            );
            for (path, result) in [("sequential", &sequential), ("parallel", &parallel)] {
                assert_eq!(
                    function_section_mismatches_in(
                        &rows,
                        &result.object_code,
                        function_sections,
                        &expected
                    ),
                    Vec::<String>::new(),
                    "{label} {path}"
                );
            }
            assert!(
                parallel.object_code == sequential.object_code,
                "{label}: the parallel object differs from the sequential one"
            );
        }
    }
    println!("explicit function sections on the parallel emission path passed: O0..O3");
}

/// A COMDAT (`LinkOnceOdr`) function with an explicit section is alone in a
/// `GRP_COMDAT` group of that name signed by its weak symbol; its call
/// relocation joins the group. The strong caller stays in `.text`.
#[test]
fn comdat_function_with_an_explicit_section_forms_its_group_under_that_name() {
    let mut module = Module::new("tcg_comdat_section_v45");
    let leaf = define(
        &mut module,
        "tcg_seven",
        vec![Ty::U64],
        Linkage::External,
        vec![const_u64(7, 0), ret(&[0])],
    );
    let odr = define(
        &mut module,
        "tcg_odr",
        vec![Ty::U64],
        Linkage::LinkOnceOdr,
        calls_plus(leaf, 1),
    );
    module.functions[odr.index() as usize].section = Some("tcg_odr_code".into());
    define(
        &mut module,
        "tcg_odr_caller",
        vec![Ty::U64],
        Linkage::External,
        calls_plus(odr, 1),
    );
    let elf = Elf::parse(&compile(&module, LINUX, false));
    let section = elf.index_of("tcg_odr_code");
    let rela = elf.rela_section_for(section).expect(".rela.tcg_odr_code");
    assert_eq!(
        elf.groups(),
        vec![("tcg_odr".to_string(), vec![section as u32, rela as u32])]
    );
    let flags = elf.sections[section].flags;
    assert_eq!(flags, SHF_ALLOC | SHF_EXECINSTR | SHF_GROUP);
    assert_eq!(elf.symbol("tcg_odr").bind, STB_WEAK);
    assert_eq!(elf.section_of("tcg_odr").name, "tcg_odr_code");
    assert_eq!(elf.section_of("tcg_odr_caller").name, ".text");
    assert!(
        !elf.has(".text.tcg_odr"),
        "the explicit name replaces .text.<symbol>"
    );
}

/// Every function section no AArch64 ELF emitter can honour is refused by
/// name before emission: data-class names (including `.jcr`,
/// `.tm_clone_table` and `.rodata1`), the unwind and debug families
/// (`.stab`, `.eh_frame.x`, ...), any other dot-prefixed name outside the
/// `.text` family, reserved names, a Mach-O pair, a
/// name a data global also uses, a COMDAT function naming `.text`, and a
/// malformed name (on every lane). Mach-O, x86-64 and RISC-V refuse the
/// facet itself, and `-g` refuses the split text.
#[test]
fn unhonorable_function_sections_are_refused_by_name() {
    let with_section = |section: &str| {
        let mut module = sectioned_function_module(false);
        module.functions[1].section = Some(section.to_string());
        module
    };
    for (section, needle) in [
        (
            ".data",
            "[TCG-SECTION-DATA] function `tcg_hot` requests ELF section `.data`",
        ),
        (".rodata.hot", "[TCG-SECTION-DATA]"),
        (".bss", "[TCG-SECTION-DATA]"),
        (".init_array", "[TCG-SECTION-DATA]"),
        // GNU ld 2.42's default script maps these into RELRO data, read-only
        // data, unwind or unloaded output; `.jcr` and `.tm_clone_table`
        // linked into an RWX segment and `.jcr` crashed, `.stab` broke the
        // link, before the classifier became an allowlist.
        (
            ".jcr",
            "[TCG-SECTION-DATA] function `tcg_hot` requests ELF section `.jcr`",
        ),
        (".tm_clone_table", "[TCG-SECTION-DATA]"),
        (".rodata1", "[TCG-SECTION-DATA]"),
        (".stab", "[TCG-SECTION-RESERVED] function `tcg_hot`"),
        (".eh_frame.x", "[TCG-SECTION-RESERVED]"),
        (".gcc_except_table.f", "[TCG-SECTION-RESERVED]"),
        (".sframe", "[TCG-SECTION-RESERVED]"),
        (".custom_code", "[TCG-SECTION-RESERVED]"),
        (".init", "[TCG-SECTION-RESERVED] function `tcg_hot`"),
        (".eh_frame", "[TCG-SECTION-RESERVED]"),
        (".rela.text", "[TCG-SECTION-RESERVED]"),
        // The one undotted name a default link maps: GNU ld 2.42 and LLD
        // 22.1.6 fold the common-symbol pseudo-section `COMMON` into `.bss`
        // (the probe's function there ran from an RWX `.bss` segment).
        (
            "COMMON",
            "[TCG-SECTION-DATA] function `tcg_hot` requests ELF section `COMMON`",
        ),
        (
            "__TEXT,__text",
            "[TCG-SECTION-NAME] function `tcg_hot` requests ELF section",
        ),
        (
            "",
            "[TCG-SECTION-NAME] function `tcg_hot` requests malformed explicit section",
        ),
        (
            "bad\u{1}name",
            "[TCG-SECTION-NAME] function `tcg_hot` requests malformed",
        ),
        (
            "tab\tname",
            "[TCG-SECTION-NAME] function `tcg_hot` requests malformed",
        ),
    ] {
        let module = with_section(section);
        let error = compile_with(&module, LINUX, OptLevel::O0, false).expect_err(section);
        // A section trust-ir itself refuses (a blank or NUL-bearing name,
        // `InvalidFunctionSection`) is refused by that finding at ingestion
        // since WS7.3; the others by the backend's named rule. trust-ir judges
        // the module as `compile_with` compiles it: pinned, under `Permit`.
        match admission_expect::names_first_finding(
            &pinned_target::pinned(&module, LINUX),
            &error,
            &permit_unlicensed(),
        ) {
            Some(named) => assert!(named, "{section:?}: {error}"),
            None => assert!(error.contains(needle), "{section:?}: {error}"),
        }
    }

    let mut shared_with_data = with_section("tcg_registry");
    let mut registry = global(
        "tcg_registry_table",
        Ty::U64,
        u64_value(1),
        Linkage::External,
    );
    registry.section = Some("tcg_registry".into());
    shared_with_data.globals.push(registry);
    let error = compile_with(&shared_with_data, LINUX, OptLevel::O0, false).expect_err("shared");
    assert!(
        error.contains("[TCG-SECTION-FLAGS] function `tcg_hot`")
            && error.contains("tcg_registry_table"),
        "{error}"
    );

    let mut comdat_text = with_section(".text");
    comdat_text.functions[1].linkage = Linkage::LinkOnceOdr;
    let error = compile_with(&comdat_text, LINUX, OptLevel::O0, false).expect_err("comdat");
    assert!(
        error.contains("[TCG-SECTION-RESERVED] function `tcg_hot`"),
        "{error}"
    );

    for triple in [
        DARWIN,
        "x86_64-unknown-linux-gnu",
        "riscv64-unknown-linux-gnu",
    ] {
        let target_spec = TargetSpec::parse(triple).expect("triple");
        let error = Compiler::new_for_target_spec(
            CompilerConfig {
                target: target_spec.architecture,
                opt_level: OptLevel::O0,
                parallel: false,
                ..CompilerConfig::default()
            },
            target_spec,
        )
        .with_codegen_license(permit_unlicensed())
        .compile(&with_section(".text.hot"))
        .map(|_| ())
        .expect_err(triple)
        .to_string();
        assert!(
            error.contains("function `tcg_hot` states trust-ir v45 `section` = \".text.hot\""),
            "{triple}: {error}"
        );
    }

    let error = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            parallel: false,
            emit_debug: true,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(LINUX).expect("triple"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&with_section(".text.hot"))
    .map(|_| ())
    .expect_err("-g with an explicit function section")
    .to_string();
    assert!(
        error.contains("DWARF debug sections (-g)") && error.contains("explicit function sections"),
        "{error}"
    );
}

/// The JIT installs no object sections: an explicit function section is
/// refused by its v45 facet, and the unsectioned control JIT-compiles.
#[cfg(target_arch = "aarch64")]
#[test]
fn jit_refuses_explicit_function_sections_by_name() {
    let mut module = Module::new("tcg_jit_function_section");
    define(
        &mut module,
        "tcg_jit_hot",
        vec![Ty::U64],
        Linkage::External,
        vec![const_u64(7, 0), ret(&[0])],
    );
    module.functions[0].section = Some(".text.hot".into());
    let compiler =
        Compiler::new(CompilerConfig::default()).with_codegen_license(permit_unlicensed());
    let externs = std::collections::HashMap::new();
    let error = match compiler.compile_module_to_jit(&module, &externs) {
        Ok(_) => panic!("a sectioned JIT function must be refused"),
        Err(error) => error.to_string(),
    };
    assert!(
        error.contains("function `tcg_jit_hot` states trust-ir v45 `section`"),
        "{error}"
    );
    module.functions[0].section = None;
    compiler
        .compile_module_to_jit(&module, &externs)
        .unwrap_or_else(|error| panic!("the unsectioned control must JIT-compile: {error}"));
}

// =============================================================================
// Native execution (shared glue; the Linux and Darwin tests below drive it)
// =============================================================================

/// Link `objects` with a C `driver` using the host C compiler.
#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_os = "macos", target_arch = "aarch64")
    )),
    allow(dead_code)
)]
fn link(
    dir: &Path,
    objects: &[(&str, Vec<u8>)],
    driver: &str,
    extra: &[&str],
) -> Result<PathBuf, String> {
    let driver_path = dir.join("driver.c");
    std::fs::write(&driver_path, driver).unwrap();
    let mut command = Command::new("cc");
    command.arg("-O0").arg(&driver_path);
    for (name, bytes) in objects {
        let path = dir.join(name);
        std::fs::write(&path, bytes).unwrap();
        command.arg(path);
    }
    let exe = dir.join("program");
    let output = command
        .args(extra)
        .arg("-o")
        .arg(&exe)
        .output()
        .expect("run cc");
    if output.status.success() {
        Ok(exe)
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_os = "macos", target_arch = "aarch64")
    )),
    allow(dead_code)
)]
fn run(exe: &Path) -> (i32, String) {
    let output = Command::new(exe).output().expect("run program");
    (
        output.status.code().expect("program exited normally"),
        String::from_utf8_lossy(&output.stdout).into_owned(),
    )
}

/// The C side of the constructor control: `tcg_state` must already be 142
/// at `main` (the prioritized constructor ran first, then the plain one),
/// and `tcg_note_fini` must run after `main` returns.
#[cfg_attr(
    not(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu")),
    allow(dead_code)
)]
const CONSTRUCTOR_DRIVER: &str = r#"
#include <stdint.h>
#include <string.h>
#include <unistd.h>
extern volatile uint64_t tcg_state;
static int main_done = 0;
void tcg_note_fini(void) {
    const char *msg = main_done ? "fini-after-main\n" : "fini-before-main\n";
    write(1, msg, strlen(msg));
}
int main(void) {
    if (tcg_state != 142) return 3;
    main_done = 1;
    write(1, "main-done\n", 10);
    return 0;
}
"#;

/// The Mach-O twin of the constructor module: `__mod_init_func` entries
/// (dyld runs them in order) and no destructor table (refused on Mach-O).
fn macho_constructor_module() -> Module {
    let mut module = constructor_module();
    module.globals.truncate(3);
    module.globals[1].section = Some("__DATA,__mod_init_func,mod_init_funcs".into());
    module.globals[2].section = Some("__DATA,__mod_init_func".into());
    // The early constructor must come first: swap the table order.
    module.globals.swap(1, 2);
    module
}

#[cfg_attr(
    not(all(target_os = "macos", target_arch = "aarch64")),
    allow(dead_code)
)]
const MACHO_CONSTRUCTOR_DRIVER: &str = r#"
#include <stdint.h>
extern volatile uint64_t tcg_state;
void tcg_note_fini(void) {}
int main(void) { return tcg_state == 142 ? 0 : 3; }
"#;

/// Mach-O constructor tables: `S_MOD_INIT_FUNC_POINTERS` sections whose slots
/// are `ARM64_RELOC_UNSIGNED` against the constructors; `__mod_term_func` is
/// refused by name.
#[test]
fn macho_mod_init_func_is_a_constructor_pointer_table() {
    let obj = compile(&macho_constructor_module(), DARWIN, false);
    // Mach-O 64 header, LC_SEGMENT_64 sections.
    assert_eq!(rd_u32(&obj, 0), 0xfeed_facf);
    let ncmds = rd_u32(&obj, 16);
    let mut off = 32;
    let mut init_sections = Vec::new();
    for _ in 0..ncmds {
        let (cmd, size) = (rd_u32(&obj, off), rd_u32(&obj, off + 4) as usize);
        if cmd == 0x19 {
            let nsects = rd_u32(&obj, off + 64);
            for s in 0..nsects as usize {
                let h = off + 72 + s * 80;
                let raw = &obj[h..h + 16];
                let sectname = String::from_utf8_lossy(raw)
                    .trim_end_matches('\0')
                    .to_string();
                if sectname == "__mod_init_func" {
                    init_sections.push((
                        rd_u64(&obj, h + 40),
                        rd_u32(&obj, h + 56),
                        rd_u32(&obj, h + 60),
                        rd_u32(&obj, h + 64),
                    ));
                }
            }
        }
        off += size;
    }
    assert_eq!(init_sections.len(), 1, "both entries share one table");
    let (size, reloff, nreloc, flags) = init_sections[0];
    assert_eq!(size, 16);
    assert_eq!(flags, 0x9, "S_MOD_INIT_FUNC_POINTERS");
    assert_eq!(nreloc, 2);
    for r in 0..nreloc as usize {
        let info = rd_u32(&obj, reloff as usize + r * 8 + 4);
        assert_eq!(info >> 28, 0, "ARM64_RELOC_UNSIGNED");
        assert_eq!((info >> 25) & 3, 3, "8-byte pointer");
    }

    let mut module = macho_constructor_module();
    module.globals[1].section = Some("__DATA,__mod_term_func".into());
    let error = compile_with(&module, DARWIN, OptLevel::O0, false).expect_err("term funcs");
    assert!(error.contains("TCG-SECTION-RESERVED"), "{error}");
}

/// Darwin native control: dyld runs the `__mod_init_func` constructors, in
/// table order, before `main`. Compiled (type-checked) on every host; a test
/// only where the Darwin linker exists.
#[cfg_attr(all(target_os = "macos", target_arch = "aarch64"), test)]
#[cfg_attr(
    not(all(target_os = "macos", target_arch = "aarch64")),
    allow(dead_code)
)]
fn macho_constructors_run_before_main_natively() {
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_with(&macho_constructor_module(), DARWIN, opt_level, false).unwrap();
        let dir = scratch_dir("macho-ctor");
        let exe = link(&dir, &[("ctor.o", obj)], MACHO_CONSTRUCTOR_DRIVER, &[])
            .unwrap_or_else(|error| panic!("link: {error}"));
        assert_eq!(
            run(&exe).0,
            0,
            "{opt_level:?}: constructors ran before main"
        );
        let _ = std::fs::remove_dir_all(dir);
    }
}

#[cfg_attr(
    not(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu")),
    allow(dead_code)
)]
const GC_DRIVER: &str = r#"
#include <stdint.h>
extern uint64_t tcg_caller(void);
int main(void) { return tcg_caller() == 8 ? 0 : 3; }
"#;

#[cfg_attr(
    not(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu")),
    allow(dead_code)
)]
const COMDAT_DRIVER: &str = r#"
#include <stdint.h>
extern uint64_t tcg_from_a(void), tcg_from_b(void), tcg_shared(void);
extern const uint64_t tcg_shared_table;
int main(void) {
    if (tcg_from_a() != 8 || tcg_from_b() != 9 || tcg_shared() != 7) return 3;
    return tcg_shared_table == 0x5eed5eed ? 0 : 4;
}
"#;

/// Defined symbols of `exe` named `name` (via `nm`).
#[cfg_attr(
    not(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu")),
    allow(dead_code)
)]
fn defined_symbols(exe: &Path, name: &str) -> usize {
    let output = Command::new("nm").arg(exe).output().expect("run nm");
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter(|line| line.split_whitespace().last() == Some(name) && !line.contains(" U "))
        .count()
}

/// Linux GNU native controls. Compiled (type-checked) on every host; tests
/// only where the Linux AArch64 GNU toolchain exists.
#[cfg_attr(
    not(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu")),
    allow(dead_code)
)]
mod linux_native {
    use super::*;

    /// The prioritized constructor, then the plain one, run before `main`;
    /// the destructor runs after `main` returns.
    #[cfg_attr(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        test
    )]
    fn init_array_constructors_run_before_main_and_fini_after() {
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            let obj = compile_with(&constructor_module(), LINUX, opt_level, false).unwrap();
            let dir = scratch_dir("linux-ctor");
            let exe = link(&dir, &[("ctor.o", obj)], CONSTRUCTOR_DRIVER, &[])
                .unwrap_or_else(|error| panic!("link: {error}"));
            let (status, stdout) = run(&exe);
            assert_eq!(
                status, 0,
                "{opt_level:?}: constructors ran in priority order before main"
            );
            assert_eq!(stdout, "main-done\nfini-after-main\n", "{opt_level:?}");
            let _ = std::fs::remove_dir_all(dir);
        }
    }

    /// `--gc-sections` drops the unreferenced function only when it has its
    /// own section; the kept program still runs.
    #[cfg_attr(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        test
    )]
    fn gc_sections_drops_an_unused_function_only_with_function_sections() {
        for function_sections in [true, false] {
            // O0 keeps `tcg_caller`'s call to `tcg_leaf` (no inlining), so the
            // leaf is reachable and must survive.
            let obj = compile_with(
                &three_function_module(),
                LINUX,
                OptLevel::O0,
                function_sections,
            )
            .unwrap();
            let dir = scratch_dir("linux-gc");
            let exe = link(&dir, &[("fns.o", obj)], GC_DRIVER, &["-Wl,--gc-sections"])
                .unwrap_or_else(|error| panic!("link: {error}"));
            assert_eq!(run(&exe).0, 0);
            assert_eq!(defined_symbols(&exe, "tcg_caller"), 1);
            assert_eq!(defined_symbols(&exe, "tcg_leaf"), 1);
            assert_eq!(
                defined_symbols(&exe, "tcg_unused"),
                usize::from(!function_sections),
                "function_sections={function_sections}"
            );
            let _ = std::fs::remove_dir_all(dir);
        }
    }

    /// Two objects defining the same link-once-ODR function and table link
    /// ONCE: the second copy's groups are discarded, one definition of each
    /// survives, and every caller reaches it. The strong-linkage control is
    /// a multiple-definition link error.
    #[cfg_attr(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        test
    )]
    fn comdat_function_and_table_link_once_across_objects() {
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            let a = compile_with(
                &comdat_unit("a", 1, Linkage::LinkOnceOdr),
                LINUX,
                opt_level,
                false,
            )
            .unwrap();
            let b = compile_with(
                &comdat_unit("b", 2, Linkage::WeakOdr),
                LINUX,
                opt_level,
                false,
            )
            .unwrap();
            let dir = scratch_dir("linux-comdat");
            let map = dir.join("link.map");
            let map_flag = format!("-Wl,-Map,{}", map.display());
            let exe = link(&dir, &[("a.o", a), ("b.o", b)], COMDAT_DRIVER, &[&map_flag])
                .unwrap_or_else(|error| panic!("link: {error}"));
            assert_eq!(run(&exe).0, 0, "{opt_level:?}");
            assert_eq!(defined_symbols(&exe, "tcg_shared"), 1);
            assert_eq!(defined_symbols(&exe, "tcg_shared_table"), 1);
            let map_text = std::fs::read_to_string(&map).unwrap();
            let discarded = map_text
                .split("Discarded input sections")
                .nth(1)
                .and_then(|rest| rest.split("Memory Configuration").next())
                .expect("GNU ld map lists discarded input sections");
            for section in [".text.tcg_shared", ".rodata.tcg_shared_table"] {
                assert!(
                    discarded.contains(section),
                    "{opt_level:?}: the duplicate {section} group is discarded:\n{discarded}"
                );
            }
            let _ = std::fs::remove_dir_all(dir);

            let a = compile_with(
                &comdat_unit("a", 1, Linkage::External),
                LINUX,
                opt_level,
                false,
            )
            .unwrap();
            let b = compile_with(
                &comdat_unit("b", 2, Linkage::External),
                LINUX,
                opt_level,
                false,
            )
            .unwrap();
            let dir = scratch_dir("linux-strong");
            let error = link(&dir, &[("a.o", a), ("b.o", b)], COMDAT_DRIVER, &[])
                .expect_err("two strong definitions must not link");
            assert!(error.contains("multiple definition"), "{error}");
            let _ = std::fs::remove_dir_all(dir);
        }
    }

    /// The C side of the explicit zero-fill control: every placed global
    /// starts zero, the C and CG views agree on each address and alignment,
    /// writes persist, and the `.tbss.tcg` template is a separate zero block
    /// in each of three live threads.
    const EXPLICIT_ZERO_FILL_DRIVER: &str = r#"
#define _GNU_SOURCE
#include <pthread.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#define ZF_BIG ((size_t)2 << 20)
extern uint8_t tcg_zf_big[];
extern uint64_t tcg_zf_a, tcg_zf_comdat, tcg_zf_lbss[64];
extern const uint64_t tcg_zf_b[2];
extern uint32_t tcg_zf_sbss;
extern __thread uint64_t tcg_zf_tls[4];
extern uint8_t *tcg_zf_big_addr(void);
extern uint64_t *tcg_zf_a_addr(void), *tcg_zf_b_addr(void), *tcg_zf_lbss_addr(void);
extern uint64_t *tcg_zf_tls_addr(void), *tcg_zf_comdat_addr(void), *tcg_zf_local_addr(void);
extern uint32_t *tcg_zf_sbss_addr(void);
extern uint64_t tcg_zf_a_bump(void), tcg_zf_tls_bump(void), tcg_zf_comdat_bump(void);
extern uint64_t tcg_zf_local_bump(void);
static pthread_barrier_t barrier;
static uintptr_t tls_addresses[3];

static int check_thread(int id) {
    uint64_t *t = tcg_zf_tls_addr();
    if (t != tcg_zf_tls || (uintptr_t)t % 64) return 30;
    for (int j = 0; j < 4; ++j) if (t[j]) return 31;
    tls_addresses[id] = (uintptr_t)t;
    for (uint64_t k = 1; k <= 20 + (uint64_t)id; ++k)
        if (tcg_zf_tls_bump() != 3 * k || tcg_zf_tls[0] != 3 * k) return 32;
    return 0;
}

static void *worker(void *arg) {
    int failed = check_thread((int)(intptr_t)arg);
    pthread_barrier_wait(&barrier);
    return (void *)(intptr_t)failed;
}

int main(void) {
    uint8_t *big = tcg_zf_big_addr();
    if (big != tcg_zf_big || (uintptr_t)big % 256) return 1;
    for (size_t k = 0; k < ZF_BIG; ++k) if (big[k]) return 2;
    big[ZF_BIG - 1] = 0x5a;
    if (tcg_zf_big[ZF_BIG - 1] != 0x5a) return 3;
    if (tcg_zf_a_addr() != &tcg_zf_a || tcg_zf_a) return 4;
    if (tcg_zf_a_bump() != 3 || tcg_zf_a_bump() != 6 || tcg_zf_a != 6) return 5;
    if (tcg_zf_b_addr() != tcg_zf_b || (uintptr_t)tcg_zf_b % 16 || tcg_zf_b[0] || tcg_zf_b[1]) return 6;
    uint64_t *local = tcg_zf_local_addr();
    if (*local || (uintptr_t)local % 8 || tcg_zf_local_bump() != 3 || *local != 3) return 7;
    if (local == &tcg_zf_a || tcg_zf_a != 6) return 8;
    if (tcg_zf_sbss_addr() != &tcg_zf_sbss || tcg_zf_sbss) return 9;
    tcg_zf_sbss = 77;
    if (*tcg_zf_sbss_addr() != 77) return 10;
    if (tcg_zf_lbss_addr() != tcg_zf_lbss || (uintptr_t)tcg_zf_lbss % 64) return 11;
    for (int j = 0; j < 64; ++j) if (tcg_zf_lbss[j]) return 12;
    if (tcg_zf_comdat_addr() != &tcg_zf_comdat || tcg_zf_comdat) return 13;
    if (tcg_zf_comdat_bump() != 3 || tcg_zf_comdat != 3) return 14;
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
    if (tcg_zf_tls[0] != 60) return 23;
    for (int a = 0; a < 3; ++a)
        for (int b = a + 1; b < 3; ++b)
            if (tls_addresses[a] == tls_addresses[b]) return 24;
    puts("explicit zero-fill sections matched in three threads");
    return 0;
}
"#;

    /// Explicit zero-fill sections link with `cc` and run at O0-O3: every
    /// placed global starts zero and keeps its writes, the thread-local is
    /// a separate zero block per thread, the 2 MiB zero global leaves the
    /// executable under 1 MiB, and in the linked image every placed symbol
    /// (read with the independent reader) sits in an `SHT_NOBITS` output
    /// section, the template in an `SHF_TLS` one. The constructor module
    /// with its all-zero state in `.bss.tcg` still runs its constructors
    /// before `main` and the destructor after it.
    #[cfg_attr(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        test
    )]
    fn explicit_zero_fill_sections_link_run_and_take_no_file_bytes() {
        // `TCG_RETAIN_TEST_EVIDENCE` keeps each level's objects, readelf
        // listings and run output for an evidence archive.
        let finish = |dir: crate::fresh_dir::ScratchDir| {
            if std::env::var_os("TCG_RETAIN_TEST_EVIDENCE").is_some() {
                println!("evidence retained in {}", dir.keep().display());
            }
        };
        let listing = |path: &Path, flags: &[&str]| {
            let output = Command::new("readelf")
                .env("LC_ALL", "C")
                .args(flags)
                .arg("-W")
                .arg(path)
                .output()
                .expect("run readelf");
            String::from_utf8_lossy(&output.stdout).into_owned()
        };
        for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let obj = compile_with(&explicit_zero_fill_module(), LINUX, opt_level, false).unwrap();
            let dir = scratch_dir("linux-explicit-nobits");
            let exe = link(
                &dir,
                &[("zero_fill.o", obj)],
                EXPLICIT_ZERO_FILL_DRIVER,
                &["-pthread"],
            )
            .unwrap_or_else(|error| panic!("{opt_level:?} link: {error}"));
            std::fs::write(
                dir.join("readelf.txt"),
                format!(
                    "{}\n{}",
                    listing(&dir.join("zero_fill.o"), &["-S", "-g", "-s"]),
                    listing(&exe, &["-S", "-l"])
                ),
            )
            .unwrap();
            let size = std::fs::metadata(&exe).unwrap().len();
            assert!(
                size < (1 << 20),
                "{opt_level:?}: {ZF_BIG} zero bytes inflated the executable to {size} bytes"
            );
            let image = Elf::parse(&std::fs::read(&exe).unwrap());
            for (symbol, ..) in EXPLICIT_ZERO_FILL {
                let section = image.section_of(symbol);
                assert_eq!(
                    section.sh_type, SHT_NOBITS,
                    "{opt_level:?}: {symbol} in {}",
                    section.name
                );
                assert_eq!(
                    section.flags & SHF_TLS != 0,
                    symbol == "tcg_zf_tls",
                    "{opt_level:?}: {symbol} in {}",
                    section.name
                );
            }
            let (status, stdout) = run(&exe);
            std::fs::write(
                dir.join("run.txt"),
                format!("status {status}\nsize {size}\n{stdout}"),
            )
            .unwrap();
            assert_eq!(status, 0, "{opt_level:?}: {stdout}");
            assert_eq!(
                stdout, "explicit zero-fill sections matched in three threads\n",
                "{opt_level:?}"
            );
            finish(dir);

            let mut constructors = constructor_module();
            constructors.globals[0].section = Some(".bss.tcg".into());
            let obj = compile_with(&constructors, LINUX, opt_level, false).unwrap();
            let dir = scratch_dir("linux-ctor-nobits");
            let exe = link(&dir, &[("ctor.o", obj)], CONSTRUCTOR_DRIVER, &[])
                .unwrap_or_else(|error| panic!("{opt_level:?} link: {error}"));
            let image = Elf::parse(&std::fs::read(&exe).unwrap());
            assert_eq!(image.section_of("tcg_state").sh_type, SHT_NOBITS);
            let (status, stdout) = run(&exe);
            std::fs::write(
                dir.join("readelf.txt"),
                listing(&dir.join("ctor.o"), &["-S", "-s"]),
            )
            .unwrap();
            std::fs::write(dir.join("run.txt"), format!("status {status}\n{stdout}")).unwrap();
            assert_eq!(status, 0, "{opt_level:?}: constructors wrote .bss.tcg");
            assert_eq!(stdout, "main-done\nfini-after-main\n", "{opt_level:?}");
            finish(dir);
        }
    }

    // =========================================================================
    // Default-link placement controls (GNU ld 2.42 and LLD 22.1.6)
    // =========================================================================

    /// The directory holding `ld.lld` for `cc -fuse-ld=lld -B<dir>`:
    /// `TCG_LLD_DIR`, else `~/.local/bin`, else the first `PATH` entry with
    /// one. `TCG_REQUIRE_LLD` turns a missing LLD into a failure.
    fn lld_dir() -> Option<PathBuf> {
        let found = std::env::var_os("TCG_LLD_DIR")
            .map(PathBuf::from)
            .or_else(|| std::env::var_os("HOME").map(|home| Path::new(&home).join(".local/bin")))
            .filter(|dir| dir.join("ld.lld").is_file())
            .or_else(|| {
                std::env::var_os("PATH").and_then(|paths| {
                    std::env::split_paths(&paths).find(|dir| dir.join("ld.lld").is_file())
                })
            });
        if found.is_none() {
            assert!(
                std::env::var_os("TCG_REQUIRE_LLD").is_none(),
                "TCG_REQUIRE_LLD is set but no ld.lld was found"
            );
            eprintln!(
                "SKIP: no ld.lld (TCG_LLD_DIR, ~/.local/bin, PATH); the LLD legs did not run"
            );
        }
        found
    }

    /// The linkers of a placement control: GNU ld through the host `cc`,
    /// and LLD through `cc -fuse-ld=lld -B<dir>` when one is installed.
    fn linkers() -> Vec<(&'static str, Vec<String>)> {
        let mut linkers = vec![("gnu", Vec::new())];
        if let Some(dir) = lld_dir() {
            let version = Command::new(dir.join("ld.lld"))
                .arg("--version")
                .output()
                .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_string())
                .unwrap_or_default();
            eprintln!("LLD leg: {} ({version})", dir.display());
            linkers.push((
                "lld",
                vec!["-fuse-ld=lld".to_string(), format!("-B{}", dir.display())],
            ));
        }
        linkers
    }

    /// `TCG_RETAIN_TEST_EVIDENCE` keeps a control's directory for an
    /// evidence archive.
    fn finish(dir: crate::fresh_dir::ScratchDir) {
        if std::env::var_os("TCG_RETAIN_TEST_EVIDENCE").is_some() {
            println!("evidence retained in {}", dir.keep().display());
        }
    }

    /// What a control program did: its exit code, or the signal that
    /// killed it, and its stdout.
    fn run_status(exe: &Path) -> (Option<i32>, Option<i32>, String) {
        use std::os::unix::process::ExitStatusExt;
        let output = Command::new(exe).output().expect("run program");
        (
            output.status.code(),
            output.status.signal(),
            String::from_utf8_lossy(&output.stdout).into_owned(),
        )
    }

    /// `(type, flags)` of every program header covering `addr` in `image`,
    /// from `readelf -lW` (`LOAD` with `R E`/`RW `/`RWE`, `GNU_RELRO`, ...).
    fn segments_covering(image: &Path, addr: u64) -> Vec<(String, String)> {
        let output = Command::new("readelf")
            .env("LC_ALL", "C")
            .args(["-lW"])
            .arg(image)
            .output()
            .expect("run readelf");
        String::from_utf8_lossy(&output.stdout)
            .lines()
            .filter_map(|line| {
                let fields: Vec<&str> = line.split_whitespace().collect();
                if fields.len() < 8 || !fields[1].starts_with("0x") {
                    return None;
                }
                let vaddr = u64::from_str_radix(fields[2].trim_start_matches("0x"), 16).ok()?;
                let memsz = u64::from_str_radix(fields[5].trim_start_matches("0x"), 16).ok()?;
                (vaddr <= addr && addr < vaddr + memsz.max(1))
                    .then(|| (fields[0].to_string(), fields[6..fields.len() - 1].join("")))
            })
            .collect()
    }

    /// The victim of the placement controls: a hidden `tcg_victim` in
    /// `section` (a u64, or a constructor-table slot holding `&tcg_noop`),
    /// `tcg_victim_addr`, and for a u64 `tcg_victim_bump` (`+= 3` through
    /// trust-cg's own load and store).
    fn victim_module(section: &str, table: bool, value: u64, mutable: bool) -> Module {
        let mut module = Module::new("tcg_section_victim");
        let mut victim = if table {
            let mut entry = pointer_entry("tcg_victim", "tcg_noop", section);
            entry.linkage = Linkage::External;
            entry
        } else {
            global("tcg_victim", Ty::U64, u64_value(value), Linkage::External)
        };
        victim.mutable = mutable;
        victim.visibility = Visibility::Hidden;
        victim.align = Some(8);
        victim.section = Some(section.to_string());
        module.globals.push(victim);
        victim_accessors(&mut module, table);
        module
    }

    /// A mutable link-once-ODR u64 named `symbol` without an explicit
    /// section: its implicit COMDAT section is `.data.<symbol>`, or
    /// `.bss.<symbol>` when `value` is zero.
    fn comdat_victim_module(symbol: &str, value: u64) -> Module {
        let mut module = Module::new("tcg_comdat_victim");
        let mut victim = global(symbol, Ty::U64, u64_value(value), Linkage::LinkOnceOdr);
        victim.mutable = true;
        victim.visibility = Visibility::Hidden;
        victim.align = Some(8);
        module.globals.push(victim);
        victim_accessors(&mut module, false);
        module
    }

    /// `tcg_noop`, `tcg_victim_addr` and, for a u64, `tcg_victim_bump`
    /// (`+= 3` through trust-cg's own load and store) over global 0.
    fn victim_accessors(module: &mut Module, table: bool) {
        define(
            module,
            "tcg_noop",
            vec![],
            Linkage::External,
            vec![ret(&[])],
        );
        define(
            module,
            "tcg_victim_addr",
            vec![Ty::Ptr],
            Linkage::External,
            vec![
                node(
                    Inst::GlobalAddr {
                        global: GlobalId::new(0),
                    },
                    0,
                ),
                ret(&[0]),
            ],
        );
        if !table {
            define(
                module,
                "tcg_victim_bump",
                vec![Ty::U64],
                Linkage::External,
                add_three(0),
            );
        }
    }

    /// The C side of a scalar control: trust-cg's `tcg_victim_bump` loads
    /// and stores the global, and the driver checks the store landed.
    const VICTIM_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
extern uint64_t *tcg_victim_addr(void);
extern uint64_t tcg_victim_bump(void);
int main(void) {
    uint64_t *victim = tcg_victim_addr();
    uint64_t before = *victim;
    if (tcg_victim_bump() != before + 3 || *victim != before + 3) return 3;
    puts("victim store survived");
    return 0;
}
"#;

    /// The C side of a table control: rewrite the slot with its own value.
    const TABLE_DRIVER: &str = r#"
#include <stdio.h>
extern void *volatile *tcg_victim_addr(void);
int main(void) {
    void *volatile *slot = tcg_victim_addr();
    void *entry = *slot;
    *slot = entry;
    puts("victim store survived");
    return 0;
}
"#;

    /// Link `object` (as `victim.o`) with `driver` in `dir` under a linker
    /// (`flags`), as a PIE (gcc's default `-pie -z now -z relro`) or as a
    /// `-shared` library the driver links against. Returns the image that
    /// holds `tcg_victim` and the executable, or the linker's diagnostics.
    fn link_victim(
        dir: &Path,
        tag: &str,
        object: &[u8],
        driver: &str,
        flags: &[String],
        shared: bool,
    ) -> Result<(PathBuf, PathBuf), String> {
        let object_path = dir.join(format!("{tag}.o"));
        std::fs::write(&object_path, object).unwrap();
        let driver_path = dir.join("driver.c");
        std::fs::write(&driver_path, driver).unwrap();
        let exe = dir.join(format!("{tag}.exe"));
        let cc = |args: Vec<std::ffi::OsString>| {
            let output = Command::new("cc")
                .args(flags)
                .args(args)
                .output()
                .expect("run cc");
            let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
            std::fs::write(dir.join(format!("{tag}.link.txt")), &stderr).unwrap();
            if output.status.success() {
                Ok(())
            } else {
                Err(stderr)
            }
        };
        if shared {
            let library = dir.join(format!("lib{tag}.so"));
            cc(vec![
                "-shared".into(),
                "-o".into(),
                library.clone().into(),
                object_path.into(),
            ])?;
            cc(vec![
                "-O0".into(),
                driver_path.into(),
                library.clone().into(),
                format!("-Wl,-rpath,{}", dir.display()).into(),
                "-o".into(),
                exe.clone().into(),
            ])?;
            Ok((library, exe))
        } else {
            cc(vec![
                "-O0".into(),
                driver_path.into(),
                object_path.into(),
                "-o".into(),
                exe.clone().into(),
            ])?;
            Ok((exe.clone(), exe))
        }
    }

    /// What one linker does with a section name, as the placement controls
    /// assert it.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Hazard {
        /// The store through the global dies with SIGSEGV.
        StoreFaults,
        /// The link fails, with this text in the diagnostics.
        LinkFails(&'static str),
        /// The global lands in this output section.
        LandsIn(&'static str),
        /// The PT_LOAD holding the global is writable and executable.
        WritableExecutable,
        /// The global sits between crtbegin's `__TMC_LIST__` and crtend's
        /// `__TMC_END__`, the table `register_tm_clones` hands to libitm.
        InTmCloneList,
        /// Nothing: the program links, the store lands, it exits 0.
        Runs,
    }

    /// Observe `hazards` for one linked victim; `Err` describes the first
    /// that does not hold.
    fn observe(
        linked: &Result<(PathBuf, PathBuf), String>,
        symbol: &str,
        hazards: &[Hazard],
        dir: &Path,
        tag: &str,
    ) -> Result<String, String> {
        let mut seen = Vec::new();
        let (image, exe) = match (linked, hazards) {
            (Err(stderr), [Hazard::LinkFails(text)]) if stderr.contains(text) => {
                return Ok(format!(
                    "link failed: {}",
                    stderr.lines().next().unwrap_or("")
                ));
            }
            (Err(stderr), _) => return Err(format!("link failed: {stderr}")),
            (Ok(_), [Hazard::LinkFails(text)]) => {
                return Err(format!("linked, but `{text}` was expected"));
            }
            (Ok(paths), _) => paths,
        };
        let elf = Elf::parse(&std::fs::read(image).unwrap());
        let symbol = elf.symbol(symbol).clone();
        let output = elf.sections[symbol.shndx as usize].name.clone();
        let segments = segments_covering(image, symbol.value);
        let (code, signal, stdout) = run_status(exe);
        std::fs::write(
            dir.join(format!("{tag}.run.txt")),
            format!(
                "output {output}\nsegments {segments:?}\nexit {code:?} signal {signal:?}\n{stdout}"
            ),
        )
        .unwrap();
        seen.push(format!(
            "in `{output}` {segments:?}, exit {code:?} signal {signal:?}"
        ));
        for hazard in hazards {
            let holds = match hazard {
                Hazard::StoreFaults => signal == Some(11),
                Hazard::LinkFails(_) => false,
                Hazard::LandsIn(want) => output == *want,
                Hazard::WritableExecutable => segments
                    .iter()
                    .any(|(kind, flags)| kind == "LOAD" && flags == "RWE"),
                Hazard::InTmCloneList => {
                    let start = elf.symbol("__TMC_LIST__").value;
                    let end = elf.symbol("__TMC_END__").value;
                    start <= symbol.value && symbol.value < end
                }
                Hazard::Runs => code == Some(0) && stdout.contains("victim store survived"),
            };
            if !holds {
                return Err(format!("expected {hazard:?}; saw {}", seen.join("; ")));
            }
        }
        Ok(seen.join("; "))
    }

    /// Rename section `from` to `to` (same length) in an ELF object's
    /// section-name table, in place: every other byte stays as trust-cg
    /// wrote it.
    fn rename_section(object: &[u8], from: &str, to: &str) -> Vec<u8> {
        assert_eq!(from.len(), to.len());
        let mut bytes = object.to_vec();
        let shoff = rd_u64(&bytes, 0x28) as usize;
        let shstrndx = rd_u16(&bytes, 0x3e) as usize;
        let header = shoff + shstrndx * 64;
        let offset = rd_u64(&bytes, header + 0x18) as usize;
        let size = rd_u64(&bytes, header + 0x20) as usize;
        let table = &mut bytes[offset..offset + size];
        let mut renamed = 0;
        let mut at = 0;
        while let Some(found) = table[at..]
            .windows(from.len())
            .position(|window| window == from.as_bytes())
        {
            table[at + found..at + found + from.len()].copy_from_slice(to.as_bytes());
            at += found + from.len();
            renamed += 1;
        }
        assert!(renamed >= 1, "`{from}` is not a section name of the object");
        bytes
    }

    /// One refused name, the victim shape its control uses, and what each
    /// linker does with trust-cg's bytes under it.
    struct RefusedCase {
        /// The section name: explicit, or a COMDAT symbol's implicit one.
        name: &'static str,
        code: &'static str,
        /// A mutable link-once-ODR global with this symbol and no explicit
        /// section, whose implicit `<base>.<symbol>` is `name`.
        comdat_symbol: Option<&'static str>,
        /// A constructor-table slot rather than a u64.
        table: bool,
        /// Link a `-shared` library rather than a PIE.
        shared: bool,
        gnu: &'static [Hazard],
        lld: &'static [Hazard],
    }

    const fn case(
        name: &'static str,
        code: &'static str,
        gnu: &'static [Hazard],
        lld: &'static [Hazard],
    ) -> RefusedCase {
        RefusedCase {
            name,
            code,
            comdat_symbol: None,
            table: false,
            shared: false,
            gnu,
            lld,
        }
    }

    /// Every refusal-by-default name of the verifier's list and a sample of
    /// each derived class (object_sections::ELF_NAME_RULES), with the
    /// hazard the default link of each linker produces (the retained
    /// probe's matrix, re-established here with trust-cg's own bytes).
    const REFUSED_CASES: &[RefusedCase] = {
        use Hazard::*;
        const RESERVED: &str = "TCG-SECTION-RESERVED";
        const READONLY: &str = "TCG-SECTION-READONLY";
        &[
            case(
                ".tcommon",
                "TCG-SECTION-TLS",
                &[LandsIn(".tbss"), StoreFaults],
                &[Runs],
            ),
            case(
                ".gnu_extab",
                RESERVED,
                &[LandsIn(".gnu_extab"), StoreFaults],
                &[Runs],
            ),
            case(
                ".gcc_except_table.x",
                RESERVED,
                &[LandsIn(".gcc_except_table"), StoreFaults],
                &[Runs],
            ),
            case(".exception_ranges", RESERVED, &[StoreFaults], &[Runs]),
            case(".sframe", RESERVED, &[StoreFaults], &[Runs]),
            case(
                ".eh_frame.x",
                RESERVED,
                &[LandsIn(".eh_frame"), StoreFaults],
                &[Runs],
            ),
            case(".jcr", RESERVED, &[StoreFaults], &[StoreFaults]),
            case(
                ".sframe.x",
                RESERVED,
                &[LandsIn(".sframe"), StoreFaults],
                &[Runs],
            ),
            case(".exception_ranges.x", RESERVED, &[StoreFaults], &[Runs]),
            case(
                ".eh_frame_entry",
                RESERVED,
                &[LinkFails("compact frame descriptions")],
                &[Runs],
            ),
            // BFD's by-name prefix (no `.` boundary): the verifier's sweep.
            case(
                ".eh_frame_entryx",
                RESERVED,
                &[LinkFails("compact frame descriptions")],
                &[Runs],
            ),
            case(
                ".stub",
                "TCG-SECTION-EXEC",
                &[LandsIn(".text"), StoreFaults],
                &[Runs],
            ),
            case(
                ".iplt",
                "TCG-SECTION-EXEC",
                &[LandsIn(".plt"), WritableExecutable],
                &[WritableExecutable],
            ),
            case(".rodata1", READONLY, &[WritableExecutable], &[Runs]),
            case(".igot", RESERVED, &[LandsIn(".got"), StoreFaults], &[Runs]),
            case(".toc", READONLY, &[Runs], &[StoreFaults]),
            case(
                ".relro_padding",
                RESERVED,
                &[Runs],
                &[LinkFails("overlaps")],
            ),
            case("COMMON", RESERVED, &[LandsIn(".bss")], &[LandsIn(".bss")]),
            case(
                ".tm_clone_table",
                RESERVED,
                &[InTmCloneList],
                &[InTmCloneList],
            ),
            case(
                ".stab",
                RESERVED,
                &[LinkFails("PHDR segment not covered")],
                &[Runs],
            ),
            case(
                ".line",
                RESERVED,
                &[LinkFails("PHDR segment not covered")],
                &[Runs],
            ),
            case(
                ".gnu_debuglink",
                RESERVED,
                &[LinkFails("discarded section")],
                &[Runs],
            ),
            RefusedCase {
                shared: true,
                ..case(".relative", RESERVED, &[StoreFaults], &[Runs])
            },
            RefusedCase {
                shared: true,
                ..case(
                    ".relr.dyn",
                    RESERVED,
                    &[LinkFails("file format not recognized")],
                    &[Runs],
                )
            },
            RefusedCase {
                table: true,
                ..case(".init_array", READONLY, &[StoreFaults], &[StoreFaults])
            },
            RefusedCase {
                table: true,
                ..case(".fini_array", READONLY, &[StoreFaults], &[StoreFaults])
            },
            // Implicit COMDAT names: a mutable link-once global whose symbol
            // is literally `rel.ro` gets `.data.rel.ro` (nonzero) or
            // `.bss.rel.ro` (all zero).
            RefusedCase {
                comdat_symbol: Some("rel.ro"),
                ..case(".data.rel.ro", READONLY, &[StoreFaults], &[StoreFaults])
            },
            RefusedCase {
                comdat_symbol: Some("rel.ro"),
                ..case(
                    ".bss.rel.ro",
                    READONLY,
                    &[LandsIn(".bss"), Runs],
                    &[StoreFaults],
                )
            },
            // Regression rows for the earlier RELRO refusals.
            case(
                ".bss.rel.ro",
                READONLY,
                &[LandsIn(".bss"), Runs],
                &[StoreFaults],
            ),
            case(".data.rel.ro", READONLY, &[StoreFaults], &[StoreFaults]),
        ]
    };

    /// A same-length name trust-cg honours with the flags the pre-repair
    /// catch-all (or zero-fill arm) gave `name`: an undotted orphan, or a
    /// `.bss.` name for a zero-fill family.
    fn placeholder(name: &str) -> String {
        match name.strip_prefix(".bss.") {
            Some(rest) => format!(".bss.{}", "Q".repeat(rest.len())),
            None => "Q".repeat(name.len()),
        }
    }

    /// Every refusal-by-default name is refused by name at O2 (the
    /// verifier's level) with its exact code, and trust-cg's OWN bytes under
    /// that name show why: the control compiles the same mutable all-zero
    /// `tcg_victim` under a same-length placeholder trust-cg honours (the
    /// flags the pre-repair catch-all gave the name; an immutable table for
    /// the constructor tables, whose object is byte-identical to the mutable
    /// one's), renames that section in `.shstrtab`, and links it with the
    /// host `cc` (GNU ld 2.42) and, when installed, `cc -fuse-ld=lld` (LLD
    /// 22.1.6). Each linker's hazard is asserted: the store faults, the link
    /// fails, the global lands in a TLS, unwind, text or GOT output, its
    /// segment turns writable and executable, or it joins crtstuff's
    /// transactional-memory clone table. If the compiler lets a name
    /// through (a mutation removing the refusal), the escaped object itself
    /// is linked and run the same way, recorded, and the test fails.
    #[cfg_attr(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        test
    )]
    fn refused_sections_fault_or_misplace_trust_cg_bytes_under_the_named_linker() {
        let linkers = linkers();
        let mut escaped = Vec::new();
        for (index, case) in REFUSED_CASES.iter().enumerate() {
            let dir = scratch_dir(&format!("linux-refused-{index}"));
            let driver = if case.table {
                TABLE_DRIVER
            } else {
                VICTIM_DRIVER
            };
            let mut record = format!(
                "name {}\ncode {}\ncomdat symbol {:?}\n",
                case.name, case.code, case.comdat_symbol
            );
            let compile = |module: &Module, what: &str| {
                compile_with(module, LINUX, OptLevel::O2, false)
                    .unwrap_or_else(|error| panic!("{}: {what}: {error}", case.name))
            };
            // Control: trust-cg's bytes under the refused name.
            let (control_symbol, object) = if case.table {
                let object = compile(
                    &victim_module(case.name, true, 0, false),
                    "immutable table control",
                );
                ("tcg_victim".to_string(), object)
            } else if let Some(symbol) = case.comdat_symbol {
                // A same-length stand-in symbol keeps the group's implicit
                // `<base>.<symbol>` layout; only the section name is renamed.
                let stand_in = "Q".repeat(symbol.len());
                let value = if case.name.starts_with(".bss") { 0 } else { 7 };
                let object = compile(&comdat_victim_module(&stand_in, value), "COMDAT control");
                let base = case
                    .name
                    .strip_suffix(symbol)
                    .expect("implicit `<base>.<symbol>`");
                let object = rename_section(&object, &format!("{base}{stand_in}"), case.name);
                (stand_in, object)
            } else {
                let stand_in = placeholder(case.name);
                let object = compile(
                    &victim_module(&stand_in, false, 0, true),
                    "placeholder control",
                );
                (
                    "tcg_victim".to_string(),
                    rename_section(&object, &stand_in, case.name),
                )
            };
            assert_eq!(
                Elf::parse(&object).section_of(&control_symbol).name,
                case.name,
                "the control object places {control_symbol} in the refused name"
            );
            for (linker, flags) in &linkers {
                let hazards = if *linker == "gnu" { case.gnu } else { case.lld };
                let tag = format!("control-{linker}");
                let linked = link_victim(&dir, &tag, &object, driver, flags, case.shared);
                match observe(&linked, &control_symbol, hazards, &dir, &tag) {
                    Ok(seen) => record.push_str(&format!("{tag}: {hazards:?} held: {seen}\n")),
                    Err(problem) => panic!("{} under {linker}: {problem}", case.name),
                }
            }
            // The compiler refuses the mutable victim by name.
            let (victim, victim_symbol) = match case.comdat_symbol {
                Some(symbol) => (
                    comdat_victim_module(symbol, if case.name.starts_with(".bss") { 0 } else { 7 }),
                    symbol,
                ),
                None => (victim_module(case.name, case.table, 0, true), "tcg_victim"),
            };
            match compile_with(&victim, LINUX, OptLevel::O2, false) {
                Err(error) if error.contains(&format!("[{}]", case.code)) => {
                    record.push_str(&format!("refused: {error}\n"));
                }
                Err(error) => {
                    // Refused, but not by the rule that names the hazard.
                    let outcome = format!(
                        "`{}` was refused with the wrong code (expected [{}]): {error}",
                        case.name, case.code
                    );
                    record.push_str(&format!("{outcome}\n"));
                    escaped.push(outcome);
                }
                Ok(bytes) => {
                    let mut outcome = format!(
                        "`{}` was NOT refused (expected [{}]); the escaped object is {} the control",
                        case.name,
                        case.code,
                        if bytes == object {
                            "byte-identical to"
                        } else {
                            "different from"
                        }
                    );
                    for (linker, flags) in &linkers {
                        let hazards = if *linker == "gnu" { case.gnu } else { case.lld };
                        let tag = format!("escaped-{linker}");
                        let linked = link_victim(&dir, &tag, &bytes, driver, flags, case.shared);
                        let seen = observe(&linked, victim_symbol, hazards, &dir, &tag);
                        outcome.push_str(&format!("; {linker}: {seen:?}"));
                    }
                    record.push_str(&format!("{outcome}\n"));
                    escaped.push(outcome);
                }
            }
            std::fs::write(dir.join("record.txt"), &record).unwrap();
            eprint!("{record}");
            finish(dir);
        }
        assert!(
            escaped.is_empty(),
            "names escaped their refusal or its code:\n{}",
            escaped.join("\n")
        );
    }

    /// A C control for BFD's by-name `.eh_frame_entry` prefix, independent
    /// of trust-cg's bytes: gcc 13.3 places a mutable C global with
    /// `__attribute__((section(NAME)))` for each spelling the verifier's
    /// sweep found admitted, GNU ld 2.42 fails every link with "compact
    /// frame descriptions incompatible with DWARF2 .eh_frame" (it parses the
    /// section as compact unwind entries by name, although no script
    /// statement names it), LLD 22.1.6 links and runs it, and trust-cg
    /// refuses the same name for a mutable global as
    /// `[TCG-SECTION-RESERVED]`. The one-short `.eh_frame_entq` links and
    /// runs under both, and trust-cg honours it.
    #[cfg_attr(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        test
    )]
    fn c_globals_under_the_eh_frame_entry_prefix_fail_the_gnu_link() {
        let linkers = linkers();
        let dir = scratch_dir("linux-eh-frame-entry-c");
        let mut record = String::new();
        for (index, (name, gnu_fails)) in [
            (".eh_frame_entryx", true),
            (".eh_frame_entry1", true),
            (".eh_frame_entry_x", true),
            (".eh_frame_entry-x", true),
            (".eh_frame_entry$x", true),
            (".eh_frame_entq", false),
        ]
        .into_iter()
        .enumerate()
        {
            let source = dir.join(format!("c{index}.c"));
            std::fs::write(
                &source,
                format!(
                    "#include <stdio.h>\n__attribute__((section(\"{name}\"))) long v = 7;\nint main(void) {{ v += 3; printf(\"%ld\\n\", v); return v != 10; }}\n"
                ),
            )
            .unwrap();
            for (linker, flags) in &linkers {
                let exe = dir.join(format!("c{index}-{linker}.exe"));
                let output = Command::new("cc")
                    .args(flags)
                    .arg("-O0")
                    .arg(&source)
                    .arg("-o")
                    .arg(&exe)
                    .output()
                    .expect("run cc");
                let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
                let outcome = if output.status.success() {
                    let (code, signal, stdout) = run_status(&exe);
                    assert!(
                        !(*linker == "gnu" && gnu_fails),
                        "{name}: GNU ld linked it: exit {code:?} signal {signal:?}"
                    );
                    assert_eq!(
                        (code, stdout.as_str()),
                        (Some(0), "10\n"),
                        "{name} under {linker}: signal {signal:?}"
                    );
                    "linked, ran, exit 0".to_string()
                } else {
                    assert!(
                        *linker == "gnu" && gnu_fails,
                        "{name} under {linker}: {stderr}"
                    );
                    assert!(
                        stderr.contains(
                            "compact frame descriptions incompatible with DWARF2 .eh_frame"
                        ),
                        "{name}: {stderr}"
                    );
                    format!("link failed: {}", stderr.lines().next().unwrap_or(""))
                };
                record.push_str(&format!("{name} {linker}: {outcome}\n"));
            }
            let module = victim_module(name, false, 7, true);
            let compiled = compile_with(&module, LINUX, OptLevel::O2, false);
            if gnu_fails {
                let error = compiled.expect_err(name);
                assert!(error.contains("[TCG-SECTION-RESERVED]"), "{name}: {error}");
                record.push_str(&format!("{name} trust-cg: {error}\n"));
            } else {
                compiled.unwrap_or_else(|error| panic!("{name}: {error}"));
                record.push_str(&format!("{name} trust-cg: honoured\n"));
            }
        }
        std::fs::write(dir.join("record.txt"), &record).unwrap();
        eprint!("{record}");
        finish(dir);
    }

    /// The honoured writable names still link and survive a store under
    /// BOTH linkers: mutable globals in named writable outputs (`.data.tcg`,
    /// `.data1`, NOBITS `.bss.tcg`/`.sbss.tcg`/`.lbss.tcg`) and in names one
    /// character past a special family (`.bss.rel.rox`, `.data.rel.rox`,
    /// `.tcommon.x`, `.jcrx`, `.eh_framex`, `.rodata1.x`, `.stabx`,
    /// `.relro`, `tcg_custom_rw`) keep their initial values and every store,
    /// and immutable globals in the immutable-only families (`.rodata1`,
    /// `.toc`, `.data.rel.ro.tcg`) read back, at O0 and O2, as PIEs and as a
    /// `-shared` library.
    #[cfg_attr(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        test
    )]
    fn honoured_writable_sections_survive_a_store_under_gnu_ld_and_lld() {
        const WRITABLE: [(&str, u64); 14] = [
            (".data.tcg", 11),
            (".data1", 12),
            (".bss.tcg", 0),
            (".sbss.tcg", 0),
            (".lbss.tcg", 0),
            (".bss.rel.rox", 0),
            (".data.rel.rox", 13),
            (".tcommon.x", 14),
            (".jcrx", 15),
            (".eh_framex", 16),
            (".rodata1.x", 17),
            (".stabx", 18),
            (".relro", 19),
            ("tcg_custom_rw", 20),
        ];
        const IMMUTABLE: [(&str, u64); 3] =
            [(".rodata1", 101), (".toc", 102), (".data.rel.ro.tcg", 103)];
        let mut module = Module::new("tcg_honoured_sections");
        for (index, (name, value)) in WRITABLE.iter().enumerate() {
            let mut g = global(
                &format!("tcg_rw_{index}"),
                Ty::U64,
                u64_value(*value),
                Linkage::External,
            );
            g.mutable = true;
            g.visibility = Visibility::Hidden;
            g.section = Some(name.to_string());
            module.globals.push(g);
        }
        for (index, (name, value)) in IMMUTABLE.iter().enumerate() {
            let mut g = global(
                &format!("tcg_ro_{index}"),
                Ty::U64,
                u64_value(*value),
                Linkage::External,
            );
            g.visibility = Visibility::Hidden;
            g.section = Some(name.to_string());
            module.globals.push(g);
        }
        for index in 0..WRITABLE.len() {
            define(
                &mut module,
                &format!("tcg_rw_{index}_bump"),
                vec![Ty::U64],
                Linkage::External,
                add_three(index as u32),
            );
        }
        for index in 0..IMMUTABLE.len() {
            define(
                &mut module,
                &format!("tcg_ro_{index}_load"),
                vec![Ty::U64],
                Linkage::External,
                vec![
                    node(
                        Inst::GlobalAddr {
                            global: GlobalId::new((WRITABLE.len() + index) as u32),
                        },
                        0,
                    ),
                    node(
                        Inst::Load {
                            ty: Ty::U64,
                            ptr: ValueId::new(0),
                            volatile: true,
                            align: Some(8),
                        },
                        1,
                    ),
                    ret(&[1]),
                ],
            );
        }
        let mut driver = String::from("#include <stdint.h>\n#include <stdio.h>\n");
        for index in 0..WRITABLE.len() {
            driver.push_str(&format!("extern uint64_t tcg_rw_{index}_bump(void);\n"));
        }
        for index in 0..IMMUTABLE.len() {
            driver.push_str(&format!("extern uint64_t tcg_ro_{index}_load(void);\n"));
        }
        driver.push_str("int main(void) {\n");
        for (index, (_, value)) in WRITABLE.iter().enumerate() {
            driver.push_str(&format!(
                "    if (tcg_rw_{index}_bump() != {value}u + 3 || tcg_rw_{index}_bump() != {value}u + 6) return {};\n",
                index + 1
            ));
        }
        for (index, (_, value)) in IMMUTABLE.iter().enumerate() {
            driver.push_str(&format!(
                "    if (tcg_ro_{index}_load() != {value}u) return {};\n",
                50 + index
            ));
        }
        driver
            .push_str("    puts(\"honoured sections survived every store\");\n    return 0;\n}\n");
        let linkers = linkers();
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            let object = compile_with(&module, LINUX, opt_level, false)
                .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
            let dir = scratch_dir(&format!("linux-honoured-{opt_level:?}"));
            std::fs::write(dir.join("honoured.o"), &object).unwrap();
            std::fs::write(dir.join("driver.c"), &driver).unwrap();
            let mut record = String::new();
            for (linker, flags) in &linkers {
                for shared in [false, true] {
                    let tag = format!("{linker}-{}", if shared { "shared" } else { "pie" });
                    let (image, exe) = link_victim(&dir, &tag, &object, &driver, flags, shared)
                        .unwrap_or_else(|error| panic!("{opt_level:?} {tag}: link: {error}"));
                    let (code, signal, stdout) = run_status(&exe);
                    let elf = Elf::parse(&std::fs::read(&image).unwrap());
                    let mut placed = Vec::new();
                    for (index, (name, _)) in WRITABLE.iter().enumerate() {
                        let symbol = elf.symbol(&format!("tcg_rw_{index}")).clone();
                        let output = &elf.sections[symbol.shndx as usize];
                        let segments = segments_covering(&image, symbol.value);
                        assert!(
                            output.flags & SHF_WRITE != 0
                                && !segments.iter().any(|(kind, _)| kind == "GNU_RELRO")
                                && segments
                                    .iter()
                                    .any(|(kind, flags)| kind == "LOAD" && flags == "RW"),
                            "{opt_level:?} {tag}: {name} landed in {} {segments:?}",
                            output.name
                        );
                        placed.push(format!("{name}->{}", output.name));
                    }
                    record.push_str(&format!(
                        "{tag}: exit {code:?} signal {signal:?}; {}\n{stdout}",
                        placed.join(" ")
                    ));
                    assert_eq!(
                        (code, stdout.as_str()),
                        (Some(0), "honoured sections survived every store\n"),
                        "{opt_level:?} {tag}: signal {signal:?}"
                    );
                }
            }
            std::fs::write(dir.join("record.txt"), &record).unwrap();
            eprint!("{opt_level:?}\n{record}");
            finish(dir);
        }
    }

    /// `tcg_keep_me` (`.text.keep_me`, 7) and `tcg_drop_me` (`.text.drop_me`,
    /// 9) each own a named section; `tcg_shared_used` (11) and
    /// `tcg_shared_unused` (13) share `.text.shared`. Only `tcg_keep_me` and
    /// `tcg_shared_used` are referenced, by the C driver.
    fn gc_named_section_module() -> Module {
        let mut module = Module::new("tcg_gc_named_sections");
        for (name, section, value) in [
            ("tcg_keep_me", ".text.keep_me", 7),
            ("tcg_drop_me", ".text.drop_me", 9),
            ("tcg_shared_used", ".text.shared", 11),
            ("tcg_shared_unused", ".text.shared", 13),
        ] {
            let id = define(
                &mut module,
                name,
                vec![Ty::U64],
                Linkage::External,
                vec![const_u64(value, 0), ret(&[0])],
            );
            module.functions[id.index() as usize].section = Some(section.to_string());
        }
        module
    }

    const GC_NAMED_DRIVER: &str = r#"
#include <stdint.h>
extern uint64_t tcg_keep_me(void), tcg_shared_used(void);
int main(void) { return tcg_keep_me() == 7 && tcg_shared_used() == 11 ? 0 : 3; }
"#;

    /// trust-ir v45 named function sections under `ld --gc-sections`
    /// (O0-O3): the linker keeps `.text.keep_me` and the shared
    /// `.text.shared` (so the unreferenced `tcg_shared_unused` survives with
    /// its section-mate) and drops only `.text.drop_me`, which
    /// `--print-gc-sections` names; the program runs. Without
    /// `--gc-sections` nothing is dropped, so the drop is the linker's
    /// section-granular decision, not the compiler's. Execution evidence of
    /// GNU ld on this host.
    #[cfg_attr(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        test
    )]
    fn gc_sections_keeps_or_drops_named_function_sections_by_reference() {
        for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let dir = scratch_dir("linux-named-gc");
            let object = dir.join("named.o");
            std::fs::write(
                &object,
                compile_with(&gc_named_section_module(), LINUX, opt_level, false).unwrap(),
            )
            .unwrap();
            let sections = Command::new("readelf")
                .env("LC_ALL", "C")
                .args(["-S", "-W"])
                .arg(&object)
                .output()
                .expect("run readelf");
            let sections = String::from_utf8_lossy(&sections.stdout).into_owned();
            std::fs::write(dir.join("sections.txt"), &sections).unwrap();
            for name in [".text.keep_me", ".text.drop_me", ".text.shared"] {
                assert!(
                    sections
                        .lines()
                        .any(|line| line.contains(&format!(" {name} "))
                            && line.contains("PROGBITS")
                            && line.contains(" AX ")),
                    "{opt_level:?}: readelf -S {name} AX\n{sections}"
                );
            }
            let driver = dir.join("driver.c");
            std::fs::write(&driver, GC_NAMED_DRIVER).unwrap();
            for gc in [true, false] {
                let exe = dir.join(if gc { "gc" } else { "nogc" });
                let mut command = Command::new("cc");
                command.arg("-O0").arg(&driver).arg(&object);
                if gc {
                    command.args(["-Wl,--gc-sections", "-Wl,--print-gc-sections"]);
                }
                let output = command.arg("-o").arg(&exe).output().expect("run cc");
                let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
                assert!(output.status.success(), "{opt_level:?} gc={gc}: {stderr}");
                std::fs::write(dir.join(format!("link-gc-{gc}.txt")), &stderr).unwrap();
                let removed: BTreeSet<String> = stderr
                    .lines()
                    .filter(|line| {
                        line.contains("removing unused section") && line.contains("named.o")
                    })
                    .filter_map(|line| line.split('\'').nth(1).map(str::to_string))
                    .collect();
                let (status, _) = run(&exe);
                assert_eq!(status, 0, "{opt_level:?} gc={gc}");
                assert_eq!(
                    defined_symbols(&exe, "tcg_keep_me"),
                    1,
                    "{opt_level:?} gc={gc}"
                );
                assert_eq!(
                    defined_symbols(&exe, "tcg_shared_used"),
                    1,
                    "{opt_level:?} gc={gc}"
                );
                assert_eq!(
                    defined_symbols(&exe, "tcg_shared_unused"),
                    1,
                    "{opt_level:?} gc={gc}: kept with its section-mate"
                );
                if gc {
                    assert_eq!(
                        removed,
                        BTreeSet::from([".text.drop_me".to_string()]),
                        "{opt_level:?}: {stderr}"
                    );
                    assert_eq!(defined_symbols(&exe, "tcg_drop_me"), 0, "{opt_level:?}");
                } else {
                    assert!(removed.is_empty(), "{opt_level:?}: {stderr}");
                    assert_eq!(defined_symbols(&exe, "tcg_drop_me"), 1, "{opt_level:?}");
                }
            }
            eprintln!("named function sections under --gc-sections passed: {opt_level:?} {dir:?}");
        }
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
