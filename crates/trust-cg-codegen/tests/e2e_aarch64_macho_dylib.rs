// trust-cg-codegen/tests/e2e_aarch64_macho_dylib.rs - CG-built Mach-O dylibs:
// visibility, weak coalescing, namespaces, interposition and __DATA_CONST.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Trust-cg AArch64 Mach-O objects linked into `MH_DYLIB` images, by ld64
//! (`clang -dynamiclib`) and by the in-repo standalone linker (`link_dylib`).
//!
//! The dylib body comes from two CG objects. A trust-ir module compiled by
//! `Compiler` (the production AArch64 Mach-O AOT path) defines exported,
//! hidden and weak data, an exported and a weak function, a relocated
//! immutable vtable and a relocated constant slot pointing at the weak data,
//! and calls an import (`cg_provider_fn`) served by a second dylib. A
//! Pipeline object carries the one construct trust-ir functions cannot spell,
//! a hidden (`N_PEXT`) function, plus its exported caller.
//!
//! Object level (every host): the nlist bindings (`N_EXT`, `N_PEXT`,
//! `N_WEAK_DEF`), GOT-indirect access to the dyld-coalescable weak data
//! (never a direct page reference), the vtable's `__DATA,__const` placement,
//! and the standalone dylib's exports, weak-lookup binds and read-only
//! `__DATA_CONST,__const` section, read back by this file's own parsers.
//!
//! Native (macOS AArch64 only): a C program `dlopen`s each dylib and checks
//! `dlsym` visibility of exported versus hidden symbols; dyld weak coalescing
//! with the executable's own weak definitions (and the dylib's fallback when
//! the executable defines none) under the two-level namespace and, for ld64,
//! `-flat_namespace` (which also rebinds the dylib's import to the
//! executable's definition); interposition through `DYLD_INSERT_LIBRARIES`
//! and `__DATA,__interpose`, which reaches the executable's and the dylib's
//! imports but not the dylib's direct internal call; and a store into the
//! relocated vtable, which faults once dyld has applied its fixups, beside a
//! mutable-vtable control whose store succeeds. ld64 `-dead_strip` keeps a
//! retained (`N_NO_DEAD_STRIP`) CG definition and drops an unreferenced plain
//! one. A direct page reference to a weak definition is a mutation control:
//! this host's ld64 accepts it without a diagnostic and dyld cannot coalesce
//! it, which the harness detects, and the standalone linker refuses it by
//! name.
//!
//! This is execution evidence for these programs on this host, not a linker
//! or loader proof.

#[path = "common/pinned_target.rs"]
mod pinned_target;

use std::collections::{BTreeMap, BTreeSet};

use trust_cg_codegen::macho::linker::{DylibConfig, LinkerError, MachOParser, link_dylib};
use trust_cg_codegen::pipeline::{
    FunctionSymbolBinding, ObjectGlobal, OptLevel, Pipeline, PipelineConfig,
};
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_cg_lower::function::{BasicBlock, Function as LirFunction, Signature};
use trust_cg_lower::instructions::{Block as LirBlock, Instruction, Opcode, Value};
use trust_cg_lower::types::Type as LirType;
use trust_ir::value::GlobalId;
use trust_ir::{
    Block, BlockId, CastOp, Constant, FuncId, FuncTy, Function, Global, Inst, InstrNode, Linkage,
    Module, Ty, ValueId, Visibility,
};

const DARWIN: &str = "aarch64-apple-darwin";
const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const PROVIDER_INSTALL_NAME: &str = "@loader_path/libprov.dylib";

// =============================================================================
// CG objects
// =============================================================================

fn value_function(module: &mut Module, name: &str, linkage: Linkage, value: i128) -> FuncId {
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, sig, BlockId::new(0));
    function.linkage = linkage;
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(value),
        })
        .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    function.blocks.push(block);
    module.functions.push(function);
    id
}

fn body_function(module: &mut Module, name: &str, returns: Ty, body: Vec<InstrNode>) {
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![returns],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, sig, BlockId::new(0));
    function.linkage = Linkage::External;
    let mut block = Block::new(BlockId::new(0));
    block.body = body;
    function.blocks.push(block);
    module.functions.push(function);
}

fn returning(node: InstrNode) -> Vec<InstrNode> {
    vec![
        node.with_result(ValueId::new(0)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }),
    ]
}

fn data_global(name: &str, linkage: Linkage, visibility: Visibility, value: i128) -> Global {
    Global {
        name: name.into(),
        ty: Ty::I64,
        mutable: true,
        initializer: Some(Constant::Int(value)),
        linkage,
        tls: None,
        align: Some(8),
        section: None,
        visibility,
        retained: false,
    }
}

/// The trust-ir dylib body. `mutable_vtable` is the protection control: the
/// same relocated table, but writable, so it stays in `__DATA,__data`.
fn core_module(mutable_vtable: bool) -> Module {
    let mut module = Module::new("cg_dylib_core");
    pinned_target::pin(&mut module, "aarch64-apple-darwin");
    module.globals = vec![
        data_global("cg_export_data", Linkage::External, Visibility::Default, 11),
        data_global("cg_hidden_data", Linkage::External, Visibility::Hidden, 12),
        data_global("cg_weak_data", Linkage::Weak, Visibility::Default, 13),
    ];
    let pointer = module
        .add_type(Ty::Ptr)
        .expect("Module::add_type: test fixture");
    module.globals.push(Global {
        name: "cg_vtable".into(),
        ty: Ty::Array(pointer, 2),
        mutable: mutable_vtable,
        initializer: Some(Constant::Aggregate(vec![
            Constant::SymbolAddr {
                symbol: "cg_export_fn".into(),
                addend: 0,
            },
            Constant::SymbolAddr {
                symbol: "cg_export_data".into(),
                addend: 0,
            },
        ])),
        linkage: Linkage::External,
        tls: None,
        align: Some(8),
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });
    module.globals.push(Global {
        name: "cg_weak_slot".into(),
        ty: Ty::Ptr,
        mutable: false,
        initializer: Some(Constant::SymbolAddr {
            symbol: "cg_weak_data".into(),
            addend: 0,
        }),
        linkage: Linkage::External,
        tls: None,
        align: Some(8),
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });

    let export_fn = value_function(&mut module, "cg_export_fn", Linkage::External, 1001);
    let weak_fn = value_function(&mut module, "cg_weak_fn", Linkage::Weak, 3001);
    let provider_sig = module.functions[export_fn.index() as usize].ty;
    let provider = FuncId::new(module.functions.len() as u32);
    let mut declaration = Function::new(provider, "cg_provider_fn", provider_sig, BlockId::new(0));
    declaration.linkage = Linkage::External;
    module.functions.push(declaration);
    for (name, callee) in [
        ("cg_call_export_fn", export_fn),
        ("cg_call_weak_fn", weak_fn),
        ("cg_call_provider", provider),
    ] {
        body_function(
            &mut module,
            name,
            Ty::I64,
            returning(InstrNode::new(Inst::Call {
                callee,
                args: vec![],
            })),
        );
    }
    for (name, global) in [
        ("cg_export_data_addr", 0),
        ("cg_hidden_data_addr", 1),
        ("cg_weak_data_addr", 2),
        ("cg_vtable_addr", 3),
        ("cg_weak_slot_addr", 4),
    ] {
        body_function(
            &mut module,
            name,
            Ty::Ptr,
            returning(InstrNode::new(Inst::GlobalAddr {
                global: GlobalId::new(global),
            })),
        );
    }
    let weak_fn_ty = Ty::Func(module.functions[weak_fn.index() as usize].ty);
    body_function(
        &mut module,
        "cg_weak_fn_addr",
        Ty::Ptr,
        vec![
            InstrNode::new(Inst::Const {
                ty: weak_fn_ty.clone(),
                value: Constant::FnDef(weak_fn),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Cast {
                op: CastOp::ReifyFnPointer,
                src_ty: weak_fn_ty,
                dst_ty: Ty::Ptr,
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    );
    module
}

fn compile_core(opt_level: OptLevel, mutable_vtable: bool) -> Vec<u8> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(DARWIN).expect("Darwin triple"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&core_module(mutable_vtable))
    .unwrap_or_else(|error| panic!("{opt_level:?}: core module: {error}"))
    .object_code
}

fn lir_function(name: &str, instructions: Vec<Instruction>) -> LirFunction {
    let mut function = LirFunction::new(
        name.to_owned(),
        Signature {
            params: vec![],
            returns: vec![LirType::I64],
        },
    );
    function.entry_block = LirBlock(0);
    function.block_order = vec![LirBlock(0)];
    function.blocks.insert(
        LirBlock(0),
        BasicBlock {
            params: vec![],
            instructions,
            source_locs: vec![],
        },
    );
    function
}

fn lir_returning(name: &str, opcode: Opcode) -> LirFunction {
    lir_function(
        name,
        vec![
            Instruction {
                opcode,
                args: vec![],
                results: vec![Value(0)],
            },
            Instruction {
                opcode: Opcode::Return,
                args: vec![Value(0)],
                results: vec![],
            },
        ],
    )
}

fn darwin_pipeline(opt_level: OptLevel) -> Pipeline {
    Pipeline::new(PipelineConfig {
        target_triple: DARWIN.into(),
        opt_level,
        ..PipelineConfig::default()
    })
}

fn emit_lir(
    opt_level: OptLevel,
    functions: &[LirFunction],
    globals: &[ObjectGlobal],
    bindings: &[FunctionSymbolBinding],
) -> Vec<u8> {
    let pipeline = darwin_pipeline(opt_level);
    let (prepared, layouts): (Vec<_>, Vec<_>) = functions
        .iter()
        .map(|function| {
            let (prepared, metrics) = pipeline
                .prepare_function_with_metrics(function, None)
                .unwrap_or_else(|error| panic!("prepare {}: {error}", function.name));
            (prepared, metrics.frame_layout)
        })
        .unzip();
    pipeline
        .compile_module_emission(&prepared, globals, &layouts, bindings)
        .unwrap_or_else(|error| panic!("{opt_level:?}: Pipeline object: {error}"))
        .object
}

/// `cg_hidden_fn` (hidden, 2002) and its exported caller.
fn hidden_object(opt_level: OptLevel) -> Vec<u8> {
    emit_lir(
        opt_level,
        &[
            lir_returning(
                "cg_hidden_fn",
                Opcode::Iconst {
                    ty: LirType::I64,
                    imm: 2002,
                },
            ),
            lir_returning(
                "cg_call_hidden_fn",
                Opcode::Call {
                    name: "cg_hidden_fn".into(),
                    binding: Default::default(),
                },
            ),
        ],
        &[],
        &[FunctionSymbolBinding::HIDDEN, FunctionSymbolBinding::GLOBAL],
    )
}

/// Mutation control: weak data `cg_direct_weak` (21) addressed by a DIRECT
/// page reference, which dyld cannot rebind to another image's definition.
fn direct_weak_object(opt_level: OptLevel) -> Vec<u8> {
    let weak = ObjectGlobal {
        name: "cg_direct_weak".into(),
        data: 21i64.to_le_bytes().to_vec(),
        mutable: true,
        is_external: true,
        symbol_refs: vec![],
        is_thread_local: false,
        is_import: false,
        is_weak: true,
        align: 8,
        visibility: Visibility::Default,
        retained: false,
        section: None,
        comdat: false,
    };
    emit_lir(
        opt_level,
        &[lir_returning(
            "cg_direct_weak_addr",
            Opcode::GlobalRef {
                name: "cg_direct_weak".into(),
            },
        )],
        &[weak],
        &[],
    )
}

fn provider_config() -> DylibConfig {
    let mut config = DylibConfig::with_libsystem();
    config.add_dylib(
        PROVIDER_INSTALL_NAME,
        ["_cg_provider_fn".to_string()].into_iter().collect(),
    );
    config
}

/// Two unreferenced definitions, one `#[used]`-retained, and an entry point.
fn dead_strip_module() -> Module {
    let mut module = Module::new("cg_dead_strip");
    pinned_target::pin(&mut module, "aarch64-apple-darwin");
    let mut retained = data_global("cg_retained", Linkage::External, Visibility::Default, 1);
    retained.retained = true;
    module.globals = vec![
        retained,
        data_global("cg_unretained", Linkage::External, Visibility::Default, 2),
    ];
    value_function(&mut module, "cg_dead_strip_entry", Linkage::External, 7);
    module
}

fn compile_dead_strip(opt_level: OptLevel) -> Vec<u8> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(DARWIN).expect("Darwin triple"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&dead_strip_module())
    .unwrap_or_else(|error| panic!("{opt_level:?}: dead-strip module: {error}"))
    .object_code
}

fn standalone_dylib(objects: &[Vec<u8>], install_name: &str) -> Result<Vec<u8>, LinkerError> {
    let parsed: Vec<_> = objects
        .iter()
        .map(|bytes| MachOParser::parse(bytes).expect("CG object parses"))
        .collect();
    link_dylib(&parsed, &provider_config(), install_name)
}

// =============================================================================
// Independent Mach-O readers
// =============================================================================

const N_EXT: u8 = 0x01;
const N_PEXT: u8 = 0x10;
const N_WEAK_DEF: u16 = 0x0080;
const LC_SYMTAB: u32 = 0x2;
const LC_SEGMENT_64: u32 = 0x19;
const LC_DYLD_EXPORTS_TRIE: u32 = 0x8000_0033;
const LC_DYLD_CHAINED_FIXUPS: u32 = 0x8000_0034;
const MH_DYLIB: u32 = 0x6;
const MH_WEAK_DEFINES: u32 = 0x8000;
const MH_BINDS_TO_WEAK: u32 = 0x1_0000;
const SG_READ_ONLY: u32 = 0x10;
const ARM64_RELOC_UNSIGNED: u8 = 0;
const ARM64_RELOC_BRANCH26: u8 = 2;
const ARM64_RELOC_PAGE21: u8 = 3;
const ARM64_RELOC_PAGEOFF12: u8 = 4;
const ARM64_RELOC_GOT_LOAD_PAGE21: u8 = 5;
const ARM64_RELOC_GOT_LOAD_PAGEOFF12: u8 = 6;
const WEAK_LOOKUP_ORDINAL: u32 = 0xFD;
const EXPORT_WEAK_DEFINITION: u64 = 0x04;

fn u16_at(bytes: &[u8], at: usize) -> u16 {
    u16::from_le_bytes(bytes[at..at + 2].try_into().unwrap())
}

fn u32_at(bytes: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap())
}

fn u64_at(bytes: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap())
}

fn fixed_name(bytes: &[u8]) -> String {
    let end = bytes.iter().position(|&b| b == 0).unwrap_or(bytes.len());
    String::from_utf8_lossy(&bytes[..end]).into_owned()
}

fn cstring(bytes: &[u8], at: usize) -> String {
    let end = at + bytes[at..].iter().position(|&b| b == 0).unwrap();
    String::from_utf8_lossy(&bytes[at..end]).into_owned()
}

/// `(cmd, offset)` of every load command.
fn load_commands(bytes: &[u8]) -> Vec<(u32, usize)> {
    assert_eq!(u32_at(bytes, 0), 0xFEED_FACF, "MH_MAGIC_64");
    let mut commands = Vec::new();
    let mut at = 32;
    for _ in 0..u32_at(bytes, 16) {
        commands.push((u32_at(bytes, at), at));
        at += u32_at(bytes, at + 4) as usize;
    }
    commands
}

#[derive(Debug, Clone)]
struct Section {
    segment: String,
    name: String,
    addr: u64,
    size: u64,
    reloff: usize,
    nreloc: usize,
}

#[derive(Debug, Clone)]
struct Segment {
    name: String,
    vmaddr: u64,
    fileoff: u64,
    flags: u32,
}

fn segments_and_sections(bytes: &[u8]) -> (Vec<Segment>, Vec<Section>) {
    let mut segments = Vec::new();
    let mut sections = Vec::new();
    for (cmd, at) in load_commands(bytes) {
        if cmd != LC_SEGMENT_64 {
            continue;
        }
        segments.push(Segment {
            name: fixed_name(&bytes[at + 8..at + 24]),
            vmaddr: u64_at(bytes, at + 24),
            fileoff: u64_at(bytes, at + 40),
            flags: u32_at(bytes, at + 68),
        });
        for index in 0..u32_at(bytes, at + 64) as usize {
            let header = at + 72 + index * 80;
            sections.push(Section {
                name: fixed_name(&bytes[header..header + 16]),
                segment: fixed_name(&bytes[header + 16..header + 32]),
                addr: u64_at(bytes, header + 32),
                size: u64_at(bytes, header + 40),
                reloff: u32_at(bytes, header + 56) as usize,
                nreloc: u32_at(bytes, header + 60) as usize,
            });
        }
    }
    (segments, sections)
}

#[derive(Debug, Clone)]
struct Symbol {
    n_type: u8,
    section: u8,
    desc: u16,
    value: u64,
}

/// nlist_64 entries by name, plus the name of each index.
fn symbols(object: &[u8]) -> (BTreeMap<String, Symbol>, Vec<String>) {
    let mut by_name = BTreeMap::new();
    let mut names = Vec::new();
    for (cmd, at) in load_commands(object) {
        if cmd != LC_SYMTAB {
            continue;
        }
        let (symoff, nsyms, stroff) = (
            u32_at(object, at + 8) as usize,
            u32_at(object, at + 12) as usize,
            u32_at(object, at + 16) as usize,
        );
        for index in 0..nsyms {
            let entry = symoff + index * 16;
            let name = cstring(object, stroff + u32_at(object, entry) as usize);
            names.push(name.clone());
            by_name.insert(
                name,
                Symbol {
                    n_type: object[entry + 4],
                    section: object[entry + 5],
                    desc: u16_at(object, entry + 6),
                    value: u64_at(object, entry + 8),
                },
            );
        }
    }
    (by_name, names)
}

/// `(offset, type, symbol)` of every external relocation in `section`.
fn relocations(object: &[u8], section: &Section, names: &[String]) -> Vec<(u32, u8, String)> {
    (0..section.nreloc)
        .filter_map(|index| {
            let at = section.reloff + index * 8;
            let info = u32_at(object, at + 4);
            let external = (info >> 27) & 1 == 1;
            external.then(|| {
                (
                    u32_at(object, at),
                    (info >> 28) as u8,
                    names[(info & 0x00FF_FFFF) as usize].clone(),
                )
            })
        })
        .collect()
}

/// Every name the image's exports trie spells, with its flags and offset.
fn exports(image: &[u8]) -> BTreeMap<String, (u64, u64)> {
    fn uleb(bytes: &[u8], at: &mut usize) -> u64 {
        let (mut value, mut shift) = (0u64, 0);
        loop {
            let byte = bytes[*at];
            *at += 1;
            value |= u64::from(byte & 0x7F) << shift;
            if byte & 0x80 == 0 {
                return value;
            }
            shift += 7;
        }
    }
    let (_, at) = load_commands(image)
        .into_iter()
        .find(|(cmd, _)| *cmd == LC_DYLD_EXPORTS_TRIE)
        .expect("exports trie");
    let start = u32_at(image, at + 8) as usize;
    let trie = &image[start..start + u32_at(image, at + 12) as usize];
    let mut found = BTreeMap::new();
    let mut pending = vec![(0usize, Vec::new())];
    while let Some((node, prefix)) = pending.pop() {
        let mut at = node;
        let terminal = uleb(trie, &mut at) as usize;
        let children = at + terminal;
        if terminal != 0 {
            let flags = uleb(trie, &mut at);
            let offset = uleb(trie, &mut at);
            found.insert(String::from_utf8(prefix.clone()).unwrap(), (flags, offset));
        }
        at = children;
        let count = trie[at];
        at += 1;
        for _ in 0..count {
            let end = at + trie[at..].iter().position(|&b| b == 0).unwrap();
            let mut name = prefix.clone();
            name.extend_from_slice(&trie[at..end]);
            at = end + 1;
            let child = uleb(trie, &mut at) as usize;
            pending.push((child, name));
        }
    }
    found
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Fixup {
    Rebase(u64),
    Bind { symbol: String, ordinal: u32 },
}

/// DYLD_CHAINED_PTR_64 chains per `<mach-o/fixup-chains.h>`.
fn fixups(image: &[u8]) -> BTreeMap<u64, Fixup> {
    let (segments, _) = segments_and_sections(image);
    let (_, at) = load_commands(image)
        .into_iter()
        .find(|(cmd, _)| *cmd == LC_DYLD_CHAINED_FIXUPS)
        .expect("chained fixups");
    let start = u32_at(image, at + 8) as usize;
    let starts = start + u32_at(image, start + 4) as usize;
    let imports = start + u32_at(image, start + 8) as usize;
    let names = start + u32_at(image, start + 12) as usize;
    let mut decoded = BTreeMap::new();
    for (index, segment) in segments.iter().enumerate() {
        let info = u32_at(image, starts + 4 + index * 4) as usize;
        if info == 0 {
            continue;
        }
        let seg = starts + info;
        assert_eq!(u16_at(image, seg + 6), 2, "DYLD_CHAINED_PTR_64");
        for page in 0..u16_at(image, seg + 20) as u64 {
            let first = u16_at(image, seg + 22 + page as usize * 2);
            if first == 0xFFFF {
                continue;
            }
            let mut offset = page * 0x4000 + u64::from(first);
            loop {
                let raw = u64_at(image, (segment.fileoff + offset) as usize);
                let fixup = if raw >> 63 == 1 {
                    let entry = u32_at(image, imports + (raw & 0xFF_FFFF) as usize * 4);
                    Fixup::Bind {
                        symbol: cstring(image, names + (entry >> 9) as usize),
                        ordinal: entry & 0xFF,
                    }
                } else {
                    Fixup::Rebase(raw & ((1 << 36) - 1))
                };
                decoded.insert(segment.vmaddr + offset, fixup);
                let next = (raw >> 51) & 0xFFF;
                if next == 0 {
                    break;
                }
                offset += next * 4;
            }
        }
    }
    decoded
}

// =============================================================================
// Object-level evidence (every host)
// =============================================================================

#[test]
fn cg_objects_spell_visibility_weakness_got_access_and_relocated_constants() {
    for opt_level in OPT_LEVELS {
        let core = compile_core(opt_level, false);
        let (by_name, names) = symbols(&core);
        let symbol = |name: &str| {
            by_name
                .get(name)
                .unwrap_or_else(|| panic!("{name} missing"))
        };
        for name in ["_cg_export_fn", "_cg_export_data", "_cg_vtable"] {
            let s = symbol(name);
            assert_eq!(s.n_type & (N_EXT | N_PEXT), N_EXT, "{opt_level:?} {name}");
            assert_eq!(s.desc & N_WEAK_DEF, 0, "{opt_level:?} {name}");
        }
        for name in ["_cg_weak_fn", "_cg_weak_data"] {
            let s = symbol(name);
            assert_eq!(s.n_type & (N_EXT | N_PEXT), N_EXT, "{opt_level:?} {name}");
            assert_eq!(s.desc & N_WEAK_DEF, N_WEAK_DEF, "{opt_level:?} {name}");
        }
        let hidden = symbol("_cg_hidden_data");
        assert_eq!(hidden.n_type & (N_EXT | N_PEXT), N_EXT | N_PEXT);

        let (_, sections) = segments_and_sections(&core);
        let section_of = |s: &Symbol| sections[usize::from(s.section) - 1].clone();
        let vtable = section_of(symbol("_cg_vtable"));
        assert_eq!(
            (vtable.segment.as_str(), vtable.name.as_str()),
            ("__DATA", "__const"),
            "{opt_level:?}: a relocated immutable global is read-only after fixups"
        );
        assert_eq!(
            (section_of(symbol("_cg_weak_slot")).name.as_str()),
            "__const"
        );
        assert_eq!(section_of(symbol("_cg_export_data")).name, "__data");
        let slot_relocs = relocations(&core, &vtable, &names);
        let base = symbol("_cg_vtable").value - vtable.addr;
        for (slot, target) in [(0, "_cg_export_fn"), (8, "_cg_export_data")] {
            assert!(
                slot_relocs.contains(&((base + slot) as u32, ARM64_RELOC_UNSIGNED, target.into())),
                "{opt_level:?}: {slot_relocs:?}"
            );
        }

        // Every reference to a dyld-coalescable weak definition is
        // GOT-indirect or a branch the linker can route through a stub; no
        // direct page reference names it.
        let text = sections
            .iter()
            .find(|s| s.segment == "__TEXT" && s.name == "__text")
            .unwrap();
        let text_relocs = relocations(&core, text, &names);
        for weak in ["_cg_weak_data", "_cg_weak_fn"] {
            let kinds: BTreeSet<u8> = text_relocs
                .iter()
                .filter(|(_, _, name)| name == weak)
                .map(|(_, kind, _)| *kind)
                .collect();
            assert!(!kinds.is_empty(), "{opt_level:?}: {weak} is referenced");
            assert!(
                !kinds.contains(&ARM64_RELOC_PAGE21) && !kinds.contains(&ARM64_RELOC_PAGEOFF12),
                "{opt_level:?}: {weak} must not be addressed directly: {kinds:?}"
            );
        }
        assert!(text_relocs.iter().any(|(_, kind, name)| {
            *kind == ARM64_RELOC_GOT_LOAD_PAGE21 && name == "_cg_weak_data"
        }));
        assert!(text_relocs.iter().any(|(_, kind, name)| {
            *kind == ARM64_RELOC_GOT_LOAD_PAGEOFF12 && name == "_cg_weak_fn"
        }));
        // At every level: a non-ODR weak body is never inlined, so the call
        // keeps its symbol relocation for the linker to route through a stub.
        assert!(
            text_relocs
                .iter()
                .any(|(_, kind, name)| *kind == ARM64_RELOC_BRANCH26 && name == "_cg_weak_fn"),
            "{opt_level:?}: the weak call keeps its symbol relocation"
        );
        // Strong exported data stays a direct page reference.
        assert!(
            text_relocs.iter().any(|(_, kind, name)| {
                *kind == ARM64_RELOC_PAGE21 && name == "_cg_export_data"
            })
        );

        let hidden_object = hidden_object(opt_level);
        let (lir_symbols, _) = symbols(&hidden_object);
        assert_eq!(
            lir_symbols["_cg_hidden_fn"].n_type & (N_EXT | N_PEXT),
            N_EXT | N_PEXT
        );
        assert_eq!(
            lir_symbols["_cg_call_hidden_fn"].n_type & (N_EXT | N_PEXT),
            N_EXT
        );

        // The mutable-vtable control keeps its table writable.
        let control = compile_core(opt_level, true);
        let (control_symbols, _) = symbols(&control);
        let (_, control_sections) = segments_and_sections(&control);
        let table = &control_sections[usize::from(control_symbols["_cg_vtable"].section) - 1];
        assert_eq!(
            (table.segment.as_str(), table.name.as_str()),
            ("__DATA", "__data")
        );
    }
}

#[test]
fn standalone_cg_dylib_exports_weak_definitions_and_protects_relocated_constants() {
    for opt_level in OPT_LEVELS {
        let image = standalone_dylib(
            &[compile_core(opt_level, false), hidden_object(opt_level)],
            "@rpath/libcg.dylib",
        )
        .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
        assert_eq!(u32_at(&image, 12), MH_DYLIB);
        let flags = u32_at(&image, 24);
        assert_eq!(
            flags & (MH_WEAK_DEFINES | MH_BINDS_TO_WEAK),
            MH_WEAK_DEFINES | MH_BINDS_TO_WEAK
        );
        let exported = exports(&image);
        for name in [
            "_cg_export_fn",
            "_cg_export_data",
            "_cg_call_hidden_fn",
            "_cg_vtable",
        ] {
            let (flags, _) = exported
                .get(name)
                .unwrap_or_else(|| panic!("{opt_level:?}: {name} not exported"));
            assert_eq!(flags & EXPORT_WEAK_DEFINITION, 0, "{name}");
        }
        for name in ["_cg_weak_fn", "_cg_weak_data"] {
            assert_eq!(
                exported[name].0 & EXPORT_WEAK_DEFINITION,
                EXPORT_WEAK_DEFINITION,
                "{opt_level:?}: {name} is exported weak"
            );
        }
        for hidden in ["_cg_hidden_fn", "_cg_hidden_data"] {
            assert!(!exported.contains_key(hidden), "{opt_level:?}: {hidden}");
        }

        let (segments, sections) = segments_and_sections(&image);
        let data_const = segments.iter().find(|s| s.name == "__DATA_CONST").unwrap();
        assert_eq!(data_const.flags & SG_READ_ONLY, SG_READ_ONLY);
        let constant = sections
            .iter()
            .find(|s| s.segment == "__DATA_CONST" && s.name == "__const")
            .expect("__DATA_CONST,__const");
        let vtable = exported["_cg_vtable"].1;
        let slot = exported["_cg_weak_slot"].1;
        for address in [vtable, vtable + 8, slot] {
            assert!(
                (constant.addr..constant.addr + constant.size).contains(&address),
                "{opt_level:?}: {address:#x} outside __DATA_CONST,__const"
            );
        }
        let fixups = fixups(&image);
        assert_eq!(
            fixups[&vtable],
            Fixup::Rebase(exported["_cg_export_fn"].1),
            "{opt_level:?}"
        );
        assert_eq!(
            fixups[&(vtable + 8)],
            Fixup::Rebase(exported["_cg_export_data"].1)
        );
        assert_eq!(
            fixups[&slot],
            Fixup::Bind {
                symbol: "_cg_weak_data".into(),
                ordinal: WEAK_LOOKUP_ORDINAL
            },
            "{opt_level:?}: the relocated slot binds through dyld's weak lookup"
        );
        let binds: BTreeSet<(String, u32)> = fixups
            .values()
            .filter_map(|fixup| match fixup {
                Fixup::Bind { symbol, ordinal } => Some((symbol.clone(), *ordinal)),
                Fixup::Rebase(_) => None,
            })
            .collect();
        for weak in ["_cg_weak_fn", "_cg_weak_data"] {
            assert!(
                binds.contains(&(weak.into(), WEAK_LOOKUP_ORDINAL)),
                "{binds:?}"
            );
        }
        assert!(binds.iter().any(|(symbol, ordinal)| {
            symbol == "_cg_provider_fn" && *ordinal != WEAK_LOOKUP_ORDINAL
        }));
        assert!(
            !binds
                .iter()
                .any(|(symbol, _)| symbol.starts_with("_cg_hidden")
                    || symbol == "_cg_export_fn"
                    || symbol == "_cg_export_data"),
            "{opt_level:?}: strong and hidden definitions bind directly: {binds:?}"
        );

        // Mutation control: a direct page reference to a weak definition is
        // refused by name rather than silently kept on this image's copy.
        let error =
            standalone_dylib(&[direct_weak_object(opt_level)], "@rpath/libd.dylib").unwrap_err();
        assert!(
            matches!(
                error,
                LinkerError::DirectWeakDefinitionReference { ref symbol, .. }
                    if symbol == "_cg_direct_weak"
            ),
            "{opt_level:?}: {error:?}"
        );
    }
}

#[test]
fn retained_definitions_carry_n_no_dead_strip() {
    const N_NO_DEAD_STRIP: u16 = 0x0020;
    for opt_level in OPT_LEVELS {
        let (symbols, _) = symbols(&compile_dead_strip(opt_level));
        assert_eq!(
            symbols["_cg_retained"].desc & N_NO_DEAD_STRIP,
            N_NO_DEAD_STRIP,
            "{opt_level:?}"
        );
        assert_eq!(
            symbols["_cg_unretained"].desc & N_NO_DEAD_STRIP,
            0,
            "{opt_level:?}"
        );
    }
}

#[test]
fn a_mutable_global_in_data_const_is_refused_by_name() {
    let mut module = core_module(false);
    module.globals[0].section = Some("__DATA,__const".into());
    let error = Compiler::new_for_target_spec(
        CompilerConfig::default(),
        TargetSpec::parse(DARWIN).unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&module)
    .unwrap_err()
    .to_string();
    assert!(
        error.contains("TCG-SECTION") && error.contains("__DATA_CONST"),
        "{error}"
    );
    // An immutable relocated global may name the implicit section.
    let mut module = core_module(false);
    module.globals[3].section = Some("__DATA,__const".into());
    let object = Compiler::new_for_target_spec(
        CompilerConfig::default(),
        TargetSpec::parse(DARWIN).unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&module)
    .expect("explicit __DATA,__const for an immutable table")
    .object_code;
    let (_, sections) = segments_and_sections(&object);
    assert_eq!(
        sections
            .iter()
            .filter(|s| s.segment == "__DATA" && s.name == "__const")
            .count(),
        1,
        "the explicit request joins the implicit section"
    );
}

// =============================================================================
// Native execution (macOS AArch64)
// =============================================================================

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[path = "common/rosetta.rs"]
mod rosetta;

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
mod native {
    use super::rosetta::command_output_with_timeout;
    use super::*;
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::time::Duration;

    const PROVIDER_SOURCE: &str = "long cg_provider_fn(void) { return 5; }\n";

    const DLOPEN_DRIVER: &str = r#"
#include <dlfcn.h>
#include <signal.h>
#include <stdio.h>
#include <sys/wait.h>
#include <unistd.h>

#if EXE_WEAK
__attribute__((weak)) long cg_weak_data = 900;
__attribute__((weak)) long cg_weak_fn(void) { return 9001; }
#endif
/* Under -flat_namespace the dylib's import binds to the first definition in
   load order, which is this one; under the two-level namespace it binds to
   libprov's. */
long cg_provider_fn(void) { return 6; }

typedef long (*value_fn)(void);

static void *need(void *handle, const char *name) {
    void *symbol = dlsym(handle, name);
    if (!symbol) { printf("missing %s\n", name); fflush(stdout); _exit(90); }
    return symbol;
}

/* 1: a store into *slot faults (SIGBUS/SIGSEGV); 0: it succeeds. */
static int store_faults(void **slot) {
    fflush(stdout);
    pid_t child = fork();
    if (child == 0) { *(void *volatile *)slot = (void *)0x1; _exit(0); }
    int status = 0;
    if (waitpid(child, &status, 0) != child) return 9;
    if (WIFSIGNALED(status))
        return WTERMSIG(status) == SIGBUS || WTERMSIG(status) == SIGSEGV ? 1 : 8;
    return WIFEXITED(status) && WEXITSTATUS(status) == 0 ? 0 : 7;
}

int main(int argc, char **argv) {
    void *h = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
    if (!h) { printf("dlopen: %s\n", dlerror()); return 91; }
    printf("dlsym export_fn=%d export_data=%d weak_fn=%d weak_data=%d hidden_fn=%d hidden_data=%d\n",
           dlsym(h, "cg_export_fn") != 0, dlsym(h, "cg_export_data") != 0,
           dlsym(h, "cg_weak_fn") != 0, dlsym(h, "cg_weak_data") != 0,
           dlsym(h, "cg_hidden_fn") != 0, dlsym(h, "cg_hidden_data") != 0);
    value_fn export_fn = need(h, "cg_export_fn");
    long *export_data = need(h, "cg_export_data");
    long *(*hidden_addr)(void) = need(h, "cg_hidden_data_addr");
    long *(*weak_addr)(void) = need(h, "cg_weak_data_addr");
    long **(*weak_slot)(void) = need(h, "cg_weak_slot_addr");
    void *(*weak_fn_addr)(void) = need(h, "cg_weak_fn_addr");
    void **(*vtable)(void) = need(h, "cg_vtable_addr");
    long *(*export_addr)(void) = need(h, "cg_export_data_addr");
    printf("values export=%ld hidden_fn=%ld hidden_data=%ld intra=%ld provider=%ld\n",
           export_fn(), ((value_fn)need(h, "cg_call_hidden_fn"))(), *hidden_addr(),
           ((value_fn)need(h, "cg_call_export_fn"))(),
           ((value_fn)need(h, "cg_call_provider"))());
    long *weak_seen = weak_addr();
#if EXE_WEAK
    int data_is_exe = weak_seen == &cg_weak_data;
    int fn_is_exe = weak_fn_addr() == (void *)cg_weak_fn;
#else
    int data_is_exe = 0;
    int fn_is_exe = 0;
#endif
    printf("weak data=%ld fn=%ld data_is_exe=%d fn_is_exe=%d slot_agrees=%d\n",
           *weak_seen, ((value_fn)need(h, "cg_call_weak_fn"))(), data_is_exe, fn_is_exe,
           *weak_slot() == weak_seen);
    void **table = vtable();
    printf("const table_fn=%d table_data=%d data_addr=%d table_store_faults=%d data_store_faults=%d\n",
           table[0] == (void *)export_fn, table[1] == (void *)export_data,
           export_addr() == export_data, store_faults(table), store_faults((void **)export_data));
    return 0;
}
"#;

    const DIRECT_DRIVER: &str = r#"
#include <dlfcn.h>
#include <stdio.h>
__attribute__((weak)) long cg_direct_weak = 901;
__attribute__((weak)) long cg_weak_data = 900;
int main(int argc, char **argv) {
    void *h = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
    if (!h) { printf("dlopen: %s\n", dlerror()); return 91; }
    long *(*direct)(void) = dlsym(h, "cg_direct_weak_addr");
    long *(*got)(void) = dlsym(h, "cg_weak_data_addr");
    if (!direct || !got) return 90;
    printf("direct_is_exe=%d direct=%ld got_is_exe=%d got=%ld\n",
           direct() == &cg_direct_weak, *direct(), got() == &cg_weak_data, *got());
    return 0;
}
"#;

    const LINKED_DRIVER: &str = r#"
#include <stdio.h>
extern long cg_export_fn(void);
extern long cg_call_export_fn(void);
extern long cg_call_provider(void);
extern long cg_call_hidden_fn(void);
int main(void) {
    printf("export=%ld intra=%ld provider=%ld hidden=%ld\n", cg_export_fn(),
           cg_call_export_fn(), cg_call_provider(), cg_call_hidden_fn());
    return 0;
}
"#;

    const INTERPOSER: &str = r#"
extern long cg_export_fn(void);
extern long cg_provider_fn(void);
static long replacement_export(void) { return 7777; }
static long replacement_provider(void) { return 8888; }
__attribute__((used)) static struct { const void *replacement; const void *replacee; }
    interposers[] __attribute__((section("__DATA,__interpose"))) = {
    { (const void *)replacement_export, (const void *)cg_export_fn },
    { (const void *)replacement_provider, (const void *)cg_provider_fn },
};
"#;

    fn run_checked(command: &mut Command, what: &str) -> std::process::Output {
        let output = command_output_with_timeout(command, Duration::from_secs(120))
            .unwrap_or_else(|error| panic!("{what}: {error}"));
        assert!(!output.timed_out, "{what} timed out");
        assert!(
            output.output.status.success(),
            "{what} failed: {}",
            String::from_utf8_lossy(&output.output.stderr)
        );
        output.output
    }

    fn clang() -> Command {
        Command::new("/usr/bin/clang")
    }

    fn write(path: &Path, bytes: impl AsRef<[u8]>) -> PathBuf {
        std::fs::write(path, bytes).unwrap();
        path.to_path_buf()
    }

    /// Build `libprov.dylib` (install name `@loader_path/libprov.dylib`) in
    /// `directory`.
    fn provider(directory: &Path) {
        let source = write(&directory.join("prov.c"), PROVIDER_SOURCE);
        run_checked(
            clang()
                .args(["-dynamiclib", "-O1", "-install_name", PROVIDER_INSTALL_NAME])
                .arg(&source)
                .arg("-o")
                .arg(directory.join("libprov.dylib")),
            "libprov.dylib",
        );
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Linker {
        Ld64 { flat: bool },
        Standalone,
    }

    /// Link the CG objects into `libcg.dylib` in `directory`.
    fn cg_dylib(directory: &Path, linker: Linker, objects: &[Vec<u8>]) {
        let dylib = directory.join("libcg.dylib");
        let install_name = "@loader_path/libcg.dylib";
        match linker {
            Linker::Standalone => {
                let image = standalone_dylib(objects, install_name)
                    .unwrap_or_else(|error| panic!("standalone dylib: {error}"));
                write(&dylib, image);
            }
            Linker::Ld64 { flat } => {
                let mut command = clang();
                command.args(["-dynamiclib", "-install_name", install_name]);
                if flat {
                    command.arg("-flat_namespace");
                }
                for (index, bytes) in objects.iter().enumerate() {
                    command.arg(write(&directory.join(format!("cg{index}.o")), bytes));
                }
                run_checked(
                    command
                        .arg("-L")
                        .arg(directory)
                        .arg("-lprov")
                        .arg("-o")
                        .arg(&dylib),
                    "ld64 libcg.dylib",
                );
            }
        }
    }

    fn validate(path: &Path) {
        let output = run_checked(
            Command::new("/usr/bin/dyld_info")
                .arg("-validate_only")
                .arg(path),
            "dyld_info -validate_only",
        );
        let report = String::from_utf8_lossy(&output.stdout).to_ascii_lowercase()
            + &String::from_utf8_lossy(&output.stderr).to_ascii_lowercase();
        assert!(
            !report.contains("malformed") && !report.contains("error"),
            "dyld_info rejected {}: {report}",
            path.display()
        );
    }

    fn program(directory: &Path, name: &str, source: &str, defines: &[&str], link: &[&str]) {
        let source = write(&directory.join(format!("{name}.c")), source);
        run_checked(
            clang()
                .args(["-O1", "-fno-stack-protector"])
                .args(defines)
                .arg(&source)
                .args(link)
                .arg("-o")
                .arg(directory.join(name)),
            &format!("clang {name}"),
        );
    }

    fn run(path: &Path, args: &[&Path], environment: &[(&str, &Path)]) -> String {
        let mut command = Command::new(path);
        command.args(args);
        for (key, value) in environment {
            command.env(key, value);
        }
        let output = command_output_with_timeout(&mut command, Duration::from_secs(60))
            .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        assert!(!output.timed_out, "{} timed out", path.display());
        assert_eq!(
            output.output.status.code(),
            Some(0),
            "{}: stdout={} stderr={}",
            path.display(),
            String::from_utf8_lossy(&output.output.stdout),
            String::from_utf8_lossy(&output.output.stderr)
        );
        String::from_utf8(output.output.stdout).unwrap()
    }

    fn expected_dlopen(exe_weak: bool, flat: bool, mutable_vtable: bool) -> String {
        let (weak_data, weak_fn, is_exe) = if exe_weak {
            (900, 9001, 1)
        } else {
            (13, 3001, 0)
        };
        format!(
            "dlsym export_fn=1 export_data=1 weak_fn=1 weak_data=1 hidden_fn=0 hidden_data=0\n\
             values export=1001 hidden_fn=2002 hidden_data=12 intra=1001 provider={}\n\
             weak data={weak_data} fn={weak_fn} data_is_exe={is_exe} fn_is_exe={is_exe} slot_agrees=1\n\
             const table_fn=1 table_data=1 data_addr=1 table_store_faults={} data_store_faults=0\n",
            if flat { 6 } else { 5 },
            if mutable_vtable { 0 } else { 1 },
        )
    }

    /// dlopen each CG dylib from a C program: visibility through `dlsym`,
    /// dyld weak coalescing with (and without) the executable's weak
    /// definitions, two-level versus flat import binding, and the store fault
    /// on the relocated vtable once dyld has applied its fixups.
    #[test]
    fn dlopen_sees_exports_not_hidden_coalesces_weak_and_write_protects_data_const() {
        let linkers = [
            Linker::Ld64 { flat: false },
            Linker::Ld64 { flat: true },
            Linker::Standalone,
        ];
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            for mutable_vtable in [false, true] {
                let objects = [
                    compile_core(opt_level, mutable_vtable),
                    hidden_object(opt_level),
                ];
                for linker in linkers {
                    let label = format!("{opt_level:?} {linker:?} mutable_vtable={mutable_vtable}");
                    let directory = tempfile::Builder::new()
                        .prefix("trust-cg-macho-dylib-")
                        .tempdir()
                        .unwrap();
                    provider(directory.path());
                    cg_dylib(directory.path(), linker, &objects);
                    let dylib = directory.path().join("libcg.dylib");
                    validate(&dylib);
                    let binds = weak_coalesce_binds(&dylib);
                    assert!(
                        binds.contains("_cg_weak_data") && binds.contains("_cg_weak_fn"),
                        "{label}: dyld must coalesce both weak definitions: {binds:?}"
                    );
                    for exe_weak in [true, false] {
                        let name = format!("dlopen_{}", u8::from(exe_weak));
                        program(
                            directory.path(),
                            &name,
                            DLOPEN_DRIVER,
                            &[&format!("-DEXE_WEAK={}", u8::from(exe_weak))],
                            &[],
                        );
                        let stdout = run(&directory.path().join(&name), &[&dylib], &[]);
                        let flat = linker == Linker::Ld64 { flat: true };
                        assert_eq!(
                            stdout,
                            expected_dlopen(exe_weak, flat, mutable_vtable),
                            "{label} exe_weak={exe_weak}"
                        );
                    }
                }
            }
        }
    }

    /// Interposition: an inserted library's `__DATA,__interpose` tuples
    /// replace the executable's call into the CG dylib and the CG dylib's own
    /// import, but not the dylib's direct internal call (two-level namespace
    /// binds it at static link).
    #[test]
    fn dyld_insert_libraries_interposes_cg_dylib_exports_and_imports() {
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            let objects = [compile_core(opt_level, false), hidden_object(opt_level)];
            for linker in [Linker::Ld64 { flat: false }, Linker::Standalone] {
                let label = format!("{opt_level:?} {linker:?}");
                let directory = tempfile::Builder::new()
                    .prefix("trust-cg-macho-interpose-")
                    .tempdir()
                    .unwrap();
                let dir = directory.path();
                provider(dir);
                cg_dylib(dir, linker, &objects);
                validate(&dir.join("libcg.dylib"));
                let rpath = format!("-Wl,-rpath,{}", dir.display());
                let libs = [
                    "-L",
                    dir.to_str().unwrap(),
                    "-lcg",
                    "-lprov",
                    rpath.as_str(),
                ];
                program(dir, "linked", LINKED_DRIVER, &[], &libs);
                let interposer = write(&dir.join("interpose.c"), INTERPOSER);
                run_checked(
                    clang()
                        .args(["-dynamiclib", "-O1"])
                        .arg(&interposer)
                        .args(libs)
                        .arg("-o")
                        .arg(dir.join("libinterpose.dylib")),
                    "libinterpose.dylib",
                );
                let executable = dir.join("linked");
                assert_eq!(
                    run(&executable, &[], &[]),
                    "export=1001 intra=1001 provider=5 hidden=2002\n",
                    "{label}: without interposition"
                );
                assert_eq!(
                    run(
                        &executable,
                        &[],
                        &[("DYLD_INSERT_LIBRARIES", &dir.join("libinterpose.dylib"))]
                    ),
                    "export=7777 intra=1001 provider=8888 hidden=2002\n",
                    "{label}: under DYLD_INSERT_LIBRARIES"
                );
            }
        }
    }

    /// ld64 `-dead_strip` keeps the retained (`N_NO_DEAD_STRIP`) definition
    /// and drops the unreferenced plain one from a linked executable.
    #[test]
    fn ld64_dead_strip_keeps_only_retained_cg_definitions() {
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            let directory = tempfile::Builder::new()
                .prefix("trust-cg-macho-dead-strip-")
                .tempdir()
                .unwrap();
            let dir = directory.path();
            let object = write(&dir.join("cg.o"), compile_dead_strip(opt_level));
            let source = write(
                &dir.join("main.c"),
                "extern long cg_dead_strip_entry(void);\n\
                 int main(void) { return cg_dead_strip_entry() == 7 ? 0 : 1; }\n",
            );
            let executable = dir.join("main");
            run_checked(
                clang()
                    .args(["-O1", "-Wl,-dead_strip"])
                    .arg(&source)
                    .arg(&object)
                    .arg("-o")
                    .arg(&executable),
                "ld64 -dead_strip link",
            );
            assert_eq!(run(&executable, &[], &[]), "", "{opt_level:?}");
            let names = run_checked(Command::new("/usr/bin/nm").arg(&executable), "nm");
            let names = String::from_utf8_lossy(&names.stdout).into_owned();
            let defined: BTreeSet<&str> = names
                .lines()
                .filter_map(|line| line.split_whitespace().last())
                .collect();
            assert!(defined.contains("_cg_retained"), "{opt_level:?}: {names}");
            assert!(
                !defined.contains("_cg_unretained"),
                "{opt_level:?}: {names}"
            );
        }
    }

    /// Weak-coalescing binds dyld applies to `image`, as reported by the
    /// platform's `dyld_info` (`<weak-def-coalesce>/_name`).
    fn weak_coalesce_binds(image: &Path) -> BTreeSet<String> {
        let output = run_checked(
            Command::new("/usr/bin/dyld_info").arg("-fixups").arg(image),
            "dyld_info -fixups",
        );
        String::from_utf8_lossy(&output.stdout)
            .lines()
            .filter_map(|line| {
                let target = line.split_whitespace().last()?;
                target
                    .strip_prefix("<weak-def-coalesce>/")
                    .map(str::to_string)
            })
            .collect()
    }

    /// Mutation control for the coalescing harness: a direct page reference
    /// to a weak definition leaves no dyld bind, so it stays on the dylib's
    /// own copy while the GOT-indirect reference coalesces with the
    /// executable's. This host's ld64 (ld-prime) accepts the direct access
    /// without a diagnostic, so only the runtime check detects it; the
    /// standalone linker refuses it by name (object-level test above).
    #[test]
    fn direct_weak_reference_is_not_coalesced_by_ld64() {
        let directory = tempfile::Builder::new()
            .prefix("trust-cg-macho-direct-weak-")
            .tempdir()
            .unwrap();
        let dir = directory.path();
        provider(dir);
        cg_dylib(
            dir,
            Linker::Ld64 { flat: false },
            &[
                compile_core(OptLevel::O0, false),
                hidden_object(OptLevel::O0),
                direct_weak_object(OptLevel::O0),
            ],
        );
        let dylib = dir.join("libcg.dylib");
        let binds = weak_coalesce_binds(&dylib);
        assert!(binds.contains("_cg_weak_data"), "{binds:?}");
        assert!(!binds.contains("_cg_direct_weak"), "{binds:?}");
        program(dir, "direct", DIRECT_DRIVER, &[], &[]);
        assert_eq!(
            run(&dir.join("direct"), &[&dylib], &[]),
            "direct_is_exe=0 direct=21 got_is_exe=1 got=900\n"
        );
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
