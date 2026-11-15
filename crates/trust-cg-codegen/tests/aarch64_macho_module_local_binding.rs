// trust-cg-codegen/tests/aarch64_macho_module_local_binding.rs
//
// AArch64 Mach-O binding of module-local (Internal/Private) functions.
//
// Object level (every host): `Compiler::compile` admits direct calls to and
// every address form of an Internal or Private function for
// `aarch64-apple-darwin` (O0-O3, sequential and parallel). In each object the
// helper is one non-external `N_SECT` symbol (`n_type` exactly `N_SECT`) in
// `__TEXT,__text`, and every relocation that names it (the `BRANCH26` call,
// the `PAGE21`/`PAGEOFF12` address takings, the `UNSIGNED` data slot) names
// that symbol; none is a GOT relocation. Symbols and relocations are read
// back by an independent Mach-O reader below, not by the emitter's model nor
// by the crate's own reader. A hidden External helper is one private-extern
// (`N_EXT | N_PEXT`) definition; the other ELF-only object facts stay refused
// on Mach-O.
//
// Native (macOS AArch64 host only, O0-O3): two modules, each with its own
// Internal or Private `helper`, linked with a C object defining a global
// `helper` into one executable by `cc` (ld64) and by `run_link`, each reach
// their own helper through direct calls, function pointers in a local and in
// a global, and address takings; `nm` reads two non-external helpers and one
// external one, and `objdump` shows `a_direct` and `b_direct` branching to
// two different non-external helpers. The clang twin with `static` functions
// prints the same. Each module linked into its own dylib resists a
// `DYLD_INSERT_LIBRARIES` interposer under a forced flat namespace; the
// near-twin with an External helper is interposed, so the interposer is
// load-bearing. Execution evidence for ld64 and dyld on this host, not a
// linker or loader proof.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::BTreeSet;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{CompilationResult, Compiler, CompilerConfig, CompilerTraceLevel};
use trust_ir::value::GlobalId;
use trust_ir::{
    Block, BlockId, CastOp, Constant, FuncId, FuncTy, Function, Global, Inst, InstrNode, Linkage,
    Module, Ty, ValueId, Visibility,
};

const DARWIN: &str = "aarch64-apple-darwin";
const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

// =============================================================================
// Independent Mach-O 64 relocatable-object reader
// =============================================================================

const MH_MAGIC_64: u32 = 0xfeed_facf;
const CPU_TYPE_ARM64: u32 = 0x0100_000c;
const LC_SEGMENT_64: u32 = 0x19;
const LC_SYMTAB: u32 = 0x02;
const N_STAB: u8 = 0xe0;
const N_SECT: u8 = 0x0e;
const ARM64_RELOC_UNSIGNED: u8 = 0;
const ARM64_RELOC_BRANCH26: u8 = 2;
const ARM64_RELOC_PAGE21: u8 = 3;
const ARM64_RELOC_PAGEOFF12: u8 = 4;
const ARM64_RELOC_GOT_LOAD_PAGE21: u8 = 5;
const ARM64_RELOC_GOT_LOAD_PAGEOFF12: u8 = 6;
const ARM64_RELOC_POINTER_TO_GOT: u8 = 7;

fn rd_u32(b: &[u8], off: usize) -> u32 {
    u32::from_le_bytes(b[off..off + 4].try_into().unwrap())
}

fn rd_u64(b: &[u8], off: usize) -> u64 {
    u64::from_le_bytes(b[off..off + 8].try_into().unwrap())
}

fn name16(b: &[u8], off: usize) -> String {
    let raw = &b[off..off + 16];
    let end = raw.iter().position(|&c| c == 0).unwrap_or(16);
    String::from_utf8_lossy(&raw[..end]).into_owned()
}

#[derive(Debug, Clone)]
struct Section {
    segname: String,
    sectname: String,
    data: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Symbol {
    name: String,
    n_type: u8,
    n_sect: u8,
    n_value: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Reloc {
    /// `segname,sectname` of the section the record patches.
    section: String,
    address: u32,
    kind: u8,
    external: bool,
    /// The symbol's name for an external record, else the section ordinal.
    target: String,
}

#[derive(Debug)]
struct MachO {
    sections: Vec<Section>,
    symbols: Vec<Symbol>,
    relocs: Vec<Reloc>,
}

impl MachO {
    /// The symbols spelled `name` (debugger entries excluded).
    fn named(&self, name: &str) -> Vec<&Symbol> {
        self.symbols
            .iter()
            .filter(|symbol| symbol.n_type & N_STAB == 0 && symbol.name == name)
            .collect()
    }

    fn section_of(&self, symbol: &Symbol) -> String {
        let section = &self.sections[usize::from(symbol.n_sect) - 1];
        format!("{},{}", section.segname, section.sectname)
    }

    fn text(&self) -> &[u8] {
        &self
            .sections
            .iter()
            .find(|section| section.segname == "__TEXT" && section.sectname == "__text")
            .expect("__TEXT,__text")
            .data
    }
}

fn parse_macho(b: &[u8]) -> MachO {
    assert_eq!(rd_u32(b, 0), MH_MAGIC_64, "MH_MAGIC_64");
    assert_eq!(rd_u32(b, 4), CPU_TYPE_ARM64, "CPU_TYPE_ARM64");
    let ncmds = rd_u32(b, 16) as usize;
    let mut sections = Vec::new();
    let mut raw_relocs = Vec::new();
    let mut symtab = None;
    let mut command = 32;
    for _ in 0..ncmds {
        let cmd = rd_u32(b, command);
        let size = rd_u32(b, command + 4) as usize;
        if cmd == LC_SEGMENT_64 {
            let nsects = rd_u32(b, command + 64) as usize;
            for index in 0..nsects {
                let header = command + 72 + index * 80;
                let size = rd_u64(b, header + 40) as usize;
                let offset = rd_u32(b, header + 48) as usize;
                let flags = rd_u32(b, header + 64);
                let zerofill = matches!(flags & 0xff, 0x01 | 0x0c | 0x12);
                sections.push(Section {
                    sectname: name16(b, header),
                    segname: name16(b, header + 16),
                    data: if zerofill {
                        Vec::new()
                    } else {
                        b[offset..offset + size].to_vec()
                    },
                });
                raw_relocs.push((
                    rd_u32(b, header + 56) as usize,
                    rd_u32(b, header + 60) as usize,
                ));
            }
        } else if cmd == LC_SYMTAB {
            symtab = Some((
                rd_u32(b, command + 8) as usize,
                rd_u32(b, command + 12) as usize,
                rd_u32(b, command + 16) as usize,
            ));
        }
        command += size;
    }
    let (symoff, nsyms, stroff) = symtab.expect("LC_SYMTAB");
    let symbols: Vec<Symbol> = (0..nsyms)
        .map(|index| {
            let entry = symoff + index * 16;
            let strx = stroff + rd_u32(b, entry) as usize;
            let end = b[strx..].iter().position(|&c| c == 0).unwrap() + strx;
            Symbol {
                name: String::from_utf8_lossy(&b[strx..end]).into_owned(),
                n_type: b[entry + 4],
                n_sect: b[entry + 5],
                n_value: rd_u64(b, entry + 8),
            }
        })
        .collect();
    let mut relocs = Vec::new();
    for (section, (reloff, nreloc)) in sections.iter().zip(raw_relocs) {
        for index in 0..nreloc {
            let record = reloff + index * 8;
            let word1 = rd_u32(b, record + 4);
            let symbolnum = word1 & 0x00ff_ffff;
            let external = (word1 >> 27) & 1 != 0;
            relocs.push(Reloc {
                section: format!("{},{}", section.segname, section.sectname),
                address: rd_u32(b, record),
                kind: (word1 >> 28) as u8,
                external,
                target: if external {
                    symbols[symbolnum as usize].name.clone()
                } else {
                    format!("section #{symbolnum}")
                },
            });
        }
    }
    MachO {
        sections,
        symbols,
        relocs,
    }
}

// =============================================================================
// The module
// =============================================================================

/// Number of External `<tag>_pad_<n>` fillers, enough for the parallel
/// emitter (`worker_count_for_items` needs at least 32 items).
const LOCAL_BINDING_PADDING: usize = 32;

/// Definitions of [`local_binding_module`] before its padding.
const LOCAL_BINDING_CORE_FUNCTIONS: usize = 9;

/// A module whose bodied `helper` (linkage `helper_linkage`) computes
/// `x + offset` and counts its calls in the Internal global `<tag>_count`.
/// The store keeps it out of the module inliner, so its direct calls stay
/// calls. Its External entry points:
///
/// * `<tag>_direct(x)`: a direct `Call`;
/// * `<tag>_via_local(x)`: a `CallIndirect` through its `FnDef` address held
///   in a local (a static-call candidate the AOT adapter keeps indirect);
/// * `<tag>_via_global(x)`: a `CallIndirect` through the pointer loaded from
///   `<tag>_slot`, an External global initialized with `SymbolAddr(helper)`;
/// * `<tag>_addr()` and `<tag>_addr_again()`: two separate `FnDef` takings;
/// * `<tag>_addr_raw()`: a body `SymbolAddr(helper)` taking;
/// * `<tag>_same()`: 1 when the `FnDef` address equals the slot's pointer;
/// * `<tag>_calls()`: the call count;
///
/// plus [`LOCAL_BINDING_PADDING`] External `<tag>_pad_<n>` fillers. (The
/// AArch64 ELF twin is `aarch64_elf_symbol_binding.rs`'s module of the same
/// name; this one carries no target info, so the Darwin triple applies.)
fn local_binding_module(tag: &str, helper_linkage: Linkage, offset: i128) -> Module {
    let mut module = Module::new(format!("module_local_binding_{tag}"));
    let unary = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let pointer = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let nullary = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let global = |name: String, ty: Ty, initializer: Constant, linkage: Linkage| Global {
        name,
        ty,
        mutable: true,
        initializer: Some(initializer),
        linkage,
        tls: None,
        align: Some(8),
        section: None,
        visibility: Visibility::Default,
        retained: false,
    };
    module.globals.push(global(
        format!("{tag}_count"),
        Ty::U64,
        Constant::Int(0),
        Linkage::Internal,
    ));
    module.globals.push(global(
        format!("{tag}_slot"),
        Ty::Ptr,
        Constant::SymbolAddr {
            symbol: "helper".into(),
            addend: 0,
        },
        Linkage::External,
    ));
    let counter = GlobalId::new(0);
    let slot = GlobalId::new(1);
    let helper = FuncId::new(0);
    let value = ValueId::new;
    let node = |inst: Inst, result: u32| InstrNode::new(inst).with_result(value(result));
    let ret = |result: u32| {
        InstrNode::new(Inst::Return {
            values: vec![value(result)],
        })
    };
    let fn_def = |result: u32| {
        [
            node(
                Inst::Const {
                    ty: Ty::Func(unary),
                    value: Constant::FnDef(helper),
                },
                result,
            ),
            node(
                Inst::Cast {
                    op: CastOp::ReifyFnPointer,
                    src_ty: Ty::Func(unary),
                    dst_ty: Ty::Ptr,
                    operand: value(result),
                },
                result + 1,
            ),
        ]
    };
    let load_slot = |result: u32| {
        [
            node(Inst::GlobalAddr { global: slot }, result),
            node(
                Inst::Load {
                    ty: Ty::Ptr,
                    ptr: value(result),
                    volatile: false,
                    align: Some(8),
                },
                result + 1,
            ),
        ]
    };
    let call_indirect = |callee: u32, argument: u32, result: u32| {
        node(
            Inst::CallIndirect {
                callee: value(callee),
                sig: unary,
                args: vec![value(argument)],
                calling_conv: trust_ir::CallingConv::C,
            },
            result,
        )
    };
    let mut define = |name: String, sig, params: Vec<(ValueId, Ty)>, body: Vec<InstrNode>| {
        let id = FuncId::new(module.functions.len() as u32);
        let mut function = Function::new(id, name, sig, BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.params = params;
        block.body = body;
        function.blocks.push(block);
        module.functions.push(function);
        id
    };
    let x = || vec![(value(0), Ty::U64)];
    let constant = |value: i128, result: u32| {
        node(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(value),
            },
            result,
        )
    };
    let add = |lhs: u32, rhs: u32, result: u32| {
        node(
            Inst::BinOp {
                op: trust_ir::BinOp::Add,
                ty: Ty::U64,
                lhs: value(lhs),
                rhs: value(rhs),
            },
            result,
        )
    };
    let load_count = |address: u32, result: u32| {
        [
            node(Inst::GlobalAddr { global: counter }, address),
            node(
                Inst::Load {
                    ty: Ty::U64,
                    ptr: value(address),
                    volatile: false,
                    align: Some(8),
                },
                result,
            ),
        ]
    };

    let mut helper_body = load_count(1, 2).to_vec();
    helper_body.extend([
        constant(1, 3),
        add(2, 3, 4),
        InstrNode::new(Inst::Store {
            ty: Ty::U64,
            ptr: value(1),
            value: value(4),
            volatile: false,
            align: Some(8),
        }),
        constant(offset, 5),
        add(0, 5, 6),
        ret(6),
    ]);
    assert_eq!(define("helper".into(), unary, x(), helper_body), helper);
    define(
        format!("{tag}_direct"),
        unary,
        x(),
        vec![
            node(
                Inst::Call {
                    callee: helper,
                    args: vec![value(0)],
                },
                1,
            ),
            ret(1),
        ],
    );
    let mut via_local = fn_def(1).to_vec();
    via_local.push(node(
        Inst::Copy {
            ty: Ty::Ptr,
            operand: value(2),
        },
        3,
    ));
    via_local.extend([call_indirect(3, 0, 4), ret(4)]);
    define(format!("{tag}_via_local"), unary, x(), via_local);
    let mut via_global = load_slot(1).to_vec();
    via_global.extend([call_indirect(2, 0, 3), ret(3)]);
    define(format!("{tag}_via_global"), unary, x(), via_global);
    for name in ["addr", "addr_again"] {
        let mut body = fn_def(0).to_vec();
        body.push(ret(1));
        define(format!("{tag}_{name}"), pointer, vec![], body);
    }
    define(
        format!("{tag}_addr_raw"),
        pointer,
        vec![],
        vec![
            node(
                Inst::Const {
                    ty: Ty::Ptr,
                    value: Constant::SymbolAddr {
                        symbol: "helper".into(),
                        addend: 0,
                    },
                },
                0,
            ),
            ret(0),
        ],
    );
    let mut same = fn_def(0).to_vec();
    same.extend(load_slot(2));
    same.extend([
        node(
            Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: Ty::U64,
                operand: value(1),
            },
            4,
        ),
        node(
            Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: Ty::U64,
                operand: value(3),
            },
            5,
        ),
        node(
            Inst::ICmp {
                op: trust_ir::ICmpOp::Eq,
                ty: Ty::U64,
                lhs: value(4),
                rhs: value(5),
            },
            6,
        ),
        node(
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::U64,
                operand: value(6),
            },
            7,
        ),
        ret(7),
    ]);
    define(format!("{tag}_same"), nullary, vec![], same);
    let mut calls = load_count(0, 1).to_vec();
    calls.push(ret(1));
    let core = define(format!("{tag}_calls"), nullary, vec![], calls);
    assert_eq!(core.index() as usize + 1, LOCAL_BINDING_CORE_FUNCTIONS);
    for index in 0..LOCAL_BINDING_PADDING {
        define(
            format!("{tag}_pad_{index}"),
            nullary,
            vec![],
            vec![constant(index as i128, 0), ret(0)],
        );
    }
    module.functions[helper.index() as usize].linkage = helper_linkage;
    module
}

fn darwin_compiler(opt_level: OptLevel, parallel: bool) -> Compiler {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            parallel,
            trace_level: CompilerTraceLevel::Full,
            ..Default::default()
        },
        TargetSpec::parse(DARWIN).expect("triple"),
    )
    .with_codegen_license(permit_unlicensed())
}

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

/// Every reference to `_helper` in `object` names its one non-external
/// definition in `__TEXT,__text`: the direct call (`BRANCH26`), the `FnDef`
/// and `SymbolAddr` takings (`PAGE21` + `PAGEOFF12`, never a GOT relocation)
/// and the data slot (`UNSIGNED` in `__DATA`). Returns the parsed object.
fn assert_helper_references_bind_locally(object: &[u8], label: &str) -> MachO {
    let macho = parse_macho(object);
    let helpers = macho.named("_helper");
    assert!(
        matches!(helpers.as_slice(), [helper] if helper.n_type == N_SECT),
        "{label}: `_helper` must be one non-external N_SECT definition: {helpers:?}"
    );
    assert_eq!(
        macho.section_of(helpers[0]),
        "__TEXT,__text",
        "{label}: helper is defined in __text"
    );
    let kinds: BTreeSet<(String, u8)> = macho
        .relocs
        .iter()
        .filter(|reloc| reloc.external && reloc.target == "_helper")
        .map(|reloc| (reloc.section.clone(), reloc.kind))
        .collect();
    for kind in [
        ARM64_RELOC_BRANCH26,
        ARM64_RELOC_PAGE21,
        ARM64_RELOC_PAGEOFF12,
    ] {
        assert!(
            kinds.contains(&("__TEXT,__text".to_string(), kind)),
            "{label}: __text relocation kind {kind} names the local helper: {kinds:?}"
        );
    }
    assert!(
        kinds
            .iter()
            .any(|(section, kind)| section.starts_with("__DATA,") && *kind == ARM64_RELOC_UNSIGNED),
        "{label}: the data slot relocates against the local helper: {kinds:?}"
    );
    assert!(
        kinds.iter().all(|(_, kind)| ![
            ARM64_RELOC_GOT_LOAD_PAGE21,
            ARM64_RELOC_GOT_LOAD_PAGEOFF12,
            ARM64_RELOC_POINTER_TO_GOT
        ]
        .contains(kind)),
        "{label}: no GOT access to a local function: {kinds:?}"
    );
    macho
}

/// `Compiler::compile` admits direct calls to and every address form of an
/// Internal or Private function on AArch64 Mach-O, O0-O3, sequential and
/// parallel (the trace names the emission path). In each object the helper
/// is one non-external `N_SECT` symbol and every relocation that names it
/// (call, page address, data slot) names that symbol; no GOT relocation
/// names it. The sequential and parallel objects carry the same text and
/// relocations.
#[test]
fn compiler_binds_module_local_function_references_locally_on_aarch64_macho() {
    let functions = LOCAL_BINDING_CORE_FUNCTIONS + LOCAL_BINDING_PADDING;
    for helper_linkage in [Linkage::Internal, Linkage::Private] {
        let module = local_binding_module("a", helper_linkage, 100);
        for opt_level in OPT_LEVELS {
            let mut objects = Vec::new();
            for parallel in [false, true] {
                let label = format!("{helper_linkage} {opt_level:?} parallel={parallel}");
                let compiler = darwin_compiler(opt_level, parallel);
                assert!(compiler.object_binds_module_local_functions(), "{label}");
                let result = compiler
                    .compile(&module)
                    .unwrap_or_else(|error| panic!("{label}: {error}"));
                let path = emission_path(&result);
                assert!(
                    path.starts_with(&format!("{functions} functions, "))
                        && path.contains(if parallel {
                            "parallel preparation and emission"
                        } else {
                            "sequential preparation and emission"
                        }),
                    "{label}: {path}"
                );
                objects.push(assert_helper_references_bind_locally(
                    &result.object_code,
                    &label,
                ));
            }
            let (sequential, parallel) = (&objects[0], &objects[1]);
            assert_eq!(
                sequential.text(),
                parallel.text(),
                "{helper_linkage} {opt_level:?}"
            );
            let relocations =
                |macho: &MachO| -> BTreeSet<Reloc> { macho.relocs.iter().cloned().collect() };
            assert_eq!(
                relocations(sequential),
                relocations(parallel),
                "{helper_linkage} {opt_level:?}"
            );
        }
    }
}

/// The same module with an External `helper` (the near-twin) binds it
/// external (`N_SECT | N_EXT`), so the reader above tells the two apart.
#[test]
fn external_helper_near_twin_is_an_external_definition() {
    let result = darwin_compiler(OptLevel::O2, false)
        .compile(&local_binding_module("a", Linkage::External, 100))
        .expect("External helper compiles");
    let macho = parse_macho(&result.object_code);
    let helpers = macho.named("_helper");
    assert!(
        matches!(helpers.as_slice(), [helper] if helper.n_type == N_SECT | 0x01),
        "{helpers:?}"
    );
}

/// The module's `helper` function.
fn helper_mut(module: &mut Module) -> &mut Function {
    module
        .functions
        .iter_mut()
        .find(|function| function.name == "helper")
        .expect("the module defines `helper`")
}

/// The same module with a HIDDEN External `helper` (the rustc bridge's
/// CGU-private function shape) binds it private extern
/// (`N_SECT | N_EXT | N_PEXT`) at every opt level: external for static
/// linking, demoted to a local by the final link, never exported.
#[test]
fn hidden_external_helper_is_a_private_extern_definition() {
    for opt_level in OPT_LEVELS {
        let mut module = local_binding_module("a", Linkage::External, 100);
        helper_mut(&mut module).visibility = Visibility::Hidden;
        let result = darwin_compiler(opt_level, false)
            .compile(&module)
            .unwrap_or_else(|error| panic!("{opt_level:?}: hidden External helper: {error:?}"));
        let macho = parse_macho(&result.object_code);
        let helpers = macho.named("_helper");
        assert!(
            matches!(helpers.as_slice(), [helper] if helper.n_type == N_SECT | 0x01 | 0x10),
            "{opt_level:?}: `_helper` must be one private-extern definition: {helpers:?}"
        );
    }
}

/// Mach-O binds module-local functions and admits one v45 function fact,
/// hidden visibility on an `External` definition (above); everything else
/// stays refused there by name: an `ExternalWeak` declaration, hidden
/// visibility on a module-local definition, protected visibility (no Mach-O
/// spelling), and an explicit section on a function definition.
#[test]
fn macho_keeps_refusing_the_elf_only_object_facts() {
    let base = || local_binding_module("a", Linkage::Internal, 100);
    let mut weak = base();
    let signature = weak.functions[0].ty;
    let mut declaration = Function::new(
        FuncId::new(weak.functions.len() as u32),
        "maybe_absent",
        signature,
        BlockId::new(0),
    );
    declaration.linkage = Linkage::ExternalWeak;
    weak.functions.push(declaration);
    // The weak import is an FFI boundary: trust-ir requires the pinned target
    // (`TargetInfoRequired`), which every ingestion entry enforces (WS7.3), so
    // the module names the Mach-O triple it is compiled for and the refusal
    // below is the adapter's object-fact policy, as before.
    pinned_target::pin(&mut weak, DARWIN);
    let mut hidden = base();
    helper_mut(&mut hidden).visibility = Visibility::Hidden;
    let mut protected = local_binding_module("a", Linkage::External, 100);
    helper_mut(&mut protected).visibility = Visibility::Protected;
    let mut sectioned = base();
    sectioned.functions[1].section = Some("__TEXT,__tcg_local".into());
    for (label, module, needle) in [
        ("external weak", weak, "linkage: ExternalWeak"),
        (
            "hidden module-local",
            hidden,
            "function: \"helper\", facet: \"visibility\", value: \"hidden\"",
        ),
        (
            "protected",
            protected,
            "function: \"helper\", facet: \"visibility\", value: \"protected\"",
        ),
        ("section", sectioned, "facet: \"section\""),
    ] {
        let error = darwin_compiler(OptLevel::O2, false)
            .compile(&module)
            .expect_err("an ELF-only object fact on Mach-O");
        let debug = format!("{error:?}");
        assert!(
            debug.starts_with("Adapter(") && debug.contains(needle),
            "{label}: refused by the adapter's object-fact policy: {debug}"
        );
    }
}

/// A module with module-local (`linkage`) `sin` and `cos` that add 1.0 and
/// 2.0 to their argument and count their calls in an Internal global (the
/// store keeps them out of the module inliner), and an External
/// `trig_sum(x) = sin(x) + cos(x)`: the same-argument pair the Darwin
/// `sincos-merge` pass fuses into one `___sincos_stret` call by name.
fn local_trig_module(linkage: Linkage) -> Module {
    let mut module = Module::new("module_local_trig");
    let unary = module
        .add_func_type(FuncTy {
            params: vec![Ty::F64],
            returns: vec![Ty::F64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module.globals.push(Global {
        name: "trig_count".into(),
        ty: Ty::U64,
        mutable: true,
        initializer: Some(Constant::Int(0)),
        linkage: Linkage::Internal,
        tls: None,
        align: Some(8),
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });
    let value = ValueId::new;
    let node = |inst: Inst, result: u32| InstrNode::new(inst).with_result(value(result));
    let x = || vec![(value(0), Ty::F64)];
    let mut define = |name: &str, body: Vec<InstrNode>| {
        let id = FuncId::new(module.functions.len() as u32);
        let mut function = Function::new(id, name, unary, BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.params = x();
        block.body = body;
        function.blocks.push(block);
        module.functions.push(function);
        id
    };
    let counted = |offset: f64| {
        vec![
            node(
                Inst::GlobalAddr {
                    global: GlobalId::new(0),
                },
                1,
            ),
            node(
                Inst::Load {
                    ty: Ty::U64,
                    ptr: value(1),
                    volatile: false,
                    align: Some(8),
                },
                2,
            ),
            node(
                Inst::Const {
                    ty: Ty::U64,
                    value: Constant::Int(1),
                },
                3,
            ),
            node(
                Inst::BinOp {
                    op: trust_ir::BinOp::Add,
                    ty: Ty::U64,
                    lhs: value(2),
                    rhs: value(3),
                },
                4,
            ),
            InstrNode::new(Inst::Store {
                ty: Ty::U64,
                ptr: value(1),
                value: value(4),
                volatile: false,
                align: Some(8),
            }),
            node(
                Inst::Const {
                    ty: Ty::F64,
                    value: Constant::Float(offset),
                },
                5,
            ),
            node(
                Inst::BinOp {
                    op: trust_ir::BinOp::FAdd,
                    ty: Ty::F64,
                    lhs: value(0),
                    rhs: value(5),
                },
                6,
            ),
            InstrNode::new(Inst::Return {
                values: vec![value(6)],
            }),
        ]
    };
    let sin = define("sin", counted(1.0));
    let cos = define("cos", counted(2.0));
    define(
        "trig_sum",
        vec![
            node(
                Inst::Call {
                    callee: sin,
                    args: vec![value(0)],
                },
                1,
            ),
            node(
                Inst::Call {
                    callee: cos,
                    args: vec![value(0)],
                },
                2,
            ),
            node(
                Inst::BinOp {
                    op: trust_ir::BinOp::FAdd,
                    ty: Ty::F64,
                    lhs: value(1),
                    rhs: value(2),
                },
                3,
            ),
            InstrNode::new(Inst::Return {
                values: vec![value(3)],
            }),
        ],
    );
    module.functions[sin.index() as usize].linkage = linkage;
    module.functions[cos.index() as usize].linkage = linkage;
    module
}

/// The Darwin `sincos-merge` pass fuses a same-argument `Bl sin` / `Bl cos`
/// pair into one `___sincos_stret` call by callee name. With module-local
/// functions now bound on Mach-O, a module's own Internal or Private `sin`
/// and `cos` would have their calls replaced by libm's (measured before the
/// refusal: `trig_sum(0.5)` printed `1.3570081004945758`, libm's
/// `sin(0.5) + cos(0.5)`, at O2 and O3 instead of the module's `4`). So on
/// `aarch64-apple-darwin` a referenced module-local `sin` is refused by name
/// at every opt level. Near twins: the same functions unreferenced still
/// compile on Darwin, and the referenced module compiles for AArch64 ELF
/// (where the pass is inert) with no `__sincos_stret` reference.
#[test]
fn referenced_module_local_sin_and_cos_are_refused_where_sincos_merge_runs() {
    for linkage in [Linkage::Internal, Linkage::Private] {
        for opt_level in OPT_LEVELS {
            let label = format!("{linkage} {opt_level:?}");
            let error = darwin_compiler(opt_level, false)
                .compile(&local_trig_module(linkage))
                .expect_err("a referenced module-local sin on Darwin");
            assert!(
                matches!(
                    &error,
                    trust_cg_codegen::CompileError::ModuleLocalFunctionShadowsRuntimeSymbol {
                        function,
                        target,
                    } if function == "sin" && target == DARWIN
                ),
                "{label}: {error}"
            );
            let mut unreferenced = local_trig_module(linkage);
            unreferenced.functions.pop();
            darwin_compiler(opt_level, false)
                .compile(&unreferenced)
                .unwrap_or_else(|error| panic!("{label} unreferenced: {error}"));
            let elf = Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level,
                    ..Default::default()
                },
                TargetSpec::parse("aarch64-unknown-linux-gnu").expect("triple"),
            )
            .with_codegen_license(permit_unlicensed())
            .compile(&local_trig_module(linkage))
            .unwrap_or_else(|error| panic!("{label} ELF: {error}"))
            .object_code;
            assert!(
                !elf.windows(b"sincos".len())
                    .any(|window| window == b"sincos"),
                "{label}: the ELF object names no sincos routine"
            );
        }
    }
}

#[path = "common/rosetta.rs"]
mod process;

#[path = "common/pinned_target.rs"]
mod pinned_target;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
mod native {
    use super::*;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::Command;

    /// A row's scratch directory, owned (RAII): removed when the row ends,
    /// passed or failed, and kept (its path printed) for a failing row only
    /// when `TRUST_CG_KEEP_TEST_OBJECTS` is set.
    fn scratch(tag: &str) -> crate::fresh_dir::ScratchDir {
        crate::fresh_dir::create(&format!("tcg-macho-binding-{tag}-"))
    }

    fn run(command: &mut Command, directory: &Path) -> (bool, String, String) {
        let result = crate::process::command_output_with_timeout(
            command,
            crate::process::codegen_link_timeout(),
        )
        .expect("native tool launches");
        assert!(
            !result.timed_out,
            "{command:?} timed out; preserved files={directory:?}"
        );
        (
            result.output.status.success(),
            String::from_utf8_lossy(&result.output.stdout).into_owned(),
            String::from_utf8_lossy(&result.output.stderr).into_owned(),
        )
    }

    fn ok(command: &mut Command, directory: &Path) -> String {
        let (success, stdout, stderr) = run(command, directory);
        assert!(
            success,
            "{command:?} failed; preserved files={directory:?}\nstdout={stdout}\nstderr={stderr}"
        );
        stdout
    }

    fn write(directory: &Path, name: &str, bytes: impl AsRef<[u8]>) -> PathBuf {
        let path = directory.join(name);
        fs::write(&path, bytes).unwrap();
        path
    }

    /// The clang twin of [`local_binding_module`]: a `static` helper and
    /// counter behind the same External entry points.
    fn local_binding_c_source(tag: &str, offset: u64) -> String {
        format!(
            "#include <stdint.h>\n\
             typedef uint64_t (*unary)(uint64_t);\n\
             static uint64_t {tag}_count;\n\
             static uint64_t helper(uint64_t x) {{ {tag}_count += 1; return x + {offset}; }}\n\
             unary {tag}_slot = helper;\n\
             uint64_t {tag}_direct(uint64_t x) {{ return helper(x); }}\n\
             uint64_t {tag}_via_local(uint64_t x) {{ unary p = helper; return p(x); }}\n\
             uint64_t {tag}_via_global(uint64_t x) {{ return {tag}_slot(x); }}\n\
             void *{tag}_addr(void) {{ return (void *)helper; }}\n\
             void *{tag}_addr_again(void) {{ return (void *)helper; }}\n\
             void *{tag}_addr_raw(void) {{ return (void *)&helper; }}\n\
             uint64_t {tag}_same(void) {{ return (void *)helper == (void *){tag}_slot; }}\n\
             uint64_t {tag}_calls(void) {{ return {tag}_count; }}\n"
        )
    }

    /// Driver for modules `a` (helper `x + 100`) and `b` (`x + 200`). With
    /// `global_helper` it also calls the image's global `helper` (`x + 300`,
    /// a third object) and checks that neither module's address taking
    /// yields it.
    fn local_binding_driver(global_helper: bool) -> String {
        let mut source = String::from(
            "#include <stdint.h>\n#include <stdio.h>\n\
             typedef uint64_t (*unary)(uint64_t);\n\
             typedef unsigned long long ull;\n",
        );
        for tag in ["a", "b"] {
            source += &format!(
                "extern unary {tag}_slot;\n\
                 uint64_t {tag}_direct(uint64_t), {tag}_via_local(uint64_t),\n\
                   {tag}_via_global(uint64_t), {tag}_same(void), {tag}_calls(void);\n\
                 void *{tag}_addr(void), *{tag}_addr_again(void), *{tag}_addr_raw(void);\n"
            );
        }
        if global_helper {
            source += "uint64_t helper(uint64_t);\n";
        }
        source += "int main(void) {\n\
                     ull calls[6], pointers[4];\n\
                     calls[0] = a_direct(1); calls[1] = a_via_local(2);\n\
                     calls[2] = a_via_global(3); calls[3] = b_direct(1);\n\
                     calls[4] = b_via_local(2); calls[5] = b_via_global(3);\n\
                     printf(\"calls %llu %llu %llu %llu %llu %llu\\n\", calls[0], calls[1],\n\
                       calls[2], calls[3], calls[4], calls[5]);\n\
                     pointers[0] = ((unary)a_addr())(5); pointers[1] = ((unary)b_addr())(5);\n\
                     pointers[2] = a_slot(6); pointers[3] = b_slot(6);\n\
                     printf(\"pointers %llu %llu %llu %llu\\n\", pointers[0], pointers[1],\n\
                       pointers[2], pointers[3]);\n\
                     printf(\"counts %llu %llu\\n\", (ull)a_calls(), (ull)b_calls());\n\
                     printf(\"same %d %d %d %llu %d %d %d %llu\\n\",\n\
                       a_addr() == a_addr_again(), a_addr() == (void *)a_slot,\n\
                       a_addr_raw() == a_addr(), (ull)a_same(),\n\
                       b_addr() == b_addr_again(), b_addr() == (void *)b_slot,\n\
                       b_addr_raw() == b_addr(), (ull)b_same());\n\
                     printf(\"distinct %d\", a_addr() != b_addr());\n";
        if global_helper {
            source += "  printf(\" %d %d global %llu\", a_addr() != (void *)helper,\n\
                         b_addr() != (void *)helper, (ull)helper(4));\n";
        }
        source += "  printf(\"\\n\");\n  return 0;\n}\n";
        source
    }

    /// What [`local_binding_driver`] prints when every call and address
    /// taking reaches its own module's helper. `a_offset` is what module
    /// `a`'s helper adds (100, or an interposer's value).
    fn local_binding_expected(global_helper: bool) -> String {
        format!(
            "calls 101 102 103 201 202 203\npointers 105 205 106 206\ncounts 5 5\n\
             same 1 1 1 1 1 1 1 1\ndistinct 1{}\n",
            if global_helper { " 1 1 global 304" } else { "" }
        )
    }

    fn cc_object(source: &Path, object: &Path, o_flag: &str, directory: &Path) {
        ok(
            Command::new("cc")
                .args(["-c", o_flag])
                .arg(source)
                .arg("-o")
                .arg(object),
            directory,
        );
    }

    /// `nm -m` rows `(external, address)` of every defined `_helper` in an
    /// image or object.
    fn nm_helpers(path: &Path, directory: &Path) -> Vec<(bool, u64)> {
        let text = ok(Command::new("nm").arg("-m").arg(path), directory);
        text.lines()
            .filter(|line| line.ends_with(" _helper") && line.contains("(__TEXT,__text)"))
            .map(|line| {
                let address = u64::from_str_radix(line.split_whitespace().next().unwrap(), 16)
                    .expect("nm address");
                (!line.contains("non-external"), address)
            })
            .collect()
    }

    /// The targets of every `bl`/`b` in `function` of a linked image, read
    /// by `objdump`.
    fn branch_targets(image: &Path, function: &str, directory: &Path) -> BTreeSet<u64> {
        let text = ok(
            Command::new("objdump")
                .args(["-d", "--no-show-raw-insn"])
                .arg(format!("--disassemble-symbols=_{function}"))
                .arg(image),
            directory,
        );
        text.lines()
            .filter_map(|line| {
                let mut words = line.split_whitespace().skip(1);
                let mnemonic = words.next()?;
                if mnemonic != "bl" && mnemonic != "b" {
                    return None;
                }
                let target = words.next()?.trim_start_matches("0x");
                u64::from_str_radix(target, 16).ok()
            })
            .collect()
    }

    /// Two trust-ir modules `a` and `b`, each with its own Internal (`a`) or
    /// Private (`b`) `helper`, compiled by `Compiler::compile` at O0-O3,
    /// sequential and parallel, linked with a third C object defining a
    /// global `helper` into one executable by `cc` (ld64) and by `run_link`.
    /// Every direct call, function pointer in a local, function pointer in
    /// a global and address taking in `a` and `b` reaches its own module's
    /// helper; the two takings in each module and its data slot agree; the
    /// three helpers are distinct. `nm` reads two non-external `_helper`s and
    /// one external one, and `objdump` shows `a_direct` and `b_direct`
    /// branching to two different non-external helpers, never the external
    /// one. The clang twin with `static` functions prints the same.
    #[test]
    fn module_local_functions_bind_to_their_own_object_in_executables() {
        let modules = [
            ("a", local_binding_module("a", Linkage::Internal, 100)),
            ("b", local_binding_module("b", Linkage::Private, 200)),
        ];
        let expected = local_binding_expected(true);
        for opt_level in OPT_LEVELS {
            let directory = scratch("exe");
            let o_flag = format!("-O{}", opt_level as u8);
            let driver = directory.join("driver.o");
            cc_object(
                &write(&directory, "driver.c", local_binding_driver(true)),
                &driver,
                &o_flag,
                &directory,
            );
            let global = directory.join("global_helper.o");
            cc_object(
                &write(
                    &directory,
                    "global_helper.c",
                    "#include <stdint.h>\nuint64_t helper(uint64_t x) { return x + 300; }\n",
                ),
                &global,
                &o_flag,
                &directory,
            );
            let mut clang_objects = Vec::new();
            for (tag, offset) in [("a", 100), ("b", 200)] {
                let object = directory.join(format!("clang_{tag}.o"));
                cc_object(
                    &write(
                        &directory,
                        &format!("clang_{tag}.c"),
                        local_binding_c_source(tag, offset),
                    ),
                    &object,
                    &o_flag,
                    &directory,
                );
                clang_objects.push(object);
            }
            let clang_binary = directory.join("clang_program");
            ok(
                Command::new("cc")
                    .arg(&driver)
                    .arg(&global)
                    .args(&clang_objects)
                    .arg("-o")
                    .arg(&clang_binary),
                &directory,
            );
            let clang_output = ok(&mut Command::new(&clang_binary), &directory);
            assert_eq!(clang_output, expected, "clang {opt_level:?}");

            for parallel in [false, true] {
                let label = format!("{opt_level:?} parallel={parallel}");
                let leg = directory.join(if parallel { "parallel" } else { "sequential" });
                fs::create_dir_all(&leg).unwrap();
                let mut objects = Vec::new();
                for (tag, module) in &modules {
                    let result = darwin_compiler(opt_level, parallel)
                        .compile(module)
                        .unwrap_or_else(|error| panic!("{label} {tag}: {error}"));
                    assert_helper_references_bind_locally(
                        &result.object_code,
                        &format!("{label} {tag}"),
                    );
                    let object = write(&leg, &format!("{tag}.o"), &result.object_code);
                    assert_eq!(
                        nm_helpers(&object, &leg),
                        vec![(false, nm_helpers(&object, &leg)[0].1)],
                        "{label} {tag}: nm reads one non-external _helper"
                    );
                    objects.push(object);
                }
                for linker in ["cc", "run_link"] {
                    let label = format!("{label} {linker}");
                    let binary = leg.join(format!("program-{linker}"));
                    let mut inputs = vec![driver.clone(), global.clone()];
                    inputs.extend(objects.iter().cloned());
                    if linker == "run_link" {
                        let request = trust_cg_codegen::link_driver::LinkRequest::executable(
                            TargetSpec::parse(DARWIN).expect("triple"),
                            inputs,
                            binary.clone(),
                        );
                        trust_cg_codegen::link_driver::run_link(&request, "cc")
                            .unwrap_or_else(|error| panic!("{label}: {error}"));
                    } else {
                        ok(
                            Command::new("cc").args(&inputs).arg("-o").arg(&binary),
                            &leg,
                        );
                    }
                    let output = ok(&mut Command::new(&binary), &leg);
                    assert_eq!(output, expected, "{label}");
                    assert_eq!(output, clang_output, "{label}: the clang twin agrees");

                    let helpers = nm_helpers(&binary, &leg);
                    let locals: Vec<u64> = helpers
                        .iter()
                        .filter(|(external, _)| !external)
                        .map(|(_, address)| *address)
                        .collect();
                    let externals: Vec<u64> = helpers
                        .iter()
                        .filter(|(external, _)| *external)
                        .map(|(_, address)| *address)
                        .collect();
                    assert!(
                        locals.len() == 2 && externals.len() == 1,
                        "{label}: two non-external helpers and one external: {helpers:?}"
                    );
                    let target = |function: &str| {
                        let targets = branch_targets(&binary, function, &leg);
                        assert!(
                            targets.len() == 1
                                && targets.iter().all(|target| locals.contains(target)),
                            "{label}: `{function}` must branch only to one non-external helper \
                             {locals:x?} (external {externals:x?}): {targets:x?}"
                        );
                        *targets.first().unwrap()
                    };
                    assert_ne!(
                        target("a_direct"),
                        target("b_direct"),
                        "{label}: each module calls its own helper"
                    );
                }
            }
            eprintln!("Mach-O module-local executable binding passed: {opt_level:?}");
        }
    }

    /// The Darwin linked-image evidence replay (`record_darwin_linked_image`)
    /// resolves a relocation against a non-external definition inside its
    /// own object, and it places atoms by the image's symbol table. An image
    /// with one module's Internal `helper` beside the executable's global
    /// `helper` is replayed and recorded (one non-external `_helper` for one
    /// object definition); the image with both modules' local helpers names
    /// `_helper` twice as a local, so the replay refuses to place them
    /// (removing the output) instead of guessing which object owns each:
    /// the evidence lane fails closed on the case it cannot tell apart. (A
    /// residual of the replay, not of the binding: the executable itself
    /// runs correctly, as the row above shows.)
    /// (The C objects are built at `-O0`: clang's optimized objects carry
    /// linker optimization hints, which the replay refuses by name.)
    #[test]
    fn linked_image_evidence_replays_one_local_helper_and_refuses_two() {
        let directory = scratch("evidence");
        let global = directory.join("global_helper.o");
        cc_object(
            &write(
                &directory,
                "global_helper.c",
                "#include <stdint.h>\nuint64_t helper(uint64_t x) { return x + 300; }\n",
            ),
            &global,
            "-O0",
            &directory,
        );
        // Drivers without string literals (the replay refuses `__cstring`,
        // which ld64 deduplicates): each returns 0 exactly when every call,
        // pointer and taking reaches its own module's helper.
        let evidence_driver = |tags: &[(&str, u64)]| {
            let mut source = String::from(
                "#include <stdint.h>\ntypedef uint64_t (*unary)(uint64_t);\n\
                 uint64_t helper(uint64_t);\n",
            );
            let mut checks = vec!["helper(4) == 304".to_string()];
            for (tag, offset) in tags {
                source += &format!(
                    "extern unary {tag}_slot;\n\
                     uint64_t {tag}_direct(uint64_t), {tag}_via_local(uint64_t),\n\
                       {tag}_via_global(uint64_t);\nvoid *{tag}_addr(void);\n"
                );
                checks.extend([
                    format!("{tag}_direct(1) == {}", offset + 1),
                    format!("{tag}_via_local(2) == {}", offset + 2),
                    format!("{tag}_via_global(3) == {}", offset + 3),
                    format!("((unary){tag}_addr())(5) == {}", offset + 5),
                    format!("{tag}_addr() != (void *)helper"),
                ]);
            }
            source + &format!("int main(void) {{ return !({}); }}\n", checks.join(" && "))
        };
        let single_driver = directory.join("single.o");
        cc_object(
            &write(&directory, "single.c", evidence_driver(&[("a", 100)])),
            &single_driver,
            "-O0",
            &directory,
        );
        let two_driver = directory.join("driver.o");
        cc_object(
            &write(
                &directory,
                "driver.c",
                evidence_driver(&[("a", 100), ("b", 200)]),
            ),
            &two_driver,
            "-O0",
            &directory,
        );
        let mut objects = Vec::new();
        for (tag, linkage, offset) in [("a", Linkage::Internal, 100), ("b", Linkage::Private, 200)]
        {
            objects.push(write(
                &directory,
                &format!("{tag}.o"),
                darwin_compiler(OptLevel::O2, false)
                    .compile(&local_binding_module(tag, linkage, offset))
                    .unwrap_or_else(|error| panic!("{tag}: {error}"))
                    .object_code,
            ));
        }
        let link = |name: &str, inputs: Vec<PathBuf>| {
            let request = trust_cg_codegen::link_driver::LinkRequest::executable(
                TargetSpec::parse(DARWIN).expect("triple"),
                inputs,
                directory.join(name),
            );
            trust_cg_codegen::link_driver::run_link(&request, "cc")
                .unwrap_or_else(|error| panic!("{name}: {error}"));
            request
        };

        let single = link(
            "single",
            vec![single_driver, global.clone(), objects[0].clone()],
        );
        ok(&mut Command::new(&single.output), &directory);
        let record = trust_cg_codegen::link_driver::record_darwin_linked_image(&single, "cc", &[])
            .unwrap_or_else(|error| panic!("one local helper is replayed: {error}"));
        assert!(record.is_file(), "{record:?}");

        let both = link(
            "both",
            vec![two_driver, global, objects[0].clone(), objects[1].clone()],
        );
        ok(&mut Command::new(&both.output), &directory);
        let error = trust_cg_codegen::link_driver::record_darwin_linked_image(&both, "cc", &[])
            .expect_err("two local helpers of one name cannot be placed by the symbol table");
        let text = error.to_string();
        assert!(
            text.contains("_helper") && text.contains("does not locate it"),
            "{text}"
        );
        // Two placement findings (one per unplaced local helper atom); every
        // other finding is a consequence of those atoms staying unplaced.
        assert_eq!(text.matches("[TCG-IMAGE-PLACEMENT]").count(), 2, "{text}");
        assert!(
            text.lines()
                .filter(|line| line.starts_with("  ["))
                .all(|line| {
                    [
                        "[TCG-IMAGE-PLACEMENT]",
                        "[TCG-IMAGE-DEAD-STRIP]",
                        "[TCG-IMAGE-UNACCOUNTED-CONTENT]",
                    ]
                    .iter()
                    .any(|code| line.starts_with(&format!("  {code}")))
                }),
            "{text}"
        );
        assert!(!both.output.exists(), "a refused replay removes the output");
    }

    /// Modules `a` (Internal helper) and `b` (Private helper) compiled at
    /// O0-O3 and each linked by `cc -dynamiclib -Wl,-interposable` into its
    /// own dylib, both loaded by one program whose executable defines a
    /// global `helper` (`x + 300`) and is itself linked `-interposable`.
    /// Neither dylib exports a helper. An interposer loaded through
    /// `DYLD_INSERT_LIBRARIES`, whose `__DATA,__interpose` tuple replaces
    /// `helper` (`x + 5000`), takes over the executable's own `helper` call
    /// (`global 5004`: it is live in the same run) and reaches none of the
    /// modules' calls, pointers or takings. The clang twins with `static`
    /// functions behave the same. Near-twin control: with `a`'s helper
    /// External its dylib exports `_helper`, and the same interposer takes
    /// over `a`'s direct call while `b`'s Private helper stays its own.
    /// (`DYLD_FORCE_FLAT_NAMESPACE` interposes nothing on this dyld, so the
    /// interposer is a tuple, as dyld documents.)
    #[test]
    fn module_local_functions_resist_interposition_in_a_dylib() {
        let expected = local_binding_expected(true);
        let interposed = expected.replace(" global 304", " global 5004");
        assert_ne!(expected, interposed);
        for opt_level in OPT_LEVELS {
            let directory = scratch("dylib");
            let o_flag = format!("-O{}", opt_level as u8);
            let interposer = directory.join("libinterpose.dylib");
            ok(
                Command::new("cc")
                    .args(["-dynamiclib", "-Wl,-undefined,dynamic_lookup"])
                    .arg(write(
                        &directory,
                        "interpose.c",
                        "#include <stdint.h>\n\
                         uint64_t helper(uint64_t x);\n\
                         static uint64_t replacement(uint64_t x) { return x + 5000; }\n\
                         __attribute__((used)) static struct { const void *replacement; \
                         const void *replacee; } interposers[] \
                         __attribute__((section(\"__DATA,__interpose\"))) = \
                         { { (const void *)replacement, (const void *)helper } };\n",
                    ))
                    .arg("-o")
                    .arg(&interposer),
                &directory,
            );
            let driver = write(&directory, "driver.c", local_binding_driver(true));
            let global = write(
                &directory,
                "global_helper.c",
                "#include <stdint.h>\nuint64_t helper(uint64_t x) { return x + 300; }\n",
            );
            let near_twin_driver = write(&directory, "near_twin.c", local_binding_driver(false));
            let dylib = |name: &str, object: &Path| {
                let path = directory.join(format!("lib{name}.dylib"));
                ok(
                    Command::new("cc")
                        .args(["-dynamiclib", "-Wl,-interposable"])
                        .arg(object)
                        .arg(format!("-Wl,-install_name,@rpath/lib{name}.dylib"))
                        .arg("-o")
                        .arg(&path),
                    &directory,
                );
                path
            };
            let program = |label: &str, sources: &[&Path], libraries: &[PathBuf]| {
                let binary = directory.join(format!("program-{label}"));
                ok(
                    Command::new("cc")
                        .args(["-O0", "-Wl,-interposable"])
                        .args(sources)
                        .args(libraries)
                        .arg(format!("-Wl,-rpath,{}", directory.display()))
                        .arg("-o")
                        .arg(&binary),
                    &directory,
                );
                binary
            };
            let run_both = |binary: &Path| {
                let plain = ok(&mut Command::new(binary), &directory);
                let preloaded = ok(
                    Command::new(binary).env("DYLD_INSERT_LIBRARIES", &interposer),
                    &directory,
                );
                (plain, preloaded)
            };

            // trust-cg objects.
            let mut libraries = Vec::new();
            for (tag, linkage, offset) in
                [("a", Linkage::Internal, 100), ("b", Linkage::Private, 200)]
            {
                let object = write(
                    &directory,
                    &format!("{tag}.o"),
                    darwin_compiler(opt_level, false)
                        .compile(&local_binding_module(tag, linkage, offset))
                        .unwrap_or_else(|error| panic!("{opt_level:?} {tag}: {error}"))
                        .object_code,
                );
                let library = dylib(tag, &object);
                assert!(
                    nm_helpers(&library, &directory)
                        .iter()
                        .all(|(external, _)| !external),
                    "{opt_level:?} {tag}: the dylib exports no helper"
                );
                libraries.push(library);
            }
            let (plain, preloaded) = run_both(&program("cg", &[&driver, &global], &libraries));
            assert_eq!(plain, expected, "{opt_level:?} trust-cg");
            assert_eq!(preloaded, interposed, "{opt_level:?} trust-cg interposed");

            // The clang twins.
            let mut clang_libraries = Vec::new();
            for (tag, offset) in [("a", 100), ("b", 200)] {
                let object = directory.join(format!("clang_{tag}.o"));
                cc_object(
                    &write(
                        &directory,
                        &format!("clang_{tag}.c"),
                        local_binding_c_source(tag, offset),
                    ),
                    &object,
                    &o_flag,
                    &directory,
                );
                clang_libraries.push(dylib(&format!("clang_{tag}"), &object));
            }
            let (plain, preloaded) =
                run_both(&program("clang", &[&driver, &global], &clang_libraries));
            assert_eq!(plain, expected, "{opt_level:?} clang");
            assert_eq!(preloaded, interposed, "{opt_level:?} clang interposed");

            // Near-twin control: `a`'s helper External, no executable helper.
            let object = write(
                &directory,
                "a_external.o",
                darwin_compiler(opt_level, false)
                    .compile(&local_binding_module("a", Linkage::External, 100))
                    .unwrap_or_else(|error| panic!("{opt_level:?} external: {error}"))
                    .object_code,
            );
            let external = dylib("a_external", &object);
            assert!(
                nm_helpers(&external, &directory)
                    .iter()
                    .any(|(external, _)| *external),
                "{opt_level:?}: the near-twin dylib exports _helper"
            );
            let (plain, preloaded) = run_both(&program(
                "external",
                &[&near_twin_driver],
                &[external, libraries[1].clone()],
            ));
            assert_eq!(
                plain,
                local_binding_expected(false),
                "{opt_level:?} near-twin, not interposed"
            );
            let first_line = preloaded.lines().next().unwrap_or_default();
            assert!(
                first_line.starts_with("calls 5001 "),
                "{opt_level:?}: the interposer must take over the External helper's direct \
                 call (the control is load-bearing): {preloaded}"
            );
            assert!(
                first_line.ends_with(" 201 202 203"),
                "{opt_level:?}: module b's Private helper stays its own: {preloaded}"
            );
            eprintln!("Mach-O module-local dylib interposition passed: {opt_level:?}");
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
