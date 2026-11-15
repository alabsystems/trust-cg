// trust-cg-codegen/tests/aarch64_elf_symbol_binding.rs
//
// AArch64 ELF function symbol bindings and weak undefined references.
//
// Object level (every host): the three AArch64 ELF module emitters spell every
// function binding (STB_LOCAL / STB_GLOBAL / STB_WEAK x STV_DEFAULT /
// STV_HIDDEN / STV_PROTECTED) and every weak undefined reference, and each
// relocation still names the symbol it named before bindings existed. Symbols
// and relocations are read back by an independent ELF64 parser below, never
// by the emitter's own writer model. `Compiler::compile` maps trust-ir
// function linkage and v45 function visibility onto those bindings and
// `Linkage::ExternalWeak` onto weak undefined, GOT-indirect references on
// AArch64 ELF only; visibility no ELF emitter spells (local, import) and every
// non-default function visibility off AArch64 ELF (Mach-O, x86-64, RISC-V,
// JIT) is refused by name. Direct calls to and every address form of an
// Internal/Private function compile on AArch64 ELF (O0-O3, static/pie/pic,
// sequential and parallel, function and explicit sections), with every
// relocation naming the one STB_LOCAL definition; the other object paths keep
// refusing them.
//
// Native (Linux AArch64 glibc only, O0-O3): a strong definition overrides a CG
// weak definition, two CG weak definitions coalesce, Internal functions with
// one name link from separate objects, a hidden function stays out of a
// CG-built shared object's `.dynsym` while a protected one binds locally
// against an interposing executable (GNU ld, gold and LLD), and ExternalWeak
// references read null when nothing defines them and resolve when a provider
// is linked. The same hidden/protected controls run from a trust-ir v45 text
// module through `Compiler::compile`, with an `LD_PRELOAD` interposer, under
// GNU ld, gold and LLD. A `pic` library with
// default, protected and hidden functions AND data, linked by GNU ld, gold and
// LLD, shows every reference from inside it to a protected or hidden symbol
// binding locally (no GOT relocation, dynamic relocation, GOT slot or PLT
// branch), only the default references interposing, and the linkers refusing
// to copy protected data. Two modules each with their own Internal/Private
// `helper`, linked with a C global `helper`, each reach their own helper
// through direct calls, local and global function pointers and address
// takings (GNU ld through `run_link`, gold, LLD), and an `LD_PRELOAD`
// interposer reaches none of them inside a `run_link` shared library; gcc
// twins with `static` functions agree.
//
// L02-P6 closure-audit residuals: hidden and protected DATA declarations
// (strong, weak, `AvailableExternally`, thread-local, and one naming a C
// IFUNC function) compile on AArch64 ELF with their visibility on the
// undefined symbol and a GOT address, refused by every other object path,
// and bind inside a non-PIE, static, PIE, static-PIE and shared image with
// GNU ld, gold and LLD; `merge_modules` gives a data definition the most
// constraining visibility of the imports it satisfies, so an `LD_PRELOAD`
// interposer cannot take a merged hidden word; an external personality's
// `DW.ref` slot is `WEAK HIDDEN` in its own COMDAT group, so a `pic` EH
// module links into a shared object with every linker, exports nothing and
// shares one slot with other CG and GCC objects while a C++ throw crosses
// its frames; and a strong hidden thread-local's TLS descriptors name an
// object-local anchor.
//
// L02-P6 closure audit 2: weak and COMDAT (`linkonce`, `linkonce_odr`,
// `weak_odr`) data DEFINITIONS carry their hidden or protected visibility
// onto the `STB_WEAK` object symbol under every relocation model; in a `pic`
// library linked by GNU ld, gold and LLD the hidden ones stay out of
// `.dynsym`, only the default ones are interposed by `LD_PRELOAD`, a non-PIE
// executable cannot link a hidden one or copy a protected one, and the COMDAT
// ones coalesce with g++ `inline` variables in both input orders. The
// hidden thread-local anchor is also checked through the public Pipeline
// API, whose layout-less route reaches the other relocating ELF emitter,
// with every linker's `.dynsym`. This is execution evidence, not a linker or
// dynamic-loader proof.
//
// L02-P6 closure audit 3: STRONG hidden and protected data definitions in
// every implicit section (mutable `.data` and zero `.bss` words, immutable
// `.rodata` words and `.data.rel.ro` pointers) carry their visibility through
// `Compiler::compile` (every relocation model, sequential and parallel) and
// both relocating Pipeline emitters; in a `pic` library linked by GNU ld,
// gold and LLD no hidden one reaches `.dynsym` and none is named by a
// dynamic relocation or held in a GOT slot, `LD_PRELOAD` takes over only
// the default ones, and a non-PIE executable cannot link a hidden one or
// copy a protected one. The v45 interposition row also covers COMDAT
// (`linkonce_odr`) hidden and protected functions.
//
// L02-P6 closure audit 4: instead of one more row per surviving class, the
// visibility cross-product table (`aarch64_elf_symbol_binding/
// visibility_table.rs`) generates every {definition, declaration} x linkage x
// visibility x kind x placement case, classifies each as admitted, refused
// by a named diagnostic or inexpressible, and checks every admitted case's
// symbol, section, COMDAT group and address form through `Compiler::compile`
// (sequential and parallel) and the three Pipeline module emitters under
// `static`, `pie` and `pic`, with and without function sections, plus the
// emitters' relocation-model backstop. Its native row links every route's
// `pic` object into one shared library with GNU ld, gold and LLD and checks
// `.dynsym` and `LD_PRELOAD` interposition for every admitted case.
//
// L02-P6 closure audit 6, under WS7.3 ingestion admission (LD-54): two
// bodyless declarations of one symbol in one module, identical or not, are
// refused by `Compiler::compile` from the text, binary (`TRUST_IR` and
// `tMBC`) and JSON entries under every relocation model at O0-O3, by
// trust-ir's `DuplicateFunctionSymbol`. The function catalog that still
// guards the adapter's unadmitted diagnostic entries refuses every pair that
// differs in visibility or in linkage (`external` beside `external_weak`,
// either order) and two `external_weak` ones, and lets identical `external`
// pairs share the symbol; `merge_modules` folds an input's repeated
// `external` declarations into the most constraining visibility, and the
// folded module compiles from every entry. The `pic` declaration library also runs
// a default `AvailableExternally` function, whose call an `LD_PRELOAD`
// interposer takes.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#[path = "common/pinned_target.rs"]
mod pinned_target;

#[path = "common/admission_expect.rs"]
mod admission_expect;

use std::collections::BTreeSet;

use trust_cg_codegen::pipeline::{
    FunctionSymbolBinding, FunctionSymbolLinkage, GlobalSymbolRef, ModuleSymbolLinkage,
    ObjectGlobal, OptLevel, Pipeline, PipelineConfig, PipelineError, TextFunctionExtent,
};
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{
    CompilationResult, CompileError, Compiler, CompilerConfig, CompilerTraceLevel,
};
use trust_cg_lower::function::{BasicBlock, Function as LirFunction, Signature};
use trust_cg_lower::instructions::{Block as LirBlock, Instruction, Opcode, Value};
use trust_cg_lower::types::Type as LirType;
use trust_ir::value::GlobalId;
use trust_ir::{
    Block, BlockId, CastOp, Constant, Endianness, FuncId, FuncTy, Function, Global, Inst,
    InstrNode, Linkage, Module, StructPassingPolicy, TargetInfo, Ty, ValueId, Visibility,
};

const LINUX: &str = "aarch64-unknown-linux-gnu";
const DARWIN: &str = "aarch64-apple-darwin";
/// The Mach-O triples whose module emitters spell a hidden `External`
/// function definition (`N_SECT | N_EXT | N_PEXT`).
const MACHO_TRIPLES: [&str; 2] = [DARWIN, "x86_64-apple-darwin"];
const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

// =============================================================================
// Independent ELF64 relocatable-object reader
// =============================================================================

const STB_LOCAL: u8 = 0;
const STB_GLOBAL: u8 = 1;
const STB_WEAK: u8 = 2;
const STT_NOTYPE: u8 = 0;
const STT_OBJECT: u8 = 1;
const STT_FUNC: u8 = 2;
const STT_SECTION: u8 = 3;
const STV_DEFAULT: u8 = 0;
const STV_HIDDEN: u8 = 2;
const STV_PROTECTED: u8 = 3;
const R_AARCH64_ABS64: u32 = 257;
const R_AARCH64_PREL32: u32 = 261;
const R_AARCH64_ADR_PREL_PG_HI21: u32 = 275;
const R_AARCH64_ADD_ABS_LO12_NC: u32 = 277;
/// The fused `LDR/STR #:lo12:` direct-access kinds (LDST8, 16, 32, 64, 128).
const R_AARCH64_LDST_ABS_LO12_NC: [u32; 5] = [278, 284, 285, 286, 299];
const R_AARCH64_JUMP26: u32 = 282;
const R_AARCH64_CALL26: u32 = 283;
const R_AARCH64_ADR_GOT_PAGE: u32 = 311;
const R_AARCH64_LD64_GOT_LO12_NC: u32 = 312;
const R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21: u32 = 541;
const R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC: u32 = 542;
const R_AARCH64_TLSLE_ADD_TPREL_HI12: u32 = 549;
const R_AARCH64_TLSLE_ADD_TPREL_LO12_NC: u32 = 551;
/// `R_AARCH64_TLSDESC_ADR_PAGE21`, `_LD64_LO12`, `_ADD_LO12` and `_CALL`.
const R_AARCH64_TLSDESC: [u32; 4] = [562, 563, 564, 569];
const STT_TLS: u8 = 6;

fn rd_u16(b: &[u8], off: usize) -> u16 {
    u16::from_le_bytes([b[off], b[off + 1]])
}
fn rd_u32(b: &[u8], off: usize) -> u32 {
    u32::from_le_bytes(b[off..off + 4].try_into().unwrap())
}
fn rd_u64(b: &[u8], off: usize) -> u64 {
    u64::from_le_bytes(b[off..off + 8].try_into().unwrap())
}
fn cstr(b: &[u8], start: usize) -> String {
    let end = start + b[start..].iter().position(|&byte| byte == 0).unwrap();
    String::from_utf8(b[start..end].to_vec()).unwrap()
}

#[derive(Debug, Clone)]
struct Sym {
    name: String,
    bind: u8,
    kind: u8,
    visibility: u8,
    shndx: u16,
    value: u64,
    size: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Reloc {
    section: String,
    offset: u64,
    kind: u32,
    symbol: String,
    addend: i64,
}

struct Elf {
    /// (name, sh_type, bytes) per section header index.
    sections: Vec<(String, u32, Vec<u8>)>,
    /// Symbol table in final index order (index 0 is the null symbol).
    symbols: Vec<Sym>,
    /// `.symtab` `sh_info`: one past the last local.
    first_global: u32,
    relocs: Vec<Reloc>,
}

fn parse_elf(bytes: &[u8]) -> Elf {
    assert_eq!(&bytes[..4], b"\x7fELF", "ELF magic");
    assert_eq!(bytes[4], 2, "ELFCLASS64");
    assert_eq!(bytes[5], 1, "little-endian");
    assert_eq!(rd_u16(bytes, 16), 1, "ET_REL");
    assert_eq!(rd_u16(bytes, 18), 183, "EM_AARCH64");
    let shoff = rd_u64(bytes, 0x28) as usize;
    let shentsize = rd_u16(bytes, 0x3a) as usize;
    let shnum = rd_u16(bytes, 0x3c) as usize;
    let shstrndx = rd_u16(bytes, 0x3e) as usize;
    let header = |index: usize| shoff + index * shentsize;
    let raw: Vec<(u32, u32, usize, usize, u32, u32)> = (0..shnum)
        .map(|index| {
            let h = header(index);
            (
                rd_u32(bytes, h),
                rd_u32(bytes, h + 4),
                rd_u64(bytes, h + 0x18) as usize,
                rd_u64(bytes, h + 0x20) as usize,
                rd_u32(bytes, h + 0x28),
                rd_u32(bytes, h + 0x2c),
            )
        })
        .collect();
    let shstr = raw[shstrndx].2;
    let sections: Vec<(String, u32, Vec<u8>)> = raw
        .iter()
        .map(|&(name, sh_type, offset, size, _, _)| {
            let data = if sh_type == 8 {
                Vec::new() // SHT_NOBITS
            } else {
                bytes[offset..offset + size].to_vec()
            };
            (cstr(bytes, shstr + name as usize), sh_type, data)
        })
        .collect();
    let symtab = raw
        .iter()
        .position(|section| section.1 == 2)
        .expect("SHT_SYMTAB");
    let (_, _, sym_off, sym_size, strtab, first_global) = raw[symtab];
    let str_off = raw[strtab as usize].2;
    let symbols: Vec<Sym> = (sym_off..sym_off + sym_size)
        .step_by(24)
        .map(|entry| Sym {
            name: cstr(bytes, str_off + rd_u32(bytes, entry) as usize),
            bind: bytes[entry + 4] >> 4,
            kind: bytes[entry + 4] & 0xf,
            visibility: bytes[entry + 5] & 0x3,
            shndx: rd_u16(bytes, entry + 6),
            value: rd_u64(bytes, entry + 8),
            size: rd_u64(bytes, entry + 16),
        })
        .collect();
    let mut relocs = Vec::new();
    for &(_, sh_type, offset, size, link, info) in &raw {
        if sh_type != 4 {
            continue; // SHT_RELA
        }
        assert_eq!(link as usize, symtab, "rela links the symtab");
        for entry in (offset..offset + size).step_by(24) {
            let r_info = rd_u64(bytes, entry + 8);
            let symbol = &symbols[(r_info >> 32) as usize];
            relocs.push(Reloc {
                section: sections[info as usize].0.clone(),
                offset: rd_u64(bytes, entry),
                kind: r_info as u32,
                symbol: if symbol.kind == STT_SECTION {
                    format!("<section {}>", sections[symbol.shndx as usize].0)
                } else {
                    symbol.name.clone()
                },
                addend: rd_u64(bytes, entry + 16) as i64,
            });
        }
    }
    let elf = Elf {
        sections,
        symbols,
        first_global,
        relocs,
    };
    // gABI: every local precedes every global/weak, and sh_info splits them.
    for (index, symbol) in elf.symbols.iter().enumerate() {
        assert_eq!(
            symbol.bind == STB_LOCAL,
            (index as u32) < elf.first_global,
            "symbol {index} {symbol:?} is on the wrong side of sh_info {}",
            elf.first_global
        );
    }
    elf
}

impl Elf {
    fn symbol(&self, name: &str) -> &Sym {
        let matches: Vec<&Sym> = self.symbols.iter().filter(|s| s.name == name).collect();
        assert_eq!(matches.len(), 1, "exactly one `{name}` symbol");
        matches[0]
    }

    fn section(&self, name: &str) -> &[u8] {
        &self
            .sections
            .iter()
            .find(|section| section.0 == name)
            .unwrap_or_else(|| panic!("section {name}"))
            .2
    }

    fn relocs_in(&self, section: &str) -> Vec<&Reloc> {
        self.relocs
            .iter()
            .filter(|r| r.section == section)
            .collect()
    }
}

fn assert_symbol(elf: &Elf, name: &str, bind: u8, kind: u8, visibility: u8, defined: bool) {
    let symbol = elf.symbol(name);
    assert_eq!(symbol.bind, bind, "{name} binding: {symbol:?}");
    assert_eq!(symbol.kind, kind, "{name} type: {symbol:?}");
    assert_eq!(
        symbol.visibility, visibility,
        "{name} visibility: {symbol:?}"
    );
    assert_eq!(symbol.shndx != 0, defined, "{name} definedness: {symbol:?}");
}

/// Every `SHT_GROUP` section of `bytes` as `(signature symbol, member section
/// names)`, each checked to carry the `GRP_COMDAT` flag word.
fn comdat_groups(bytes: &[u8]) -> Vec<(String, Vec<String>)> {
    const SHT_GROUP: u32 = 17;
    const GRP_COMDAT: u32 = 1;
    let elf = parse_elf(bytes);
    let shoff = rd_u64(bytes, 0x28) as usize;
    let shentsize = rd_u16(bytes, 0x3a) as usize;
    let mut groups = Vec::new();
    for (index, (_, sh_type, data)) in elf.sections.iter().enumerate() {
        if *sh_type != SHT_GROUP {
            continue;
        }
        let signature = rd_u32(bytes, shoff + index * shentsize + 0x2c) as usize;
        assert_eq!(rd_u32(data, 0), GRP_COMDAT, "group {index} flag word");
        let members = (4..data.len())
            .step_by(4)
            .map(|at| elf.sections[rd_u32(data, at) as usize].0.clone())
            .collect();
        groups.push((elf.symbols[signature].name.clone(), members));
    }
    groups
}

// =============================================================================
// Hand-built LIR for the Pipeline API (bindings passed directly, including
// the local x non-default rows trust-ir cannot state)
// =============================================================================

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

fn returns_constant(name: &str, value: i64) -> LirFunction {
    lir_function(
        name,
        vec![
            Instruction {
                opcode: Opcode::Iconst {
                    ty: LirType::I64,
                    imm: value,
                },
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

fn returns_call(name: &str, callee: &str) -> LirFunction {
    lir_function(
        name,
        vec![
            Instruction {
                opcode: Opcode::Call {
                    name: callee.to_owned(),
                    binding: Default::default(),
                },
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

fn returns_got_address(name: &str, symbol: &str) -> LirFunction {
    lir_function(
        name,
        vec![
            Instruction {
                opcode: Opcode::ExternRef {
                    name: symbol.to_owned(),
                },
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

fn returns_direct_address(name: &str, symbol: &str) -> LirFunction {
    lir_function(
        name,
        vec![
            Instruction {
                opcode: Opcode::GlobalRef {
                    name: symbol.to_owned(),
                },
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

fn pipeline(triple: &str, opt_level: OptLevel) -> Pipeline {
    Pipeline::new(PipelineConfig {
        target_triple: triple.to_string(),
        opt_level,
        ..PipelineConfig::default()
    })
}

type Prepared = (
    Vec<trust_cg_ir::MachFunction>,
    Vec<Option<trust_cg_codegen::frame::FrameLayout>>,
);

fn prepare(pipeline: &Pipeline, functions: &[LirFunction]) -> Prepared {
    functions
        .iter()
        .map(|function| {
            let (prepared, metrics) = pipeline
                .prepare_function_with_metrics(function, None)
                .unwrap_or_else(|error| panic!("prepare {}: {error}", function.name));
            (prepared, metrics.frame_layout)
        })
        .unzip()
}

fn object_global(name: &str, data: Vec<u8>) -> ObjectGlobal {
    ObjectGlobal {
        name: name.to_string(),
        data,
        mutable: true,
        is_external: true,
        symbol_refs: vec![],
        is_thread_local: false,
        is_import: false,
        is_weak: false,
        align: 8,
        visibility: Visibility::Default,
        retained: false,
        section: None,
        comdat: false,
    }
}

fn import(name: &str, weak: bool) -> ObjectGlobal {
    ObjectGlobal {
        data: vec![],
        is_import: true,
        is_weak: weak,
        ..object_global(name, vec![])
    }
}

/// Every (linkage, visibility) request, with the symbol attributes ELF must
/// carry for it. A local binding's visibility is vacuous and normalizes to
/// default.
fn binding_matrix() -> Vec<(String, FunctionSymbolBinding, u8, u8)> {
    let mut rows = Vec::new();
    for (linkage, bind) in [
        (FunctionSymbolLinkage::Global, STB_GLOBAL),
        (FunctionSymbolLinkage::Local, STB_LOCAL),
        (FunctionSymbolLinkage::Weak, STB_WEAK),
    ] {
        for (visibility, stv) in [
            (Visibility::Default, STV_DEFAULT),
            (Visibility::Hidden, STV_HIDDEN),
            (Visibility::Protected, STV_PROTECTED),
        ] {
            let name = format!("bind_{linkage:?}_{visibility}").to_lowercase();
            let stv = if linkage == FunctionSymbolLinkage::Local {
                STV_DEFAULT
            } else {
                stv
            };
            rows.push((
                name,
                FunctionSymbolBinding::new(linkage, visibility),
                bind,
                stv,
            ));
        }
    }
    rows
}

/// The fixup-bearing module: nine bound leaves, a GLOBAL caller per leaf,
/// GOT references to weak and strong undefined function/data symbols, a
/// direct call to a weak undefined function, and data pointer slots naming
/// every leaf plus the weak undefined function.
struct BindingModule {
    functions: Vec<LirFunction>,
    globals: Vec<ObjectGlobal>,
    linkage: ModuleSymbolLinkage,
}

fn binding_module() -> BindingModule {
    let matrix = binding_matrix();
    let mut functions = Vec::new();
    let mut bindings = Vec::new();
    for (index, (name, binding, _, _)) in matrix.iter().enumerate() {
        functions.push(returns_constant(name, 100 + index as i64));
        bindings.push(*binding);
    }
    for (name, _, _, _) in &matrix {
        functions.push(returns_call(&format!("call_{name}"), name));
        bindings.push(FunctionSymbolBinding::GLOBAL);
    }
    for (function, symbol) in [
        ("weak_fn_address", "maybe_fn"),
        ("weak_data_address", "maybe_data"),
        ("strong_fn_address", "strong_fn"),
        ("strong_data_address", "strong_data"),
    ] {
        functions.push(returns_got_address(function, symbol));
        bindings.push(FunctionSymbolBinding::GLOBAL);
    }
    functions.push(returns_call("call_maybe_fn", "maybe_fn"));
    bindings.push(FunctionSymbolBinding::HIDDEN);

    let mut table = object_global("local_table", vec![0; 8 * (matrix.len() + 1)]);
    table.is_external = false;
    table.symbol_refs = matrix
        .iter()
        .map(|(name, _, _, _)| name.as_str())
        .chain(["maybe_fn"])
        .enumerate()
        .map(|(slot, symbol)| GlobalSymbolRef {
            offset: 8 * slot as u64,
            symbol: symbol.to_string(),
            addend: slot as i64,
        })
        .collect();
    let mut local_word = object_global("local_word", 7u64.to_le_bytes().to_vec());
    local_word.is_external = false;
    local_word.mutable = false;
    let mut weak_word = object_global("weak_word", 9u64.to_le_bytes().to_vec());
    weak_word.is_weak = true;
    let globals = vec![
        table,
        local_word,
        weak_word,
        import("maybe_data", true),
        import("strong_data", false),
    ];
    BindingModule {
        functions,
        globals,
        linkage: ModuleSymbolLinkage::new(bindings, BTreeSet::from(["maybe_fn".to_string()])),
    }
}

fn branch_kinds() -> [u32; 2] {
    [R_AARCH64_CALL26, R_AARCH64_JUMP26]
}

/// Assert the bound object's symbol attributes and that every relocation
/// names exactly the intended symbol, from exactly the intended function.
fn assert_binding_object(elf: &Elf, extents: &[TextFunctionExtent], with_unwind: bool) {
    for (name, _, bind, visibility) in binding_matrix() {
        assert_symbol(elf, &name, bind, STT_FUNC, visibility, true);
        assert_symbol(
            elf,
            &format!("call_{name}"),
            STB_GLOBAL,
            STT_FUNC,
            STV_DEFAULT,
            true,
        );
    }
    assert_symbol(elf, "call_maybe_fn", STB_GLOBAL, STT_FUNC, STV_HIDDEN, true);
    assert_symbol(elf, "maybe_fn", STB_WEAK, STT_NOTYPE, STV_DEFAULT, false);
    assert_symbol(elf, "maybe_data", STB_WEAK, STT_NOTYPE, STV_DEFAULT, false);
    assert_symbol(elf, "strong_fn", STB_GLOBAL, STT_NOTYPE, STV_DEFAULT, false);
    assert_symbol(
        elf,
        "strong_data",
        STB_GLOBAL,
        STT_NOTYPE,
        STV_DEFAULT,
        false,
    );
    assert_symbol(elf, "local_table", STB_LOCAL, STT_OBJECT, STV_DEFAULT, true);
    assert_symbol(elf, "local_word", STB_LOCAL, STT_OBJECT, STV_DEFAULT, true);
    assert_symbol(elf, "weak_word", STB_WEAK, STT_OBJECT, STV_DEFAULT, true);

    // .text: each caller's one branch names its own callee, each address
    // getter's GOT pair names its own symbol, and nothing else is relocated
    // (never a direct page reference). The source function of a relocation is
    // the emitter-reported extent that contains its offset.
    const BRANCH: u32 = u32::MAX;
    let mut expected: BTreeSet<(String, String, u32)> = BTreeSet::new();
    for (name, _, _, _) in binding_matrix() {
        expected.insert((format!("call_{name}"), name, BRANCH));
    }
    expected.insert(("call_maybe_fn".into(), "maybe_fn".into(), BRANCH));
    for (getter, symbol) in [
        ("weak_fn_address", "maybe_fn"),
        ("weak_data_address", "maybe_data"),
        ("strong_fn_address", "strong_fn"),
        ("strong_data_address", "strong_data"),
    ] {
        for kind in [R_AARCH64_ADR_GOT_PAGE, R_AARCH64_LD64_GOT_LO12_NC] {
            expected.insert((getter.into(), symbol.into(), kind));
        }
    }
    let text = elf.relocs_in(".text");
    let actual: BTreeSet<(String, String, u32)> = text
        .iter()
        .map(|reloc| {
            let function = extents
                .iter()
                .find(|extent| (extent.offset..extent.offset + extent.len).contains(&reloc.offset))
                .unwrap_or_else(|| panic!("{reloc:?} lies in no function"));
            let kind = if branch_kinds().contains(&reloc.kind) {
                BRANCH
            } else {
                reloc.kind
            };
            (function.name.clone(), reloc.symbol.clone(), kind)
        })
        .collect();
    assert_eq!(
        text.len(),
        expected.len(),
        "one relocation per expected row"
    );
    assert_eq!(actual, expected, ".text relocation sources and targets");

    // .data: every pointer slot names its own target with its own addend.
    let data: Vec<(String, u32, i64)> = elf
        .relocs_in(".data")
        .into_iter()
        .map(|reloc| (reloc.symbol.clone(), reloc.kind, reloc.addend))
        .collect();
    let expected_data: Vec<(String, u32, i64)> = binding_matrix()
        .into_iter()
        .map(|row| row.0)
        .chain(["maybe_fn".to_string()])
        .enumerate()
        .map(|(slot, symbol)| (symbol, R_AARCH64_ABS64, slot as i64))
        .collect();
    assert_eq!(data, expected_data, ".data pointer slots");

    let eh = elf.relocs_in(".eh_frame");
    if with_unwind {
        assert_eq!(
            eh.len(),
            binding_module().functions.len(),
            "one FDE per function"
        );
        for reloc in eh {
            assert_eq!(reloc.kind, R_AARCH64_PREL32, "{reloc:?}");
            assert_eq!(reloc.symbol, "<section .text>", "{reloc:?}");
        }
    } else {
        assert!(eh.is_empty());
    }
}

/// Everything but symbol attributes: section bytes and relocations (by
/// target NAME) are identical with and without bindings.
fn assert_same_code_and_relocations(bound: &Elf, legacy: &Elf) {
    for section in [".text", ".data", ".rodata"] {
        assert_eq!(bound.section(section), legacy.section(section), "{section}");
    }
    let mut a = bound.relocs.clone();
    let mut b = legacy.relocs.clone();
    a.sort();
    b.sort();
    assert_eq!(a, b, "relocation targets must not move with bindings");
}

#[test]
fn every_function_binding_and_weak_reference_is_spelled_by_each_elf_emitter() {
    for opt_level in OPT_LEVELS {
        let module = binding_module();
        let pipeline = pipeline(LINUX, opt_level);
        let (functions, layouts) = prepare(&pipeline, &module.functions);
        for with_unwind in [false, true] {
            let layouts: &[_] = if with_unwind { &layouts } else { &[] };
            let bound = pipeline
                .compile_module_emission_with_symbol_linkage(
                    &functions,
                    &module.globals,
                    layouts,
                    &module.linkage,
                )
                .unwrap_or_else(|error| panic!("{opt_level:?} unwind={with_unwind}: {error}"))
                .into_emission();
            let elf = parse_elf(&bound.object);
            assert_binding_object(&elf, &bound.text_extents, with_unwind);

            let parallel = pipeline
                .compile_module_parallel_emission_with_symbol_linkage(
                    &functions,
                    &module.globals,
                    layouts,
                    &module.linkage,
                )
                .expect("parallel emission")
                .into_emission();
            assert_eq!(parallel.object, bound.object, "parallel == sequential");

            // The legacy emission (every definition global, every reference
            // strong) of the same functions differs ONLY in symbol attributes.
            let legacy_globals: Vec<ObjectGlobal> = module
                .globals
                .iter()
                .cloned()
                .map(|mut global| {
                    global.is_weak &= !global.is_import;
                    global
                })
                .collect();
            let legacy = pipeline
                .compile_module_with_globals_and_layouts(&functions, &legacy_globals, layouts)
                .expect("legacy emission");
            let legacy_elf = parse_elf(&legacy);
            assert_same_code_and_relocations(&elf, &legacy_elf);
            assert_eq!(legacy_elf.symbol("maybe_fn").bind, STB_GLOBAL);
            assert_eq!(legacy_elf.symbol("bind_local_default").bind, STB_GLOBAL);
            assert_eq!(
                bound.text_extents,
                pipeline
                    .compile_module_emission(&functions, &legacy_globals, layouts, &[])
                    .unwrap()
                    .text_extents
            );
        }
    }
}

#[test]
fn relocation_free_objects_carry_function_bindings_too() {
    // No fixup and no pointer slot selects the plain function-symbol emitter.
    let matrix = binding_matrix();
    let leaves: Vec<LirFunction> = matrix
        .iter()
        .enumerate()
        .map(|(index, (name, ..))| returns_constant(name, index as i64))
        .collect();
    let bindings: Vec<FunctionSymbolBinding> = matrix.iter().map(|row| row.1).collect();
    for opt_level in OPT_LEVELS {
        let pipeline = pipeline(LINUX, opt_level);
        let (functions, _) = prepare(&pipeline, &leaves);
        let object = pipeline
            .compile_module_emission(&functions, &[], &[], &bindings)
            .expect("plain emission")
            .object;
        let elf = parse_elf(&object);
        assert!(elf.relocs.is_empty());
        for (name, _, bind, visibility) in &matrix {
            assert_symbol(&elf, name, *bind, STT_FUNC, *visibility, true);
        }
        let legacy = parse_elf(&pipeline.compile_module(&functions).unwrap());
        assert_eq!(elf.section(".text"), legacy.section(".text"));
    }
}

#[test]
fn inconsistent_symbol_linkage_is_refused_before_emission() {
    let module = binding_module();
    let pipeline = pipeline(LINUX, OptLevel::O0);
    let (functions, _) = prepare(&pipeline, &module.functions);
    let refuse = |globals: &[ObjectGlobal], linkage: &ModuleSymbolLinkage| {
        pipeline
            .compile_module_emission_with_symbol_linkage(&functions, globals, &[], linkage)
            .expect_err("inconsistent linkage")
            .to_string()
    };

    let short = ModuleSymbolLinkage::new(vec![FunctionSymbolBinding::LOCAL], BTreeSet::new());
    assert!(refuse(&module.globals, &short).contains("1:1"));

    let defined = ModuleSymbolLinkage::new(
        module.linkage.function_bindings().to_vec(),
        BTreeSet::from(["bind_global_default".to_string()]),
    );
    let error = refuse(&module.globals, &defined);
    assert!(error.contains("also defined in this object"), "{error}");

    let mut clash = module.globals.clone();
    clash.push(import("maybe_fn", false));
    let error = refuse(&clash, &module.linkage);
    assert!(error.contains("also names a data global"), "{error}");

    let mut weak_tls = module.globals.clone();
    let mut tls = import("maybe_tls", true);
    tls.is_thread_local = true;
    weak_tls.push(tls);
    let error = refuse(&weak_tls, &module.linkage);
    assert!(error.contains("weak thread-local import"), "{error}");
}

/// `(n_type, n_desc)` of every nlist_64 entry of a Mach-O relocatable object,
/// keyed by name, read from `LC_SYMTAB` by this test rather than the
/// emitter's writer model.
fn macho_nlist(object: &[u8]) -> std::collections::BTreeMap<String, (u8, u16)> {
    let u32_at = |at: usize| u32::from_le_bytes(object[at..at + 4].try_into().unwrap());
    assert_eq!(u32_at(0), 0xFEED_FACF, "MH_MAGIC_64");
    let mut symbols = std::collections::BTreeMap::new();
    let mut cursor = 32;
    for _ in 0..u32_at(16) {
        if u32_at(cursor) == 0x2 {
            let (symoff, nsyms, stroff) = (
                u32_at(cursor + 8) as usize,
                u32_at(cursor + 12) as usize,
                u32_at(cursor + 16) as usize,
            );
            for index in 0..nsyms {
                let entry = symoff + index * 16;
                let name_at = stroff + u32_at(entry) as usize;
                let len = object[name_at..].iter().position(|&b| b == 0).unwrap();
                let name = String::from_utf8(object[name_at..name_at + len].to_vec()).unwrap();
                let desc = u16::from_le_bytes(object[entry + 6..entry + 8].try_into().unwrap());
                assert!(
                    symbols.insert(name, (object[entry + 4], desc)).is_none(),
                    "duplicate nlist name"
                );
            }
        }
        cursor += u32_at(cursor + 4) as usize;
    }
    symbols
}

#[test]
fn macho_spells_weak_definitions_and_keeps_refusing_weak_references() {
    const N_EXT: u8 = 0x01;
    const N_PEXT: u8 = 0x10;
    const N_WEAK_DEF: u16 = 0x0080;
    let module = binding_module();
    let pipeline = pipeline("aarch64-apple-darwin", OptLevel::O0);
    let (functions, _) = prepare(&pipeline, &module.functions);
    let strong_globals: Vec<ObjectGlobal> = module
        .globals
        .iter()
        .filter(|global| !global.is_import)
        .cloned()
        .collect();
    let bindings = module.linkage.function_bindings().to_vec();
    let refused = |globals: &[ObjectGlobal], linkage: ModuleSymbolLinkage| match pipeline
        .compile_module_emission_with_symbol_linkage(&functions, globals, &[], &linkage)
    {
        Err(PipelineError::TargetObjectUnsupported { format, reason, .. }) => {
            assert_eq!(format, "Mach-O");
            reason
        }
        other => panic!("expected a Mach-O refusal, got {other:?}"),
    };

    // Every definition binding emits: weak as `N_EXT | N_WEAK_DEF` (plus
    // `N_PEXT` when hidden), hidden as `N_PEXT`, protected as default and
    // local without `N_EXT`.
    let object = pipeline
        .compile_module_emission_with_symbol_linkage(
            &functions,
            &strong_globals,
            &[],
            &ModuleSymbolLinkage::new(bindings.clone(), BTreeSet::new()),
        )
        .expect("Mach-O honours every definition binding")
        .into_emission()
        .object;
    let nlist = macho_nlist(&object);
    for (name, binding, _, _) in binding_matrix() {
        let (n_type, desc) = nlist[&format!("_{name}")];
        let (external, weak) = match binding.linkage() {
            FunctionSymbolLinkage::Global => (true, false),
            FunctionSymbolLinkage::Local => (false, false),
            FunctionSymbolLinkage::Weak => (true, true),
        };
        let hidden = external && binding.visibility() == Visibility::Hidden;
        assert_eq!(n_type & N_EXT != 0, external, "{name}: N_EXT");
        assert_eq!(n_type & N_PEXT != 0, hidden, "{name}: N_PEXT");
        assert_eq!(desc & N_WEAK_DEF != 0, weak, "{name}: N_WEAK_DEF");
    }

    // A COMDAT function must be a weak definition on Mach-O too.
    let weak_leaf = "bind_weak_default".to_string();
    pipeline
        .compile_module_emission_with_symbol_linkage(
            &functions,
            &strong_globals,
            &[],
            &ModuleSymbolLinkage::new(bindings.clone(), BTreeSet::new())
                .with_comdat_functions(BTreeSet::from([weak_leaf])),
        )
        .expect("a weak-bound COMDAT function is an N_WEAK_DEF definition");
    let reason = refused(
        &strong_globals,
        ModuleSymbolLinkage::new(bindings.clone(), BTreeSet::new())
            .with_comdat_functions(BTreeSet::from(["bind_global_default".to_string()])),
    );
    assert!(
        reason.contains("COMDAT") && reason.contains("N_WEAK_DEF"),
        "{reason}"
    );

    // Weak undefined references stay refused by name.
    let reason = refused(
        &strong_globals,
        ModuleSymbolLinkage::new(bindings.clone(), BTreeSet::from(["maybe_fn".to_string()])),
    );
    assert!(
        reason.contains("N_WEAK_REF") && reason.contains("maybe_fn"),
        "{reason}"
    );
    let reason = refused(
        &module.globals,
        ModuleSymbolLinkage::new(bindings, BTreeSet::new()),
    );
    assert!(
        reason.contains("N_WEAK_REF") && reason.contains("maybe_data"),
        "{reason}"
    );
}

#[cfg(feature = "verify")]
#[test]
fn relocation_inventory_refuses_branches_to_weak_undefined_but_keeps_got_and_data_rows() {
    let module = binding_module();
    let pipeline = pipeline(LINUX, OptLevel::O0);
    let (functions, _) = prepare(&pipeline, &module.functions);
    match pipeline.module_relocation_inventory_report_with_symbol_linkage(
        &functions,
        &module.globals,
        &[],
        &module.linkage,
        "binding.o",
    ) {
        Err(PipelineError::ObjectRelocationInventoryIncomplete { reason, .. }) => {
            assert!(reason.contains("weak undefined `maybe_fn`"), "{reason}");
        }
        other => panic!("expected an incomplete inventory, got {other:?}"),
    }
    // Without the direct branch, GOT and ABS64 references to weak symbols keep
    // their modeled formulas (S = 0) and the inventory is issued.
    let keep = module.functions.len() - 1;
    let mut bindings = module.linkage.function_bindings().to_vec();
    bindings.truncate(keep);
    let report = pipeline
        .module_relocation_inventory_report_with_symbol_linkage(
            &functions[..keep],
            &module.globals,
            &[],
            &ModuleSymbolLinkage::new(bindings, module.linkage.weak_undefined_functions().clone()),
            "binding.o",
        )
        .expect("inventory")
        .expect("ELF inventory");
    assert!(!report.entries.is_empty());
}

/// A tail call to a weak undefined function is a `JUMP26`, not a `CALL26`.
/// Both are outside the modeled branch formula, so the inventory must refuse
/// the tail branch too; at least one level must actually emit it, so the
/// `JUMP26` arm is exercised rather than assumed.
#[cfg(feature = "verify")]
#[test]
fn relocation_inventory_refuses_tail_branches_to_weak_undefined_at_every_opt_level() {
    let weak = ModuleSymbolLinkage::new(Vec::new(), BTreeSet::from(["maybe_fn".to_string()]));
    let mut kinds_seen = BTreeSet::new();
    for opt_level in OPT_LEVELS {
        let pipeline = pipeline(LINUX, opt_level);
        let (functions, _) = prepare(&pipeline, &[returns_call("tail_maybe_fn", "maybe_fn")]);
        let object = pipeline
            .compile_module_emission_with_symbol_linkage(&functions, &[], &[], &weak)
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
            .into_emission()
            .object;
        let elf = parse_elf(&object);
        assert_symbol(&elf, "maybe_fn", STB_WEAK, STT_NOTYPE, STV_DEFAULT, false);
        let kinds: Vec<u32> = elf
            .relocs_in(".text")
            .iter()
            .filter(|reloc| reloc.symbol == "maybe_fn")
            .map(|reloc| reloc.kind)
            .collect();
        assert!(
            kinds.len() == 1 && branch_kinds().contains(&kinds[0]),
            "{opt_level:?}: one branch to the weak symbol: {kinds:?}"
        );
        kinds_seen.insert(kinds[0]);
        match pipeline.module_relocation_inventory_report_with_symbol_linkage(
            &functions,
            &[],
            &[],
            &weak,
            "tail.o",
        ) {
            Err(PipelineError::ObjectRelocationInventoryIncomplete { reason, .. }) => {
                assert!(
                    reason.contains("weak undefined `maybe_fn`"),
                    "{opt_level:?}: {reason}"
                );
            }
            other => panic!("{opt_level:?}: expected an incomplete inventory, got {other:?}"),
        }
        // Control: the same branch to a STRONG undefined symbol is inventoried.
        pipeline
            .module_relocation_inventory_report_with_symbol_linkage(
                &functions,
                &[],
                &[],
                &ModuleSymbolLinkage::default(),
                "tail.o",
            )
            .unwrap_or_else(|error| panic!("{opt_level:?}: strong branch inventory: {error}"))
            .expect("ELF inventory");
    }
    assert!(
        kinds_seen.contains(&R_AARCH64_JUMP26),
        "no level emitted a tail branch: {kinds_seen:?}"
    );
}

// =============================================================================
// Compiler::compile: trust-ir linkage -> ELF binding; ExternalWeak
// =============================================================================

fn linux_target_info() -> TargetInfo {
    TargetInfo {
        triple: LINUX.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn compiler(triple: &str, opt_level: OptLevel, parallel: bool) -> Compiler {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            parallel,
            ..Default::default()
        },
        TargetSpec::parse(triple).expect("triple"),
    )
    .with_codegen_license(permit_unlicensed())
}

/// `() -> u64` function returning `value`.
fn constant_function(module: &mut Module, name: &str, linkage: Linkage, value: i128) -> FuncId {
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
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
            ty: Ty::U64,
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

/// `() -> u64` function returning `callee()`.
fn calling_function(module: &mut Module, name: &str, callee: FuncId) -> FuncId {
    let sig = module.functions[callee.index() as usize].ty;
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, sig, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Call {
            callee,
            args: vec![],
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

const LINKAGE_ROWS: [(&str, Linkage, u8); 7] = [
    ("external_fn", Linkage::External, STB_GLOBAL),
    ("weak_fn", Linkage::Weak, STB_WEAK),
    ("link_once_fn", Linkage::LinkOnce, STB_WEAK),
    ("weak_odr_fn", Linkage::WeakOdr, STB_WEAK),
    ("link_once_odr_fn", Linkage::LinkOnceOdr, STB_WEAK),
    ("internal_fn", Linkage::Internal, STB_LOCAL),
    ("private_fn", Linkage::Private, STB_LOCAL),
];

#[test]
fn compiler_maps_trust_ir_function_linkage_to_elf_bindings() {
    let mut module = Module::new("linkage_bindings");
    module.target_info = Some(linux_target_info());
    for (index, (name, linkage, _)) in LINKAGE_ROWS.iter().enumerate() {
        constant_function(&mut module, name, *linkage, index as i128);
    }
    // A strong external caller of a weak definition: the call names the weak
    // symbol, so a strong definition elsewhere can take it over at link time.
    calling_function(&mut module, "call_weak_fn", FuncId::new(1));
    for opt_level in OPT_LEVELS {
        for parallel in [false, true] {
            let object = compiler(LINUX, opt_level, parallel)
                .compile(&module)
                .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
                .object_code;
            let elf = parse_elf(&object);
            for (name, _, bind) in LINKAGE_ROWS {
                assert_symbol(&elf, name, bind, STT_FUNC, STV_DEFAULT, true);
            }
            assert!(
                elf.relocs_in(".text")
                    .iter()
                    .any(|reloc| reloc.symbol == "weak_fn" && branch_kinds().contains(&reloc.kind)),
                "{opt_level:?}: call_weak_fn must branch to the weak symbol"
            );
        }
    }
}

/// `maybe_fn` (bodyless `ExternalWeak` `() -> u64`) and `maybe_data`
/// (initializer-less `ExternalWeak` `u64`), with getters for both addresses
/// and, when `with_uses`, a direct call and a load through them.
fn external_weak_module(with_uses: bool) -> Module {
    let mut module = Module::new("external_weak_refs");
    module.target_info = Some(linux_target_info());
    let u64_sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let ptr_sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut maybe_fn = Function::new(FuncId::new(0), "maybe_fn", u64_sig, BlockId::new(0));
    maybe_fn.linkage = Linkage::ExternalWeak;
    module.functions.push(maybe_fn);
    module.globals.push(Global {
        name: "maybe_data".into(),
        ty: Ty::U64,
        mutable: true,
        initializer: None,
        linkage: Linkage::ExternalWeak,
        tls: None,
        align: Some(8),
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });
    let mut push = |name: &str, sig, body: Vec<InstrNode>| {
        let id = FuncId::new(module.functions.len() as u32);
        let mut function = Function::new(id, name, sig, BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.body = body;
        function.blocks.push(block);
        module.functions.push(function);
    };
    // A weak declaration's address is nullable, so trust-ir spells it as a
    // `SymbolAddr` at `Ty::Ptr` (a `FnDef` of it is `WeakDeclarationAsFnDef`,
    // a direct call `DirectCallToWeakDeclaration`), and since WS7.3 every
    // ingestion entry refuses what the validator refuses.
    push(
        "maybe_fn_address",
        ptr_sig,
        vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Ptr,
                value: Constant::SymbolAddr {
                    symbol: "maybe_fn".into(),
                    addend: 0,
                },
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    );
    push(
        "maybe_data_address",
        ptr_sig,
        vec![
            InstrNode::new(Inst::GlobalAddr {
                global: GlobalId::new(0),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }),
        ],
    );
    if with_uses {
        // The call goes through the symbol's address at its exact signature
        // and convention, the one call trust-ir admits to a weak declaration.
        push(
            "call_maybe_fn",
            u64_sig,
            vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::Ptr,
                    value: Constant::SymbolAddr {
                        symbol: "maybe_fn".into(),
                        addend: 0,
                    },
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::CallIndirect {
                    callee: ValueId::new(1),
                    sig: u64_sig,
                    args: vec![],
                    calling_conv: trust_ir::CallingConv::C,
                })
                .with_result(ValueId::new(0)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(0)],
                }),
            ],
        );
        push(
            "load_maybe_data",
            u64_sig,
            vec![
                InstrNode::new(Inst::GlobalAddr {
                    global: GlobalId::new(0),
                })
                .with_result(ValueId::new(0)),
                InstrNode::new(Inst::Load {
                    ty: Ty::U64,
                    ptr: ValueId::new(0),
                    volatile: false,
                    align: Some(8),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(1)],
                }),
            ],
        );
    }
    module
}

#[test]
fn compiler_emits_external_weak_as_weak_undefined_got_references_on_aarch64_elf() {
    let module = external_weak_module(true);
    for opt_level in OPT_LEVELS {
        for parallel in [false, true] {
            let object = compiler(LINUX, opt_level, parallel)
                .compile(&module)
                .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
                .object_code;
            let elf = parse_elf(&object);
            assert_symbol(&elf, "maybe_fn", STB_WEAK, STT_NOTYPE, STV_DEFAULT, false);
            assert_symbol(&elf, "maybe_data", STB_WEAK, STT_NOTYPE, STV_DEFAULT, false);
            for name in [
                "maybe_fn_address",
                "maybe_data_address",
                "call_maybe_fn",
                "load_maybe_data",
            ] {
                assert_symbol(&elf, name, STB_GLOBAL, STT_FUNC, STV_DEFAULT, true);
            }
            for symbol in ["maybe_fn", "maybe_data"] {
                let kinds: BTreeSet<u32> = elf
                    .relocs_in(".text")
                    .iter()
                    .filter(|reloc| reloc.symbol == symbol)
                    .map(|reloc| reloc.kind)
                    .collect();
                assert!(
                    kinds.contains(&R_AARCH64_ADR_GOT_PAGE)
                        && kinds.contains(&R_AARCH64_LD64_GOT_LO12_NC),
                    "{opt_level:?}: {symbol} addressed through the GOT: {kinds:?}"
                );
                assert!(
                    !kinds.contains(&R_AARCH64_ADR_PREL_PG_HI21)
                        && !kinds.contains(&R_AARCH64_ADD_ABS_LO12_NC)
                        && !R_AARCH64_LDST_ABS_LO12_NC
                            .iter()
                            .any(|kind| kinds.contains(kind)),
                    "{opt_level:?}: {symbol} must never be addressed directly: {kinds:?}"
                );
            }
            // The call is indirect through the GOT-loaded address (a direct
            // call to a weak declaration is not valid trust-ir), so no branch
            // relocation may name the weak symbol.
            assert!(
                !elf.relocs_in(".text").iter().any(|reloc| {
                    reloc.symbol == "maybe_fn" && branch_kinds().contains(&reloc.kind)
                }),
                "{opt_level:?}: no direct branch to the weak symbol"
            );
        }
    }
}

#[test]
fn external_weak_stays_refused_off_aarch64_elf() {
    let module = external_weak_module(true);
    for (triple, target) in [
        ("aarch64-apple-darwin", trust_cg_codegen::Target::Aarch64),
        ("x86_64-apple-darwin", trust_cg_codegen::Target::X86_64),
        ("x86_64-unknown-linux-gnu", trust_cg_codegen::Target::X86_64),
    ] {
        let mut module = module.clone();
        pinned_target::pin(&mut module, triple);
        let error = Compiler::new_for_target_spec(
            CompilerConfig {
                target,
                opt_level: OptLevel::O0,
                parallel: false,
                ..Default::default()
            },
            TargetSpec::parse(triple).unwrap(),
        )
        .with_codegen_license(permit_unlicensed())
        .compile(&module)
        .expect_err("no weak undefined channel")
        .to_string();
        assert!(error.contains("external_weak"), "{triple}: {error}");
    }
}

#[test]
fn external_weak_that_is_not_a_weak_declaration_is_refused_on_aarch64_elf() {
    let refused = |module: &Module| {
        compiler(LINUX, OptLevel::O0, false)
            .compile(module)
            .expect_err("not a weak declaration")
            .to_string()
    };
    let mut bodied = Module::new("bodied_external_weak");
    bodied.target_info = Some(linux_target_info());
    constant_function(&mut bodied, "has_body", Linkage::ExternalWeak, 1);
    let error = refused(&bodied);
    assert!(
        error.contains("external_weak") && error.contains("body"),
        "{error}"
    );

    let mut initialized = external_weak_module(false);
    initialized.globals[0].initializer = Some(Constant::Int(3));
    assert!(refused(&initialized).contains("initializer"));

    let mut thread_local = external_weak_module(false);
    thread_local.globals[0].tls = Some(trust_ir::TlsModel::LocalExec);
    assert!(refused(&thread_local).contains("thread-local"));

    // A hidden weak data reference is a weak declaration too (L02-P6): its
    // undefined symbol is `WEAK HIDDEN`, still addressed through the GOT.
    let mut hidden = external_weak_module(false);
    hidden.globals[0].visibility = Visibility::Hidden;
    let elf = parse_elf(
        &compiler(LINUX, OptLevel::O0, false)
            .compile(&hidden)
            .unwrap_or_else(|error| panic!("hidden weak data reference: {error}"))
            .object_code,
    );
    assert_symbol(&elf, "maybe_data", STB_WEAK, STT_NOTYPE, STV_HIDDEN, false);
    let kinds: Vec<u32> = elf
        .relocs
        .iter()
        .filter(|reloc| reloc.symbol == "maybe_data")
        .map(|reloc| reloc.kind)
        .collect();
    assert_eq!(
        kinds,
        [R_AARCH64_ADR_GOT_PAGE, R_AARCH64_LD64_GOT_LO12_NC],
        "the hidden weak data reference stays GOT-addressed"
    );
}

#[cfg(feature = "verify")]
#[test]
fn proof_emission_refuses_a_direct_branch_to_a_weak_undefined_function() {
    // A DIRECT call to a weak declaration (whose symbol may resolve to null)
    // is not valid trust-ir (`DirectCallToWeakDeclaration`): since WS7.3 it is
    // refused at ingestion, before the proof lane's CALL26 refusal is reached,
    // with or without proofs.
    let mut module = external_weak_module(true);
    let call = module
        .functions
        .iter_mut()
        .find(|function| function.name == "call_maybe_fn")
        .expect("call_maybe_fn");
    call.blocks[0].body = vec![
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![],
        })
        .with_result(ValueId::new(0)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }),
    ];
    for emit_proofs in [true, false] {
        let error = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: OptLevel::O0,
                parallel: false,
                emit_proofs,
                ..Default::default()
            },
            TargetSpec::parse(LINUX).unwrap(),
        )
        .with_codegen_license(permit_unlicensed())
        .compile(&module)
        .expect_err("a direct call to a weak declaration is refused");
        match error {
            CompileError::InvalidTrustIr(refusal) => assert!(
                refusal.any(|finding| matches!(
                    finding,
                    trust_ir_build::ValidationError::DirectCallToWeakDeclaration { .. }
                )),
                "{refusal}"
            ),
            other => panic!("expected the admission refusal, got {other}"),
        }
    }
}

// =============================================================================
// Compiler::compile: trust-ir v45 function visibility -> ELF STV_*
// =============================================================================

/// Every (linkage, visibility) a trust-ir v45 function DEFINITION may state,
/// with the ELF binding and visibility its symbol must carry. The default
/// rows are the controls.
const VISIBILITY_ROWS: [(&str, Linkage, Visibility, u8, u8); 12] = [
    (
        "vis_external_default",
        Linkage::External,
        Visibility::Default,
        STB_GLOBAL,
        STV_DEFAULT,
    ),
    (
        "vis_external_hidden",
        Linkage::External,
        Visibility::Hidden,
        STB_GLOBAL,
        STV_HIDDEN,
    ),
    (
        "vis_external_protected",
        Linkage::External,
        Visibility::Protected,
        STB_GLOBAL,
        STV_PROTECTED,
    ),
    (
        "vis_weak_default",
        Linkage::Weak,
        Visibility::Default,
        STB_WEAK,
        STV_DEFAULT,
    ),
    (
        "vis_weak_hidden",
        Linkage::Weak,
        Visibility::Hidden,
        STB_WEAK,
        STV_HIDDEN,
    ),
    (
        "vis_weak_protected",
        Linkage::Weak,
        Visibility::Protected,
        STB_WEAK,
        STV_PROTECTED,
    ),
    (
        "vis_link_once_hidden",
        Linkage::LinkOnce,
        Visibility::Hidden,
        STB_WEAK,
        STV_HIDDEN,
    ),
    (
        "vis_link_once_protected",
        Linkage::LinkOnce,
        Visibility::Protected,
        STB_WEAK,
        STV_PROTECTED,
    ),
    (
        "vis_weak_odr_hidden",
        Linkage::WeakOdr,
        Visibility::Hidden,
        STB_WEAK,
        STV_HIDDEN,
    ),
    (
        "vis_weak_odr_protected",
        Linkage::WeakOdr,
        Visibility::Protected,
        STB_WEAK,
        STV_PROTECTED,
    ),
    (
        "vis_link_once_odr_hidden",
        Linkage::LinkOnceOdr,
        Visibility::Hidden,
        STB_WEAK,
        STV_HIDDEN,
    ),
    (
        "vis_link_once_odr_protected",
        Linkage::LinkOnceOdr,
        Visibility::Protected,
        STB_WEAK,
        STV_PROTECTED,
    ),
];

/// Name suffixes of the copies of [`VISIBILITY_ROWS`] in
/// [`visibility_module`]. Two copies make 48 definitions, past the 32 that
/// `resource_limits::worker_count_for_items` needs before `Compiler::compile`
/// takes its parallel preparation and emission path.
const VISIBILITY_COPIES: [&str; 2] = ["", "_b"];

/// Every `(symbol, linkage, visibility, bind, st_other)` row of
/// [`visibility_module`]: each [`VISIBILITY_ROWS`] entry once per copy.
fn visibility_symbol_rows() -> Vec<(String, Linkage, Visibility, u8, u8)> {
    VISIBILITY_COPIES
        .iter()
        .flat_map(|suffix| {
            VISIBILITY_ROWS
                .iter()
                .map(move |(name, linkage, visibility, bind, st_other)| {
                    (
                        format!("{name}{suffix}"),
                        *linkage,
                        *visibility,
                        *bind,
                        *st_other,
                    )
                })
        })
        .collect()
}

/// One `() -> u64` leaf per [`visibility_symbol_rows`] entry plus a
/// default-visibility `call_<leaf>` caller for each (48 definitions).
fn visibility_module() -> Module {
    let mut module = Module::new("v45_function_visibility");
    module.target_info = Some(linux_target_info());
    let rows = visibility_symbol_rows();
    for (index, (name, linkage, visibility, _, _)) in rows.iter().enumerate() {
        let id = constant_function(&mut module, name, *linkage, 100 + index as i128);
        module.functions[id.index() as usize].visibility = *visibility;
    }
    for (index, (name, ..)) in rows.iter().enumerate() {
        calling_function(
            &mut module,
            &format!("call_{name}"),
            FuncId::new(index as u32),
        );
    }
    module
}

/// Each row whose symbol does not carry the expected binding and visibility,
/// read by the independent parser. Empty for a faithful object.
fn visibility_row_mismatches(elf: &Elf) -> Vec<String> {
    let mut mismatches = Vec::new();
    for (name, _, _, bind, visibility) in visibility_symbol_rows() {
        let symbol = elf.symbol(&name);
        if (symbol.bind, symbol.kind, symbol.visibility) != (bind, STT_FUNC, visibility)
            || symbol.shndx == 0
        {
            mismatches.push(format!("{name}: {symbol:?}"));
        }
        let caller = elf.symbol(&format!("call_{name}"));
        if (caller.bind, caller.visibility) != (STB_GLOBAL, STV_DEFAULT) {
            mismatches.push(format!("call_{name}: {caller:?}"));
        }
    }
    mismatches
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

/// Assert that `result` came from the parallel preparation and emission path
/// when `parallel` is set and from the sequential one otherwise. A parallel
/// row that the budget kept sequential (too few items, a one-worker
/// `TRUST_CG_MAX_PARALLELISM`, a single CPU) fails by name instead of
/// silently re-testing the sequential emitter.
fn assert_emission_path(result: &CompilationResult, parallel: bool, functions: usize, label: &str) {
    let path = emission_path(result);
    assert!(
        path.starts_with(&format!("{functions} functions, ")),
        "{label}: {path}"
    );
    if parallel {
        assert!(
            path.contains("parallel preparation and emission"),
            "{label}: the parallel row ran `{path}`; worker_count_for_items({functions}) = {:?} \
             (it needs at least 32 items, TRUST_CG_MAX_PARALLELISM above 1 and two CPUs)",
            trust_cg_codegen::resource_limits::worker_count_for_items(functions)
        );
    } else {
        assert!(
            path.ends_with("sequential preparation and emission"),
            "{label}: {path}"
        );
    }
}

/// Byte offset of `name`'s `Elf64_Sym` in a relocatable object, located from
/// the section headers without the parser above (mutation controls only).
fn symbol_entry_offset(bytes: &[u8], name: &str) -> usize {
    let shoff = rd_u64(bytes, 0x28) as usize;
    let shnum = rd_u16(bytes, 0x3c) as usize;
    let header = |index: usize| shoff + index * 64;
    let symtab = (0..shnum)
        .find(|&index| rd_u32(bytes, header(index) + 4) == 2)
        .expect("SHT_SYMTAB");
    let (offset, size) = (
        rd_u64(bytes, header(symtab) + 0x18) as usize,
        rd_u64(bytes, header(symtab) + 0x20) as usize,
    );
    let strtab = rd_u32(bytes, header(symtab) + 0x28) as usize;
    let strings = rd_u64(bytes, header(strtab) + 0x18) as usize;
    (offset..offset + size)
        .step_by(24)
        .find(|&entry| cstr(bytes, strings + rd_u32(bytes, entry) as usize) == name)
        .unwrap_or_else(|| panic!("symbol {name}"))
}

/// `.text` bytes and every relocation (by target name) of two objects agree:
/// a symbol's visibility is a symbol-table attribute only.
fn assert_same_text_and_relocations(bound: &Elf, control: &Elf, label: &str) {
    assert_eq!(bound.section(".text"), control.section(".text"), "{label}");
    let mut a = bound.relocs.clone();
    let mut b = control.relocs.clone();
    a.sort();
    b.sort();
    assert_eq!(
        a, b,
        "{label}: relocation targets must not move with visibility"
    );
}

/// Under `pic` a hidden or protected definition is not preemptible, so the
/// module inliner may splice a strong one into its caller. A weak one stays
/// out of the inliner, because another object may replace it at static link.
/// Every named-symbol relocation of `bound` is therefore `control`'s (the
/// same module with every visibility default), except the calls to the
/// strong hidden and protected leaves, which O1-O3 inline.
fn assert_pic_visibility_unpreempts_only_strong_leaves(
    bound: &Elf,
    control: &Elf,
    opt_level: OptLevel,
    label: &str,
) {
    let named = |elf: &Elf| -> Vec<(u32, String)> {
        let mut rows: Vec<(u32, String)> = elf
            .relocs
            .iter()
            .filter(|reloc| !reloc.symbol.starts_with("<section "))
            .map(|reloc| (reloc.kind, reloc.symbol.clone()))
            .collect();
        rows.sort();
        rows
    };
    let strong_bound_leaf = |symbol: &str| {
        VISIBILITY_COPIES.iter().any(|suffix| {
            symbol == format!("vis_external_hidden{suffix}")
                || symbol == format!("vis_external_protected{suffix}")
        })
    };
    let mut expected = named(control);
    if opt_level != OptLevel::O0 {
        let before = expected.len();
        expected
            .retain(|(kind, symbol)| !(branch_kinds().contains(kind) && strong_bound_leaf(symbol)));
        assert_eq!(
            before - expected.len(),
            4,
            "{label}: the control calls each strong hidden/protected leaf once"
        );
    }
    assert_eq!(named(bound), expected, "{label}");
}

/// `Compiler::compile` carries trust-ir v45 visibility onto every global and
/// weak AArch64 ELF function definition, O0-O3, sequential and parallel,
/// static and PIC. The 48-definition module is large enough for the parallel
/// preparation and emission path, and each row asserts from the compiler
/// trace which path produced its object. The same module with every
/// visibility reset to default has only default symbols. Under `static` it
/// has identical text and relocations. Under `pic` it differs only where
/// the preemption predicate reads visibility (see
/// [`assert_pic_visibility_unpreempts_only_strong_leaves`]). The row checker
/// refuses an object whose `st_other` or `st_info` is mutated.
#[test]
fn compiler_maps_trust_ir_function_visibility_to_elf_symbols() {
    let module = visibility_module();
    let functions = module.functions.len();
    assert_eq!(functions, 48);
    let mut control = module.clone();
    for function in &mut control.functions {
        function.visibility = Visibility::Default;
    }
    for relocation_model in [
        trust_cg_codegen::RelocationModel::Static,
        trust_cg_codegen::RelocationModel::Pic,
    ] {
        for opt_level in OPT_LEVELS {
            for parallel in [false, true] {
                let label = format!("{relocation_model} {opt_level:?} parallel={parallel}");
                let compile = |module: &Module| {
                    Compiler::new_for_target_spec(
                        CompilerConfig {
                            opt_level,
                            parallel,
                            relocation_model,
                            trace_level: CompilerTraceLevel::Full,
                            ..Default::default()
                        },
                        TargetSpec::parse(LINUX).expect("triple"),
                    )
                    .with_codegen_license(permit_unlicensed())
                    .compile(module)
                    .map(|result| {
                        assert_emission_path(&result, parallel, functions, &label);
                        result.object_code
                    })
                    .unwrap_or_else(|error| panic!("{label}: {error}"))
                };
                let object = compile(&module);
                let elf = parse_elf(&object);
                assert_eq!(
                    visibility_row_mismatches(&elf),
                    Vec::<String>::new(),
                    "{label}"
                );
                let control_elf = parse_elf(&compile(&control));
                if relocation_model == trust_cg_codegen::RelocationModel::Static {
                    assert_same_text_and_relocations(&elf, &control_elf, &label);
                } else {
                    assert_pic_visibility_unpreempts_only_strong_leaves(
                        &elf,
                        &control_elf,
                        opt_level,
                        &label,
                    );
                }
                for (name, _, visibility, _, _) in visibility_symbol_rows() {
                    assert_eq!(
                        control_elf.symbol(&name).visibility,
                        STV_DEFAULT,
                        "{label}: the control resets {name} ({visibility})"
                    );
                }

                // Mutation controls: the row checker is load-bearing.
                let mut hidden_to_default = object.clone();
                hidden_to_default[symbol_entry_offset(&object, "vis_external_hidden") + 5] &= !3;
                let mismatches = visibility_row_mismatches(&parse_elf(&hidden_to_default));
                assert!(
                    mismatches.len() == 1 && mismatches[0].starts_with("vis_external_hidden: "),
                    "{label}: {mismatches:?}"
                );
                let mut weak_to_global = object.clone();
                let info = symbol_entry_offset(&object, "vis_weak_protected") + 4;
                weak_to_global[info] = (STB_GLOBAL << 4) | (weak_to_global[info] & 0xf);
                let mismatches = visibility_row_mismatches(&parse_elf(&weak_to_global));
                assert!(
                    mismatches.len() == 1 && mismatches[0].starts_with("vis_weak_protected: "),
                    "{label}: {mismatches:?}"
                );
            }
        }
    }
}

/// Function visibility no emitter spells is refused through
/// `Compiler::compile` with its named reason: a local function's on AArch64
/// ELF, and every non-default visibility, on a definition or an import, on
/// Mach-O, x86-64 COFF and RISC-V, except hidden on an External definition on
/// AArch64 and x86-64 Mach-O (spelled `N_PEXT`). An import's visibility compiles on AArch64 ELF
/// (see
/// [`compiler_spells_declaration_visibility_and_addresses_it_by_the_shared_predicate`]).
#[test]
fn function_visibility_the_emitters_cannot_spell_is_refused_by_name() {
    let refused = |triple: &str, module: &Module| {
        let target_spec = TargetSpec::parse(triple).expect("triple");
        Compiler::new_for_target_spec(
            CompilerConfig {
                target: target_spec.architecture,
                opt_level: OptLevel::O0,
                parallel: false,
                ..Default::default()
            },
            target_spec,
        )
        .with_codegen_license(permit_unlicensed())
        .compile(module)
        .map(|_| ())
        .expect_err("visibility must be refused")
        .to_string()
    };
    for linkage in [Linkage::Internal, Linkage::Private] {
        for visibility in [Visibility::Hidden, Visibility::Protected] {
            let mut module = Module::new("local_visibility");
            module.target_info = Some(linux_target_info());
            constant_function(&mut module, "local_fn", linkage, 1);
            module.functions[0].visibility = visibility;
            // trust-ir refuses the pair itself (`ContradictoryFunctionVisibility`)
            // and since WS7.3 ingestion admission names that finding first;
            // the backend's `[TCG-FUNCTION-VISIBILITY]` arm stays behind it.
            let error = refused(LINUX, &module);
            assert!(
                error.contains("ContradictoryFunctionVisibility"),
                "{linkage} {visibility}: {error}"
            );
        }
    }

    // An import (a bodyless declaration) that a definition calls compiles on
    // AArch64 ELF, its undefined symbol hidden.
    let mut import = Module::new("import_visibility");
    import.target_info = Some(linux_target_info());
    let sig = import
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut declared = Function::new(FuncId::new(0), "imported_fn", sig, BlockId::new(0));
    declared.visibility = Visibility::Hidden;
    import.functions.push(declared);
    calling_function(&mut import, "call_imported_fn", FuncId::new(0));
    let elf = parse_elf(
        &compiler(LINUX, OptLevel::O0, false)
            .compile(&import)
            .unwrap_or_else(|error| panic!("the hidden import compiles: {error}"))
            .object_code,
    );
    assert_symbol(
        &elf,
        "imported_fn",
        STB_GLOBAL,
        STT_NOTYPE,
        STV_HIDDEN,
        false,
    );

    // Every other object lane refuses the facet itself, on a definition and
    // on an import.
    for visibility in [Visibility::Hidden, Visibility::Protected] {
        let mut module = Module::new("off_elf_visibility");
        constant_function(&mut module, "visible_fn", Linkage::External, 1);
        module.functions[0].visibility = visibility;
        for triple in [
            "aarch64-apple-darwin",
            "x86_64-unknown-linux-gnu",
            "x86_64-apple-darwin",
            "riscv64-unknown-linux-gnu",
        ] {
            // The import is an FFI boundary: it names the target it is
            // compiled for (`TargetInfoRequired`; WS7.3 ingestion admission).
            let mut import = pinned_target::pinned(&import, triple);
            import.functions[0].visibility = visibility;
            for (module, function) in [(&module, "visible_fn"), (&import, "imported_fn")] {
                // The one shape the Mach-O emitters spell is checked below.
                if MACHO_TRIPLES.contains(&triple)
                    && function == "visible_fn"
                    && visibility == Visibility::Hidden
                {
                    continue;
                }
                // x86-64 ELF spells both visibilities on definitions and
                // declarations. Its own independent object-reader tests bind
                // both admitted shapes across O0-O3; other lanes keep the
                // named refusals below.
                if triple == "x86_64-unknown-linux-gnu" {
                    continue;
                }
                let error = refused(triple, module);
                assert!(
                    error.contains(&format!(
                        "function `{function}` states trust-ir v45 `visibility` = {visibility}"
                    )),
                    "{triple} {visibility} {function}: {error}"
                );
            }
        }
        // The AArch64 and x86-64 Mach-O module emitters spell exactly one of
        // these: hidden on an External definition (`N_SECT | N_EXT | N_PEXT`,
        // the rustc bridge's CGU-private functions).
        if visibility == Visibility::Hidden {
            for triple in MACHO_TRIPLES {
                let target_spec = TargetSpec::parse(triple).expect("triple");
                let object = Compiler::new_for_target_spec(
                    CompilerConfig {
                        target: target_spec.architecture,
                        opt_level: OptLevel::O0,
                        parallel: false,
                        ..Default::default()
                    },
                    target_spec,
                )
                .with_codegen_license(permit_unlicensed())
                .compile(&module)
                .unwrap_or_else(|error| {
                    panic!("{triple}: the hidden Mach-O definition compiles: {error}")
                })
                .object_code;
                assert_eq!(
                    macho_nlist(&object)
                        .get("_visible_fn")
                        .map(|(n_type, _)| *n_type),
                    Some(0x0e | 0x01 | 0x10),
                    "{triple}: a hidden External definition is N_SECT | N_EXT | N_PEXT"
                );
            }
        }
    }
}

/// The JIT installs no object symbol table: non-default function visibility
/// is refused by its v45 facet, on a definition and on an import, and the
/// default-visibility control compiles.
#[cfg(target_arch = "aarch64")]
#[test]
fn jit_refuses_function_visibility_by_name() {
    let mut module = Module::new("jit_visibility");
    constant_function(&mut module, "jit_visible_fn", Linkage::External, 5);
    module.functions[0].visibility = Visibility::Hidden;
    let compiler =
        Compiler::new(CompilerConfig::default()).with_codegen_license(permit_unlicensed());
    let externs = std::collections::HashMap::new();
    let error = match compiler.compile_module_to_jit(&module, &externs) {
        Ok(_) => panic!("hidden visibility must be refused by the JIT"),
        Err(error) => error.to_string(),
    };
    assert!(
        error.contains("function `jit_visible_fn` states trust-ir v45 `visibility` = hidden"),
        "{error}"
    );
    module.functions[0].visibility = Visibility::Default;
    compiler
        .compile_module_to_jit(&module, &externs)
        .unwrap_or_else(|error| panic!("the default-visibility control must JIT-compile: {error}"));

    let mut import = Module::new("jit_import_visibility");
    // An FFI boundary names its target (`TargetInfoRequired`; WS7.3).
    pinned_target::pin(&mut import, pinned_target::host_triple());
    let sig = import
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut declared = Function::new(FuncId::new(0), "jit_imported_fn", sig, BlockId::new(0));
    declared.visibility = Visibility::Protected;
    import.functions.push(declared);
    calling_function(&mut import, "jit_call_imported_fn", FuncId::new(0));
    let error = match compiler.compile_module_to_jit(&import, &externs) {
        Ok(_) => panic!("protected import visibility must be refused by the JIT"),
        Err(error) => error.to_string(),
    };
    assert!(
        error.contains("function `jit_imported_fn` states trust-ir v45 `visibility` = protected"),
        "{error}"
    );
}

// =============================================================================
// Compiler::compile: hidden and protected function DECLARATIONS
// =============================================================================

/// The declaration shapes a module only references: `(tag, linkage,
/// bodied)`. `avail` is an `AvailableExternally` function WITH a body, which
/// is never emitted and resolves like an import.
const DECLARATION_SHAPES: [(&str, Linkage, bool); 3] = [
    ("import", Linkage::External, false),
    ("avail", Linkage::AvailableExternally, true),
    ("maybe", Linkage::ExternalWeak, false),
];

const VISIBILITIES: [Visibility; 3] = [
    Visibility::Default,
    Visibility::Hidden,
    Visibility::Protected,
];

/// The ELF `STV_*` value of `visibility`.
fn stv(visibility: Visibility) -> u8 {
    match visibility {
        Visibility::Default => STV_DEFAULT,
        Visibility::Hidden => STV_HIDDEN,
        Visibility::Protected => STV_PROTECTED,
    }
}

/// A `() -> T` accessor with one block.
fn push_accessor(module: &mut Module, name: String, sig: trust_ir::FuncTyId, body: Vec<InstrNode>) {
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, sig, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body = body;
    function.blocks.push(block);
    module.functions.push(function);
}

/// Push the `() -> u64` declaration `name` (with a body returning `0xbad`
/// when `bodied`) and its default-visibility accessors:
///
/// * `addr_<name>`: a `SymbolAddr` constant, the one address form trust-ir
///   admits for a weak declaration;
/// * for a strong declaration, `fnaddr_<name>` (a `FnDef` address) and
///   `call_<name>` (a direct call);
/// * for a weak one, `call_<name>`: the call trust-ir admits, through its
///   address guarded by a null check, returning 7 when it is null.
fn push_declaration(
    module: &mut Module,
    name: &str,
    linkage: Linkage,
    visibility: Visibility,
    bodied: bool,
) -> FuncId {
    let u64_sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let ptr_sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut declaration = Function::new(id, name, u64_sig, BlockId::new(0));
    declaration.linkage = linkage;
    declaration.visibility = visibility;
    if bodied {
        let mut block = Block::new(BlockId::new(0));
        block.body = vec![
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(0xbad),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }),
        ];
        declaration.blocks.push(block);
    }
    module.functions.push(declaration);
    let symbol_addr = || {
        InstrNode::new(Inst::Const {
            ty: Ty::Ptr,
            value: Constant::SymbolAddr {
                symbol: name.to_string(),
                addend: 0,
            },
        })
        .with_result(ValueId::new(0))
    };
    push_accessor(
        module,
        format!("addr_{name}"),
        ptr_sig,
        vec![
            symbol_addr(),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }),
        ],
    );
    if linkage == Linkage::ExternalWeak {
        let call_id = FuncId::new(module.functions.len() as u32);
        let mut call = Function::new(call_id, format!("call_{name}"), u64_sig, BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0));
        entry.body = vec![
            symbol_addr(),
            InstrNode::new(Inst::NullPtr).with_result(ValueId::new(1)),
            InstrNode::new(Inst::ICmp {
                op: trust_ir::ICmpOp::Eq,
                ty: Ty::Ptr,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::CondBr {
                cond: ValueId::new(2),
                then_target: BlockId::new(1),
                then_args: vec![],
                else_target: BlockId::new(2),
                else_args: vec![],
            }),
        ];
        let mut absent = Block::new(BlockId::new(1));
        absent.body = vec![
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(7),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ];
        let mut present = Block::new(BlockId::new(2));
        present.body = vec![
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(0),
                sig: u64_sig,
                args: vec![],
                calling_conv: trust_ir::CallingConv::C,
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(4)],
            }),
        ];
        call.blocks = vec![entry, absent, present];
        module.functions.push(call);
    } else {
        push_accessor(
            module,
            format!("fnaddr_{name}"),
            ptr_sig,
            vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::Func(u64_sig),
                    value: Constant::FnDef(id),
                })
                .with_result(ValueId::new(0)),
                InstrNode::new(Inst::Cast {
                    op: CastOp::ReifyFnPointer,
                    src_ty: Ty::Func(u64_sig),
                    dst_ty: Ty::Ptr,
                    operand: ValueId::new(0),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(1)],
                }),
            ],
        );
        calling_function(module, &format!("call_{name}"), id);
    }
    id
}

/// External filler definitions that lift [`declaration_visibility_module`]
/// over the parallel emitter's 32-item threshold.
const DECLARATION_PADDING: usize = 10;

/// Emitted functions of [`declaration_visibility_module`]: three accessors
/// per strong declaration, two per weak one, and the padding.
const DECLARATION_MODULE_FUNCTIONS: usize = 6 * 3 + 3 * 2 + DECLARATION_PADDING;

/// Every row of [`declaration_visibility_module`]: `(symbol, linkage,
/// visibility)`, named `decl_<shape>_<visibility>`.
fn declaration_rows() -> Vec<(String, Linkage, Visibility, bool)> {
    DECLARATION_SHAPES
        .iter()
        .flat_map(|(tag, linkage, bodied)| {
            VISIBILITIES.iter().map(move |visibility| {
                (
                    format!("decl_{tag}_{visibility}"),
                    *linkage,
                    *visibility,
                    *bodied,
                )
            })
        })
        .collect()
}

/// Each declaration shape at each visibility (nine declarations, none
/// emitted), their accessors (see [`push_declaration`]) and
/// [`DECLARATION_PADDING`] External fillers.
fn declaration_visibility_module() -> Module {
    let mut module = Module::new("v45_declaration_visibility");
    module.target_info = Some(linux_target_info());
    for (name, linkage, visibility, bodied) in declaration_rows() {
        push_declaration(&mut module, &name, linkage, visibility, bodied);
    }
    for index in 0..DECLARATION_PADDING {
        constant_function(
            &mut module,
            &format!("decl_pad_{index}"),
            Linkage::External,
            index as i128,
        );
    }
    module
}

/// Each declaration row whose undefined symbol does not carry the expected
/// binding and visibility, read by the independent parser. Empty for a
/// faithful object.
fn declaration_symbol_mismatches(elf: &Elf) -> Vec<String> {
    let mut mismatches = Vec::new();
    for (name, linkage, visibility, _) in declaration_rows() {
        let bind = if linkage == Linkage::ExternalWeak {
            STB_WEAK
        } else {
            STB_GLOBAL
        };
        let symbol = elf.symbol(&name);
        if (symbol.bind, symbol.kind, symbol.visibility, symbol.shndx)
            != (bind, STT_NOTYPE, stv(visibility), 0)
        {
            mismatches.push(format!("{name}: {symbol:?}"));
        }
    }
    mismatches
}

/// The `.text` relocation kinds naming `symbol`, sorted, with `CALL26` and
/// `JUMP26` folded into `u32::MAX` (the tail-call choice varies by level).
fn declaration_relocation_kinds(elf: &Elf, symbol: &str) -> Vec<u32> {
    let mut kinds: Vec<u32> = elf
        .relocs_in(".text")
        .iter()
        .filter(|reloc| reloc.symbol == symbol)
        .map(|reloc| {
            if branch_kinds().contains(&reloc.kind) {
                u32::MAX
            } else {
                reloc.kind
            }
        })
        .collect();
    kinds.sort_unstable();
    kinds
}

/// Whether `Compiler::compile` splices a declaration row's body into its
/// `call_` accessor: only an `AvailableExternally` row carries a body, the
/// AOT inliner runs at O1+, and a default-visibility body is preemptible
/// under `pic` and withheld (`trust_cg_lower::translate_inline_only_bodies`).
/// Written out here rather than read from the admission code.
fn declaration_body_spliced(
    linkage: Linkage,
    visibility: Visibility,
    relocation_model: trust_cg_codegen::RelocationModel,
    opt_level: OptLevel,
) -> bool {
    linkage == Linkage::AvailableExternally
        && opt_level != OptLevel::O0
        && !(relocation_model == trust_cg_codegen::RelocationModel::Pic
            && visibility == Visibility::Default)
}

/// The `.text` relocations a declaration row must have, whatever its
/// visibility: two GOT address pairs (a declaration's definition may be in
/// another image, absent, or a GNU IFUNC) and, for a strong declaration, one
/// direct branch. Written out here rather than read from
/// `RelocationModel::symbol_address_is_got_indirect`, so a drifted predicate
/// fails the rows below.
fn expected_declaration_relocation_kinds(linkage: Linkage) -> Vec<u32> {
    let (page, low) = (R_AARCH64_ADR_GOT_PAGE, R_AARCH64_LD64_GOT_LO12_NC);
    let mut kinds = vec![page, page, low, low];
    if linkage != Linkage::ExternalWeak {
        kinds.push(u32::MAX);
    }
    kinds.sort_unstable();
    kinds
}

/// `Compiler::compile` spells trust-ir v45 visibility on each codegen
/// declaration's undefined symbol on AArch64 ELF and addresses it as the
/// shared address predicate says, under `static`, `pie` and `pic`, O0-O3,
/// sequential and parallel (the trace names the emission path). For a bodyless
/// `External` import, an `AvailableExternally` function with a body and a
/// bodyless `ExternalWeak` reference, each default, hidden and protected:
///
/// * the symbol is `SHN_UNDEF`, `STT_NOTYPE`, `STB_GLOBAL` (`STB_WEAK` for the
///   weak shape) with the stated `STV_*`;
/// * both address forms are `ADR_GOT_PAGE` + `LD64_GOT_LO12_NC` under every
///   model, whatever the visibility (never a PC-relative page);
/// * a strong declaration's call is one `CALL26`/`JUMP26` whatever its
///   visibility, and a weak declaration's guarded call has no direct branch —
///   except where the AOT seam splices an `AvailableExternally` body into
///   its call ([`declaration_body_spliced`]): that call is gone, the address
///   forms stay, and the object discloses the splice.
///
/// The row checker refuses an object whose `st_other` or `st_info` is mutated.
#[test]
fn compiler_spells_declaration_visibility_and_addresses_it_by_the_shared_predicate() {
    let module = declaration_visibility_module();
    for relocation_model in RELOCATION_MODELS {
        for opt_level in OPT_LEVELS {
            for parallel in [false, true] {
                let label = format!("{relocation_model} {opt_level:?} parallel={parallel}");
                let result = Compiler::new_for_target_spec(
                    CompilerConfig {
                        opt_level,
                        parallel,
                        relocation_model,
                        trace_level: CompilerTraceLevel::Full,
                        ..Default::default()
                    },
                    TargetSpec::parse(LINUX).expect("triple"),
                )
                .with_codegen_license(permit_unlicensed())
                .compile(&module)
                .unwrap_or_else(|error| panic!("{label}: {error}"));
                assert_emission_path(&result, parallel, DECLARATION_MODULE_FUNCTIONS, &label);
                let expected_spliced: Vec<(String, usize)> = declaration_rows()
                    .into_iter()
                    .filter(|(_, linkage, visibility, _)| {
                        declaration_body_spliced(*linkage, *visibility, relocation_model, opt_level)
                    })
                    .map(|(name, ..)| (name, 1))
                    .collect();
                let spliced: Vec<(String, usize)> = result
                    .inline_only_bodies
                    .spliced
                    .iter()
                    .map(|use_| (use_.name.clone(), use_.sites))
                    .collect();
                assert_eq!(spliced, expected_spliced, "{label}");
                let object = result.object_code;
                let elf = parse_elf(&object);
                assert_eq!(
                    declaration_symbol_mismatches(&elf),
                    Vec::<String>::new(),
                    "{label}"
                );
                for (name, linkage, visibility, _) in declaration_rows() {
                    let mut expected = expected_declaration_relocation_kinds(linkage);
                    if declaration_body_spliced(linkage, visibility, relocation_model, opt_level) {
                        expected.retain(|kind| *kind != u32::MAX);
                    }
                    assert_eq!(
                        declaration_relocation_kinds(&elf, &name),
                        expected,
                        "{label}: `{name}`"
                    );
                }

                // Mutation controls: the row checker is load-bearing.
                let mut hidden_to_default = object.clone();
                hidden_to_default[symbol_entry_offset(&object, "decl_import_hidden") + 5] &= !3;
                let mismatches = declaration_symbol_mismatches(&parse_elf(&hidden_to_default));
                assert!(
                    mismatches.len() == 1 && mismatches[0].starts_with("decl_import_hidden: "),
                    "{label}: {mismatches:?}"
                );
                let mut weak_to_global = object.clone();
                let info = symbol_entry_offset(&object, "decl_maybe_protected") + 4;
                weak_to_global[info] = (STB_GLOBAL << 4) | (weak_to_global[info] & 0xf);
                let mismatches = declaration_symbol_mismatches(&parse_elf(&weak_to_global));
                assert!(
                    mismatches.len() == 1 && mismatches[0].starts_with("decl_maybe_protected: "),
                    "{label}: {mismatches:?}"
                );
            }
        }
    }
}

/// The ELF emitters' own checks on declaration visibility, through the
/// Pipeline API. A GOT reference to a weak or strong undefined function,
/// default, hidden or protected, emits under every model, and the object
/// spells the stated visibility on the undefined symbol. A PC-relative page
/// reference to the same described reference is refused under every model,
/// with its reason: a weak one must read 0 when absent, and a declared one's
/// definition may be a GNU IFUNC. A PC-relative page reference to an
/// undescribed undefined symbol is refused under `pic` only. A visibility
/// naming a function the object defines, or a data global, is refused before
/// emission, and Mach-O refuses any non-default undefined visibility.
#[test]
#[allow(clippy::result_large_err)] // Test helper returns the compiler's own error type unchanged.
fn pipeline_declaration_visibility_reads_the_shared_predicate() {
    let target = |weak: bool, visibility: Visibility| {
        format!("ext_{}_{visibility}", if weak { "weak" } else { "strong" })
    };
    for relocation_model in RELOCATION_MODELS {
        let pipeline = Pipeline::new(PipelineConfig {
            target_triple: LINUX.to_owned(),
            relocation_model,
            ..PipelineConfig::default()
        });
        for weak in [false, true] {
            for visibility in VISIBILITIES {
                let symbol = target(weak, visibility);
                let label = format!("{relocation_model} {symbol}");
                assert!(
                    relocation_model.symbol_address_is_got_indirect(
                        trust_cg_codegen::SymbolBinding::Undefined { weak },
                        visibility,
                    ),
                    "{label}: the predicate's table"
                );
                let linkage = ModuleSymbolLinkage::new(
                    Vec::new(),
                    if weak {
                        BTreeSet::from([symbol.clone()])
                    } else {
                        BTreeSet::new()
                    },
                )
                .with_undefined_function_visibility(
                    std::collections::BTreeMap::from([(symbol.clone(), visibility)]),
                );
                let emit = |function: LirFunction| {
                    let (functions, _) = prepare(&pipeline, &[function]);
                    pipeline
                        .compile_module_emission_with_symbol_linkage(&functions, &[], &[], &linkage)
                        .map(|emission| emission.into_emission().object)
                };
                let elf = parse_elf(
                    &emit(returns_got_address("getter", &symbol))
                        .unwrap_or_else(|error| panic!("{label}: the GOT form emits: {error}")),
                );
                assert_symbol(
                    &elf,
                    &symbol,
                    if weak { STB_WEAK } else { STB_GLOBAL },
                    STT_NOTYPE,
                    stv(visibility),
                    false,
                );
                let kinds: BTreeSet<u32> = elf
                    .relocs_in(".text")
                    .iter()
                    .map(|reloc| reloc.kind)
                    .collect();
                assert_eq!(
                    kinds,
                    BTreeSet::from([R_AARCH64_ADR_GOT_PAGE, R_AARCH64_LD64_GOT_LO12_NC]),
                    "{label}"
                );

                let error = emit(returns_direct_address("getter", &symbol))
                    .map(|_| ())
                    .expect_err("a PC-relative page reference to a described declaration")
                    .to_string();
                let reason = if weak {
                    format!("addresses `{symbol}`, a weak undefined symbol")
                } else {
                    format!(
                        "addresses `{symbol}`, a declared function (visibility {visibility}), \
                         PC-relatively"
                    )
                };
                assert!(
                    error.contains(&reason) && (weak || error.contains("GNU IFUNC")),
                    "{label}: {error}"
                );
            }
        }
        // An undefined symbol the plan does not describe may be data, which
        // an executable's copy relocation resolves PC-relatively.
        let (functions, _) = prepare(&pipeline, &[returns_direct_address("getter", "ext_data")]);
        let undescribed = pipeline.compile_module_emission_with_symbol_linkage(
            &functions,
            &[],
            &[],
            &ModuleSymbolLinkage::default(),
        );
        if relocation_model == trust_cg_codegen::RelocationModel::Pic {
            let error = undescribed
                .map(|_| ())
                .expect_err("pic refuses a PC-relative undefined symbol")
                .to_string();
            assert!(
                error.contains("addresses `ext_data`, an undefined symbol"),
                "{error}"
            );
        } else {
            undescribed.unwrap_or_else(|error| panic!("{relocation_model}: {error}"));
        }
    }

    // Refused before emission: a visibility for a defined function or a
    // data global, and any non-default undefined visibility on Mach-O.
    let linux = pipeline(LINUX, OptLevel::O0);
    let (functions, _) = prepare(
        &linux,
        &[
            returns_got_address("getter", "ext_fn"),
            returns_constant("defined_fn", 1),
        ],
    );
    let visible = |name: &str| {
        ModuleSymbolLinkage::default().with_undefined_function_visibility(
            std::collections::BTreeMap::from([(name.to_string(), Visibility::Hidden)]),
        )
    };
    let refuse = |globals: &[ObjectGlobal], linkage: &ModuleSymbolLinkage| {
        linux
            .compile_module_emission_with_symbol_linkage(&functions, globals, &[], linkage)
            .expect_err("inconsistent undefined visibility")
            .to_string()
    };
    let error = refuse(&[], &visible("defined_fn"));
    assert!(error.contains("also defined in this object"), "{error}");
    let error = refuse(&[import("ext_data", false)], &visible("ext_data"));
    assert!(error.contains("also names a data global"), "{error}");
    let error = refuse(&[], &visible(""));
    assert!(error.contains("empty symbol"), "{error}");
    linux
        .compile_module_emission_with_symbol_linkage(&functions, &[], &[], &visible("ext_fn"))
        .expect("a hidden undefined function reference");

    let darwin = pipeline(DARWIN, OptLevel::O0);
    let (functions, _) = prepare(&darwin, &[returns_got_address("getter", "ext_fn")]);
    match darwin.compile_module_emission_with_symbol_linkage(
        &functions,
        &[],
        &[],
        &visible("ext_fn"),
    ) {
        Err(PipelineError::TargetObjectUnsupported { format, reason, .. }) => {
            assert_eq!(format, "Mach-O");
            assert!(
                reason.contains("`ext_fn` states visibility `hidden`"),
                "{reason}"
            );
        }
        other => panic!("Mach-O must refuse a hidden undefined reference: {other:?}"),
    }
    darwin
        .compile_module_emission_with_symbol_linkage(
            &functions,
            &[],
            &[],
            &ModuleSymbolLinkage::default().with_undefined_function_visibility(
                std::collections::BTreeMap::from([("ext_fn".to_string(), Visibility::Default)]),
            ),
        )
        .expect("an explicit default visibility is the legacy Mach-O reference");
}

/// `ModuleSymbolLinkage::with_declared_undefined_symbols` through the
/// public Pipeline API (`Compiler::compile` derives the set itself, so only
/// this route can name an inconsistent one). Each declared name that the
/// plan binds as an undefined reference (a weak or visible function
/// declaration, or a data import of either visibility) is written as an
/// undefined symbol with that binding and visibility although nothing in
/// the object references it, by each of the three AArch64 ELF module
/// emitters: the unwind emitter (frame layouts given), the layout-less one
/// without fixups (`emit_elf_with_function_symbols`) and the layout-less one
/// with fixups. Without the set none of them is written. A name the object
/// defines (a function or a data global), a default strong function
/// declaration the plan does not describe, and a name nothing declares are
/// refused by name before emission, and Mach-O refuses any non-empty set.
#[test]
fn pipeline_declared_undefined_symbols_are_bound_or_refused() {
    let linux = pipeline(LINUX, OptLevel::O0);
    let mut hidden_import = import("gh", false);
    hidden_import.visibility = Visibility::Hidden;
    let globals = vec![
        import("gd", false),
        hidden_import,
        object_global("defined_data", vec![1, 0, 0, 0, 0, 0, 0, 0]),
    ];
    let linkage = |declared: &[&str]| {
        ModuleSymbolLinkage::new(Vec::new(), BTreeSet::from(["dw".to_string()]))
            .with_undefined_function_visibility(std::collections::BTreeMap::from([
                ("dh".to_string(), Visibility::Hidden),
                ("dp".to_string(), Visibility::Protected),
            ]))
            .with_declared_undefined_symbols(declared.iter().map(|name| name.to_string()).collect())
    };
    let declared = ["dw", "dh", "dp", "gd", "gh"];
    let expected = [
        ("dw", STB_WEAK, STV_DEFAULT),
        ("dh", STB_GLOBAL, STV_HIDDEN),
        ("dp", STB_GLOBAL, STV_PROTECTED),
        ("gd", STB_GLOBAL, STV_DEFAULT),
        ("gh", STB_GLOBAL, STV_HIDDEN),
    ];
    for (route, function, with_layouts) in [
        ("unwind", returns_constant("anchor", 1), true),
        ("layout-less", returns_constant("anchor", 1), false),
        (
            "layout-less with fixups",
            returns_got_address("anchor", "other_ext"),
            false,
        ),
    ] {
        let (functions, layouts) = prepare(&linux, std::slice::from_ref(&function));
        let layouts = if with_layouts { layouts } else { Vec::new() };
        let emit = |linkage: &ModuleSymbolLinkage| {
            linux
                .compile_module_emission_with_symbol_linkage(
                    &functions, &globals, &layouts, linkage,
                )
                .map(|emission| parse_elf(&emission.into_emission().object))
                .map_err(|error| error.to_string())
        };
        let elf = emit(&linkage(&declared)).unwrap_or_else(|error| panic!("{route}: {error}"));
        for (name, bind, visibility) in expected {
            assert_symbol(&elf, name, bind, STT_NOTYPE, visibility, false);
        }
        let elf = emit(&linkage(&[])).unwrap_or_else(|error| panic!("{route}: {error}"));
        for (name, _, _) in expected {
            assert!(
                !elf.symbols.iter().any(|symbol| symbol.name == name),
                "{route}: nothing references `{name}`, so without the set it is not written"
            );
        }
        for wrong in ["anchor", "defined_data", "dd", "nowhere"] {
            let error = emit(&linkage(&["dh", wrong]))
                .map(|_| ())
                .expect_err("an unbound declared name");
            assert!(
                error.contains(&format!(
                    "ELF declared undefined symbol `{wrong}` is not a weak or visible function \
                     declaration or a data import of this object"
                )),
                "{route} {wrong}: {error}"
            );
        }
    }

    let darwin = pipeline(DARWIN, OptLevel::O0);
    let (functions, _) = prepare(&darwin, &[returns_constant("anchor", 1)]);
    match darwin.compile_module_emission_with_symbol_linkage(
        &functions,
        &[import("gd", false)],
        &[],
        &ModuleSymbolLinkage::default()
            .with_declared_undefined_symbols(BTreeSet::from(["gd".to_string()])),
    ) {
        Err(PipelineError::TargetObjectUnsupported { format, reason, .. }) => {
            assert_eq!(format, "Mach-O");
            assert!(
                reason.contains("declaration `gd` is to be written as an undefined symbol"),
                "{reason}"
            );
        }
        other => panic!("Mach-O must refuse a declared undefined set: {other:?}"),
    }
}

/// The more constraining of two visibilities, as the static linker merges
/// them (gABI): hidden over protected over default.
fn most_constraining(a: Visibility, b: Visibility) -> Visibility {
    let rank = |visibility| match visibility {
        Visibility::Default => 0,
        Visibility::Protected => 1,
        Visibility::Hidden => 2,
    };
    if rank(a) >= rank(b) { a } else { b }
}

/// `merge_modules` gives a merged function the most constraining visibility
/// any input states for its name, as the static linker would under separate
/// compilation (gABI): a hidden or protected declaration in one input
/// restricts the definition another input supplies, whatever the
/// definition's own visibility (a hidden declaration of a protected
/// definition is hidden), in either input order, and hidden wins over
/// protected. The merged object's definition carries it; the unmerged
/// definition's object carries its own.
#[test]
fn merged_declaration_visibility_restricts_the_definition() {
    let declaring = |tag: &str, visibility: Visibility| {
        let mut module = Module::new(format!("declares_{tag}"));
        module.target_info = Some(linux_target_info());
        let sig = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::U64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut declaration = Function::new(FuncId::new(0), "mv_helper", sig, BlockId::new(0));
        declaration.visibility = visibility;
        module.functions.push(declaration);
        calling_function(&mut module, &format!("{tag}_calls_helper"), FuncId::new(0));
        module
    };
    for defined in VISIBILITIES {
        let mut defining = Module::new("defines_helper");
        defining.target_info = Some(linux_target_info());
        let id = constant_function(&mut defining, "mv_helper", Linkage::External, 5);
        defining.functions[id.index() as usize].visibility = defined;
        for declarations in [
            vec![Visibility::Default],
            vec![Visibility::Hidden],
            vec![Visibility::Protected],
            vec![Visibility::Protected, Visibility::Hidden],
            vec![Visibility::Hidden, Visibility::Protected],
            vec![Visibility::Default, Visibility::Protected],
        ] {
            let merged_visibility = declarations.iter().fold(defined, |merged, declared| {
                most_constraining(merged, *declared)
            });
            let inputs: Vec<Module> = declarations
                .iter()
                .enumerate()
                .map(|(index, visibility)| declaring(&format!("in{index}"), *visibility))
                .collect();
            for definition_first in [false, true] {
                let mut ordered = inputs.clone();
                if definition_first {
                    ordered.insert(0, defining.clone());
                } else {
                    ordered.push(defining.clone());
                }
                let label = format!(
                    "defined {defined} declared {declarations:?} \
                     definition_first={definition_first}"
                );
                let merged = trust_cg_codegen::module_merge::merge_modules(&ordered)
                    .unwrap_or_else(|error| panic!("{label}: {error}"));
                let helper = merged
                    .functions
                    .iter()
                    .find(|function| function.name == "mv_helper")
                    .expect("merged helper");
                assert!(!helper.blocks.is_empty(), "{label}: the definition wins");
                assert_eq!(helper.visibility, merged_visibility, "{label}");
                let elf = parse_elf(
                    &compiler(LINUX, OptLevel::O0, false)
                        .compile(&merged)
                        .unwrap_or_else(|error| panic!("{label}: {error}"))
                        .object_code,
                );
                assert_symbol(
                    &elf,
                    "mv_helper",
                    STB_GLOBAL,
                    STT_FUNC,
                    stv(merged_visibility),
                    true,
                );
            }
        }
        let elf = parse_elf(
            &compiler(LINUX, OptLevel::O0, false)
                .compile(&defining)
                .expect("the definition alone")
                .object_code,
        );
        assert_symbol(&elf, "mv_helper", STB_GLOBAL, STT_FUNC, stv(defined), true);
    }
}

// =============================================================================
// Compiler::compile: hidden and protected DATA declarations (L02-P6)
// =============================================================================

/// Data DECLARATIONS (imports) a module only references, all `u64` words:
/// `(name, trust-ir text linkage, visibility, thread-local)`.
/// `dd_avail_hidden` is `AvailableExternally` with an initializer (2989)
/// that is never emitted.
const DATA_DECLARATIONS: [(&str, &str, Visibility, bool); 9] = [
    ("dd_default", "external", Visibility::Default, false),
    ("dd_protected", "external", Visibility::Protected, false),
    ("dd_hidden", "external", Visibility::Hidden, false),
    (
        "dd_avail_hidden",
        "available_externally",
        Visibility::Hidden,
        false,
    ),
    ("dw_default", "external_weak", Visibility::Default, false),
    (
        "dw_protected",
        "external_weak",
        Visibility::Protected,
        false,
    ),
    ("dw_hidden", "external_weak", Visibility::Hidden, false),
    ("dt_protected", "external", Visibility::Protected, true),
    ("dt_hidden", "external", Visibility::Hidden, true),
];

/// `.trust_ir` text of a module that declares `rows` and, for each word `w`,
/// defines `load_w() -> u64`, `addr_w() -> ptr` and (for a strong one)
/// `store_w(u64)`, each through `global_addr`.
fn data_declaration_text(module: &str, rows: &[(&str, &str, Visibility, bool)]) -> String {
    let mut text = format!(
        "module \"{module}\"\nfuncty.0 = () -> (u64)\nfuncty.1 = () -> (ptr)\n\
         functy.2 = (u64) -> ()\n"
    );
    for (name, linkage, visibility, thread_local) in rows {
        let tls = if *thread_local {
            " tls(general_dynamic)"
        } else {
            ""
        };
        let initializer = if *linkage == "available_externally" {
            " = 2989"
        } else {
            ""
        };
        text.push_str(&format!(
            "global {linkage}{tls} mut visibility({visibility}) @{name} u64{initializer}\n"
        ));
    }
    for (index, (name, linkage, ..)) in rows.iter().enumerate() {
        text.push_str(&format!(
            "fn @load_{name}(functy.0) {{\nbb0:\n    %0 = global_addr @global.{index}\n    \
             %1 = load u64, ptr %0\n    ret %1\n}}\n\
             fn @addr_{name}(functy.1) {{\nbb0:\n    %0 = global_addr @global.{index}\n    \
             ret %0\n}}\n"
        ));
        if *linkage != "external_weak" {
            text.push_str(&format!(
                "fn @store_{name}(functy.2) {{\nbb0(%0: u64):\n    \
                 %1 = global_addr @global.{index}\n    store u64 %0, ptr %1\n    ret\n}}\n"
            ));
        }
    }
    text
}

/// The data-declaration module, parsed from [`data_declaration_text`] (the
/// `visibility(...)` spelling of each global round-trips).
fn data_declaration_module(rows: &[(&str, &str, Visibility, bool)]) -> Module {
    let module = parse_linux(&data_declaration_text("data_declarations", rows));
    for ((name, _, visibility, _), global) in rows.iter().zip(&module.globals) {
        assert_eq!(
            (global.name.as_str(), global.visibility),
            (*name, *visibility)
        );
    }
    module
}

/// The relocation kinds an object names data declaration `name` with: the
/// GOT pair for every word under every model; a TLS descriptor under `pic`
/// and initial-exec under `static`/`pie` for a thread-local.
fn expected_data_declaration_kinds(
    thread_local: bool,
    model: trust_cg_codegen::RelocationModel,
) -> BTreeSet<u32> {
    if !thread_local {
        BTreeSet::from([R_AARCH64_ADR_GOT_PAGE, R_AARCH64_LD64_GOT_LO12_NC])
    } else if model == trust_cg_codegen::RelocationModel::Pic {
        BTreeSet::from(R_AARCH64_TLSDESC)
    } else {
        BTreeSet::from([
            R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21,
            R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC,
        ])
    }
}

/// `Compiler::compile` spells a hidden or protected DATA declaration on its
/// undefined symbol and addresses it through the GOT (L02-P6), under
/// `static`, `pie` and `pic`, O0-O3, sequential and parallel: an
/// initializer-less `External` import, an `AvailableExternally` one with an
/// initializer (never emitted), `ExternalWeak` references and thread-local
/// imports, each default, hidden or protected. The undefined symbol is
/// `STB_GLOBAL` (`STB_WEAK` for `ExternalWeak`) with its `STV_*`, `STT_TLS`
/// for a thread-local, and every relocation naming a word is the GOT pair
/// (never a PC-relative page: the name may be a GNU IFUNC function); a
/// thread-local takes the model's TLS access.
#[test]
fn compiler_spells_data_declaration_visibility_and_addresses_it_through_the_got() {
    let module = data_declaration_module(&DATA_DECLARATIONS);
    for model in RELOCATION_MODELS {
        for opt_level in OPT_LEVELS {
            for parallel in [false, true] {
                let label = format!("{model} {opt_level:?} parallel={parallel}");
                let object = local_binding_compiler(LINUX, opt_level, model, parallel)
                    .compile(&module)
                    .unwrap_or_else(|error| panic!("{label}: {error}"))
                    .object_code;
                let elf = parse_elf(&object);
                for (name, linkage, visibility, thread_local) in DATA_DECLARATIONS {
                    assert_symbol(
                        &elf,
                        name,
                        if linkage == "external_weak" {
                            STB_WEAK
                        } else {
                            STB_GLOBAL
                        },
                        if thread_local { STT_TLS } else { STT_NOTYPE },
                        stv(visibility),
                        false,
                    );
                    let kinds: BTreeSet<u32> = elf
                        .relocs
                        .iter()
                        .filter(|reloc| reloc.symbol == name)
                        .map(|reloc| reloc.kind)
                        .collect();
                    assert_eq!(
                        kinds,
                        expected_data_declaration_kinds(thread_local, model),
                        "{label}: `{name}` ({linkage} {visibility})"
                    );
                }
            }
        }
    }
}

/// The ELF emitters' own checks on a data import's visibility, through the
/// Pipeline API. A GOT reference to a strong or weak import, default,
/// hidden or protected, emits under every model and spells the visibility
/// on the undefined symbol. A PC-relative page reference to a weak or a
/// non-default import is refused under every model, with its reason (a weak
/// one must read 0 when absent; a stated visibility names a symbol that may
/// be a GNU IFUNC function); a default strong one is refused under `pic`
/// only. A non-default import named like a function the object defines is
/// refused, and Mach-O refuses any non-default import.
#[test]
#[allow(clippy::result_large_err)] // Test helper returns the compiler's own error type unchanged.
fn pipeline_data_import_visibility_reads_the_shared_predicate() {
    for relocation_model in RELOCATION_MODELS {
        let pipeline = Pipeline::new(PipelineConfig {
            target_triple: LINUX.to_owned(),
            relocation_model,
            ..PipelineConfig::default()
        });
        for weak in [false, true] {
            for visibility in VISIBILITIES {
                let symbol = format!("data_{}_{visibility}", if weak { "weak" } else { "strong" });
                let label = format!("{relocation_model} {symbol}");
                let globals = [ObjectGlobal {
                    visibility,
                    ..import(&symbol, weak)
                }];
                let emit = |function: LirFunction| {
                    let (functions, _) = prepare(&pipeline, &[function]);
                    pipeline
                        .compile_module_emission_with_symbol_linkage(
                            &functions,
                            &globals,
                            &[],
                            &ModuleSymbolLinkage::default(),
                        )
                        .map(|emission| emission.into_emission().object)
                };
                let elf = parse_elf(
                    &emit(returns_got_address("getter", &symbol))
                        .unwrap_or_else(|error| panic!("{label}: the GOT form emits: {error}")),
                );
                assert_symbol(
                    &elf,
                    &symbol,
                    if weak { STB_WEAK } else { STB_GLOBAL },
                    STT_NOTYPE,
                    stv(visibility),
                    false,
                );
                let direct = emit(returns_direct_address("getter", &symbol));
                let reason = if weak {
                    Some(format!("addresses `{symbol}`, a weak undefined symbol"))
                } else if visibility != Visibility::Default {
                    Some(format!(
                        "addresses `{symbol}`, a data import (visibility {visibility}), \
                         PC-relatively"
                    ))
                } else if relocation_model == trust_cg_codegen::RelocationModel::Pic {
                    Some(format!("addresses `{symbol}`, an undefined symbol"))
                } else {
                    None
                };
                match (reason, direct) {
                    (Some(reason), Err(error)) => {
                        let error = error.to_string();
                        assert!(
                            error.contains(&reason)
                                && (weak
                                    || visibility == Visibility::Default
                                    || error.contains("GNU IFUNC")),
                            "{label}: {error}"
                        );
                    }
                    (None, Ok(_)) => {}
                    (reason, result) => panic!(
                        "{label}: expected {reason:?}, got {:?}",
                        result.map(|_| "an object")
                    ),
                }
            }
        }
    }

    let linux = pipeline(LINUX, OptLevel::O0);
    let (functions, _) = prepare(
        &linux,
        &[
            returns_got_address("getter", "data_hidden"),
            returns_constant("data_hidden_twin", 1),
        ],
    );
    let hidden = |name: &str| ObjectGlobal {
        visibility: Visibility::Hidden,
        ..import(name, false)
    };
    let error = linux
        .compile_module_emission_with_symbol_linkage(
            &functions,
            &[hidden("data_hidden_twin")],
            &[],
            &ModuleSymbolLinkage::default(),
        )
        .expect_err("a hidden import named like a defined function")
        .to_string();
    assert!(
        error.contains("also defined as a function in this object"),
        "{error}"
    );

    let darwin = pipeline(DARWIN, OptLevel::O0);
    let (functions, _) = prepare(&darwin, &[returns_got_address("getter", "data_hidden")]);
    let error = darwin
        .compile_module_emission_with_symbol_linkage(
            &functions,
            &[hidden("data_hidden")],
            &[],
            &ModuleSymbolLinkage::default(),
        )
        .expect_err("Mach-O spells no undefined data visibility")
        .to_string();
    assert!(
        error.contains("`data_hidden` is an import with visibility `hidden`")
            && error.contains("only the ELF emitters"),
        "{error}"
    );
    darwin
        .compile_module_emission_with_symbol_linkage(
            &functions,
            &[import("data_hidden", false)],
            &[],
            &ModuleSymbolLinkage::default(),
        )
        .expect("the default-visibility Mach-O import");
}

/// A data import's visibility that no emitter spells is refused through
/// `Compiler::compile` by name: on Mach-O, x86-64 and RISC-V objects and by
/// the JIT, for a hidden and a protected import. An `Internal`/`Private`
/// thread-local import stays refused on AArch64 ELF too.
#[test]
fn data_import_visibility_the_emitters_cannot_spell_is_refused_by_name() {
    for visibility in [Visibility::Hidden, Visibility::Protected] {
        let rows = [("dr_word", "external", visibility, false)];
        let mut module = data_declaration_module(&rows);
        module.target_info = None;
        for triple in [
            "aarch64-apple-darwin",
            "x86_64-unknown-linux-gnu",
            "x86_64-apple-darwin",
            "riscv64-unknown-linux-gnu",
        ] {
            let target_spec = TargetSpec::parse(triple).expect("triple");
            let error = Compiler::new_for_target_spec(
                CompilerConfig {
                    target: target_spec.architecture,
                    opt_level: OptLevel::O0,
                    parallel: false,
                    ..Default::default()
                },
                target_spec,
            )
            .with_codegen_license(permit_unlicensed())
            .compile(&module)
            .map(|_| ())
            .expect_err("import visibility must be refused")
            .to_string();
            assert!(
                error.contains(&format!(
                    "global `dr_word` is a cross-object import with visibility `{visibility}`"
                )),
                "{triple} {visibility}: {error}"
            );
        }
        #[cfg(target_arch = "aarch64")]
        {
            let error = match Compiler::new(CompilerConfig::default())
                .with_codegen_license(permit_unlicensed())
                .compile_module_to_jit(&module, &std::collections::HashMap::new())
            {
                Ok(_) => panic!("{visibility}: the JIT must refuse import visibility"),
                Err(error) => error.to_string(),
            };
            assert!(
                error.contains("global `dr_word` is a cross-object import with visibility"),
                "JIT {visibility}: {error}"
            );
        }
    }
    for linkage in ["internal", "private"] {
        let module = parse_linux(&format!(
            "module \"local_tls_import\"\nfuncty.0 = () -> (u64)\n\
             global {linkage} tls(general_dynamic) mut visibility(hidden) @dr_tls u64\n\
             fn @load_dr_tls(functy.0) {{\nbb0:\n    %0 = global_addr @global.0\n    \
             %1 = load u64, ptr %0\n    ret %1\n}}\n"
        ));
        let error = compiler(LINUX, OptLevel::O0, false)
            .compile(&module)
            .map(|_| ())
            .expect_err("a module-local thread-local import's visibility")
            .to_string();
        assert!(
            error.contains("global `dr_tls` is a cross-object import with visibility `hidden`"),
            "{linkage}: {error}"
        );
    }
}

/// `merge_modules` gives a merged GLOBAL the most constraining visibility any
/// input states for its name, as it does a function (L02-P6): a hidden or
/// protected data import in one input restricts the definition another input
/// supplies, whatever the definition's own visibility (a hidden import of a
/// protected definition is hidden), in either input order. The merged `pic`
/// object defines the word with that visibility and, because a hidden or
/// protected definition is not preemptible, addresses it PC-relatively, never
/// through the GOT. A default import leaves a default definition default and
/// GOT-addressed.
#[test]
fn merged_data_import_visibility_restricts_the_definition() {
    for defined in VISIBILITIES {
        let provider = parse_linux(&format!(
            "module \"provider\"\nfuncty.0 = () -> (u64)\n\
             global external mut visibility({defined}) @mdv_word u64 = 5\n\
             fn @provider_load(functy.0) {{\nbb0:\n    %0 = global_addr @global.0\n    \
             %1 = load u64, ptr %0\n    ret %1\n}}\n"
        ));
        for declared in VISIBILITIES {
            let visibility = most_constraining(declared, defined);
            let consumer = parse_linux(&data_declaration_text(
                "consumer",
                &[("mdv_word", "external", declared, false)],
            ));
            for provider_first in [false, true] {
                let ordered = if provider_first {
                    [provider.clone(), consumer.clone()]
                } else {
                    [consumer.clone(), provider.clone()]
                };
                let label = format!(
                    "declared {declared} defined {defined} provider_first={provider_first}"
                );
                let merged = trust_cg_codegen::module_merge::merge_modules(&ordered)
                    .unwrap_or_else(|error| panic!("{label}: {error}"));
                let word = merged
                    .globals
                    .iter()
                    .find(|global| global.name == "mdv_word")
                    .expect("merged word");
                assert!(word.initializer.is_some(), "{label}: the definition wins");
                assert_eq!(word.visibility, visibility, "{label}");
                for opt_level in OPT_LEVELS {
                    let elf = parse_elf(
                        &local_binding_compiler(
                            LINUX,
                            opt_level,
                            trust_cg_codegen::RelocationModel::Pic,
                            false,
                        )
                        .compile(&merged)
                        .unwrap_or_else(|error| panic!("{label} {opt_level:?}: {error}"))
                        .object_code,
                    );
                    assert_symbol(
                        &elf,
                        "mdv_word",
                        STB_GLOBAL,
                        STT_OBJECT,
                        stv(visibility),
                        true,
                    );
                    let got = elf.relocs.iter().any(|reloc| {
                        reloc.symbol == "mdv_word"
                            && [R_AARCH64_ADR_GOT_PAGE, R_AARCH64_LD64_GOT_LO12_NC]
                                .contains(&reloc.kind)
                    });
                    assert_eq!(
                        got,
                        visibility == Visibility::Default,
                        "{label} {opt_level:?}: GOT-addressed exactly when preemptible"
                    );
                }
            }
        }
    }
}

// =============================================================================
// L02-P6 closure audit 5: merges that hold no definition or two identical
// ones, and the `SymbolAddr` and global-address-stub forms of data addresses
// =============================================================================
//
// The fifth closure audit (at `159f53415`) found seven visibility mutants no
// floor target killed. The rows below and their native twins kill them; the
// native row `data_symbol_and_stub_addresses_bind_like_global_addr_in_a_
// shared_object` lists each mutant's edit and what killed it.

/// The ordered visibility pairs a two-input merge of one name is run with in
/// a shared object: each pair of distinct visibilities in both orders. The
/// merged visibility does not depend on the order; a merge that kept the
/// first or the last input's visibility is right in one order only. Only the
/// Linux-native shared-object row reads it, so it carries that row's cfg (off
/// it, `-D warnings` refuses the target as dead code).
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
const VISIBILITY_PAIRS: [(Visibility, Visibility); 6] = [
    (Visibility::Default, Visibility::Hidden),
    (Visibility::Hidden, Visibility::Default),
    (Visibility::Default, Visibility::Protected),
    (Visibility::Protected, Visibility::Default),
    (Visibility::Protected, Visibility::Hidden),
    (Visibility::Hidden, Visibility::Protected),
];

/// The data definitions of the audit-5 merge rows that every input states
/// byte for byte, so a merge takes its identical-definition branch: `(name,
/// read-only linkage, value)`, one per linkage the merge deduplicates.
const MERGE_UNIT_DEFINITIONS: [(&str, &str, u64); 4] = [
    ("mu_odr", "linkonce_odr", 17),
    ("mu_weak_const", "weak", 18),
    ("mu_lo", "linkonce", 19),
    ("mu_wodr", "weak_odr", 20),
];

/// `.trust_ir` text of input `tag` of the audit-5 merge rows. Every name it
/// uses is stated with `visibility`, and no input defines one differently:
///
/// * `mu_fn` is a function DECLARATION: `<tag>_call_mu_fn` calls it and
///   `<tag>_addr_mu_fn` takes its `SymbolAddr`;
/// * `mu_word` is a data import, read by `<tag>_load_mu_word`;
/// * each of [`MERGE_UNIT_DEFINITIONS`] is a read-only data definition,
///   read through the address `<tag>_addr_<name>` takes with `global_addr`
///   (no optimization folds an address as it may fold a load of
///   one-definition-rule data).
///
/// `merge_modules` refuses `external_weak` and `available_externally`
/// names in any input, so these are the declarations a merge can hold.
fn merge_unit_text(tag: &str, visibility: Visibility) -> String {
    let mut text = format!(
        "module \"mu_{tag}\"\nfuncty.0 = () -> (u64)\nfuncty.1 = () -> (ptr)\n\
         global external mut visibility({visibility}) @mu_word u64\n"
    );
    for (name, linkage, value) in MERGE_UNIT_DEFINITIONS {
        text.push_str(&format!(
            "global {linkage} visibility({visibility}) @{name} u64 = {value}\n"
        ));
    }
    text.push_str(&format!(
        "external fn @mu_fn(functy.0) {{\n    ; #visibility: {visibility}\n}}\n\
         fn @{tag}_call_mu_fn(functy.0) {{\nbb0:\n    %0 = call @func.0()\n    ret %0\n}}\n\
         fn @{tag}_addr_mu_fn(functy.1) {{\nbb0:\n    %0 = const ptr symaddr<mu_fn>\n    \
         ret %0\n}}\n\
         fn @{tag}_load_mu_word(functy.0) {{\nbb0:\n    %0 = global_addr @global.0\n    \
         %1 = load u64, ptr %0\n    ret %1\n}}\n"
    ));
    for (index, (name, ..)) in MERGE_UNIT_DEFINITIONS.iter().enumerate() {
        text.push_str(&format!(
            "fn @{tag}_addr_{name}(functy.1) {{\nbb0:\n    %0 = global_addr @global.{}\n    \
             ret %0\n}}\n",
            index + 1
        ));
    }
    text
}

/// The names of the audit-5 merge rows with the ELF symbol a merged object
/// must give each: `(name, binding, type, defined)`; the visibility is the
/// most constraining one the inputs state.
const MERGE_UNIT_SYMBOLS: [(&str, u8, u8, bool); 6] = [
    ("mu_fn", STB_GLOBAL, STT_NOTYPE, false),
    ("mu_word", STB_GLOBAL, STT_NOTYPE, false),
    ("mu_odr", STB_WEAK, STT_OBJECT, true),
    ("mu_weak_const", STB_WEAK, STT_OBJECT, true),
    ("mu_lo", STB_WEAK, STT_OBJECT, true),
    ("mu_wodr", STB_WEAK, STT_OBJECT, true),
];

/// L02-P6 closure audit 5: `merge_modules` gives a name the most
/// constraining visibility its inputs state when NO input defines it (two
/// declarations of a function, two imports of a word) and when every input
/// defines it identically (a read-only `linkonce_odr`, `weak`, `linkonce`
/// and `weak_odr` word, which the merge deduplicates), for every ordered
/// pair of visibilities, as the static linker would under separate
/// compilation. The merged module keeps each name once (the function without
/// a body, the import without an initializer); the merged object, under
/// `static`, `pie` and `pic` at O0-O3, spells the visibility on each
/// undefined symbol and on the definitions, addresses the declarations
/// through the GOT, and addresses the definitions through the GOT exactly
/// when they are default under `pic`. The earlier merge rows always merged a
/// definition with declarations of it, so a merge that set the visibility
/// only on a bodied function, or skipped it for identical inputs, passed
/// every floor target. An input with an `external_weak` or
/// `available_externally` function or global is refused by name.
#[test]
fn merged_declarations_and_identical_definitions_take_the_most_constraining_visibility() {
    for first in VISIBILITIES {
        for second in VISIBILITIES {
            let visibility = most_constraining(first, second);
            let label = format!("{first} then {second}");
            let merged = trust_cg_codegen::module_merge::merge_modules(&[
                parse_linux(&merge_unit_text("a", first)),
                parse_linux(&merge_unit_text("b", second)),
            ])
            .unwrap_or_else(|error| panic!("{label}: {error}"));
            let functions: Vec<&Function> = merged
                .functions
                .iter()
                .filter(|function| function.name == "mu_fn")
                .collect();
            assert!(
                matches!(functions.as_slice(), [function]
                    if function.blocks.is_empty() && function.visibility == visibility),
                "{label}: `mu_fn` is one {visibility} declaration: {functions:?}"
            );
            for (name, _, _, defined) in &MERGE_UNIT_SYMBOLS[1..] {
                let globals: Vec<&Global> = merged
                    .globals
                    .iter()
                    .filter(|global| global.name == *name)
                    .collect();
                assert!(
                    matches!(globals.as_slice(), [global]
                        if global.initializer.is_some() == *defined
                            && global.visibility == visibility),
                    "{label}: `{name}` is one {visibility} global: {globals:?}"
                );
            }
            for model in RELOCATION_MODELS {
                for opt_level in OPT_LEVELS {
                    let label = format!("{label} {model} {opt_level:?}");
                    let elf = parse_elf(
                        &local_binding_compiler(LINUX, opt_level, model, false)
                            .compile(&merged)
                            .unwrap_or_else(|error| panic!("{label}: {error}"))
                            .object_code,
                    );
                    for (name, bind, kind, defined) in MERGE_UNIT_SYMBOLS {
                        assert_symbol(&elf, name, bind, kind, stv(visibility), defined);
                        let kinds: BTreeSet<u32> = elf
                            .relocs_in(".text")
                            .iter()
                            .filter(|reloc| reloc.symbol == name)
                            .map(|reloc| {
                                if branch_kinds().contains(&reloc.kind) {
                                    u32::MAX
                                } else {
                                    reloc.kind
                                }
                            })
                            .collect();
                        let got = !defined
                            || (model == trust_cg_codegen::RelocationModel::Pic
                                && visibility == Visibility::Default);
                        let mut expected = if got {
                            BTreeSet::from([R_AARCH64_ADR_GOT_PAGE, R_AARCH64_LD64_GOT_LO12_NC])
                        } else {
                            BTreeSet::from([R_AARCH64_ADR_PREL_PG_HI21, R_AARCH64_ADD_ABS_LO12_NC])
                        };
                        if name == "mu_fn" {
                            expected.insert(u32::MAX);
                        }
                        assert_eq!(kinds, expected, "{label}: `{name}`");
                    }
                }
            }
        }
    }
    // The other two declaration linkages have no merge rule: an input that
    // states one, beside a unit above, is refused by name.
    for (linkage, declaration) in [
        (
            "external_weak",
            "external_weak fn @mu_other(functy.0) {\n    ; #visibility: hidden\n}\n",
        ),
        (
            "available_externally",
            "available_externally fn @mu_other(functy.0) {\n    ; #visibility: hidden\n\
             bb0:\n    %0 = const u64 3\n    ret %0\n}\n",
        ),
        (
            "external_weak",
            "global external_weak mut visibility(hidden) @mu_other u64\n",
        ),
        (
            "available_externally",
            "global available_externally visibility(hidden) @mu_other u64 = 3\n",
        ),
    ] {
        let other = parse_linux(&format!(
            "module \"mu_other\"\nfuncty.0 = () -> (u64)\n{declaration}"
        ));
        let error = trust_cg_codegen::module_merge::merge_modules(&[
            parse_linux(&merge_unit_text("a", Visibility::Hidden)),
            other,
        ])
        .map(|_| ())
        .expect_err(&format!(
            "an input with {linkage} `mu_other` must be refused"
        ));
        assert!(
            error.contains(&format!("`mu_other` has linkage `{linkage}`")),
            "{linkage}: {error}"
        );
    }
}

/// The linkages a bodyless function declaration states; a bodyless function
/// with a definition linkage is refused before the function catalog, as
/// `[TCG-DECLARATION-LINKAGE]`.
const DECLARATION_LINKAGES: [Linkage; 2] = [Linkage::External, Linkage::ExternalWeak];

/// The gate authority the repeated-declaration rows stamp on every body, so
/// the binary containers decode the module (a v41+ blob must license each
/// body), and that their compiler recognizes.
const REPEATED_DECLARATION_AUTHORITY: &str = "tcg-test-repeated-declarations";

/// A module declaring `rd_ext` twice without a body, as `first` then
/// `second` (`(linkage, visibility)`), with a direct call through each
/// declaration's own `FuncId` and a `SymbolAddr` of the name.
fn repeated_declaration_text(
    first: (Linkage, Visibility),
    second: (Linkage, Visibility),
) -> String {
    let mut text = String::from(
        "module \"repeated_declarations\"\nfuncty.0 = () -> (u64)\nfuncty.1 = () -> (ptr)\n",
    );
    for (linkage, visibility) in [first, second] {
        text.push_str(&format!(
            "{linkage} fn @rd_ext(functy.0) {{\n    ; #visibility: {visibility}\n}}\n"
        ));
    }
    text.push_str(
        "fn @rd_call_first(functy.0) {\nbb0:\n    %0 = call @func.0()\n    ret %0\n}\n\
         fn @rd_call_second(functy.0) {\nbb0:\n    %0 = call @func.1()\n    ret %0\n}\n\
         fn @rd_addr(functy.1) {\nbb0:\n    %0 = const ptr symaddr<rd_ext>\n    ret %0\n}\n",
    );
    text
}

/// `module` as each entry that hands `Compiler::compile` a whole module from
/// bytes decodes it: the `.trust_ir` text printer and parser, the bare
/// `TRUST_IR` binary container and trust-cg's `tMBC` envelope (both through
/// `pipeline::decode_binary`), and the JSON wire format
/// (`pipeline::load_module_from_bytes`). Every body is first stamped with
/// [`REPEATED_DECLARATION_AUTHORITY`]; each decoded module gets the Linux
/// target back.
fn whole_module_entries(module: &Module) -> Vec<(&'static str, Module)> {
    let mut stamped = module.clone();
    stamped.target_info = None;
    for function in &mut stamped.functions {
        if function.has_body() {
            function.body_gate = Some(trust_ir::BodyGate::gated(
                REPEATED_DECLARATION_AUTHORITY.to_string(),
            ));
        }
    }
    let text = trust_cg_codegen::pipeline::encode_trust_ir_text(&stamped);
    let binary =
        trust_ir::binary::serialize_module(&stamped).expect("serialize_module: test fixture");
    let tmbc = trust_cg_codegen::pipeline::encode_tmbc(&stamped)
        .unwrap_or_else(|error| panic!("the module has a tMBC image: {error}"));
    let json = serde_json::to_string(&stamped).expect("the module serializes as JSON");
    [
        (
            "text",
            trust_cg_codegen::pipeline::parse_trust_ir_text(&text),
        ),
        ("binary", trust_cg_codegen::pipeline::decode_binary(&binary)),
        ("tmbc", trust_cg_codegen::pipeline::decode_binary(&tmbc)),
        (
            "json",
            trust_cg_codegen::pipeline::load_module_from_bytes(json.as_bytes()),
        ),
    ]
    .into_iter()
    .map(|(entry, decoded)| {
        let mut decoded = decoded.unwrap_or_else(|error| panic!("{entry}: {error}"));
        decoded.target_info = Some(linux_target_info());
        (entry, decoded)
    })
    .collect()
}

/// A sequential AArch64 ELF compiler that recognizes
/// [`REPEATED_DECLARATION_AUTHORITY`].
fn repeated_declaration_compiler(
    opt_level: OptLevel,
    relocation_model: trust_cg_codegen::RelocationModel,
) -> Compiler {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            parallel: false,
            relocation_model,
            ..Default::default()
        },
        TargetSpec::parse(LINUX).expect("triple"),
    )
    .with_codegen_license(
        trust_cg_codegen::CodegenLicensePolicy::default()
            .with_recognized_authority(REPEATED_DECLARATION_AUTHORITY),
    )
}

/// The `.text` relocation kinds naming `symbol`, every direct branch counted
/// as `u32::MAX`.
fn text_relocation_kinds(elf: &Elf, symbol: &str) -> BTreeSet<u32> {
    elf.relocs_in(".text")
        .iter()
        .filter(|reloc| reloc.symbol == symbol)
        .map(|reloc| {
            if branch_kinds().contains(&reloc.kind) {
                u32::MAX
            } else {
                reloc.kind
            }
        })
        .collect()
}

/// L02-P6 closure audit 6, as WS7.3 ingestion admission leaves it (LD-54):
/// one module may not declare one symbol twice. trust-ir's validator reports
/// `DuplicateFunctionSymbol` for any repeated name (since v41 a function's
/// name is its link-time symbol), and since WS7.3 every ingestion entry
/// refuses what trust-ir refuses before the backend's function catalog is
/// reached. For every ordered pair of (`external` or `external_weak`,
/// visibility) declarations, the identical ones included, the module reaches
/// `Compiler::compile` from the text parser, both binary containers and JSON
/// with both declarations intact, and is refused under `static`, `pie` and
/// `pic` at O0-O3 by that finding, naming `rd_ext`.
///
/// The function catalog's comparison (`compatible_external_declarations` in
/// trust-cg-lower) still guards the adapter's diagnostic entries, which take
/// a module without admission (the shrink-only `DIAGNOSTIC_BASELINE` of
/// `tests/ingest_admission.rs`). Through the AArch64 ELF one
/// (`translate_module_for_arch_with_tls_and_stats_with_license_and_weak_references`
/// under `ObjectSymbolPolicy::AARCH64_ELF_MODULE`, which admits
/// `external_weak` declarations and function visibility, so the catalog
/// decides), every decoded pair that differs, and two identical
/// `external_weak` ones (outside the rule, which admits only `external`), is
/// refused as an ambiguous symbol whose two bodyless declarations disagree;
/// the three identical `external` pairs translate. The audit's mutant K19
/// dropped visibility from that comparison: every pair of distinct
/// visibilities then compiled and the object spelled the declaration it met
/// last (hidden then protected gave `GLOBAL PROTECTED UND`, exported from a
/// linked shared library). K20 admitted `external_weak` beside `external`:
/// the pair compiled to a `WEAK` undefined reference, so a shared library
/// linked under `-z defs` without the definition and its call died with
/// SIGSEGV. Since WS7.3 neither reaches `Compiler::compile`; this leg fails
/// under each.
///
/// `merge_modules` folds such a module into one an ingestion entry accepts.
/// It keys functions by name, so it treats one input's repeated declarations
/// as it treats two inputs' declarations: for `external` pairs it keeps one
/// declaration with the most constraining visibility, in either order
/// (LD-06), and the folded module compiles from every entry, under every
/// model and level, to one undefined `STB_GLOBAL` `rd_ext` with that
/// visibility, GOT-addressed and called directly, so the refusals above come
/// from the repeated declaration and not from the module's shape. An input
/// with an `external_weak` function is refused by name.
#[test]
fn repeated_declarations_that_disagree_about_visibility_or_linkage_are_refused_on_every_entry() {
    let license = trust_cg_codegen::CodegenLicensePolicy::default()
        .with_recognized_authority(REPEATED_DECLARATION_AUTHORITY);
    let (mut refused, mut catalog_refused, mut catalog_shared, mut compiled) = (0, 0, 0, 0);
    for first_linkage in DECLARATION_LINKAGES {
        for first_visibility in VISIBILITIES {
            for second_linkage in DECLARATION_LINKAGES {
                for second_visibility in VISIBILITIES {
                    let first = (first_linkage, first_visibility);
                    let second = (second_linkage, second_visibility);
                    let pair = format!(
                        "{first_linkage} {first_visibility} then {second_linkage} \
                         {second_visibility}"
                    );
                    let shared = first == second && first_linkage == Linkage::External;
                    let module = parse_linux(&repeated_declaration_text(first, second));
                    for (entry, decoded) in whole_module_entries(&module) {
                        let declarations: Vec<(Linkage, Visibility, bool)> = decoded
                            .functions
                            .iter()
                            .filter(|function| function.name == "rd_ext")
                            .map(|function| {
                                (
                                    function.linkage,
                                    function.visibility,
                                    function.blocks.is_empty(),
                                )
                            })
                            .collect();
                        assert_eq!(
                            declarations,
                            [
                                (first_linkage, first_visibility, true),
                                (second_linkage, second_visibility, true)
                            ],
                            "{pair} {entry}: the entry keeps both declarations"
                        );
                        for model in RELOCATION_MODELS {
                            for opt_level in OPT_LEVELS {
                                let label = format!("{pair} {entry} {model} {opt_level:?}");
                                let error = match repeated_declaration_compiler(opt_level, model)
                                    .compile(&decoded)
                                {
                                    Ok(_) => panic!(
                                        "{label}: a module declaring `rd_ext` twice compiled"
                                    ),
                                    Err(error) => error.to_string(),
                                };
                                assert!(
                                    error.contains("DuplicateFunctionSymbol")
                                        && error.contains("share the link symbol \"rd_ext\""),
                                    "{label}: {error}"
                                );
                                refused += 1;
                            }
                        }
                        let label = format!("{pair} {entry} catalog");
                        let translated = trust_cg_lower::translate_module_for_arch_with_tls_and_stats_with_license_and_weak_references(
                            &decoded,
                            trust_cg_lower::GuardCarrierArch::AArch64,
                            trust_cg_lower::TlsDialect::ElfLocalExec,
                            &license,
                            trust_cg_lower::ObjectSymbolPolicy::AARCH64_ELF_MODULE,
                        );
                        if shared {
                            translated.unwrap_or_else(|error| panic!("{label}: {error}"));
                            catalog_shared += 1;
                            continue;
                        }
                        let error = match translated {
                            Ok(_) => panic!(
                                "{label}: two declarations of `rd_ext` that disagree translated"
                            ),
                            Err(error) => error.to_string(),
                        };
                        assert!(
                            error.contains("ambiguous lowered symbol name \"rd_ext\"")
                                && error.contains("two bodyless declarations"),
                            "{label}: {error}"
                        );
                        catalog_refused += 1;
                    }

                    let merged = trust_cg_codegen::module_merge::merge_modules(&[module]);
                    if first_linkage == Linkage::ExternalWeak
                        || second_linkage == Linkage::ExternalWeak
                    {
                        let error = merged
                            .map(|_| ())
                            .expect_err(&format!("{pair}: merge must refuse `external_weak`"));
                        assert!(
                            error.contains("`rd_ext` has linkage `external_weak`"),
                            "{pair}: {error}"
                        );
                        continue;
                    }
                    let merged = merged.unwrap_or_else(|error| panic!("{pair}: {error}"));
                    let visibility = most_constraining(first_visibility, second_visibility);
                    let declarations: Vec<&Function> = merged
                        .functions
                        .iter()
                        .filter(|function| function.name == "rd_ext")
                        .collect();
                    assert!(
                        matches!(declarations.as_slice(), [function]
                            if function.blocks.is_empty()
                                && function.linkage == Linkage::External
                                && function.visibility == visibility),
                        "{pair}: merged into one {visibility} declaration: {declarations:?}"
                    );
                    for (entry, decoded) in whole_module_entries(&merged) {
                        for model in RELOCATION_MODELS {
                            for opt_level in OPT_LEVELS {
                                let label = format!("{pair} merged {entry} {model} {opt_level:?}");
                                let elf = parse_elf(
                                    &repeated_declaration_compiler(opt_level, model)
                                        .compile(&decoded)
                                        .unwrap_or_else(|error| panic!("{label}: {error}"))
                                        .object_code,
                                );
                                assert_symbol(
                                    &elf,
                                    "rd_ext",
                                    STB_GLOBAL,
                                    STT_NOTYPE,
                                    stv(visibility),
                                    false,
                                );
                                assert_eq!(
                                    text_relocation_kinds(&elf, "rd_ext"),
                                    BTreeSet::from([
                                        R_AARCH64_ADR_GOT_PAGE,
                                        R_AARCH64_LD64_GOT_LO12_NC,
                                        u32::MAX
                                    ]),
                                    "{label}"
                                );
                                compiled += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    // Every one of the 36 ordered pairs is refused through 4 entries x 3
    // models x 4 levels. Through the diagnostic entry the catalog refuses the
    // 30 pairs that differ and the 3 identical `external_weak` pairs (33),
    // and translates the 3 identical `external` pairs, from each of the 4
    // entries. The 9 `external` pairs fold, and each folded module compiles
    // through 4 entries x 3 models x 4 levels.
    assert_eq!(
        (refused, catalog_refused, catalog_shared, compiled),
        (36 * 4 * 3 * 4, 33 * 4, 3 * 4, 9 * 4 * 3 * 4)
    );
}

/// The data definitions of the audit-5 address-form rows, each a
/// `[u64 x 2]` holding `(value, value + 1)`: `(name, trust-ir linkage,
/// mutable, visibility, value)` for a strong mutable (`.data`), a strong
/// read-only (`.rodata`), a `weak` mutable and a `linkonce_odr` read-only
/// (COMDAT) definition, each default, hidden and protected.
fn address_form_rows() -> Vec<(String, &'static str, bool, Visibility, u64)> {
    let kinds = [
        ("rw", "external", true),
        ("ro", "external", false),
        ("wk", "weak", true),
        ("lo", "linkonce_odr", false),
    ];
    let mut rows = Vec::new();
    for (kind, linkage, mutable) in kinds {
        for visibility in VISIBILITIES {
            let value = 0x100 * (rows.len() as u64 + 1);
            rows.push((
                format!("af_{kind}_{visibility}"),
                linkage,
                mutable,
                visibility,
                value,
            ));
        }
    }
    rows
}

/// An address form of the audit-5 address-form rows: each names the data
/// definition's symbol a different way, and all of them must read the shared
/// address predicate `Inst::GlobalAddr` reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AddressForm {
    /// `ga_<name>`: `Inst::GlobalAddr`, the reference form.
    GlobalAddr,
    /// `sym_<name>` and `symoff_<name>`: a function-body
    /// `Constant::SymbolAddr` with addend 0 and 8.
    SymbolAddr,
    /// `stub_<name>` and `stuboff_<name>`: the importer's in-band
    /// global-address stub (`0xFADE` tag, global index, byte offset 0 and
    /// 8) in a `ptr` constant.
    Stub,
}

impl AddressForm {
    const ALL: [Self; 3] = [Self::GlobalAddr, Self::SymbolAddr, Self::Stub];
}

/// The importer's in-band address of byte `offset` of module global `index`
/// (see `global_stub.rs`): bits 63-48 `0xFADE`, 47-32 the index, 31-0 the
/// offset.
fn global_address_stub(index: usize, offset: u32) -> i128 {
    (0xFADE_i128 << 48) | ((index as i128) << 32) | i128::from(offset)
}

/// The audit-5 address-form module: [`address_form_rows`] and, for each, the
/// accessors of every form in `forms`, each `() -> ptr`.
fn address_form_module(forms: &[AddressForm]) -> Module {
    let rows = address_form_rows();
    let mut text =
        String::from("module \"address_forms\"\ntype ty.0 = u64\nfuncty.0 = () -> (ptr)\n");
    for (name, linkage, mutable, visibility, value) in &rows {
        let mutable = if *mutable { " mut" } else { "" };
        text.push_str(&format!(
            "global {linkage}{mutable} visibility({visibility}) @{name} [ty.0 x 2] = \
             array[{value}, {}]\n",
            value + 1
        ));
    }
    for (index, (name, ..)) in rows.iter().enumerate() {
        if forms.contains(&AddressForm::GlobalAddr) {
            text.push_str(&format!(
                "fn @ga_{name}(functy.0) {{\nbb0:\n    %0 = global_addr @global.{index}\n    \
                 ret %0\n}}\n"
            ));
        }
        if forms.contains(&AddressForm::SymbolAddr) {
            text.push_str(&format!(
                "fn @sym_{name}(functy.0) {{\nbb0:\n    %0 = const ptr symaddr<{name}>\n    \
                 ret %0\n}}\n\
                 fn @symoff_{name}(functy.0) {{\nbb0:\n    %0 = const ptr symaddr<{name} + 8>\n    \
                 ret %0\n}}\n"
            ));
        }
    }
    let mut module = parse_linux(&text);
    if forms.contains(&AddressForm::Stub) {
        let returns_ptr = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::Ptr],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        for (index, (name, ..)) in rows.iter().enumerate() {
            for (prefix, offset) in [("stub", 0), ("stuboff", 8)] {
                push_accessor(
                    &mut module,
                    format!("{prefix}_{name}"),
                    returns_ptr,
                    vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::Ptr,
                            value: Constant::Int(global_address_stub(index, offset)),
                        })
                        .with_result(ValueId::new(0)),
                        InstrNode::new(Inst::Return {
                            values: vec![ValueId::new(0)],
                        }),
                    ],
                );
            }
        }
    }
    module
}

/// L02-P6 closure audit 5: the function-body `SymbolAddr` of a data
/// definition and the importer's global-address stub read the shared address
/// predicate that `Inst::GlobalAddr` reads, with and without an offset. Under
/// `static`, `pie` and `pic` at O0-O3, each form of a strong, read-only,
/// `weak` and `linkonce_odr` word, default, hidden and protected, compiled on
/// its own, names the word only with the GOT pair when it is default under
/// `pic`, and only with a PC-relative page and low-12 add otherwise; the
/// symbol keeps its visibility. Only `aarch64_elf_symbol_binding`'s table
/// addressed data through `GlobalAddr`, so an address form that ignored
/// visibility (GOT-addressing a hidden or protected word) passed every floor
/// target and was caught by a `trust-cg-lower` unit test alone.
#[test]
fn data_symbol_and_stub_addresses_read_the_shared_predicate() {
    for form in AddressForm::ALL {
        let module = address_form_module(&[form]);
        for model in RELOCATION_MODELS {
            for opt_level in OPT_LEVELS {
                let label = format!("{form:?} {model} {opt_level:?}");
                let elf = parse_elf(
                    &local_binding_compiler(LINUX, opt_level, model, false)
                        .compile(&module)
                        .unwrap_or_else(|error| panic!("{label}: {error}"))
                        .object_code,
                );
                for (name, linkage, _, visibility, _) in address_form_rows() {
                    let bind = if linkage == "external" {
                        STB_GLOBAL
                    } else {
                        STB_WEAK
                    };
                    assert_symbol(&elf, &name, bind, STT_OBJECT, stv(visibility), true);
                    let kinds: BTreeSet<u32> = elf
                        .relocs_in(".text")
                        .iter()
                        .filter(|reloc| reloc.symbol == name)
                        .map(|reloc| reloc.kind)
                        .collect();
                    let expected = if model == trust_cg_codegen::RelocationModel::Pic
                        && visibility == Visibility::Default
                    {
                        BTreeSet::from([R_AARCH64_ADR_GOT_PAGE, R_AARCH64_LD64_GOT_LO12_NC])
                    } else {
                        BTreeSet::from([R_AARCH64_ADR_PREL_PG_HI21, R_AARCH64_ADD_ABS_LO12_NC])
                    };
                    assert_eq!(kinds, expected, "{label}: `{name}`");
                }
            }
        }
    }
}

/// A weak or COMDAT definition row: `(name, trust-ir linkage, visibility,
/// explicit section, initializer)` ([`WEAK_DATA_ROWS`], [`WEAK_TLS_ROWS`]).
type WeakDefinitionRow = (
    &'static str,
    &'static str,
    Visibility,
    Option<&'static str>,
    u64,
);

/// Weak and COMDAT `u64` data DEFINITIONS with each visibility:
/// `(name, trust-ir linkage, visibility, explicit section, initializer)`.
/// `weak` is an ordinary `STB_WEAK` definition in `.data`, `.bss` (a zero
/// initializer) or an explicit section; `linkonce`, `linkonce_odr` and
/// `weak_odr` each get their own `.data.<name>` or `.bss.<name>` section
/// inside a `GRP_COMDAT` group whose signature is the symbol. Every
/// initializer but the zero ones is distinct.
const WEAK_DATA_ROWS: [WeakDefinitionRow; 15] = [
    ("wd_default", "weak", Visibility::Default, None, 0x1001),
    ("wd_hidden", "weak", Visibility::Hidden, None, 0x1002),
    ("wd_protected", "weak", Visibility::Protected, None, 0x1003),
    ("wd_bss_hidden", "weak", Visibility::Hidden, None, 0),
    (
        "wd_sec_hidden",
        "weak",
        Visibility::Hidden,
        Some(".data.wd_sec"),
        0x1005,
    ),
    ("lo_default", "linkonce", Visibility::Default, None, 0x2001),
    ("lo_hidden", "linkonce", Visibility::Hidden, None, 0x2002),
    (
        "lo_protected",
        "linkonce",
        Visibility::Protected,
        None,
        0x2003,
    ),
    (
        "lodr_default",
        "linkonce_odr",
        Visibility::Default,
        None,
        0x3001,
    ),
    (
        "lodr_hidden",
        "linkonce_odr",
        Visibility::Hidden,
        None,
        0x3002,
    ),
    (
        "lodr_protected",
        "linkonce_odr",
        Visibility::Protected,
        None,
        0x3003,
    ),
    (
        "lodr_bss_hidden",
        "linkonce_odr",
        Visibility::Hidden,
        None,
        0,
    ),
    (
        "wodr_default",
        "weak_odr",
        Visibility::Default,
        None,
        0x4001,
    ),
    ("wodr_hidden", "weak_odr", Visibility::Hidden, None, 0x4002),
    (
        "wodr_protected",
        "weak_odr",
        Visibility::Protected,
        None,
        0x4003,
    ),
];

/// The trust-ir text module `module` of `rows`, each a `u64` definition
/// (thread-local, general-dynamic, when `tls`) with a default-visibility
/// `load_<name>` (its value) and `addr_<name>` (its address) accessor,
/// parsed for the Linux target.
fn weak_definition_module(module: &str, rows: &[WeakDefinitionRow], tls: bool) -> Module {
    let mut text = format!("module \"{module}\"\nfuncty.0 = () -> (u64)\nfuncty.1 = () -> (ptr)\n");
    let tls = if tls { " tls(general_dynamic)" } else { "" };
    for (name, linkage, visibility, section, value) in rows {
        let section = section
            .map(|section| format!(" section(\"{section}\")"))
            .unwrap_or_default();
        text.push_str(&format!(
            "global {linkage}{tls} mut visibility({visibility}){section} @{name} u64 = {value}\n"
        ));
    }
    for (index, (name, ..)) in rows.iter().enumerate() {
        text.push_str(&format!(
            "fn @load_{name}(functy.0) {{\nbb0:\n    %0 = global_addr @global.{index}\n    \
             %1 = load u64, ptr %0\n    ret %1\n}}\n\
             fn @addr_{name}(functy.1) {{\nbb0:\n    %0 = global_addr @global.{index}\n    \
             ret %0\n}}\n"
        ));
    }
    parse_linux(&text)
}

/// The trust-ir text module of [`WEAK_DATA_ROWS`] ([`weak_definition_module`]).
fn weak_data_module() -> Module {
    weak_definition_module("weak_data_visibility", &WEAK_DATA_ROWS, false)
}

/// The section `Compiler::compile` places a weak or COMDAT definition in
/// (`.data`/`.bss`, or `.tdata`/`.tbss` when `tls`, by its initializer; a
/// COMDAT one in `<base>.<name>`; else its explicit section), and whether
/// that section is a COMDAT group member.
fn weak_definition_section(
    name: &str,
    linkage: &str,
    section: Option<&str>,
    value: u64,
    tls: bool,
) -> (String, bool) {
    let comdat = linkage != "weak";
    let base = match (tls, value == 0) {
        (false, true) => ".bss",
        (false, false) => ".data",
        (true, true) => ".tbss",
        (true, false) => ".tdata",
    };
    let placed = match (section, comdat) {
        (Some(section), _) => section.to_string(),
        (None, true) => format!("{base}.{name}"),
        (None, false) => base.to_string(),
    };
    (placed, comdat)
}

/// Weak and COMDAT data definitions ([`WEAK_DATA_ROWS`]) carry their
/// trust-ir visibility onto the object symbol under every relocation model,
/// O0-O3 (L02-P6 closure audit 2): each is `STB_WEAK` `STT_OBJECT` with its
/// own `STV_*`, eight bytes in the section [`weak_definition_section`] names, and
/// that section is a member of exactly the `GRP_COMDAT` group its symbol
/// signs for a COMDAT linkage and of none for plain `weak`. Under `pic`
/// every reference to a hidden or protected one is PC-relative and never a
/// GOT relocation, while the default ones come from the GOT; the executable
/// models address all of them PC-relatively. At the audited base, spelling
/// these symbols `STV_DEFAULT` passed every suite.
#[test]
fn weak_and_comdat_data_definitions_spell_their_visibility() {
    let module = weak_data_module();
    for model in RELOCATION_MODELS {
        for opt_level in OPT_LEVELS {
            let label = format!("{model} {opt_level:?}");
            let bytes = local_binding_compiler(LINUX, opt_level, model, false)
                .compile(&module)
                .unwrap_or_else(|error| panic!("{label}: {error}"))
                .object_code;
            let elf = parse_elf(&bytes);
            let groups = comdat_groups(&bytes);
            for (name, linkage, visibility, section, value) in WEAK_DATA_ROWS {
                let label = format!("{label} `{name}` ({linkage} {visibility})");
                let symbol = elf.symbol(name).clone();
                assert_eq!(
                    (symbol.bind, symbol.kind, symbol.visibility, symbol.size),
                    (STB_WEAK, STT_OBJECT, stv(visibility), 8),
                    "{label}: {symbol:?}"
                );
                assert_ne!(symbol.shndx, 0, "{label} is defined");
                let (expected, comdat) =
                    weak_definition_section(name, linkage, section, value, false);
                let placed = &elf.sections[usize::from(symbol.shndx)].0;
                assert_eq!(placed, &expected, "{label}: its section");
                let signatures: Vec<&str> = groups
                    .iter()
                    .filter(|(_, members)| members.contains(placed))
                    .map(|(signature, _)| signature.as_str())
                    .collect();
                if comdat {
                    assert_eq!(signatures, [name], "{label}: its own COMDAT group");
                } else {
                    assert!(signatures.is_empty(), "{label}: {signatures:?}");
                }
                let kinds: BTreeSet<u32> = elf
                    .relocs
                    .iter()
                    .filter(|reloc| reloc.symbol == name)
                    .map(|reloc| reloc.kind)
                    .collect();
                let preemptible = model == trust_cg_codegen::RelocationModel::Pic
                    && visibility == Visibility::Default;
                assert_eq!(
                    (
                        kinds.contains(&R_AARCH64_ADR_GOT_PAGE),
                        kinds.contains(&R_AARCH64_LD64_GOT_LO12_NC),
                        kinds.contains(&R_AARCH64_ADR_PREL_PG_HI21),
                    ),
                    (preemptible, preemptible, !preemptible),
                    "{label}: GOT-addressed exactly when preemptible: {kinds:?}"
                );
            }
        }
    }
}

/// Weak and COMDAT THREAD-LOCAL `u64` definitions with each visibility, as
/// [`WEAK_DATA_ROWS`] (L02-P6 closure audit 2, verifier round): `weak`
/// default, hidden and protected in `.tdata`, a weak protected one in
/// `.tbss` (a zero initializer) and one in an explicit `.tdata.tw_sec`, and
/// `linkonce`, `linkonce_odr` and `weak_odr` default, hidden and protected
/// in their own `.tdata.<name>` COMDAT groups, plus a zero `linkonce_odr`
/// hidden one in `.tbss.<name>`. Every initializer but the zero ones is
/// distinct. None is anchored: a weak definition may be replaced at static
/// link, so its TLS descriptors name its own symbol.
const WEAK_TLS_ROWS: [WeakDefinitionRow; 15] = [
    ("tw_default", "weak", Visibility::Default, None, 21),
    ("tw_hidden", "weak", Visibility::Hidden, None, 22),
    ("tw_protected", "weak", Visibility::Protected, None, 23),
    ("tw_bss_protected", "weak", Visibility::Protected, None, 0),
    (
        "tw_sec_protected",
        "weak",
        Visibility::Protected,
        Some(".tdata.tw_sec"),
        25,
    ),
    ("tc_lo_default", "linkonce", Visibility::Default, None, 31),
    ("tc_lo_hidden", "linkonce", Visibility::Hidden, None, 32),
    (
        "tc_lo_protected",
        "linkonce",
        Visibility::Protected,
        None,
        33,
    ),
    (
        "tc_lodr_default",
        "linkonce_odr",
        Visibility::Default,
        None,
        41,
    ),
    (
        "tc_lodr_hidden",
        "linkonce_odr",
        Visibility::Hidden,
        None,
        42,
    ),
    (
        "tc_lodr_protected",
        "linkonce_odr",
        Visibility::Protected,
        None,
        43,
    ),
    (
        "tc_lodr_bss_hidden",
        "linkonce_odr",
        Visibility::Hidden,
        None,
        0,
    ),
    ("tc_wodr_default", "weak_odr", Visibility::Default, None, 51),
    ("tc_wodr_hidden", "weak_odr", Visibility::Hidden, None, 52),
    (
        "tc_wodr_protected",
        "weak_odr",
        Visibility::Protected,
        None,
        53,
    ),
];

/// The trust-ir text module of [`WEAK_TLS_ROWS`] ([`weak_definition_module`]).
fn weak_tls_module() -> Module {
    weak_definition_module("weak_tls_visibility", &WEAK_TLS_ROWS, true)
}

/// Weak and COMDAT thread-local definitions ([`WEAK_TLS_ROWS`]) carry their
/// trust-ir visibility onto the object symbol under every relocation model,
/// O0-O3 (L02-P6 closure audit 2, verifier round): each is `STB_WEAK`
/// `STT_TLS` with its own `STV_*`, eight bytes in the section
/// [`weak_definition_section`] names, a member of exactly the `GRP_COMDAT`
/// group its symbol signs for a COMDAT linkage and of none for plain `weak`.
/// No `.Ltls.` anchor is emitted: under `pic` the four TLS descriptor
/// relocations name each variable's own symbol, and the executable models
/// use the local-exec pair. The verifier found that spelling a COMDAT
/// thread-local `STV_DEFAULT`, or a weak protected one `STV_HIDDEN`, passed
/// every suite.
#[test]
fn weak_and_comdat_thread_locals_spell_their_visibility() {
    let module = weak_tls_module();
    for model in RELOCATION_MODELS {
        for opt_level in OPT_LEVELS {
            let label = format!("{model} {opt_level:?}");
            let bytes = local_binding_compiler(LINUX, opt_level, model, false)
                .compile(&module)
                .unwrap_or_else(|error| panic!("{label}: {error}"))
                .object_code;
            let elf = parse_elf(&bytes);
            let groups = comdat_groups(&bytes);
            let anchors: Vec<&str> = elf
                .symbols
                .iter()
                .filter(|symbol| symbol.name.starts_with(".Ltls."))
                .map(|symbol| symbol.name.as_str())
                .collect();
            assert!(
                anchors.is_empty(),
                "{label}: no weak definition is anchored: {anchors:?}"
            );
            for (name, linkage, visibility, section, value) in WEAK_TLS_ROWS {
                let label = format!("{label} `{name}` ({linkage} {visibility})");
                let symbol = elf.symbol(name).clone();
                assert_eq!(
                    (symbol.bind, symbol.kind, symbol.visibility, symbol.size),
                    (STB_WEAK, STT_TLS, stv(visibility), 8),
                    "{label}: {symbol:?}"
                );
                assert_ne!(symbol.shndx, 0, "{label} is defined");
                let (expected, comdat) =
                    weak_definition_section(name, linkage, section, value, true);
                let placed = &elf.sections[usize::from(symbol.shndx)].0;
                assert_eq!(placed, &expected, "{label}: its section");
                let signatures: Vec<&str> = groups
                    .iter()
                    .filter(|(_, members)| members.contains(placed))
                    .map(|(signature, _)| signature.as_str())
                    .collect();
                if comdat {
                    assert_eq!(signatures, [name], "{label}: its own COMDAT group");
                } else {
                    assert!(signatures.is_empty(), "{label}: {signatures:?}");
                }
                let kinds: BTreeSet<u32> = elf
                    .relocs
                    .iter()
                    .filter(|reloc| reloc.symbol == name)
                    .map(|reloc| reloc.kind)
                    .collect();
                let expected_kinds = if model == trust_cg_codegen::RelocationModel::Pic {
                    BTreeSet::from(R_AARCH64_TLSDESC)
                } else {
                    BTreeSet::from([
                        R_AARCH64_TLSLE_ADD_TPREL_HI12,
                        R_AARCH64_TLSLE_ADD_TPREL_LO12_NC,
                    ])
                };
                assert_eq!(kinds, expected_kinds, "{label}: named by its own symbol");
            }
        }
    }
}

/// One TLS anchor row, in the column order of `TLS_ANCHOR_ROWS`.
type TlsAnchorRow = (
    &'static str,
    &'static str,
    &'static str,
    Option<&'static str>,
    Option<u64>,
);

/// The thread-locals of [`hidden_tls_descriptor_references_name_an_object_local_anchor`]:
/// `(name, trust-ir linkage, visibility, explicit section, initializer)`.
/// The three strong hidden definitions each sit at a NONZERO offset of a
/// different section: `.tdata` (after `ta_default`), `.tbss` (after
/// `ta_zero`) and the explicit `.tdata.ta_sec` (after `ta_sec0`).
const TLS_ANCHOR_ROWS: [TlsAnchorRow; 10] = [
    ("ta_default", "external", "default", None, Some(4)),
    ("ta_hidden", "external", "hidden", None, Some(1)),
    ("ta_weak_hidden", "weak", "hidden", None, Some(2)),
    ("ta_protected", "external", "protected", None, Some(3)),
    ("ta_local", "internal", "default", None, Some(5)),
    ("ta_hidden_import", "external", "hidden", None, None),
    ("ta_zero", "external", "default", None, Some(0)),
    ("ta_bss_hidden", "external", "hidden", None, Some(0)),
    (
        "ta_sec0",
        "external",
        "default",
        Some(".tdata.ta_sec"),
        Some(6),
    ),
    (
        "ta_sec_hidden",
        "external",
        "hidden",
        Some(".tdata.ta_sec"),
        Some(7),
    ),
];

/// The rows of [`TLS_ANCHOR_ROWS`] that get an anchor, with the section each
/// lies in.
const TLS_ANCHORED: [(&str, &str); 3] = [
    ("ta_hidden", ".tdata"),
    ("ta_bss_hidden", ".tbss"),
    ("ta_sec_hidden", ".tdata.ta_sec"),
];

/// Under `pic` the TLS descriptor relocations of a STRONG HIDDEN
/// thread-local definition name an object-local `STT_TLS` anchor at the
/// definition's own section, offset and size (as GCC's section anchor), so no
/// linker lists the variable in a shared object's `.dynsym` (L02-P6). The
/// anchored definitions lie at nonzero offsets of `.tdata`, `.tbss` and an
/// explicit TLS section, and each anchor must name exactly its variable's
/// section and offset. The global hidden symbol stays for other objects. A
/// weak hidden definition (which a strong one elsewhere may replace), a
/// protected, a default and an Internal one, and a hidden declaration, keep
/// being named by their own symbols, and so does every executable-model
/// (local-exec, initial-exec) reference. O0-O3, sequential and parallel.
#[test]
fn hidden_tls_descriptor_references_name_an_object_local_anchor() {
    let mut text = String::from("module \"tls_anchor\"\nfuncty.0 = () -> (u64)\n");
    for (name, linkage, visibility, section, initializer) in TLS_ANCHOR_ROWS {
        let section = section
            .map(|section| format!(" section(\"{section}\")"))
            .unwrap_or_default();
        let initializer = initializer
            .map(|value| format!(" = {value}"))
            .unwrap_or_default();
        text.push_str(&format!(
            "global {linkage} tls(general_dynamic) mut visibility({visibility}){section} \
             @{name} u64{initializer}\n"
        ));
    }
    for index in 0..TLS_ANCHOR_ROWS.len() {
        text.push_str(&format!(
            "fn @load_{index}(functy.0) {{\nbb0:\n    %0 = global_addr @global.{index}\n    \
             %1 = load u64, ptr %0\n    ret %1\n}}\n"
        ));
    }
    let module = parse_linux(&text);
    for model in RELOCATION_MODELS {
        for opt_level in OPT_LEVELS {
            for parallel in [false, true] {
                let label = format!("{model} {opt_level:?} parallel={parallel}");
                let elf = parse_elf(
                    &local_binding_compiler(LINUX, opt_level, model, parallel)
                        .compile(&module)
                        .unwrap_or_else(|error| panic!("{label}: {error}"))
                        .object_code,
                );
                let pic = model == trust_cg_codegen::RelocationModel::Pic;
                let anchors: Vec<&Sym> = elf
                    .symbols
                    .iter()
                    .filter(|symbol| symbol.name.starts_with(".Ltls."))
                    .collect();
                if pic {
                    assert_eq!(
                        anchors.len(),
                        TLS_ANCHORED.len(),
                        "{label}: one anchor per strong hidden definition: {anchors:?}"
                    );
                    for (name, section) in TLS_ANCHORED {
                        let variable = elf.symbol(name).clone();
                        assert_eq!(
                            (variable.bind, variable.kind, variable.visibility),
                            (STB_GLOBAL, STT_TLS, STV_HIDDEN),
                            "{label}: {variable:?}"
                        );
                        assert_eq!(
                            elf.sections[usize::from(variable.shndx)].0,
                            section,
                            "{label}: `{name}`'s section"
                        );
                        assert_ne!(variable.value, 0, "{label}: `{name}` at a nonzero offset");
                        let anchor = elf.symbol(&format!(".Ltls.{name}")).clone();
                        assert_eq!(
                            (anchor.bind, anchor.kind, anchor.visibility),
                            (STB_LOCAL, STT_TLS, STV_DEFAULT),
                            "{label}: {anchor:?}"
                        );
                        assert_eq!(
                            (anchor.shndx, anchor.value, anchor.size),
                            (variable.shndx, variable.value, variable.size),
                            "{label}: `{name}`'s anchor names its section and offset"
                        );
                    }
                } else {
                    assert!(anchors.is_empty(), "{label}: {anchors:?}");
                }
                for (name, ..) in TLS_ANCHOR_ROWS {
                    let kinds: BTreeSet<u32> = elf
                        .relocs
                        .iter()
                        .filter(|reloc| reloc.symbol == name)
                        .map(|reloc| reloc.kind)
                        .collect();
                    let anchored: BTreeSet<u32> = elf
                        .relocs
                        .iter()
                        .filter(|reloc| reloc.symbol == format!(".Ltls.{name}"))
                        .map(|reloc| reloc.kind)
                        .collect();
                    let expected = if pic {
                        BTreeSet::from(R_AARCH64_TLSDESC)
                    } else if name == "ta_hidden_import" {
                        BTreeSet::from([
                            R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21,
                            R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC,
                        ])
                    } else {
                        BTreeSet::from([
                            R_AARCH64_TLSLE_ADD_TPREL_HI12,
                            R_AARCH64_TLSLE_ADD_TPREL_LO12_NC,
                        ])
                    };
                    if pic && TLS_ANCHORED.iter().any(|(anchored, _)| *anchored == name) {
                        assert!(kinds.is_empty(), "{label}: `{name}` named: {kinds:?}");
                        assert_eq!(anchored, expected, "{label}: `{name}` through its anchor");
                    } else {
                        assert!(anchored.is_empty(), "{label}: `{name}`: {anchored:?}");
                        assert_eq!(kinds, expected, "{label}: `{name}`");
                    }
                }
            }
        }
    }
}

/// The thread-local DEFINITIONS the Pipeline-route anchor rows hand to
/// `Pipeline::compile_module_with_globals`: `(name, visibility, weak, value)`.
/// `pt_hidden` sits after `pt_default` in `.tdata` and `pt_bss_hidden` after
/// `pt_zero` in `.tbss`, each at a nonzero offset.
const PIPELINE_TLS_ROWS: [(&str, Visibility, bool, u64); 6] = [
    ("pt_default", Visibility::Default, false, 3),
    ("pt_hidden", Visibility::Hidden, false, 7),
    ("pt_weak_hidden", Visibility::Hidden, true, 8),
    ("pt_protected", Visibility::Protected, false, 9),
    ("pt_zero", Visibility::Default, false, 0),
    ("pt_bss_hidden", Visibility::Hidden, false, 0),
];

/// The rows of [`PIPELINE_TLS_ROWS`] that get an anchor, with their sections.
const PIPELINE_TLS_ANCHORED: [(&str, &str); 2] =
    [("pt_hidden", ".tdata"), ("pt_bss_hidden", ".tbss")];

/// A `() -> ptr` LIR function returning this thread's address of
/// thread-local `symbol` through a general-dynamic `TlsRef`.
fn returns_tls_address(name: &str, symbol: &str) -> LirFunction {
    lir_function(
        name,
        vec![
            Instruction {
                opcode: Opcode::TlsRef {
                    name: symbol.to_owned(),
                    model: trust_cg_ir::TlsModel::GeneralDynamic,
                    local_exec_offset: None,
                },
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

/// [`PIPELINE_TLS_ROWS`] as `pic` Pipeline input at `opt_level`: one
/// `addr_<name>` per row, prepared, with its frame layout, and the
/// thread-local `ObjectGlobal`s.
fn pipeline_tls_input(opt_level: OptLevel) -> (Pipeline, Prepared, Vec<ObjectGlobal>) {
    let pipeline = Pipeline::new(PipelineConfig {
        target_triple: LINUX.to_owned(),
        opt_level,
        relocation_model: trust_cg_codegen::RelocationModel::Pic,
        ..PipelineConfig::default()
    });
    let functions: Vec<LirFunction> = PIPELINE_TLS_ROWS
        .iter()
        .map(|(name, ..)| returns_tls_address(&format!("addr_{name}"), name))
        .collect();
    let prepared = prepare(&pipeline, &functions);
    let globals = PIPELINE_TLS_ROWS
        .iter()
        .map(|&(name, visibility, is_weak, value)| ObjectGlobal {
            is_thread_local: true,
            is_weak,
            visibility,
            ..object_global(name, value.to_le_bytes().to_vec())
        })
        .collect();
    (pipeline, prepared, globals)
}

/// The same hidden-TLS anchoring through the public Pipeline API (L02-P6
/// closure audit 2): `Pipeline::compile_module_with_globals` under `pic`,
/// O0-O3, with a general-dynamic `TlsRef` to each of [`PIPELINE_TLS_ROWS`].
/// Without frame layouts this reaches the layout-less ELF emitter (the
/// object has no `.eh_frame`); `compile_module_with_globals_and_layouts`
/// with every layout reaches the unwind emitter (`.eh_frame` present).
/// Both objects give each strong hidden definition an `STB_LOCAL` `STT_TLS`
/// `.Ltls.<name>` anchor at the variable's section, nonzero offset and size,
/// their four `R_AARCH64_TLSDESC_*` relocations name the anchor and never
/// the variable, and every other row (default, weak hidden, protected) is
/// named by its own symbol. The two emitters' `.text` relocations are equal
/// entry for entry. At the audited base, removing the layout-less emitter's
/// anchor passed every suite.
#[test]
fn pipeline_hidden_tls_descriptor_references_name_an_object_local_anchor() {
    for opt_level in OPT_LEVELS {
        let (pipeline, (functions, layouts), globals) = pipeline_tls_input(opt_level);
        let layout_less = pipeline
            .compile_module_with_globals(&functions, &globals)
            .unwrap_or_else(|error| panic!("{opt_level:?} layout-less: {error}"));
        let unwind = pipeline
            .compile_module_with_globals_and_layouts(&functions, &globals, &layouts)
            .unwrap_or_else(|error| panic!("{opt_level:?} unwind: {error}"));
        let mut text_relocations = Vec::new();
        for (route, bytes, unwind_tables) in [
            ("layout-less", &layout_less, false),
            ("unwind", &unwind, true),
        ] {
            let label = format!("{opt_level:?} {route}");
            let elf = parse_elf(bytes);
            assert_eq!(
                elf.sections
                    .iter()
                    .any(|(name, ..)| name.as_str() == ".eh_frame"),
                unwind_tables,
                "{label}: the emitter this route reaches"
            );
            let anchors: Vec<&str> = elf
                .symbols
                .iter()
                .filter(|symbol| symbol.name.starts_with(".Ltls."))
                .map(|symbol| symbol.name.as_str())
                .collect();
            assert_eq!(
                anchors.len(),
                PIPELINE_TLS_ANCHORED.len(),
                "{label}: one anchor per strong hidden definition: {anchors:?}"
            );
            for (name, section) in PIPELINE_TLS_ANCHORED {
                let variable = elf.symbol(name).clone();
                assert_eq!(
                    (variable.bind, variable.kind, variable.visibility),
                    (STB_GLOBAL, STT_TLS, STV_HIDDEN),
                    "{label}: {variable:?}"
                );
                assert_eq!(
                    elf.sections[usize::from(variable.shndx)].0,
                    section,
                    "{label}: `{name}`'s section"
                );
                assert_ne!(variable.value, 0, "{label}: `{name}` at a nonzero offset");
                let anchor = elf.symbol(&format!(".Ltls.{name}")).clone();
                assert_eq!(
                    (anchor.bind, anchor.kind, anchor.visibility),
                    (STB_LOCAL, STT_TLS, STV_DEFAULT),
                    "{label}: {anchor:?}"
                );
                assert_eq!(
                    (anchor.shndx, anchor.value, anchor.size),
                    (variable.shndx, variable.value, variable.size),
                    "{label}: `{name}`'s anchor names its section and offset"
                );
            }
            for (name, ..) in PIPELINE_TLS_ROWS {
                let kinds = |symbol: &str| -> BTreeSet<u32> {
                    elf.relocs
                        .iter()
                        .filter(|reloc| reloc.symbol == symbol)
                        .map(|reloc| reloc.kind)
                        .collect()
                };
                let (named, anchored) = (kinds(name), kinds(&format!(".Ltls.{name}")));
                if PIPELINE_TLS_ANCHORED
                    .iter()
                    .any(|(anchored, _)| *anchored == name)
                {
                    assert!(named.is_empty(), "{label}: `{name}` named: {named:?}");
                    assert_eq!(
                        anchored,
                        BTreeSet::from(R_AARCH64_TLSDESC),
                        "{label}: `{name}` through its anchor"
                    );
                } else {
                    assert!(anchored.is_empty(), "{label}: `{name}`: {anchored:?}");
                    assert_eq!(
                        named,
                        BTreeSet::from(R_AARCH64_TLSDESC),
                        "{label}: `{name}`"
                    );
                }
            }
            text_relocations.push(
                elf.relocs_in(".text")
                    .into_iter()
                    .cloned()
                    .collect::<Vec<_>>(),
            );
        }
        assert_eq!(
            text_relocations[0], text_relocations[1],
            "{opt_level:?}: both emitters relocate `.text` alike"
        );
    }
}

// =============================================================================
// L02-P6 closure audit 3: strong hidden and protected data definitions in
// every implicit section
// =============================================================================

/// A strong `External` `u64` or pointer data definition placed in one of the
/// implicit ELF sections: `(name, section, visibility, value, pointer
/// target)`. A row with a pointer target is an immutable `ptr` initialized
/// with `symaddr<target>`, and its `value` is the target's word.
type StrongDataRow = (
    &'static str,
    &'static str,
    Visibility,
    u64,
    Option<&'static str>,
);

/// Strong data definitions with each visibility in each implicit section
/// (L02-P6 closure audit 3): mutable nonzero words in `.data`, mutable zero
/// words in `.bss`, immutable words in `.rodata` and immutable pointers in
/// `.data.rel.ro`. The three `sd_rt_*` words are the pointers' hidden
/// `.rodata` targets, so no pointer's value depends on another row's
/// interposition. Every nonzero value is distinct. At the audited base, a
/// mutant spelling the strong `.bss`, `.rodata` or `.data.rel.ro` hidden or
/// protected definitions `STV_DEFAULT` passed every floor suite.
const STRONG_DATA_ROWS: [StrongDataRow; 15] = [
    (
        "sd_data_default",
        ".data",
        Visibility::Default,
        0x6001,
        None,
    ),
    ("sd_data_hidden", ".data", Visibility::Hidden, 0x6002, None),
    (
        "sd_data_protected",
        ".data",
        Visibility::Protected,
        0x6003,
        None,
    ),
    ("sd_bss_default", ".bss", Visibility::Default, 0, None),
    ("sd_bss_hidden", ".bss", Visibility::Hidden, 0, None),
    ("sd_bss_protected", ".bss", Visibility::Protected, 0, None),
    (
        "sd_ro_default",
        ".rodata",
        Visibility::Default,
        0x7001,
        None,
    ),
    ("sd_ro_hidden", ".rodata", Visibility::Hidden, 0x7002, None),
    (
        "sd_ro_protected",
        ".rodata",
        Visibility::Protected,
        0x7003,
        None,
    ),
    ("sd_rt_a", ".rodata", Visibility::Hidden, 0x8001, None),
    ("sd_rt_b", ".rodata", Visibility::Hidden, 0x8002, None),
    ("sd_rt_c", ".rodata", Visibility::Hidden, 0x8003, None),
    (
        "sd_rr_default",
        ".data.rel.ro",
        Visibility::Default,
        0x8001,
        Some("sd_rt_a"),
    ),
    (
        "sd_rr_hidden",
        ".data.rel.ro",
        Visibility::Hidden,
        0x8002,
        Some("sd_rt_b"),
    ),
    (
        "sd_rr_protected",
        ".data.rel.ro",
        Visibility::Protected,
        0x8003,
        Some("sd_rt_c"),
    ),
];

/// Whether a [`STRONG_DATA_ROWS`] section holds mutable definitions.
fn strong_data_is_mutable(section: &str) -> bool {
    matches!(section, ".data" | ".bss")
}

/// The functions of [`strong_data_module`]: `load_<name>` and `addr_<name>`
/// per row and `store_<name>` per mutable row (36, past the 32 the parallel
/// preparation and emission path needs).
const STRONG_DATA_FUNCTIONS: usize = 15 * 2 + 6;

/// The trust-ir text module of [`STRONG_DATA_ROWS`], each an `external`
/// definition (`mut` in `.data` and `.bss`) with a default-visibility
/// `load_<name>` (its value, a pointer for a pointer row) and `addr_<name>`
/// (its address), and `store_<name>` for a mutable one, parsed for the Linux
/// target.
fn strong_data_module() -> Module {
    let mut text = String::from(
        "module \"strong_data_visibility\"\nfuncty.0 = () -> (u64)\nfuncty.1 = () -> (ptr)\n\
         functy.2 = (u64) -> ()\n",
    );
    for (name, section, visibility, value, target) in STRONG_DATA_ROWS {
        let mutable = if strong_data_is_mutable(section) {
            " mut"
        } else {
            ""
        };
        let initializer = match target {
            Some(target) => format!("ptr = symaddr<{target}>"),
            None => format!("u64 = {value}"),
        };
        text.push_str(&format!(
            "global external{mutable} visibility({visibility}) @{name} {initializer}\n"
        ));
    }
    for (index, (name, section, _, _, target)) in STRONG_DATA_ROWS.iter().enumerate() {
        let (signature, ty) = if target.is_some() {
            (1, "ptr")
        } else {
            (0, "u64")
        };
        text.push_str(&format!(
            "fn @load_{name}(functy.{signature}) {{\nbb0:\n    %0 = global_addr @global.{index}\n    \
             %1 = load {ty}, ptr %0\n    ret %1\n}}\n\
             fn @addr_{name}(functy.1) {{\nbb0:\n    %0 = global_addr @global.{index}\n    \
             ret %0\n}}\n"
        ));
        if strong_data_is_mutable(section) {
            text.push_str(&format!(
                "fn @store_{name}(functy.2) {{\nbb0(%0: u64):\n    \
                 %1 = global_addr @global.{index}\n    store u64 %0, ptr %1\n    ret\n}}\n"
            ));
        }
    }
    let module = parse_linux(&text);
    assert_eq!(module.functions.len(), STRONG_DATA_FUNCTIONS);
    for ((name, section, visibility, ..), global) in STRONG_DATA_ROWS.iter().zip(&module.globals) {
        assert_eq!(
            (
                global.name.as_str(),
                global.linkage,
                global.visibility,
                global.mutable
            ),
            (
                *name,
                Linkage::External,
                *visibility,
                strong_data_is_mutable(section)
            ),
            "the text form spells `{name}`"
        );
    }
    module
}

/// Every mismatch between `elf` and [`STRONG_DATA_ROWS`] at the symbol and
/// section level: each row must be one `STB_GLOBAL` `STT_OBJECT` eight-byte
/// symbol with its own `STV_*`, defined in its implicit section at an
/// offset holding its initializer (`.bss` is `SHT_NOBITS`; a pointer row's
/// slot carries one `R_AARCH64_ABS64` naming its target), and no section of
/// a row may be a `GRP_COMDAT` member. Empty for a faithful object.
fn strong_data_mismatches(bytes: &[u8]) -> Vec<String> {
    const SHT_NOBITS: u32 = 8;
    let elf = parse_elf(bytes);
    let groups = comdat_groups(bytes);
    let mut mismatches = Vec::new();
    for (name, section, visibility, value, target) in STRONG_DATA_ROWS {
        let symbol = elf.symbol(name);
        if (symbol.bind, symbol.kind, symbol.visibility, symbol.size)
            != (STB_GLOBAL, STT_OBJECT, stv(visibility), 8)
            || symbol.shndx == 0
        {
            mismatches.push(format!("`{name}` symbol: {symbol:?}"));
            continue;
        }
        let (placed, sh_type, contents) = &elf.sections[usize::from(symbol.shndx)];
        if placed != section {
            mismatches.push(format!("`{name}` in {placed}, not {section}"));
            continue;
        }
        if groups.iter().any(|(_, members)| members.contains(placed)) {
            mismatches.push(format!("`{name}`'s {placed} is a COMDAT member"));
        }
        let offset = symbol.value as usize;
        match (section, target) {
            (".bss", _) => {
                if *sh_type != SHT_NOBITS {
                    mismatches.push(format!("`{name}`'s .bss is type {sh_type}"));
                }
            }
            (_, Some(target)) => {
                let slot: Vec<&Reloc> = elf
                    .relocs_in(section)
                    .into_iter()
                    .filter(|reloc| reloc.offset == symbol.value)
                    .collect();
                if !matches!(slot.as_slice(), [reloc]
                    if reloc.kind == R_AARCH64_ABS64 && reloc.symbol == target && reloc.addend == 0)
                {
                    mismatches.push(format!("`{name}`'s slot: {slot:?}"));
                }
            }
            _ => {
                if contents.get(offset..offset + 8) != Some(&value.to_le_bytes()[..]) {
                    mismatches.push(format!("`{name}`'s initializer at {offset:#x}"));
                }
            }
        }
    }
    mismatches
}

/// L02-P6 closure audit 3: strong (`External`) data definitions carry their
/// trust-ir visibility onto the object symbol in every implicit section
/// ([`STRONG_DATA_ROWS`]: `.data`, `.bss`, `.rodata`, `.data.rel.ro`)
/// through `Compiler::compile`, under every relocation model, O0-O3,
/// sequential and parallel (each row asserts from the compiler trace which
/// path produced its object). Every row is checked by
/// [`strong_data_mismatches`]; under `pic` every reference to a hidden or
/// protected definition is PC-relative and never a GOT relocation, while
/// the default ones come from the GOT, and the executable models address
/// all of them PC-relatively. The row checker refuses an object whose
/// `st_other` is mutated for one row of each section. At the audited base,
/// spelling the strong `.bss`, `.rodata` or `.data.rel.ro` hidden or
/// protected definitions `STV_DEFAULT` passed every floor suite.
#[test]
fn strong_data_definitions_spell_their_visibility_in_every_implicit_section() {
    let module = strong_data_module();
    for model in RELOCATION_MODELS {
        for opt_level in OPT_LEVELS {
            for parallel in [false, true] {
                let label = format!("{model} {opt_level:?} parallel={parallel}");
                let result = local_binding_compiler(LINUX, opt_level, model, parallel)
                    .compile(&module)
                    .unwrap_or_else(|error| panic!("{label}: {error}"));
                assert_emission_path(&result, parallel, STRONG_DATA_FUNCTIONS, &label);
                let bytes = result.object_code;
                let mismatches = strong_data_mismatches(&bytes);
                assert!(mismatches.is_empty(), "{label}: {mismatches:#?}");
                let elf = parse_elf(&bytes);
                for (name, _, visibility, ..) in STRONG_DATA_ROWS {
                    let kinds: BTreeSet<u32> = elf
                        .relocs
                        .iter()
                        .filter(|reloc| reloc.symbol == name && reloc.section.starts_with(".text"))
                        .map(|reloc| reloc.kind)
                        .collect();
                    let preemptible = model == trust_cg_codegen::RelocationModel::Pic
                        && visibility == Visibility::Default;
                    assert_eq!(
                        (
                            kinds.contains(&R_AARCH64_ADR_GOT_PAGE),
                            kinds.contains(&R_AARCH64_LD64_GOT_LO12_NC),
                            kinds.contains(&R_AARCH64_ADR_PREL_PG_HI21),
                        ),
                        (preemptible, preemptible, !preemptible),
                        "{label} `{name}` ({visibility}): GOT-addressed exactly when \
                         preemptible: {kinds:?}"
                    );
                }
                if (model, opt_level, parallel)
                    != (trust_cg_codegen::RelocationModel::Pic, OptLevel::O2, true)
                {
                    continue;
                }
                // Mutation controls: the checker names a row of each section
                // whose visibility is rewritten to default or hidden.
                for (name, to) in [
                    ("sd_data_hidden", STV_DEFAULT),
                    ("sd_bss_protected", STV_DEFAULT),
                    ("sd_ro_hidden", STV_DEFAULT),
                    ("sd_ro_protected", STV_DEFAULT),
                    ("sd_rr_hidden", STV_DEFAULT),
                    ("sd_rr_default", STV_HIDDEN),
                ] {
                    let mut mutated = bytes.clone();
                    let st_other = symbol_entry_offset(&mutated, name) + 5;
                    mutated[st_other] = (mutated[st_other] & !0x3) | to;
                    let mismatches = strong_data_mismatches(&mutated);
                    assert!(
                        mismatches.len() == 1 && mismatches[0].starts_with(&format!("`{name}`")),
                        "{label}: the checker must name mutated `{name}`: {mismatches:?}"
                    );
                }
            }
        }
    }
}

/// L02-P6 closure audit 3: the same strong definitions
/// ([`STRONG_DATA_ROWS`]) handed to the public Pipeline API as
/// `ObjectGlobal`s under `pic`, each with an `addr_<name>` that reads the GOT
/// for a default one (the emitter's `pic` backstop refuses a PC-relative
/// address of a preemptible definition) and is PC-relative otherwise.
/// `compile_module_with_globals` reaches the layout-less ELF emitter (no
/// `.eh_frame`) and `compile_module_with_globals_and_layouts` the unwind
/// emitter, O0-O3; both objects pass [`strong_data_mismatches`].
#[test]
fn pipeline_strong_data_definitions_spell_their_visibility_in_every_implicit_section() {
    let globals: Vec<ObjectGlobal> = STRONG_DATA_ROWS
        .iter()
        .map(|&(name, section, visibility, value, target)| {
            let (data, symbol_refs) = match target {
                Some(target) => (
                    vec![0; 8],
                    vec![GlobalSymbolRef {
                        offset: 0,
                        symbol: target.to_owned(),
                        addend: 0,
                    }],
                ),
                None => (value.to_le_bytes().to_vec(), vec![]),
            };
            ObjectGlobal {
                mutable: strong_data_is_mutable(section),
                symbol_refs,
                visibility,
                ..object_global(name, data)
            }
        })
        .collect();
    let functions: Vec<LirFunction> = STRONG_DATA_ROWS
        .iter()
        .map(|(name, _, visibility, ..)| {
            let accessor = format!("addr_{name}");
            if *visibility == Visibility::Default {
                returns_got_address(&accessor, name)
            } else {
                returns_direct_address(&accessor, name)
            }
        })
        .collect();
    for opt_level in OPT_LEVELS {
        let pipeline = Pipeline::new(PipelineConfig {
            target_triple: LINUX.to_owned(),
            opt_level,
            relocation_model: trust_cg_codegen::RelocationModel::Pic,
            ..PipelineConfig::default()
        });
        let (prepared, layouts) = prepare(&pipeline, &functions);
        let layout_less = pipeline
            .compile_module_with_globals(&prepared, &globals)
            .unwrap_or_else(|error| panic!("{opt_level:?} layout-less: {error}"));
        let unwind = pipeline
            .compile_module_with_globals_and_layouts(&prepared, &globals, &layouts)
            .unwrap_or_else(|error| panic!("{opt_level:?} unwind: {error}"));
        for (route, bytes, unwind_tables) in [
            ("layout-less", &layout_less, false),
            ("unwind", &unwind, true),
        ] {
            let label = format!("{opt_level:?} {route}");
            assert_eq!(
                parse_elf(bytes)
                    .sections
                    .iter()
                    .any(|(name, ..)| name.as_str() == ".eh_frame"),
                unwind_tables,
                "{label}: the emitter this route reaches"
            );
            let mismatches = strong_data_mismatches(bytes);
            assert!(mismatches.is_empty(), "{label}: {mismatches:#?}");
        }
    }
}

// =============================================================================
// Compiler::compile: references to module-local (Internal/Private) functions
// =============================================================================

const RELOCATION_MODELS: [trust_cg_codegen::RelocationModel; 3] = [
    trust_cg_codegen::RelocationModel::Static,
    trust_cg_codegen::RelocationModel::Pie,
    trust_cg_codegen::RelocationModel::Pic,
];

/// External filler definitions that lift a module-local binding module over
/// the parallel emitter's 32-item threshold.
const LOCAL_BINDING_PADDING: usize = 32;

/// Definitions of [`local_binding_module`] before its padding.
const LOCAL_BINDING_CORE_FUNCTIONS: usize = 9;

/// A module whose bodied `helper` (linkage `helper_linkage`) computes
/// `x + offset` and counts its calls in the Internal global `<tag>_count`.
/// The store keeps it out of the module inliner, so its direct calls stay
/// relocated calls at every optimization level. External entry points:
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
/// plus [`LOCAL_BINDING_PADDING`] External `<tag>_pad_<n>` fillers.
fn local_binding_module(tag: &str, helper_linkage: Linkage, offset: i128) -> Module {
    let mut module = Module::new(format!("module_local_binding_{tag}"));
    module.target_info = Some(linux_target_info());
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
    module.globals.push(Global {
        name: format!("{tag}_count"),
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
    module.globals.push(Global {
        name: format!("{tag}_slot"),
        ty: Ty::Ptr,
        mutable: true,
        initializer: Some(Constant::SymbolAddr {
            symbol: "helper".into(),
            addend: 0,
        }),
        linkage: Linkage::External,
        tls: None,
        align: Some(8),
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });
    let counter = GlobalId::new(0);
    let slot = GlobalId::new(1);
    let helper = FuncId::new(0);
    let value = |index: u32| ValueId::new(index);
    let node = |inst: Inst, result: u32| InstrNode::new(inst).with_result(value(result));
    let effect = |inst: Inst| InstrNode::new(inst);
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

    let helper_id = define(
        "helper".into(),
        unary,
        x(),
        vec![
            node(Inst::GlobalAddr { global: counter }, 1),
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
            effect(Inst::Store {
                ty: Ty::U64,
                ptr: value(1),
                value: value(4),
                volatile: false,
                align: Some(8),
            }),
            node(
                Inst::Const {
                    ty: Ty::U64,
                    value: Constant::Int(offset),
                },
                5,
            ),
            node(
                Inst::BinOp {
                    op: trust_ir::BinOp::Add,
                    ty: Ty::U64,
                    lhs: value(0),
                    rhs: value(5),
                },
                6,
            ),
            ret(6),
        ],
    );
    assert_eq!(helper_id, helper);
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
    define(
        format!("{tag}_calls"),
        nullary,
        vec![],
        vec![
            node(Inst::GlobalAddr { global: counter }, 0),
            node(
                Inst::Load {
                    ty: Ty::U64,
                    ptr: value(0),
                    volatile: false,
                    align: Some(8),
                },
                1,
            ),
            ret(1),
        ],
    );
    assert_eq!(module.functions.len(), LOCAL_BINDING_CORE_FUNCTIONS);
    module.functions[helper.index() as usize].linkage = helper_linkage;
    for index in 0..LOCAL_BINDING_PADDING {
        constant_function(
            &mut module,
            &format!("{tag}_pad_{index}"),
            Linkage::External,
            index as i128,
        );
    }
    module
}

/// A compiler for `triple` with an explicit relocation model and a full trace.
fn local_binding_compiler(
    triple: &str,
    opt_level: OptLevel,
    relocation_model: trust_cg_codegen::RelocationModel,
    parallel: bool,
) -> Compiler {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            parallel,
            relocation_model,
            trace_level: CompilerTraceLevel::Full,
            ..Default::default()
        },
        TargetSpec::parse(triple).expect("triple"),
    )
    .with_codegen_license(permit_unlicensed())
}

/// Every reference to `helper` in `elf` names its one defined `STB_LOCAL`
/// `STT_FUNC` symbol: the direct call (a `CALL26`/`JUMP26`), the `FnDef` and
/// `SymbolAddr` takings (`ADR_PREL_PG_HI21` + `ADD_ABS_LO12_NC`, never a GOT
/// relocation) and the data slot (`ABS64`). The independent parser above
/// reads every relocation's symbol from the symbol table, so a relocation
/// against another spelling of `helper` fails [`Elf::symbol`]'s uniqueness.
fn assert_helper_references_bind_locally(elf: &Elf, label: &str) {
    assert_symbol(elf, "helper", STB_LOCAL, STT_FUNC, STV_DEFAULT, true);
    let helper = elf.symbol("helper");
    assert_eq!(
        elf.sections[usize::from(helper.shndx)].0,
        ".text",
        "{label}: helper is defined in .text"
    );
    let kinds: BTreeSet<(String, u32)> = elf
        .relocs
        .iter()
        .filter(|reloc| reloc.symbol == "helper")
        .map(|reloc| (reloc.section.clone(), reloc.kind))
        .collect();
    assert!(
        kinds
            .iter()
            .any(|(section, kind)| section == ".text" && branch_kinds().contains(kind)),
        "{label}: the direct call relocates against the local helper: {kinds:?}"
    );
    for kind in [R_AARCH64_ADR_PREL_PG_HI21, R_AARCH64_ADD_ABS_LO12_NC] {
        assert!(
            kinds.contains(&(".text".to_string(), kind)),
            "{label}: helper's address is PC-relative ({kind}): {kinds:?}"
        );
    }
    assert!(
        kinds
            .iter()
            .any(|(section, kind)| section.starts_with(".data") && *kind == R_AARCH64_ABS64),
        "{label}: the data slot relocates against the local helper: {kinds:?}"
    );
    assert!(
        kinds
            .iter()
            .all(|(_, kind)| ![R_AARCH64_ADR_GOT_PAGE, R_AARCH64_LD64_GOT_LO12_NC].contains(kind)),
        "{label}: no GOT access to a local function: {kinds:?}"
    );
}

/// `Compiler::compile` admits direct calls to and every address form of an
/// Internal or Private function on AArch64 ELF, O0-O3, under `static`, `pie`
/// and `pic`, sequential and parallel (the trace names the emission path).
/// In each object the helper is `STB_LOCAL` and every relocation that names
/// it (call, PC-relative address, data slot) names that local symbol; no
/// GOT relocation names it. The sequential and parallel objects carry the
/// same text and relocations.
#[test]
fn compiler_binds_module_local_function_references_locally_on_aarch64_elf() {
    for helper_linkage in [Linkage::Internal, Linkage::Private] {
        let module = local_binding_module("a", helper_linkage, 100);
        let functions = LOCAL_BINDING_CORE_FUNCTIONS + LOCAL_BINDING_PADDING;
        for opt_level in OPT_LEVELS {
            for relocation_model in RELOCATION_MODELS {
                let mut objects = Vec::new();
                for parallel in [false, true] {
                    let label = format!(
                        "{helper_linkage} {opt_level:?} {relocation_model} parallel={parallel}"
                    );
                    let compiler =
                        local_binding_compiler(LINUX, opt_level, relocation_model, parallel);
                    assert!(compiler.object_binds_module_local_functions(), "{label}");
                    let result = compiler
                        .compile(&module)
                        .unwrap_or_else(|error| panic!("{label}: {error}"));
                    assert_emission_path(&result, parallel, functions, &label);
                    let elf = parse_elf(&result.object_code);
                    assert_helper_references_bind_locally(&elf, &label);
                    objects.push(elf);
                }
                assert_same_text_and_relocations(
                    &objects[0],
                    &objects[1],
                    &format!("{helper_linkage} {opt_level:?} {relocation_model}"),
                );
            }
        }
    }
}

/// Text placement does not change the binding: with function sections, an
/// explicit v45 section on the helper, or both, O0-O3 under `static` and
/// `pic`, the helper is one `STB_LOCAL` `STT_FUNC` symbol in its own section
/// (`.text.helper`, or the explicit one), never a COMDAT signature, and
/// every relocation naming it (from the callers' other text sections too)
/// names that local symbol, never through the GOT.
#[test]
fn module_local_function_references_bind_locally_across_text_sections() {
    for opt_level in OPT_LEVELS {
        for relocation_model in [
            trust_cg_codegen::RelocationModel::Static,
            trust_cg_codegen::RelocationModel::Pic,
        ] {
            for (function_sections, explicit) in [
                (true, None),
                (false, Some(".text.tcg_local")),
                (true, Some(".text.tcg_local")),
            ] {
                let label = format!(
                    "{opt_level:?} {relocation_model} function_sections={function_sections} \
                     explicit={explicit:?}"
                );
                let mut module = local_binding_module("a", Linkage::Internal, 100);
                module.functions[0].section = explicit.map(str::to_string);
                let object = Compiler::new_for_target_spec(
                    CompilerConfig {
                        opt_level,
                        relocation_model,
                        function_sections,
                        ..Default::default()
                    },
                    TargetSpec::parse(LINUX).expect("triple"),
                )
                .with_codegen_license(permit_unlicensed())
                .compile(&module)
                .unwrap_or_else(|error| panic!("{label}: {error}"))
                .object_code;
                let elf = parse_elf(&object);
                assert_symbol(&elf, "helper", STB_LOCAL, STT_FUNC, STV_DEFAULT, true);
                let helper_section = &elf.sections[usize::from(elf.symbol("helper").shndx)];
                assert_eq!(
                    helper_section.0,
                    explicit.unwrap_or(".text.helper"),
                    "{label}"
                );
                assert!(
                    elf.sections
                        .iter()
                        .all(|(_, sh_type, _)| *sh_type != 17 /* SHT_GROUP */),
                    "{label}: no COMDAT group"
                );
                let named: Vec<&Reloc> = elf
                    .relocs
                    .iter()
                    .filter(|reloc| reloc.symbol == "helper")
                    .collect();
                assert!(
                    named.iter().any(|reloc| reloc.section != helper_section.0
                        && branch_kinds().contains(&reloc.kind)),
                    "{label}: a caller in another section branches to the local helper: {named:?}"
                );
                assert!(
                    named.iter().all(
                        |reloc| ![R_AARCH64_ADR_GOT_PAGE, R_AARCH64_LD64_GOT_LO12_NC]
                            .contains(&reloc.kind)
                    ),
                    "{label}: {named:?}"
                );
            }
        }
    }
}

/// The emitters bind a reference to a module-local function by its name, so
/// that name must identify one function in the module. Two bodied Internal
/// or Private `helper`s in one module, or an Internal `helper` beside an
/// External declaration of `helper`, are refused before emission; neither
/// is renamed or merged. (Two objects each with their own `helper` are the
/// native controls' case.)
#[test]
fn module_local_function_names_must_be_unique_in_a_module() {
    for (second_linkage, second_bodied) in [
        (Linkage::Internal, true),
        (Linkage::Private, true),
        (Linkage::External, true),
        (Linkage::External, false),
    ] {
        let mut module = local_binding_module("a", Linkage::Internal, 100);
        let unary = module.functions[0].ty;
        let id = FuncId::new(module.functions.len() as u32);
        let mut twin = module.functions[0].clone();
        twin.id = id;
        twin.linkage = second_linkage;
        if !second_bodied {
            twin.blocks.clear();
        }
        module.functions.push(twin);
        let mut caller = Function::new(
            FuncId::new(id.index() + 1),
            "call_twin",
            unary,
            BlockId::new(0),
        );
        let mut block = Block::new(BlockId::new(0));
        block.params.push((ValueId::new(0), Ty::U64));
        block.body.push(
            InstrNode::new(Inst::Call {
                callee: id,
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(1)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }));
        caller.blocks.push(block);
        module.functions.push(caller);
        let label = format!("{second_linkage} bodied={second_bodied}");
        let error = match compiler(LINUX, OptLevel::O2, false).compile(&module) {
            Ok(_) => panic!("{label}: a second `helper` must be refused"),
            Err(error) => error.to_string(),
        };
        // trust-ir's validator refuses two functions with one link symbol
        // (`DuplicateFunctionSymbol`); since WS7.3 ingestion admission names
        // that finding before the backend's ambiguous-name arm is reached.
        assert!(
            error.contains("DuplicateFunctionSymbol") && error.contains("\"helper\""),
            "{label}: {error}"
        );
    }
}

/// Object paths other than AArch64/x86-64 ELF and Mach-O keep both refusals,
/// before any object or proof output: a direct call to a local function is
/// `AotDirectModuleFunctionBindingUnsupported` and a materialized address of
/// one (the `FnDef` taking, or a static-call candidate) is
/// `AotStaticFunctionIdentityBindingUnsupported`, counted with the
/// `SymbolAddr(helper)` of the kept `<tag>_slot` initializer (two; a string
/// address of a module-local function is counted since the 2026-10-24 L02-P1
/// closure audit, `module_local_binding_other_targets`). The same modules
/// compile for AArch64 ELF and for AArch64 Mach-O (whose own binding rows are
/// in `aarch64_macho_module_local_binding.rs`).
#[test]
fn module_local_function_references_stay_refused_off_locally_binding_objects() {
    let full = local_binding_module("a", Linkage::Internal, 100);
    // `helper` keeps FuncId 0 and nothing names the other kept function, so
    // renumbering keeps every reference exact.
    let keep = |names: &[&str]| {
        let mut module = full.clone();
        module.target_info = None;
        module.functions.retain(|function| {
            function.name == "helper" || names.contains(&function.name.as_str())
        });
        for (index, function) in module.functions.iter_mut().enumerate() {
            function.id = FuncId::new(index as u32);
        }
        module
    };
    let direct = keep(&["a_direct"]);
    let address = keep(&["a_addr"]);
    let candidate = keep(&["a_via_local"]);
    // x86-64 ELF binds them since ruling OD-X86-ELF-LOCAL-BINDING-20261027
    // (`tests/x86_64_elf_symbol_binding.rs`), so the paths that still refuse
    // are the x86-64 COFF writer and RISC-V.
    for triple in ["x86_64-pc-windows-msvc", "riscv64-unknown-linux-gnu"] {
        for linkage in [Linkage::Internal, Linkage::Private] {
            let compile = |module: &Module| {
                let mut module = module.clone();
                module.functions[0].linkage = linkage;
                let config = CompilerConfig {
                    emit_proofs: true,
                    opt_level: OptLevel::O2,
                    ..Default::default()
                };
                let compiler = Compiler::new_for_target_spec(
                    config,
                    TargetSpec::parse(triple).expect("triple"),
                )
                .with_codegen_license(permit_unlicensed());
                assert!(!compiler.object_binds_module_local_functions(), "{triple}");
                match compiler.compile(&module) {
                    Ok(_) => panic!("{triple} {linkage}: a module-local reference must be refused"),
                    Err(error) => error,
                }
            };
            let error = compile(&direct);
            assert!(
                matches!(
                    error,
                    trust_cg_codegen::CompileError::AotDirectModuleFunctionBindingUnsupported {
                        call_count: 1,
                        ..
                    }
                ),
                "{triple} {linkage} direct: {error}"
            );
            for (label, module) in [("address", &address), ("candidate", &candidate)] {
                let error = compile(module);
                assert!(
                    matches!(
                        error,
                        trust_cg_codegen::CompileError::AotStaticFunctionIdentityBindingUnsupported {
                            candidate_count: 2,
                            ..
                        }
                    ),
                    "{triple} {linkage} {label}: {error}"
                );
            }
        }
    }
    for module in [&direct, &address, &candidate] {
        compiler(DARWIN, OptLevel::O2, false)
            .compile(module)
            .unwrap_or_else(|error| panic!("{DARWIN} {}: {error}", module.functions[1].name));
        let mut module = module.clone();
        module.target_info = Some(linux_target_info());
        compiler(LINUX, OptLevel::O2, false)
            .compile(&module)
            .unwrap_or_else(|error| panic!("{}: {error}", module.functions[1].name));
    }
}

// -----------------------------------------------------------------------------
// Backend references by name, merged declarations and module-local personalities
// -----------------------------------------------------------------------------

/// Append a bodied function `name` (one entry block with `params`) and return
/// its id.
fn push_body(
    module: &mut Module,
    name: &str,
    sig: trust_ir::FuncTyId,
    linkage: Linkage,
    params: Vec<(ValueId, Ty)>,
    body: Vec<InstrNode>,
) -> FuncId {
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, sig, BlockId::new(0));
    function.linkage = linkage;
    let mut block = Block::new(BlockId::new(0));
    block.params = params;
    block.body = body;
    function.blocks.push(block);
    module.functions.push(function);
    id
}

/// `<runtime>(a, b) = 42.0` with `runtime_linkage` and an External
/// `my_rem(a, b) = a frem b` at `ty` (`F64` lowers to `fmod`, `F32` to
/// `fmodf`).
fn frem_module(runtime: &str, runtime_linkage: Linkage, ty: Ty) -> Module {
    let mut module = Module::new("frem_runtime_call");
    module.target_info = Some(linux_target_info());
    let sig = module
        .add_func_type(FuncTy {
            params: vec![ty.clone(), ty.clone()],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let params = || vec![(ValueId::new(0), ty.clone()), (ValueId::new(1), ty.clone())];
    push_body(
        &mut module,
        runtime,
        sig,
        runtime_linkage,
        params(),
        vec![
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value: Constant::Float(42.0),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    );
    push_body(
        &mut module,
        "my_rem",
        sig,
        Linkage::External,
        params(),
        vec![
            InstrNode::new(Inst::BinOp {
                op: trust_ir::BinOp::FRem,
                ty: ty.clone(),
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    );
    module
}

/// A call the backend makes to a runtime routine BY NAME never reaches a
/// module-local function of that name on AArch64 ELF. `frem` lowers to
/// `fmod`/`fmodf`; with a module-local `fmod`/`fmodf` defined the module is
/// refused by name at O0-O3 (at O1+ the module inliner would otherwise splice
/// the local body into the runtime call), and so is a module-local function
/// named like any other symbol of the shared `RuntimeSymbol` list (`memcpy`
/// for an aggregate copy, `__divti3`, `_Unwind_Resume`, ...), referenced or
/// not. An External definition of those names, which the linker would pick
/// for every object anyway, and a module-local function with an ordinary name
/// still compile, and so do module-local `printf`, `puts`, `sqrt`, `log`,
/// `exit`, `write` and `round` (called, and held in a data table), which the
/// backend never references. (The adapter's own by-name refusal is a
/// `trust-cg-lower` unit row.)
#[test]
fn backend_runtime_calls_never_bind_to_module_local_functions() {
    for (runtime, ty) in [("fmod", Ty::F64), ("fmodf", Ty::F32)] {
        for linkage in [Linkage::Internal, Linkage::Private] {
            for opt_level in OPT_LEVELS {
                match compiler(LINUX, opt_level, false).compile(&frem_module(
                    runtime,
                    linkage,
                    ty.clone(),
                )) {
                    Ok(_) => panic!("{runtime} {linkage} {opt_level:?}: must be refused"),
                    Err(error) => assert!(
                        matches!(
                            &error,
                            trust_cg_codegen::CompileError::ModuleLocalFunctionShadowsRuntimeSymbol {
                                function, ..
                            } if function == runtime
                        ),
                        "{runtime} {linkage} {opt_level:?}: {error}"
                    ),
                }
            }
        }
        compiler(LINUX, OptLevel::O2, false)
            .compile(&frem_module(runtime, Linkage::External, ty.clone()))
            .unwrap_or_else(|error| panic!("External {runtime}: {error}"));
        compiler(LINUX, OptLevel::O2, false)
            .compile(&frem_module(
                &format!("{runtime}_helper"),
                Linkage::Internal,
                ty.clone(),
            ))
            .unwrap_or_else(|error| panic!("{runtime}_helper: {error}"));
    }
    for name in [
        "memcpy",
        "memmove",
        "memset",
        "__divti3",
        "_Unwind_Resume",
        "__stack_chk_fail",
    ] {
        for linkage in [Linkage::Internal, Linkage::Private] {
            let mut module = Module::new("runtime_named_local");
            module.target_info = Some(linux_target_info());
            constant_function(&mut module, name, linkage, 7);
            constant_function(&mut module, "entry", Linkage::External, 1);
            match compiler(LINUX, OptLevel::O0, false).compile(&module) {
                Ok(_) => panic!("{linkage} {name}: must be refused"),
                Err(error) => assert!(
                    matches!(
                        &error,
                        trust_cg_codegen::CompileError::ModuleLocalFunctionShadowsRuntimeSymbol {
                            function, ..
                        } if function == name
                    ),
                    "{linkage} {name}: {error}"
                ),
            }
        }
        let mut external = Module::new("runtime_named_external");
        external.target_info = Some(linux_target_info());
        constant_function(&mut external, name, Linkage::External, 7);
        compiler(LINUX, OptLevel::O0, false)
            .compile(&external)
            .unwrap_or_else(|error| panic!("External {name}: {error}"));
    }
    // Names the backend never references compile as module-local functions,
    // unreferenced, called, and held only in a data table.
    for name in ["printf", "puts", "sqrt", "log", "exit", "write", "round"] {
        for linkage in [Linkage::Internal, Linkage::Private] {
            let mut module = Module::new("library_named_local");
            module.target_info = Some(linux_target_info());
            let local = constant_function(&mut module, name, linkage, 7);
            calling_function(&mut module, "entry", local);
            module.globals.push(Global {
                name: "table".into(),
                ty: Ty::Ptr,
                mutable: false,
                initializer: Some(Constant::SymbolAddr {
                    symbol: name.into(),
                    addend: 0,
                }),
                linkage: Linkage::External,
                tls: None,
                align: Some(8),
                section: None,
                visibility: Visibility::Default,
                retained: false,
            });
            for opt_level in OPT_LEVELS {
                let object = compiler(LINUX, opt_level, false)
                    .compile(&module)
                    .unwrap_or_else(|error| panic!("{linkage} {name} {opt_level:?}: {error}"))
                    .object_code;
                assert_symbol(
                    &parse_elf(&object),
                    name,
                    STB_LOCAL,
                    STT_FUNC,
                    STV_DEFAULT,
                    true,
                );
            }
        }
    }
}

/// A trust-ir text module with no target info (so it compiles for any
/// target).
fn parse_any_target(text: &str) -> Module {
    trust_ir::parser::parse_module(text).unwrap_or_else(|error| panic!("fixture parses: {error:?}"))
}

/// The verifier's shapes, each with a definition a backend by-name reference
/// would reach: `(label, trust-ir text, refused name, refused as function)`.
fn backend_symbol_shadow_fixtures() -> Vec<(&'static str, String, &'static str, bool)> {
    let frem = |definition: &str| {
        format!(
            "module \"f\"\nfunctty.0 = (f64, f64) -> (f64)\n{definition}\n\
             fn @my_rem(functy.0) {{\nbb0(%0: f64, %1: f64):\n    %2 = frem f64 %0, %1\n    ret %2\n}}\n"
        )
        .replace("functty", "functy")
    };
    let sincos = |definition: &str| {
        format!(
            "module \"s\"\nfuncty.0 = (f64) -> (f64)\n{definition}\n\
             fn @sin(functy.0) {{\n}}\nfn @cos(functy.0) {{\n}}\n\
             fn @both(functy.0) {{\nbb0(%0: f64):\n    %1 = call @func.SIN(%0)\n    \
             %2 = call @func.COS(%0)\n    %3 = fadd f64 %1, %2\n    ret %3\n}}\n"
        )
    };
    let local_fmod = "internal fn @fmod(functy.0) {\nbb0(%0: f64, %1: f64):\n    %2 = const f64 42.0\n    ret %2\n}";
    let private_fmod = local_fmod.replace("internal fn", "private fn");
    let local_stret = "internal fn @__sincos_stret(functy.0) {\nbb0(%0: f64):\n    %1 = const f64 42.0\n    ret %1\n}";
    let eh_data = |linkage: &str| {
        format!(
            "module \"gx\"\nfuncty.0 = (i32) -> (i32)\nglobal {linkage} mut @__gxx_personality_v0 u64 = 0\n\
             fn @b_mid(functy.0) {{\n}}\nfn @a_run(functy.0) {{\nbb0(%0: i32):\n    br bb3\nbb3:\n    \
             %2 = invoke @func.0(%0) to bb1() unwind bb2\nbb1:\n    ret %2\nbb2:\n    \
             %20, %21 = landingpad cleanup\n    resume %20\n}}\n"
        )
        .replace("global  mut", "global mut")
    };
    vec![
        ("internal fn fmod beside frem", frem(local_fmod), "fmod", true),
        ("private fn fmod beside frem", frem(&private_fmod), "fmod", true),
        (
            "internal fn __sincos_stret beside sin/cos",
            sincos(local_stret).replace("func.SIN", "func.1").replace("func.COS", "func.2"),
            "__sincos_stret",
            true,
        ),
        (
            "internal data __sincos_stret beside sin/cos",
            sincos("global internal mut @__sincos_stret i64 = 42")
                .replace("func.SIN", "func.0")
                .replace("func.COS", "func.1"),
            "__sincos_stret",
            false,
        ),
        ("internal data fmod beside frem", frem("global internal mut @fmod i64 = 42"), "fmod", false),
        ("external data fmod beside frem", frem("global mut @fmod i64 = 42"), "fmod", false),
        ("weak data fmod beside frem", frem("global weak mut @fmod i64 = 42"), "fmod", false),
        (
            "linkonce_odr data fmod beside frem",
            frem("global linkonce_odr mut @fmod i64 = 42"),
            "fmod",
            false,
        ),
        (
            "internal data __divti3 beside an i128 sdiv",
            "module \"d\"\nfuncty.0 = (i128, i128) -> (i128)\nglobal internal mut @__divti3 i64 = 42\n\
             fn @my_div(functy.0) {\nbb0(%0: i128, %1: i128):\n    %2 = sdiv i128 %0, %1\n    ret %2\n}\n"
                .to_string(),
            "__divti3",
            false,
        ),
        (
            "internal data memcpy beside a memcopy",
            "module \"m\"\nfuncty.0 = (ptr, ptr, usize) -> ()\nglobal internal mut @memcpy i64 = 42\n\
             fn @my_copy(functy.0) {\nbb0(%0: ptr, %1: ptr, %2: usize):\n    memcopy ptr %0, ptr %1, %2\n    ret\n}\n"
                .to_string(),
            "memcpy",
            false,
        ),
        (
            "internal data malloc beside a heap_alloc",
            "module \"h\"\nfuncty.0 = () -> (ptr)\nglobal internal mut @malloc i64 = 42\n\
             fn @my_alloc(functy.0) {\nbb0:\n    %0 = heap_alloc c_malloc u64\n    ret %0\n}\n"
                .to_string(),
            "malloc",
            false,
        ),
        ("external data personality in an EH module", eh_data(""), "__gxx_personality_v0", false),
        ("weak data personality in an EH module", eh_data("weak"), "__gxx_personality_v0", false),
    ]
}

/// Every object path resolves the backend's by-name references through the
/// module's own symbols (the verifier's AArch64 Mach-O object relocated
/// `bl _fmod` against the local `_fmod`, and at O2 inlined its body; x86-64
/// Mach-O relocated a runtime call against local data), so each of
/// [`backend_symbol_shadow_fixtures`] is refused before lowering on AArch64
/// ELF and Mach-O, x86-64 ELF and Mach-O, and RISC-V, at O0 and O2. The
/// sin/cos pair without a shadowing definition, and `frem` beside a
/// module-local `fmod_helper`, still compile on the object paths that lower
/// them.
#[test]
fn backend_symbol_shadows_are_refused_on_every_target() {
    // AArch64 ELF last: it has further layers behind the refusal (the
    // adapter and the object read-back), the others do not.
    const TARGETS: [&str; 5] = [
        DARWIN,
        "x86_64-apple-darwin",
        "x86_64-unknown-linux-gnu",
        "riscv64-unknown-linux-gnu",
        LINUX,
    ];
    for (label, text, name, function) in backend_symbol_shadow_fixtures() {
        let module = parse_any_target(&text);
        for triple in TARGETS {
            for opt_level in [OptLevel::O0, OptLevel::O2] {
                let error = match compiler(triple, opt_level, false)
                    .compile(&pinned_target::pinned(&module, triple))
                {
                    Ok(_) => panic!(
                        "{label} {triple} {opt_level:?}: compiled, but a backend reference would \
                         reach the module's definition"
                    ),
                    Err(error) => error,
                };
                let refused = match &error {
                    trust_cg_codegen::CompileError::ModuleLocalFunctionShadowsRuntimeSymbol {
                        function: refused,
                        ..
                    } => function && refused == name,
                    trust_cg_codegen::CompileError::DataShadowsBackendSymbol { global, .. } => {
                        !function && global == name
                    }
                    _ => false,
                };
                assert!(refused, "{label} {triple} {opt_level:?}: {error}");
            }
        }
    }
    let sincos = parse_any_target(
        "module \"s0\"\nfuncty.0 = (f64) -> (f64)\nfn @sin(functy.0) {\n}\nfn @cos(functy.0) {\n}\n\
         fn @both(functy.0) {\nbb0(%0: f64):\n    %1 = call @func.0(%0)\n    %2 = call @func.1(%0)\n    \
         %3 = fadd f64 %1, %2\n    ret %3\n}\n",
    );
    let helper = parse_any_target(
        "module \"f\"\nfuncty.0 = (f64, f64) -> (f64)\n\
         internal fn @fmod_helper(functy.0) {\nbb0(%0: f64, %1: f64):\n    %2 = const f64 42.0\n    ret %2\n}\n\
         fn @my_rem(functy.0) {\nbb0(%0: f64, %1: f64):\n    %2 = frem f64 %0, %1\n    ret %2\n}\n",
    );
    for (label, module) in [("sin/cos", &sincos), ("fmod_helper", &helper)] {
        for triple in [
            LINUX,
            DARWIN,
            "x86_64-apple-darwin",
            "x86_64-unknown-linux-gnu",
        ] {
            for opt_level in [OptLevel::O0, OptLevel::O2] {
                compiler(triple, opt_level, false)
                    .compile(&pinned_target::pinned(module, triple))
                    .unwrap_or_else(|error| panic!("{label} {triple} {opt_level:?}: {error}"));
            }
        }
    }
}

/// Module `a` declares `helper` and calls it from `a_call`; module `b`
/// defines an Internal (or Private) `helper` and calls it from `b_call`.
fn declaration_and_local_definition_modules(linkage: Linkage) -> (Module, Module) {
    let mut a = Module::new("declares_helper");
    a.target_info = Some(linux_target_info());
    let sig = a
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    a.functions.push(Function::new(
        FuncId::new(0),
        "helper",
        sig,
        BlockId::new(0),
    ));
    push_body(
        &mut a,
        "a_call",
        sig,
        Linkage::External,
        vec![(ValueId::new(0), Ty::U64)],
        vec![
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    );
    let mut b = Module::new("defines_local_helper");
    b.target_info = Some(linux_target_info());
    let sig = b
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let helper = push_body(
        &mut b,
        "helper",
        sig,
        linkage,
        vec![(ValueId::new(0), Ty::U64)],
        vec![
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(200),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::BinOp {
                op: trust_ir::BinOp::Add,
                ty: Ty::U64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    );
    push_body(
        &mut b,
        "b_call",
        sig,
        Linkage::External,
        vec![(ValueId::new(0), Ty::U64)],
        vec![
            InstrNode::new(Inst::Call {
                callee: helper,
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    );
    (a, b)
}

/// A module-local definition never satisfies another module's declaration.
/// The separately compiled objects say why: `a`'s object references an
/// undefined GLOBAL `helper`, `b`'s defines a LOCAL one. `merge_modules`
/// keeps that in both orders by renaming `b`'s definition apart
/// (`helper.merge.<input>`): the merged object at O0-O3 still references an
/// undefined GLOBAL `helper` and defines the renamed body LOCAL.
#[test]
fn module_local_definition_does_not_satisfy_another_modules_declaration() {
    for linkage in [Linkage::Internal, Linkage::Private] {
        let (a, b) = declaration_and_local_definition_modules(linkage);
        for (inputs, b_index) in [([a.clone(), b.clone()], 1), ([b.clone(), a.clone()], 0)] {
            let merged = trust_cg_codegen::module_merge::merge_modules(&inputs)
                .unwrap_or_else(|error| panic!("{linkage}: {error}"));
            for opt_level in OPT_LEVELS {
                let elf = parse_elf(
                    &compiler(LINUX, opt_level, false)
                        .compile(&merged)
                        .unwrap_or_else(|error| panic!("{linkage} {opt_level:?}: {error}"))
                        .object_code,
                );
                assert_symbol(&elf, "helper", STB_GLOBAL, STT_NOTYPE, STV_DEFAULT, false);
                if opt_level == OptLevel::O0 {
                    assert_symbol(
                        &elf,
                        &format!("helper.merge.{b_index}"),
                        STB_LOCAL,
                        STT_FUNC,
                        STV_DEFAULT,
                        true,
                    );
                }
            }
        }
        let a_elf = parse_elf(
            &compiler(LINUX, OptLevel::O2, false)
                .compile(&a)
                .expect("a")
                .object_code,
        );
        assert_symbol(&a_elf, "helper", STB_GLOBAL, STT_NOTYPE, STV_DEFAULT, false);
        let b_elf = parse_elf(
            &compiler(LINUX, OptLevel::O0, false)
                .compile(&b)
                .expect("b")
                .object_code,
        );
        assert_symbol(&b_elf, "helper", STB_LOCAL, STT_FUNC, STV_DEFAULT, true);
    }
}

/// Module `a` defines a module-local (`linkage`) `helper(x) = x + 200`,
/// calls it from `a_call` and returns its address from `a_ptr`. Module `b`
/// names `helper` only by `SymbolAddr`: in its global initializer `b_tbl`,
/// returned from `b_ptr`, called indirectly by `b_callp`, and loaded from
/// `b_tbl` and called by `b_tbl_call`. Separately compiled, every `b`
/// reference binds to an external `helper`.
fn symbol_address_and_local_definition_modules(linkage: &str) -> (Module, Module) {
    let text_a = "\
module \"a\"
functy.0 = (i64) -> (i64)
functy.1 = () -> (ptr)
LINKAGE fn @helper(functy.0) {
bb0(%0: i64):
    %1 = const i64 200
    %2 = add i64 %0, %1
    ret %2
}
fn @a_call(functy.0) {
bb0(%0: i64):
    %1 = call @func.0(%0)
    ret %1
}
fn @a_ptr(functy.1) {
bb0:
    %0 = const ptr symaddr<helper>
    ret %0
}
"
    .replace("LINKAGE", linkage);
    let text_b = "\
module \"b\"
functy.0 = (i64) -> (i64)
functy.1 = () -> (ptr)
global @b_tbl ptr = symaddr<helper>
fn @b_ptr(functy.1) {
bb0:
    %0 = const ptr symaddr<helper>
    ret %0
}
fn @b_callp(functy.0) {
bb0(%0: i64):
    %1 = const ptr symaddr<helper>
    %2 = call_indirect %1(functy.0)(%0)
    ret %2
}
fn @b_tbl_call(functy.0) {
bb0(%0: i64):
    %1 = global_addr @global.0
    %2 = load ptr, ptr %1
    %3 = call_indirect %2(functy.0)(%0)
    ret %3
}
";
    let parse = |text: &str| {
        let mut module = trust_ir::parser::parse_module(text)
            .unwrap_or_else(|error| panic!("fixture parses: {error:?}"));
        module.target_info = Some(linux_target_info());
        module
    };
    (parse(&text_a), parse(text_b))
}

/// Another input's `SymbolAddr` never reaches a module-local definition:
/// merged in both orders, `a`'s `helper` is renamed apart and the merged
/// object at O0-O3 keeps `helper` an undefined GLOBAL that `b_tbl`'s data
/// word is relocated against, as in `b`'s own object.
#[test]
fn merged_symbol_addresses_keep_naming_the_external_function() {
    for linkage in ["internal", "private"] {
        let (a, b) = symbol_address_and_local_definition_modules(linkage);
        let b_elf = parse_elf(
            &compiler(LINUX, OptLevel::O0, false)
                .compile(&b)
                .expect("b")
                .object_code,
        );
        assert_symbol(&b_elf, "helper", STB_GLOBAL, STT_NOTYPE, STV_DEFAULT, false);
        for (inputs, a_index) in [([a.clone(), b.clone()], 0), ([b.clone(), a.clone()], 1)] {
            let merged = trust_cg_codegen::module_merge::merge_modules(&inputs)
                .unwrap_or_else(|error| panic!("{linkage}: {error}"));
            for opt_level in OPT_LEVELS {
                let elf = parse_elf(
                    &compiler(LINUX, opt_level, false)
                        .compile(&merged)
                        .unwrap_or_else(|error| panic!("{linkage} {opt_level:?}: {error}"))
                        .object_code,
                );
                assert_symbol(&elf, "helper", STB_GLOBAL, STT_NOTYPE, STV_DEFAULT, false);
                assert_symbol(
                    &elf,
                    &format!("helper.merge.{a_index}"),
                    STB_LOCAL,
                    STT_FUNC,
                    STV_DEFAULT,
                    true,
                );
                let table: Vec<&Reloc> = elf
                    .relocs
                    .iter()
                    .filter(|reloc| reloc.kind == R_AARCH64_ABS64 && reloc.symbol == "helper")
                    .collect();
                assert_eq!(table.len(), 1, "{linkage} {opt_level:?}: {:?}", elf.relocs);
            }
        }
    }
}

/// A module-local `helper` (201) beside the module's own declaration of the
/// versioned symbol `helper@VERS_1`, and a module-local function whose own
/// name contains `@` (`probe@LOCAL`, 501) beside a declaration of `probe`,
/// each called from an External `call_*`, and an Internal global `helper@x`; the Internal globals
/// `keep_helper`/`keep_probe` hold the local bodies' addresses so they stay
/// defined at every optimization level.
fn versioned_names_module() -> Module {
    let mut module = Module::new("versioned_names");
    module.target_info = Some(linux_target_info());
    let helper = constant_function(&mut module, "helper", Linkage::Internal, 201);
    let sig = module.functions[helper.index() as usize].ty;
    let versioned = FuncId::new(module.functions.len() as u32);
    module.functions.push(Function::new(
        versioned,
        "helper@VERS_1",
        sig,
        BlockId::new(0),
    ));
    let at_local = constant_function(&mut module, "probe@LOCAL", Linkage::Private, 501);
    let probe = FuncId::new(module.functions.len() as u32);
    module
        .functions
        .push(Function::new(probe, "probe", sig, BlockId::new(0)));
    calling_function(&mut module, "call_local", helper);
    calling_function(&mut module, "call_versioned", versioned);
    calling_function(&mut module, "call_at_local", at_local);
    calling_function(&mut module, "call_probe", probe);
    module.globals.push(Global {
        name: "helper@x".into(),
        ty: Ty::I64,
        mutable: true,
        initializer: Some(Constant::Int(5)),
        linkage: Linkage::Internal,
        tls: None,
        align: Some(8),
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });
    for (global, function) in [("keep_helper", "helper"), ("keep_probe", "probe@LOCAL")] {
        module.globals.push(Global {
            name: global.into(),
            ty: Ty::Ptr,
            mutable: false,
            initializer: Some(Constant::SymbolAddr {
                symbol: function.into(),
                addend: 0,
            }),
            linkage: Linkage::External,
            tls: None,
            align: Some(8),
            section: None,
            visibility: Visibility::Default,
            retained: false,
        });
    }
    module
}

/// [`versioned_names_module`] compiles at O0-O3 (the post-emission check
/// accepts the module's own versioned declaration and its own Internal global
/// spelled `helper@x`, and checks the `@`-named local under its exact name):
/// the local bodies are defined LOCAL under their exact names, the global is
/// a LOCAL object, and the declarations are undefined GLOBAL references under
/// theirs.
#[test]
fn versioned_and_at_named_symbols_beside_module_local_functions() {
    let module = versioned_names_module();
    for opt_level in OPT_LEVELS {
        let elf = parse_elf(
            &compiler(LINUX, opt_level, false)
                .compile(&module)
                .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
                .object_code,
        );
        for (name, bind, kind, defined) in [
            ("helper", STB_LOCAL, STT_FUNC, true),
            ("helper@VERS_1", STB_GLOBAL, STT_NOTYPE, false),
            ("probe@LOCAL", STB_LOCAL, STT_FUNC, true),
            ("probe", STB_GLOBAL, STT_NOTYPE, false),
            ("helper@x", STB_LOCAL, STT_OBJECT, true),
        ] {
            assert_symbol(&elf, name, bind, kind, STV_DEFAULT, defined);
        }
    }
}

/// A trust-ir text module for the Linux target.
fn parse_linux(text: &str) -> Module {
    let mut module = trust_ir::parser::parse_module(text)
        .unwrap_or_else(|error| panic!("fixture parses: {error:?}"));
    module.target_info = Some(linux_target_info());
    module
}

/// An EH module that selects the C++ default personality (no function is
/// named `rust_eh_personality`) and defines an Internal `i64` global named
/// `data_name`: `a_run(x)` invokes the declared `b_mid(x)` with a cleanup pad.
fn eh_module_with_local_data(data_name: &str) -> Module {
    parse_linux(
        &"\
module \"gx\"
functy.0 = (i32) -> (i32)
functy.1 = () -> (u64)
global internal mut @DATA u64 = 0
fn @b_mid(functy.0) {
}
fn @a_run(functy.0) {
bb0(%0: i32):
    br bb3
bb3:
    %2 = invoke @func.0(%0) to bb1() unwind bb2
bb1:
    ret %2
bb2:
    %20, %21 = landingpad cleanup
    resume %20
}
fn @data_value(functy.1) {
bb0:
    %0 = global_addr @global.0
    %1 = load u64, ptr %0
    ret %1
}
"
        .replace("DATA", data_name),
    )
}

/// The backend's by-name references never reach module-local DATA on AArch64
/// ELF. An Internal or Private global named `fmod`/`fmodf` beside `frem`
/// (the verifier's module crashed with SIGSEGV at O0 and O2: its `CALL26
/// fmod` named the local object), one named `memcpy`, and one named
/// `__gxx_personality_v0` in an EH module that selects that personality
/// (whose object-local `DW.ref` slot would hold the data's address) are
/// refused by name at O0-O3. Data named `printf` beside `frem`, and data
/// named `rust_eh_personality` in a module that selects the C++ default,
/// still compile. AArch64 Mach-O resolves those references by name too (the
/// verifier's `fmod` module relocated its `bl` against the local `_fmod`
/// data), so the refusal and the controls also hold for `aarch64-apple-darwin`
/// at O0 and O2.
#[test]
fn module_local_data_named_like_a_backend_symbol_is_refused() {
    let data = |name: &str, linkage: Linkage| Global {
        name: name.into(),
        ty: Ty::I64,
        mutable: true,
        initializer: Some(Constant::Int(42)),
        linkage,
        tls: None,
        align: Some(8),
        section: None,
        visibility: Visibility::Default,
        retained: false,
    };
    let mut refused = Vec::new();
    for linkage in [Linkage::Internal, Linkage::Private] {
        for (runtime, ty) in [("fmod", Ty::F64), ("fmodf", Ty::F32)] {
            let mut module = frem_module("unrelated_local", Linkage::Internal, ty);
            module.globals.push(data(runtime, linkage));
            refused.push((format!("{linkage} {runtime} data"), module, runtime));
        }
        let mut module = Module::new("memcpy_data");
        module.target_info = Some(linux_target_info());
        let helper = constant_function(&mut module, "helper", Linkage::External, 1);
        calling_function(&mut module, "entry", helper);
        module.globals.push(data("memcpy", linkage));
        refused.push((format!("{linkage} memcpy data"), module, "memcpy"));
    }
    refused.push((
        "personality data".into(),
        eh_module_with_local_data("__gxx_personality_v0"),
        "__gxx_personality_v0",
    ));
    for (label, module, name) in &refused {
        let mut darwin = module.clone();
        pinned_target::pin(&mut darwin, DARWIN);
        for (triple, module, opt_level) in OPT_LEVELS
            .into_iter()
            .map(|opt_level| (LINUX, module, opt_level))
            .chain([OptLevel::O0, OptLevel::O2].map(|opt_level| (DARWIN, &darwin, opt_level)))
        {
            let error = compiler(triple, opt_level, false)
                .compile(&pinned_target::pinned(module, triple))
                .expect_err("module-local data named like a backend symbol");
            assert!(
                matches!(
                    &error,
                    trust_cg_codegen::CompileError::DataShadowsBackendSymbol {
                        global, ..
                    } if global == name
                ),
                "{label} {triple} {opt_level:?}: {error}"
            );
        }
    }
    let mut printf_data = frem_module("unrelated_local", Linkage::Internal, Ty::F64);
    printf_data.globals.push(data("printf", Linkage::Internal));
    for (label, module, local) in [
        ("printf data", printf_data, "printf"),
        (
            "rust_eh_personality data",
            eh_module_with_local_data("rust_eh_personality"),
            "rust_eh_personality",
        ),
    ] {
        for opt_level in OPT_LEVELS {
            let elf = parse_elf(
                &compiler(LINUX, opt_level, false)
                    .compile(&module)
                    .unwrap_or_else(|error| panic!("{label} {opt_level:?}: {error}"))
                    .object_code,
            );
            assert_symbol(&elf, local, STB_LOCAL, STT_OBJECT, STV_DEFAULT, true);
        }
        let mut darwin = module.clone();
        pinned_target::pin(&mut darwin, DARWIN);
        compiler(DARWIN, OptLevel::O2, false)
            .compile(&darwin)
            .unwrap_or_else(|error| panic!("{label} {DARWIN}: {error}"));
    }
}

/// An EH module (its frames select `__gxx_personality_v0`) that defines a
/// global named `slot` with `linkage`, and reads it.
fn eh_module_defining(slot: &str, linkage: &str) -> Module {
    parse_linux(&format!(
        "module \"own_slot\"\nfuncty.0 = (i32) -> (i32)\nfuncty.1 = () -> (u64)\n\
         global {linkage} mut @{slot} u64 = 42\n\
         fn @a_mid(functy.0) {{\n}}\n\
         fn @a_run(functy.0) {{\nbb0(%0: i32):\n    br bb3\nbb3:\n    \
         %2 = invoke @func.0(%0) to bb1() unwind bb2\nbb1:\n    ret %2\nbb2:\n    \
         %20, %21 = landingpad cleanup\n    resume %20\n}}\n\
         fn @read_own(functy.1) {{\nbb0:\n    %0 = global_addr @global.0\n    \
         %1 = load u64, ptr %0\n    ret %1\n}}\n"
    ))
}

/// A module that DEFINES a non-local global named like an EH personality's
/// `DW.ref` slot is refused by name (`DataShadowsBackendSymbol`), on AArch64
/// Linux at O0-O3 under every relocation model, on AArch64 Darwin and x86-64
/// Linux: every unwind table's slot of that name, its own and every other
/// object's, would resolve to it. Before the refusal, the module's own frames
/// read its word (42) as the personality pointer with GNU ld 2.42 and gold,
/// and a throw through them died with `SIGBUS`, while LLD 22 resolved the
/// module's word to a slot or refused the link. Refused: `External`, `Weak`
/// and `LinkOnceOdr` `DW.ref.__gxx_personality_v0` in an EH module, and an
/// `External` `DW.ref.rust_eh_personality` in a module without EH
/// structure. Still compiled: an `Internal` `DW.ref.__gxx_personality_v0`
/// (a separate `STB_LOCAL` symbol beside the emitter's `WEAK HIDDEN` slot)
/// and an `External` `DW.ref.my_personality`.
#[test]
#[allow(clippy::result_large_err)] // Test helper returns the compiler's own error type unchanged.
fn data_named_like_a_personality_slot_is_refused() {
    let x86_linux = |module: &Module| {
        let target_spec = TargetSpec::parse("x86_64-unknown-linux-gnu").expect("triple");
        Compiler::new_for_target_spec(
            CompilerConfig {
                target: target_spec.architecture,
                opt_level: OptLevel::O0,
                parallel: false,
                ..Default::default()
            },
            target_spec,
        )
        .with_codegen_license(permit_unlicensed())
        .compile(&pinned_target::pinned(module, "x86_64-unknown-linux-gnu"))
        .map(|_| ())
    };
    let mut no_eh = Module::new("slot_data_without_eh");
    no_eh.target_info = Some(linux_target_info());
    constant_function(&mut no_eh, "entry", Linkage::External, 1);
    no_eh.globals.push(Global {
        name: "DW.ref.rust_eh_personality".into(),
        ty: Ty::U64,
        mutable: true,
        initializer: Some(Constant::Int(42)),
        linkage: Linkage::External,
        tls: None,
        align: Some(8),
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });
    let refused = [
        (
            eh_module_defining("DW.ref.__gxx_personality_v0", "external"),
            "DW.ref.__gxx_personality_v0",
        ),
        (
            eh_module_defining("DW.ref.__gxx_personality_v0", "weak"),
            "DW.ref.__gxx_personality_v0",
        ),
        (
            eh_module_defining("DW.ref.__gxx_personality_v0", "linkonce_odr"),
            "DW.ref.__gxx_personality_v0",
        ),
        (no_eh, "DW.ref.rust_eh_personality"),
    ];
    let is_refusal = |error: &trust_cg_codegen::CompileError, name: &str| {
        matches!(
            error,
            trust_cg_codegen::CompileError::DataShadowsBackendSymbol { global, .. } if global == name
        ) && error.to_string().contains("`DW.ref` slot")
    };
    for (module, name) in &refused {
        for model in RELOCATION_MODELS {
            for opt_level in OPT_LEVELS {
                let error = local_binding_compiler(LINUX, opt_level, model, false)
                    .compile(&pinned_target::pinned(module, LINUX))
                    .map(|_| ())
                    .expect_err("data named like a personality slot");
                assert!(
                    is_refusal(&error, name),
                    "{name} {model} {opt_level:?}: {error}"
                );
            }
        }
        let mut elsewhere = module.clone();
        pinned_target::pin(&mut elsewhere, DARWIN);
        let error = compiler(DARWIN, OptLevel::O0, false)
            .compile(&elsewhere)
            .map(|_| ())
            .expect_err("Darwin");
        assert!(is_refusal(&error, name), "{name} {DARWIN}: {error}");
        let error = x86_linux(&elsewhere).expect_err("x86-64 Linux");
        assert!(is_refusal(&error, name), "{name} x86-64: {error}");
    }
    let local = eh_module_defining("DW.ref.__gxx_personality_v0", "internal");
    for model in RELOCATION_MODELS {
        let elf = parse_elf(
            &local_binding_compiler(LINUX, OptLevel::O0, model, false)
                .compile(&local)
                .unwrap_or_else(|error| panic!("internal {model}: {error}"))
                .object_code,
        );
        let spellings: Vec<(u8, u8)> = elf
            .symbols
            .iter()
            .filter(|symbol| symbol.name == "DW.ref.__gxx_personality_v0")
            .map(|symbol| (symbol.bind, symbol.visibility))
            .collect();
        assert_eq!(
            spellings,
            [(STB_LOCAL, STV_DEFAULT), (STB_WEAK, STV_HIDDEN)],
            "internal {model}: the module's local word and the emitter's slot"
        );
    }
    local_binding_compiler(
        LINUX,
        OptLevel::O0,
        trust_cg_codegen::RelocationModel::Pic,
        false,
    )
    .compile(&eh_module_defining("DW.ref.my_personality", "external"))
    .unwrap_or_else(|error| panic!("DW.ref.my_personality: {error}"));
}

/// The verifier's pair for the personality scope: module `a` has
/// exception-handling structure and a counting module-local
/// `rust_eh_personality`, and `a_run` invokes `b_mid`, which module `b`
/// defines without exception-handling structure as
/// `thrower(thrower(x) + 1)`. With `personality` = `internal`, `a`'s
/// personality is its own routine; with `fn` (a declaration, no body) it is
/// the external Rust personality.
fn personality_scope_modules(personality_local: bool) -> (Module, Module) {
    let personality = if personality_local {
        "internal fn @rust_eh_personality(functy.1) {
bb0(%0: i32, %1: i32, %2: u64, %3: ptr, %4: ptr):
    %5 = global_addr @global.0
    %6 = load u64, ptr %5
    %7 = const u64 1
    %8 = add u64 %6, %7
    store u64 %8, ptr %5
    %9 = const i32 8
    ret %9
}"
    } else {
        "fn @rust_eh_personality(functy.1) {\n}"
    };
    let a = parse_linux(
        &"\
module \"a\"
functy.0 = (i32) -> (i32)
functy.1 = (i32, i32, u64, ptr, ptr) -> (i32)
functy.2 = () -> (u64)
global internal mut @a_personality_count u64 = 0
fn @b_mid(functy.0) {
}
PERSONALITY
fn @a_run(functy.0) {
bb0(%0: i32):
    br bb3
bb3:
    %2 = invoke @func.0(%0) to bb1() unwind bb2
bb1:
    ret %2
bb2:
    %20, %21 = landingpad cleanup
    resume %20
}
fn @a_personality_calls(functy.2) {
bb0:
    %0 = global_addr @global.0
    %1 = load u64, ptr %0
    ret %1
}
"
        .replace("PERSONALITY", personality),
    );
    let b = parse_linux(
        "\
module \"b\"
functy.0 = (i32) -> (i32)
fn @thrower(functy.0) {
}
fn @b_mid(functy.0) {
bb0(%0: i32):
    %1 = call @func.0(%0)
    %2 = const i32 1
    %3 = add i32 %1, %2
    %4 = call @func.0(%3)
    ret %4
}
",
    );
    (a, b)
}

/// Every function of a module with exception-handling structure gets the
/// module's personality, so merging the verifier's pair would make `b`'s
/// frames run `a`'s module-local personality, which they never run compiled
/// separately: `merge_modules` refuses it in both orders. With `a` using the
/// external Rust personality instead the pair merges and compiles at O0-O3
/// (the accepted extra personality call for `b`'s frame).
#[test]
fn merge_keeps_other_inputs_frames_off_a_module_local_personality() {
    let (a, b) = personality_scope_modules(true);
    for inputs in [[a.clone(), b.clone()], [b.clone(), a.clone()]] {
        let error = trust_cg_codegen::module_merge::merge_modules(&inputs)
            .expect_err("b's frames would run a's module-local personality");
        assert!(
            error.contains("module-local personality `rust_eh_personality`")
                && error.contains("compiled separately they never run it"),
            "{error}"
        );
    }
    let (a, b) = personality_scope_modules(false);
    for inputs in [[a.clone(), b.clone()], [b.clone(), a.clone()]] {
        let merged = trust_cg_codegen::module_merge::merge_modules(&inputs)
            .unwrap_or_else(|error| panic!("external personality: {error}"));
        for opt_level in OPT_LEVELS {
            compiler(LINUX, opt_level, false)
                .compile(&merged)
                .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
        }
    }
}

/// `x -> invoke thrower(x)` with a cleanup pad that resumes, in a module that
/// DEFINES `rust_eh_personality` with `personality_linkage` (or only declares
/// it when `None`): `personality(version, actions, class, exception, context)`
/// counts its calls in the Internal global `<tag>_personality_count` and
/// returns `_URC_CONTINUE_UNWIND` (8). Entry points: `<tag>_run(i32) -> i32`
/// and `<tag>_personality_calls() -> u64`.
fn local_personality_module(tag: &str, personality_linkage: Option<Linkage>) -> Module {
    let mut module = Module::new(format!("local_personality_{tag}"));
    module.target_info = Some(linux_target_info());
    let unary = module
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let personality_sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32, Ty::U64, Ty::Ptr, Ty::Ptr],
            returns: vec![Ty::I32],
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
    module.globals.push(Global {
        name: format!("{tag}_personality_count"),
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
    let counter = GlobalId::new(0);
    // FuncId 0: the C thrower.
    module.functions.push(Function::new(
        FuncId::new(0),
        "thrower",
        unary,
        BlockId::new(0),
    ));
    // FuncId 1: the personality.
    match personality_linkage {
        Some(linkage) => {
            push_body(
                &mut module,
                "rust_eh_personality",
                personality_sig,
                linkage,
                vec![
                    (ValueId::new(0), Ty::I32),
                    (ValueId::new(1), Ty::I32),
                    (ValueId::new(2), Ty::U64),
                    (ValueId::new(3), Ty::Ptr),
                    (ValueId::new(4), Ty::Ptr),
                ],
                vec![
                    InstrNode::new(Inst::GlobalAddr { global: counter })
                        .with_result(ValueId::new(5)),
                    InstrNode::new(Inst::Load {
                        ty: Ty::U64,
                        ptr: ValueId::new(5),
                        volatile: false,
                        align: Some(8),
                    })
                    .with_result(ValueId::new(6)),
                    InstrNode::new(Inst::Const {
                        ty: Ty::U64,
                        value: Constant::Int(1),
                    })
                    .with_result(ValueId::new(7)),
                    InstrNode::new(Inst::BinOp {
                        op: trust_ir::BinOp::Add,
                        ty: Ty::U64,
                        lhs: ValueId::new(6),
                        rhs: ValueId::new(7),
                    })
                    .with_result(ValueId::new(8)),
                    InstrNode::new(Inst::Store {
                        ty: Ty::U64,
                        ptr: ValueId::new(5),
                        value: ValueId::new(8),
                        volatile: false,
                        align: Some(8),
                    }),
                    InstrNode::new(Inst::Const {
                        ty: Ty::I32,
                        value: Constant::Int(8),
                    })
                    .with_result(ValueId::new(9)),
                    InstrNode::new(Inst::Return {
                        values: vec![ValueId::new(9)],
                    }),
                ],
            );
        }
        None => module.functions.push(Function::new(
            FuncId::new(1),
            "rust_eh_personality",
            personality_sig,
            BlockId::new(0),
        )),
    }
    // FuncId 2: `<tag>_run`, the invoke in a block of its own.
    let mut run = Function::new(FuncId::new(2), format!("{tag}_run"), unary, BlockId::new(0));
    run.blocks = vec![
        Block {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I32)],
            body: vec![InstrNode::new(Inst::Br {
                target: BlockId::new(3),
                args: vec![],
            })],
        },
        Block {
            id: BlockId::new(3),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Invoke {
                    callee: FuncId::new(0),
                    args: vec![ValueId::new(0)],
                    normal_dest: BlockId::new(1),
                    normal_args: vec![],
                    unwind_dest: BlockId::new(2),
                })
                .with_result(ValueId::new(2)),
            ],
        },
        Block {
            id: BlockId::new(1),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            })],
        },
        Block {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::LandingPad {
                    is_cleanup: true,
                    catch_type_indices: vec![],
                })
                .with_results(vec![ValueId::new(20), ValueId::new(21)]),
                InstrNode::new(Inst::Resume {
                    exn: ValueId::new(20),
                }),
            ],
        },
    ];
    module.functions.push(run);
    // FuncId 3: the counter getter.
    push_body(
        &mut module,
        &format!("{tag}_personality_calls"),
        nullary,
        Linkage::External,
        vec![],
        vec![
            InstrNode::new(Inst::GlobalAddr { global: counter }).with_result(ValueId::new(0)),
            InstrNode::new(Inst::Load {
                ty: Ty::U64,
                ptr: ValueId::new(0),
                volatile: false,
                align: Some(8),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    );
    module
}

/// A personality the module defines locally gets an object-local
/// `DW.ref.rust_eh_personality` slot (a `STB_LOCAL` object whose `ABS64`
/// names the local personality), as GCC does for a `static` personality, at
/// O0-O3 under `static`, `pie` and `pic`; the CIE's `PREL32` names that
/// local slot. An external (declared) personality keeps the weak global slot.
#[test]
fn module_local_personality_gets_an_object_local_dw_ref_slot() {
    for opt_level in OPT_LEVELS {
        for model in RELOCATION_MODELS {
            for linkage in [Linkage::Internal, Linkage::Private] {
                let label = format!("{linkage} {opt_level:?} {model}");
                let object = local_binding_compiler(LINUX, opt_level, model, false)
                    .compile(&local_personality_module("a", Some(linkage)))
                    .unwrap_or_else(|error| panic!("{label}: {error}"))
                    .object_code;
                let elf = parse_elf(&object);
                assert_symbol(
                    &elf,
                    "rust_eh_personality",
                    STB_LOCAL,
                    STT_FUNC,
                    STV_DEFAULT,
                    true,
                );
                assert_symbol(
                    &elf,
                    "DW.ref.rust_eh_personality",
                    STB_LOCAL,
                    STT_OBJECT,
                    STV_DEFAULT,
                    true,
                );
                let slot_relocs: Vec<&Reloc> = elf
                    .relocs
                    .iter()
                    .filter(|reloc| reloc.section == ".data.DW.ref.rust_eh_personality")
                    .collect();
                assert!(
                    matches!(slot_relocs.as_slice(), [reloc] if reloc.kind == R_AARCH64_ABS64
                        && reloc.symbol == "rust_eh_personality"),
                    "{label}: {slot_relocs:?}"
                );
                assert!(
                    elf.relocs_in(".eh_frame")
                        .iter()
                        .any(|reloc| reloc.kind == R_AARCH64_PREL32
                            && reloc.symbol == "DW.ref.rust_eh_personality"),
                    "{label}: the CIE names the local slot"
                );
            }
            // An external personality's slot is GCC's: WEAK HIDDEN, alone in
            // a COMDAT group it signs (L02-P6).
            let external = local_binding_compiler(LINUX, opt_level, model, false)
                .compile(&local_personality_module("a", None))
                .unwrap_or_else(|error| panic!("external {opt_level:?} {model}: {error}"))
                .object_code;
            let elf = parse_elf(&external);
            assert_symbol(
                &elf,
                "DW.ref.rust_eh_personality",
                STB_WEAK,
                STT_OBJECT,
                STV_HIDDEN,
                true,
            );
            assert_eq!(
                comdat_groups(&external),
                [(
                    "DW.ref.rust_eh_personality".to_string(),
                    vec![
                        ".data.DW.ref.rust_eh_personality".to_string(),
                        ".rela.data.DW.ref.rust_eh_personality".to_string()
                    ]
                )],
                "external {opt_level:?} {model}"
            );
            let local = local_binding_compiler(LINUX, opt_level, model, false)
                .compile(&local_personality_module("a", Some(Linkage::Internal)))
                .unwrap_or_else(|error| panic!("local {opt_level:?} {model}: {error}"))
                .object_code;
            assert!(
                comdat_groups(&local).is_empty(),
                "local {opt_level:?} {model}: a local slot is in no group"
            );
        }
    }
}

// =============================================================================
// L02-P6 closure audit 4: the visibility cross-product table
// =============================================================================

#[path = "aarch64_elf_symbol_binding/visibility_table.rs"]
mod visibility_table;

/// L02-P6 closure audit 4: the table's classification is total and its
/// counts are pinned; every admitted case is a well-formed trust-ir module
/// that trust-ir's validator accepts.
#[test]
fn visibility_table_classifies_the_whole_cross_product() {
    visibility_table::classifies_the_whole_cross_product();
}

/// L02-P6 closure audit 4: `Compiler::compile` spells every admitted case
/// of the table under `static`, `pie` and `pic`, with and without function
/// sections, sequentially and in parallel at O0-O3 (both reach the unwind
/// emitter; the trace names the path).
#[test]
fn visibility_table_compiler_routes_spell_every_admitted_class() {
    visibility_table::compiler_routes_spell_every_admitted_class();
}

/// L02-P6 closure audit 4: the three Pipeline module emitters spell every
/// case the Pipeline API can state (the Compiler's admitted cases as
/// `ObjectGlobal` and `FunctionSymbolBinding` fields, plus local functions
/// with a stated visibility, which a `Local` binding normalizes to default)
/// under `static`, `pie` and `pic`, with and without function sections, at
/// O0 and O2; sequential and parallel emission agree byte for byte.
#[test]
fn visibility_table_pipeline_routes_spell_every_admitted_class() {
    visibility_table::pipeline_routes_spell_every_admitted_class();
}

/// L02-P6 closure audit 4: structural purity, which the module inliner and
/// the pure-callee pipeline trust, reads the same replacement predicates as
/// the table's addresses. Through the public module translation under
/// `static`, `pie` and `pic`, `call_<symbol>` names a function definition of
/// the table as a pure callee exactly when it is neither link-replaceable
/// (`weak`, `linkonce`) nor preemptible (default-visibility and non-local
/// under `pic`), whatever its section; a bodyless declaration never is.
/// Without this row a purity predicate that ignored visibility passed every
/// floor target: the AArch64 pure-call hoist that consumes it is opt-in, so
/// no object byte changed.
#[test]
fn visibility_table_purity_reads_the_replacement_predicates() {
    visibility_table::purity_reads_the_replacement_predicates();
}

/// L02-P6 closure audit 4: every pruned combination of the table is
/// accounted for. Each refused case fails `Compiler::compile` with the
/// diagnostic `visibility_table::Refusal::diagnostic` names under `static`
/// and `pic` (a
/// bodyless function with a definition linkage is trust-ir's validator's
/// `EmptyFunction`, and the backend refuses it too). Each inexpressible case
/// compiles to what its reason says: an `available_externally` definition
/// to its declaration's undefined symbol, an initializer-less `internal`
/// global to a module-local zero-fill definition, and an initializer-less
/// declaration of a zero-fill or pointer-bearing kind to the undefined
/// symbol of its mutable, read-only or thread-local twin. The relocation-free
/// Pipeline route's two structural limits hold: a pointer-bearing global
/// takes the relocating emitter, and a declaration nothing references emits
/// no symbol (checked on every relocation-free row).
#[test]
fn visibility_table_pruned_combinations_are_refused_by_name() {
    visibility_table::pruned_combinations_are_refused_by_name();
}

/// L02-P6 closure audit 4: the relocation-model backstop of the AArch64 ELF
/// module emitters (both relocating ones) reads the shared address
/// predicate for every non-thread-local case of the table: a PC-relative
/// address of each case the predicate makes GOT-indirect is refused with
/// the reason for its class, and every other PC-relative address compiles,
/// under `static`, `pie` and `pic`. Under `pic` an executable-only TLS
/// access (local-exec for a definition, initial-exec for a declaration) to
/// every thread-local case is refused.
#[test]
fn visibility_table_backstop_refuses_every_forbidden_pc_relative_address() {
    visibility_table::backstop_refuses_every_forbidden_pc_relative_address();
}

// =============================================================================
// Native Linux AArch64 controls (O0-O3)
// =============================================================================

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[path = "common/rosetta.rs"]
mod process;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
mod native {
    use super::*;
    use sha2::{Digest, Sha256};
    use std::fs;
    use std::io::Write;
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};

    const RETAIN_EVIDENCE: &str = "TCG_RETAIN_TEST_EVIDENCE";

    fn retaining_evidence() -> bool {
        std::env::var_os(RETAIN_EVIDENCE).is_some()
    }

    /// A row's scratch directory. It is removed when the row that made it
    /// ends, and kept when the row panics only while
    /// `TRUST_CG_KEEP_TEST_OBJECTS` is set; the failure message names it
    /// ("preserved files=..."). Explicit `TCG_RETAIN_TEST_EVIDENCE` retains
    /// successful native objects/images and command records for archival too.
    struct Scratch(PathBuf);

    impl std::ops::Deref for Scratch {
        type Target = Path;

        fn deref(&self) -> &Path {
            &self.0
        }
    }

    impl AsRef<Path> for Scratch {
        fn as_ref(&self) -> &Path {
            &self.0
        }
    }

    impl AsRef<std::ffi::OsStr> for Scratch {
        fn as_ref(&self) -> &std::ffi::OsStr {
            self.0.as_os_str()
        }
    }

    impl std::fmt::Debug for Scratch {
        fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            self.0.fmt(formatter)
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            if retaining_evidence() {
                return;
            }
            if !std::thread::panicking()
                || std::env::var_os(crate::fresh_dir::KEEP_ON_FAILURE).is_none()
            {
                fs::remove_dir_all(&self.0).ok();
            }
        }
    }

    fn scratch(tag: &str) -> Scratch {
        Scratch(crate::fresh_dir::create(&format!("tcg-elf-binding-{tag}-")).keep())
    }

    fn run(command: &mut Command, directory: &Path) -> (bool, String, String) {
        // Explicit native fixture paths are bounded by this fresh directory.
        // PATH-resolved system tools are identified by the qualification runner.
        let program = PathBuf::from(command.get_program());
        let native_image = retaining_evidence()
            && program.is_absolute()
            && program.starts_with(directory)
            && program.is_file()
            && !program.is_symlink();
        let before = native_image.then(|| {
            let bytes = fs::read(&program).expect("native image before execution");
            let digest = format!("{:x}", Sha256::digest(&bytes));
            let snapshot = directory.join(format!("native-image-{digest}.elf"));
            match fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&snapshot)
            {
                Ok(mut file) => file
                    .write_all(&bytes)
                    .expect("retain the image before execution"),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
                    assert!(
                        !snapshot.is_symlink(),
                        "retained image must be a regular file"
                    );
                    assert_eq!(
                        fs::read(&snapshot).unwrap(),
                        bytes,
                        "retained image digest collision"
                    );
                }
                Err(error) => panic!("retain native image: {error}"),
            }
            digest
        });
        let result = super::process::command_output_with_timeout(
            command,
            super::process::codegen_link_timeout(),
        )
        .expect("native tool launches");
        let success = result.output.status.success();
        let stdout = String::from_utf8_lossy(&result.output.stdout).into_owned();
        let stderr = String::from_utf8_lossy(&result.output.stderr).into_owned();
        if retaining_evidence() {
            let after = native_image.then(|| {
                format!(
                    "{:x}",
                    Sha256::digest(fs::read(&program).expect("native image after execution"))
                )
            });
            static NEXT_COMMAND: AtomicUsize = AtomicUsize::new(0);
            let path = directory.join(format!(
                "native-command-{:06}.json",
                NEXT_COMMAND.fetch_add(1, AtomicOrdering::Relaxed)
            ));
            let record = serde_json::json!({
                "command": format!("{command:?}"),
                "program": command.get_program().to_string_lossy(),
                "args": command.get_args().map(|arg| arg.to_string_lossy()).collect::<Vec<_>>(),
                "current_dir": command.get_current_dir(),
                "success": success,
                "exit_code": result.output.status.code(),
                "timed_out": result.timed_out,
                "native_image_sha256_before": &before,
                "native_image_sha256_after": &after,
                "retained_native_image": before.as_ref().map(|digest| format!("native-image-{digest}.elf")),
                "stdout": &stdout,
                "stderr": &stderr,
            });
            let file = fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(path)
                .expect("create a unique native command record");
            serde_json::to_writer_pretty(file, &record).expect("write native command record");
            assert_eq!(before, after, "executed native fixture changed on disk");
        }
        assert!(
            !result.timed_out,
            "{command:?} timed out; preserved files={directory:?}"
        );
        (success, stdout, stderr)
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

    /// `readelf --wide` symbol rows `(bind, vis, ndx)` for `name`.
    fn readelf_rows(
        path: &Path,
        directory: &Path,
        flag: &str,
        name: &str,
    ) -> Vec<(String, String, String)> {
        let text = ok(
            Command::new("readelf")
                .env("LC_ALL", "C")
                .args(["--wide", flag])
                .arg(path),
            directory,
        );
        text.lines()
            .filter_map(|line| {
                let columns: Vec<&str> = line.split_whitespace().collect();
                (columns.len() >= 8
                    && columns[0].ends_with(':')
                    && columns[7].split('@').next() == Some(name))
                .then(|| {
                    (
                        columns[4].to_string(),
                        columns[5].to_string(),
                        columns[6].to_string(),
                    )
                })
            })
            .collect()
    }

    fn compile_object(
        module: &Module,
        opt_level: OptLevel,
        directory: &Path,
        name: &str,
    ) -> PathBuf {
        let object = compiler(LINUX, opt_level, true)
            .compile(module)
            .unwrap_or_else(|error| panic!("{name} {opt_level:?}: {error}"))
            .object_code;
        write(directory, name, object)
    }

    #[test]
    fn strong_definitions_override_and_weak_definitions_coalesce() {
        for opt_level in OPT_LEVELS {
            let directory = scratch("weak-def");
            // Two CG objects each define weak `choose` (1 and 3) and a strong
            // caller of it. Non-ODR `Weak` is interposable, so no caller may
            // absorb its body: every call must reach the linker's choice.
            let mut objects = Vec::new();
            for (tag, value) in [("first", 1), ("second", 3)] {
                let mut module = Module::new(tag);
                module.target_info = Some(linux_target_info());
                let choose = constant_function(&mut module, "choose", Linkage::Weak, value);
                calling_function(&mut module, &format!("call_choose_{tag}"), choose);
                let object = compile_object(&module, opt_level, &directory, &format!("{tag}.o"));
                let rows = readelf_rows(&object, &directory, "--symbols", "choose");
                assert_eq!(
                    rows,
                    [("WEAK".into(), "DEFAULT".into(), "1".into())],
                    "{rows:?}"
                );
                objects.push(object);
            }
            let driver = write(
                &directory,
                "driver.c",
                "#include <stdint.h>\n\
                 uint64_t choose(void), call_choose_first(void), call_choose_second(void);\n\
                 int main(int argc, char **argv) {\n\
                   uint64_t want = (uint64_t)(argv[1][0] - '0');\n\
                   return choose() != want || call_choose_first() != want\n\
                       || call_choose_second() != want;\n\
                 }\n",
            );
            let strong = write(
                &directory,
                "strong.c",
                "#include <stdint.h>\nuint64_t choose(void) { return 2; }\n",
            );
            // Weak copies coalesce (no duplicate-definition error); the first
            // in link order is kept and every caller agrees on it.
            let coalesced = directory.join("coalesced");
            ok(
                Command::new("cc")
                    .args(["-fPIE", "-pie"])
                    .arg(&driver)
                    .args(&objects)
                    .arg("-o")
                    .arg(&coalesced),
                &directory,
            );
            ok(Command::new(&coalesced).arg("1"), &directory);
            // A strong definition takes over every weak caller.
            let overridden = directory.join("overridden");
            ok(
                Command::new("cc")
                    .args(["-fPIE", "-pie"])
                    .arg(&driver)
                    .args(&objects)
                    .arg(&strong)
                    .arg("-o")
                    .arg(&overridden),
                &directory,
            );
            ok(Command::new(&overridden).arg("2"), &directory);
            eprintln!("weak definition override/coalescence passed: {opt_level:?} {directory:?}");
        }
    }

    #[test]
    fn internal_functions_with_one_name_link_from_separate_objects() {
        for opt_level in OPT_LEVELS {
            let directory = scratch("internal");
            let mut objects = Vec::new();
            let mut strong_objects = Vec::new();
            for (tag, value) in [("a", 10), ("b", 20)] {
                for (linkage, list) in [
                    (Linkage::Internal, &mut objects),
                    (Linkage::External, &mut strong_objects),
                ] {
                    let mut module = Module::new(tag);
                    module.target_info = Some(linux_target_info());
                    constant_function(&mut module, "shared_helper", linkage, value);
                    constant_function(&mut module, &format!("get_{tag}"), Linkage::External, value);
                    let name = format!("{tag}-{linkage}.o");
                    list.push(compile_object(&module, opt_level, &directory, &name));
                }
            }
            for object in &objects {
                let rows = readelf_rows(object, &directory, "--symbols", "shared_helper");
                assert_eq!(rows.len(), 1, "{rows:?}");
                assert_eq!(rows[0].0, "LOCAL", "{rows:?}");
            }
            let driver = write(
                &directory,
                "driver.c",
                "#include <stdint.h>\nuint64_t get_a(void), get_b(void);\n\
                 int main(void) { return get_a() != 10 || get_b() != 20; }\n",
            );
            let binary = directory.join("internal");
            ok(
                Command::new("cc")
                    .arg(&driver)
                    .args(&objects)
                    .arg("-o")
                    .arg(&binary),
                &directory,
            );
            ok(&mut Command::new(&binary), &directory);
            // Control: the same pair with External helpers must collide, so
            // the positive link above is load-bearing.
            let (success, _, stderr) = run(
                Command::new("cc")
                    .arg(&driver)
                    .args(&strong_objects)
                    .arg("-o")
                    .arg(directory.join("collides")),
                &directory,
            );
            assert!(
                !success && stderr.contains("multiple definition"),
                "strong helpers must collide: {stderr}"
            );
            eprintln!("internal helper isolation passed: {opt_level:?} {directory:?}");
        }
    }

    /// The shared-library object: bound leaves plus a default-visibility
    /// caller for each (callers are what an executable reaches).
    fn shared_library_object(opt_level: OptLevel) -> Vec<u8> {
        let leaves = [
            ("so_default_fn", FunctionSymbolBinding::GLOBAL, 11),
            (
                "so_protected_fn",
                FunctionSymbolBinding::new(FunctionSymbolLinkage::Global, Visibility::Protected),
                22,
            ),
            ("so_hidden_fn", FunctionSymbolBinding::HIDDEN, 33),
            (
                "so_weak_hidden_fn",
                FunctionSymbolBinding::new(FunctionSymbolLinkage::Weak, Visibility::Hidden),
                44,
            ),
            ("so_local_fn", FunctionSymbolBinding::LOCAL, 55),
        ];
        let mut functions = Vec::new();
        let mut bindings = Vec::new();
        for (name, binding, value) in leaves {
            functions.push(returns_constant(name, value));
            bindings.push(binding);
        }
        for (name, _, _) in leaves {
            functions.push(returns_call(&format!("call_{name}"), name));
            bindings.push(FunctionSymbolBinding::GLOBAL);
        }
        // Data definitions with each visibility (no executable access, so no
        // copy relocation is involved).
        let data: Vec<ObjectGlobal> = [
            ("so_default_word", Visibility::Default),
            ("so_protected_word", Visibility::Protected),
            ("so_hidden_word", Visibility::Hidden),
        ]
        .into_iter()
        .map(|(name, visibility)| ObjectGlobal {
            visibility,
            ..object_global(name, 7u64.to_le_bytes().to_vec())
        })
        .collect();
        let pipeline = pipeline(LINUX, opt_level);
        let (prepared, layouts) = prepare(&pipeline, &functions);
        pipeline
            .compile_module_emission_with_symbol_linkage(
                &prepared,
                &data,
                &layouts,
                &ModuleSymbolLinkage::new(bindings, BTreeSet::new()),
            )
            .expect("shared-library object")
            .into_emission()
            .object
    }

    /// The Pipeline-level shared library of [`shared_library_object`], O0-O3,
    /// linked by GNU ld, gold and LLD: hidden, weak hidden and local leaves
    /// stay out of `.dynsym` and the default and protected ones are exported
    /// with their visibility. An executable that defines the default and
    /// protected leaves itself takes over only the library's default call;
    /// the protected, hidden and local calls stay inside the library, and a
    /// hidden function cannot be linked from outside.
    #[test]
    fn hidden_functions_leave_dynsym_and_protected_functions_bind_locally() {
        let linkers = linkers();
        for opt_level in OPT_LEVELS {
            let directory = scratch("visibility");
            let object = write(&directory, "bind.o", shared_library_object(opt_level));
            // The executable interposes both public leaves. Default visibility
            // is preemptible; protected binds inside the library; hidden and
            // local never leave it.
            let driver = write(
                &directory,
                "driver.c",
                "#include <stdint.h>\n\
                 uint64_t so_default_fn(void) { return 111; }\n\
                 uint64_t so_protected_fn(void) { return 222; }\n\
                 uint64_t call_so_default_fn(void), call_so_protected_fn(void),\n\
                   call_so_hidden_fn(void), call_so_weak_hidden_fn(void), call_so_local_fn(void);\n\
                 int main(void) {\n\
                   return call_so_default_fn() != 111 || call_so_protected_fn() != 22\n\
                     || call_so_hidden_fn() != 33 || call_so_weak_hidden_fn() != 44\n\
                     || call_so_local_fn() != 55;\n\
                 }\n",
            );
            let outsider = write(
                &directory,
                "outsider.c",
                "#include <stdint.h>\nuint64_t so_hidden_fn(void);\n\
                 int main(void) { return so_hidden_fn() != 33; }\n",
            );
            for (linker, flags) in &linkers {
                let label = format!("{opt_level:?} {linker}");
                let leg = directory.join(linker);
                fs::create_dir_all(&leg).unwrap();
                let library = leg.join("libtcgbind.so");
                ok(
                    cc_with(flags)
                        .args(["-shared", "-Wl,-z,defs,-z,text,-z,relro,-z,now"])
                        .arg(&object)
                        .arg("-o")
                        .arg(&library),
                    &leg,
                );
                let dynsym = |name: &str| readelf_rows(&library, &leg, "--dyn-syms", name);
                for (name, visibility) in [
                    ("so_default_fn", "DEFAULT"),
                    ("so_protected_fn", "PROTECTED"),
                    ("so_default_word", "DEFAULT"),
                    ("so_protected_word", "PROTECTED"),
                ] {
                    let rows = dynsym(name);
                    assert!(
                        matches!(rows.as_slice(), [(bind, vis, ndx)]
                            if bind == "GLOBAL" && vis == visibility && ndx != "UND"),
                        "{label}: `{name}` exported: {rows:?}"
                    );
                }
                for hidden in [
                    "so_hidden_fn",
                    "so_weak_hidden_fn",
                    "so_local_fn",
                    "so_hidden_word",
                ] {
                    assert!(
                        dynsym(hidden).is_empty(),
                        "{label}: {hidden} must not be exported: {:?}",
                        dynsym(hidden)
                    );
                }
                for caller in [
                    "call_so_default_fn",
                    "call_so_protected_fn",
                    "call_so_hidden_fn",
                    "call_so_weak_hidden_fn",
                    "call_so_local_fn",
                ] {
                    assert_eq!(dynsym(caller).len(), 1, "{label}: {caller} exported");
                }
                let binary = leg.join("interpose");
                let rpath = format!("-Wl,-rpath,{}", leg.display());
                ok(
                    cc_with(flags)
                        .args(["-fPIE", "-pie"])
                        .arg(&driver)
                        .arg(format!("-L{}", leg.display()))
                        .arg("-ltcgbind")
                        .arg(&rpath)
                        .arg("-o")
                        .arg(&binary),
                    &leg,
                );
                ok(&mut Command::new(&binary), &leg);
                // Negative control: a hidden function cannot be linked from
                // outside.
                let (success, _, stderr) = run(
                    cc_with(flags)
                        .arg(&outsider)
                        .arg(format!("-L{}", leg.display()))
                        .arg("-ltcgbind")
                        .arg(&rpath)
                        .arg("-o")
                        .arg(leg.join("outsider")),
                    &leg,
                );
                let refusal = outsider_refusal(linker, Visibility::Hidden, "so_hidden_fn")
                    .expect("a hidden name is refused");
                assert!(
                    !success && stderr.contains(&refusal),
                    "{label}: linking a hidden symbol from outside must fail with `{refusal}`: \
                     {stderr}"
                );
            }
            eprintln!(
                "hidden/protected visibility passed: {opt_level:?} {:?} {directory:?}",
                linker_names(&linkers)
            );
        }
    }

    #[test]
    fn external_weak_references_are_null_when_unlinked_and_resolved_when_linked() {
        for opt_level in OPT_LEVELS {
            let directory = scratch("external-weak");
            let module = external_weak_module(true);
            if retaining_evidence() {
                write(
                    &directory,
                    "source-module.json",
                    serde_json::to_vec_pretty(&module).unwrap(),
                );
                write(
                    &directory,
                    "case.json",
                    serde_json::to_vec_pretty(&serde_json::json!({
                        "case": "external-weak-null-resolved",
                        "optimization": format!("{opt_level:?}"),
                        "target": "aarch64-unknown-linux-gnu",
                    }))
                    .unwrap(),
                );
            }
            let object = compile_object(&module, opt_level, &directory, "weak.o");
            for name in ["maybe_fn", "maybe_data"] {
                let rows = readelf_rows(&object, &directory, "--symbols", name);
                assert_eq!(
                    rows,
                    [("WEAK".into(), "DEFAULT".into(), "UND".into())],
                    "{rows:?}"
                );
            }
            let absent = write(
                &directory,
                "absent.c",
                "#include <stddef.h>\n\
                 void *maybe_fn_address(void), *maybe_data_address(void);\n\
                 int main(void) { return maybe_fn_address() != NULL || maybe_data_address() != NULL; }\n",
            );
            let present = write(
                &directory,
                "present.c",
                "#include <stdint.h>\n\
                 uint64_t maybe_data = 0xda7a;\n\
                 uint64_t maybe_fn(void) { return 0x5eed; }\n\
                 void *maybe_fn_address(void), *maybe_data_address(void);\n\
                 uint64_t call_maybe_fn(void), load_maybe_data(void);\n\
                 int main(void) {\n\
                   return maybe_fn_address() != (void *)maybe_fn\n\
                     || maybe_data_address() != (void *)&maybe_data\n\
                     || call_maybe_fn() != 0x5eed || load_maybe_data() != 0xda7a;\n\
                 }\n",
            );
            for (driver, pie) in [(&absent, true), (&absent, false), (&present, true)] {
                let binary = directory.join(format!(
                    "{}-{}",
                    driver.file_stem().unwrap().to_string_lossy(),
                    if pie { "pie" } else { "nopie" }
                ));
                ok(
                    Command::new("cc")
                        .args(if pie {
                            ["-fPIE", "-pie"]
                        } else {
                            ["-fno-PIE", "-no-pie"]
                        })
                        .arg(driver)
                        .arg(&object)
                        .arg("-o")
                        .arg(&binary),
                    &directory,
                );
                ok(&mut Command::new(&binary), &directory);
            }
            eprintln!("ExternalWeak null/resolved passed: {opt_level:?} {directory:?}");
        }
    }

    /// The trust-ir v45 shared-library leaves: `(name, linkage, visibility,
    /// value)`. Each gets a default-visibility `call_<name>` in the library.
    /// The `linkonce_odr` leaves are COMDAT definitions (their own
    /// `.text.<name>` section in a group their symbol signs).
    const LIBRARY_LEAVES: [(&str, Linkage, Visibility, i128); 7] = [
        (
            "tv45_default_fn",
            Linkage::External,
            Visibility::Default,
            11,
        ),
        (
            "tv45_protected_fn",
            Linkage::External,
            Visibility::Protected,
            22,
        ),
        ("tv45_hidden_fn", Linkage::External, Visibility::Hidden, 33),
        (
            "tv45_weak_protected_fn",
            Linkage::Weak,
            Visibility::Protected,
            44,
        ),
        ("tv45_weak_hidden_fn", Linkage::Weak, Visibility::Hidden, 55),
        (
            "tv45_odr_hidden_fn",
            Linkage::LinkOnceOdr,
            Visibility::Hidden,
            66,
        ),
        (
            "tv45_odr_protected_fn",
            Linkage::LinkOnceOdr,
            Visibility::Protected,
            77,
        ),
    ];

    /// Build the library module, print it as `.trust_ir` text
    /// (retained as `library.tir`) and return the module PARSED BACK from that
    /// text, so the object below comes from the `; #visibility:` directives.
    fn visibility_library_from_text(directory: &Path) -> Module {
        let mut module = Module::new("v45_visibility_library");
        module.target_info = Some(linux_target_info());
        for (name, linkage, visibility, value) in LIBRARY_LEAVES {
            let id = constant_function(&mut module, name, linkage, value);
            module.functions[id.index() as usize].visibility = visibility;
        }
        for (index, (name, ..)) in LIBRARY_LEAVES.iter().enumerate() {
            calling_function(
                &mut module,
                &format!("call_{name}"),
                FuncId::new(index as u32),
            );
        }
        let text = trust_cg_codegen::pipeline::encode_trust_ir_text(&module);
        assert!(
            text.contains("; #visibility: hidden") && text.contains("; #visibility: protected"),
            "{text}"
        );
        write(directory, "library.tir", &text);
        let parsed =
            trust_cg_codegen::pipeline::parse_trust_ir_text(&text).expect("the text form parses");
        assert_eq!(parsed.functions.len(), module.functions.len());
        for (built, reparsed) in module.functions.iter().zip(&parsed.functions) {
            assert_eq!(
                (&built.name, built.linkage, built.visibility),
                (&reparsed.name, reparsed.linkage, reparsed.visibility)
            );
        }
        parsed
    }

    /// trust-ir v45 hidden and protected functions through `Compiler::compile`
    /// (PIC, O0-O3) into a `cc -shared` library linked by GNU ld, gold and
    /// LLD: hidden functions are absent from `.dynsym`, protected ones are
    /// `STV_PROTECTED` there, and the library's own calls to both are bound
    /// at link time (no `JUMP_SLOT`), so an `LD_PRELOAD` interposer defining
    /// every leaf, weak and COMDAT (`linkonce_odr`) hidden and protected ones
    /// included, rebinds only the default-visibility call. Every direct
    /// branch in the library's `call_<leaf>` of a COMDAT leaf targets that
    /// leaf, never a PLT stub (at O0 there is one; O1-O3 may inline it). The
    /// interposer does rebind the executable's own call to the protected
    /// symbol, and a hidden function cannot be linked from outside. Execution
    /// evidence of the glibc loader and these linkers on this host, not a
    /// loader proof.
    #[test]
    fn trust_ir_hidden_and_protected_functions_resist_interposition() {
        let linkers = linkers();
        for opt_level in OPT_LEVELS {
            let directory = scratch("visibility-v45");
            let module = visibility_library_from_text(&directory);
            let object = Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level,
                    parallel: true,
                    relocation_model: trust_cg_codegen::RelocationModel::Pic,
                    ..Default::default()
                },
                TargetSpec::parse(LINUX).expect("triple"),
            )
            .with_codegen_license(permit_unlicensed())
            .compile(&module)
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
            .object_code;
            let object = write(&directory, "library.o", object);
            let readelf = |flag: &str, path: &Path| {
                ok(
                    Command::new("readelf")
                        .env("LC_ALL", "C")
                        .args(["--wide", flag])
                        .arg(path),
                    &directory,
                )
            };
            write(
                &directory,
                "object-symbols.txt",
                readelf("--symbols", &object),
            );
            write(
                &directory,
                "object-relocs.txt",
                readelf("--relocs", &object),
            );
            for (name, linkage, visibility, _) in LIBRARY_LEAVES {
                let bind = if matches!(linkage, Linkage::Weak | Linkage::LinkOnceOdr) {
                    "WEAK"
                } else {
                    "GLOBAL"
                };
                let rows = readelf_rows(&object, &directory, "--symbols", name);
                assert_eq!(rows.len(), 1, "{name}: {rows:?}");
                assert_eq!(
                    (rows[0].0.as_str(), rows[0].1.as_str()),
                    (bind, visibility.to_string().to_uppercase().as_str()),
                    "{opt_level:?} {name}"
                );
                assert_ne!(rows[0].2, "UND", "{name} is defined");
            }

            let interposer_source = write(
                &directory,
                "interposer.c",
                "#include <stdint.h>\n\
                 uint64_t tv45_default_fn(void) { return 111; }\n\
                 uint64_t tv45_protected_fn(void) { return 222; }\n\
                 uint64_t tv45_hidden_fn(void) { return 333; }\n\
                 uint64_t tv45_weak_protected_fn(void) { return 444; }\n\
                 uint64_t tv45_weak_hidden_fn(void) { return 555; }\n\
                 uint64_t tv45_odr_hidden_fn(void) { return 666; }\n\
                 uint64_t tv45_odr_protected_fn(void) { return 777; }\n",
            );
            let driver = write(
                &directory,
                "driver.c",
                "#include <stdint.h>\n#include <stdio.h>\n\
                 uint64_t call_tv45_default_fn(void), call_tv45_protected_fn(void),\n\
                   call_tv45_hidden_fn(void), call_tv45_weak_protected_fn(void),\n\
                   call_tv45_weak_hidden_fn(void), call_tv45_odr_hidden_fn(void),\n\
                   call_tv45_odr_protected_fn(void), tv45_protected_fn(void);\n\
                 int main(void) {\n\
                   printf(\"default=%llu protected=%llu hidden=%llu weak_protected=%llu \
                 weak_hidden=%llu odr_hidden=%llu odr_protected=%llu exe_protected=%llu\\n\",\n\
                     (unsigned long long)call_tv45_default_fn(),\n\
                     (unsigned long long)call_tv45_protected_fn(),\n\
                     (unsigned long long)call_tv45_hidden_fn(),\n\
                     (unsigned long long)call_tv45_weak_protected_fn(),\n\
                     (unsigned long long)call_tv45_weak_hidden_fn(),\n\
                     (unsigned long long)call_tv45_odr_hidden_fn(),\n\
                     (unsigned long long)call_tv45_odr_protected_fn(),\n\
                     (unsigned long long)tv45_protected_fn());\n\
                   return 0;\n\
                 }\n",
            );
            let outsider = write(
                &directory,
                "outsider.c",
                "#include <stdint.h>\nuint64_t tv45_hidden_fn(void);\n\
                 int main(void) { return tv45_hidden_fn() != 33; }\n",
            );
            for (linker, flags) in &linkers {
                let label = format!("{opt_level:?} {linker}");
                let leg = directory.join(linker);
                fs::create_dir_all(&leg).unwrap();
                let library = leg.join("libtcgv45.so");
                ok(
                    cc_with(flags)
                        .args(["-shared", "-Wl,-z,defs,-z,text,-z,relro,-z,now"])
                        .arg(&object)
                        .arg("-o")
                        .arg(&library),
                    &leg,
                );
                write(&leg, "dynsym.txt", readelf("--dyn-syms", &library));
                let dynsym = |name: &str| readelf_rows(&library, &leg, "--dyn-syms", name);
                for (name, bind, visibility) in [
                    ("tv45_default_fn", "GLOBAL", "DEFAULT"),
                    ("tv45_protected_fn", "GLOBAL", "PROTECTED"),
                    ("tv45_weak_protected_fn", "WEAK", "PROTECTED"),
                    ("tv45_odr_protected_fn", "WEAK", "PROTECTED"),
                ] {
                    let rows = dynsym(name);
                    assert_eq!(rows.len(), 1, "{label} {name}: {rows:?}");
                    assert_eq!(
                        (rows[0].0.as_str(), rows[0].1.as_str()),
                        (bind, visibility),
                        "{label} {name}"
                    );
                }
                for hidden in [
                    "tv45_hidden_fn",
                    "tv45_weak_hidden_fn",
                    "tv45_odr_hidden_fn",
                ] {
                    assert!(
                        dynsym(hidden).is_empty(),
                        "{label}: {hidden} must not be exported: {:?}",
                        dynsym(hidden)
                    );
                }
                for (name, ..) in LIBRARY_LEAVES {
                    assert_eq!(
                        dynsym(&format!("call_{name}")).len(),
                        1,
                        "{label}: call_{name}"
                    );
                }
                // Only the default-visibility leaf is reached through the PLT.
                let library_relocs = readelf("--relocs", &library);
                write(&leg, "library-relocs.txt", &library_relocs);
                let jump_slots: Vec<&str> = library_relocs
                    .lines()
                    .filter(|line| line.contains("R_AARCH64_JUMP_SLOT"))
                    .collect();
                assert!(
                    jump_slots
                        .iter()
                        .any(|line| line.contains("tv45_default_fn")),
                    "{label}: {jump_slots:?}"
                );
                for bound in [
                    "tv45_protected_fn",
                    "tv45_hidden_fn",
                    "tv45_weak_protected_fn",
                    "tv45_weak_hidden_fn",
                    "tv45_odr_hidden_fn",
                    "tv45_odr_protected_fn",
                ] {
                    assert!(
                        !library_relocs.contains(bound),
                        "{label}: {bound} must be bound inside the library:\n{library_relocs}"
                    );
                }
                // The COMDAT leaves' callers branch straight to them: one
                // direct branch at O0 (O1-O3 may inline the leaf), never to
                // a PLT stub.
                let symbols = readelf("--syms", &library);
                let disassembly = ok(
                    Command::new("objdump")
                        .env("LC_ALL", "C")
                        .args(["-d", "--no-show-raw-insn"])
                        .arg(&library),
                    &leg,
                );
                write(&leg, "library-disassembly.txt", &disassembly);
                let branches = direct_branches(&disassembly);
                for name in ["tv45_odr_hidden_fn", "tv45_odr_protected_fn"] {
                    let leaf = symbol_value(&symbols, name)
                        .unwrap_or_else(|| panic!("{label}: `{name}` in .symtab"));
                    let caller = format!("call_{name}");
                    let targets: Vec<u64> = branches
                        .iter()
                        .filter(|(function, _)| *function == caller)
                        .map(|(_, target)| *target)
                        .collect();
                    assert!(
                        targets.iter().all(|target| *target == leaf)
                            && (opt_level != OptLevel::O0 || targets.len() == 1),
                        "{label}: `{caller}` must branch straight to `{name}` ({leaf:#x}): \
                         {targets:x?}"
                    );
                }

                let interposer = leg.join("libinterpose.so");
                ok(
                    cc_with(flags)
                        .args(["-shared", "-fPIC"])
                        .arg(&interposer_source)
                        .arg("-o")
                        .arg(&interposer),
                    &leg,
                );
                let binary = leg.join("driver");
                let rpath = format!("-Wl,-rpath,{}", leg.display());
                ok(
                    cc_with(flags)
                        .args(["-fPIE", "-pie"])
                        .arg(&driver)
                        .arg(format!("-L{}", leg.display()))
                        .arg("-ltcgv45")
                        .arg(&rpath)
                        .arg("-o")
                        .arg(&binary),
                    &leg,
                );
                let plain = ok(&mut Command::new(&binary), &leg);
                write(&leg, "run-plain.txt", &plain);
                assert_eq!(
                    plain.trim(),
                    "default=11 protected=22 hidden=33 weak_protected=44 weak_hidden=55 \
                     odr_hidden=66 odr_protected=77 exe_protected=22",
                    "{label}"
                );
                // Negative control: the interposer takes over the default call
                // and the executable's own protected reference, never the
                // library's calls to its protected and hidden definitions.
                let preloaded = ok(Command::new(&binary).env("LD_PRELOAD", &interposer), &leg);
                write(&leg, "run-preload.txt", &preloaded);
                assert_eq!(
                    preloaded.trim(),
                    "default=111 protected=22 hidden=33 weak_protected=44 weak_hidden=55 \
                     odr_hidden=66 odr_protected=77 exe_protected=222",
                    "{label}"
                );

                // Negative control: a hidden function cannot be linked from
                // outside.
                let (success, _, stderr) = run(
                    cc_with(flags)
                        .arg(&outsider)
                        .arg(format!("-L{}", leg.display()))
                        .arg("-ltcgv45")
                        .arg(&rpath)
                        .arg("-o")
                        .arg(leg.join("outsider")),
                    &leg,
                );
                let refusal = outsider_refusal(linker, Visibility::Hidden, "tv45_hidden_fn")
                    .expect("a hidden name is refused");
                assert!(
                    !success && stderr.contains(&refusal),
                    "{label}: linking a hidden symbol from outside must fail with `{refusal}`: \
                     {stderr}"
                );
            }
            eprintln!(
                "trust-ir v45 hidden/protected interposition passed: {opt_level:?} {:?} \
                 {directory:?}",
                linker_names(&linkers)
            );
        }
    }

    // -------------------------------------------------------------------------
    // Hidden and protected references bind locally in a `pic` shared object
    // -------------------------------------------------------------------------

    /// `(name, visibility, value)` of the local-binding library's `External`
    /// function definitions.
    const BOUND_FUNCTIONS: [(&str, Visibility, i128); 3] = [
        ("lb_default_fn", Visibility::Default, 11),
        ("lb_protected_fn", Visibility::Protected, 22),
        ("lb_hidden_fn", Visibility::Hidden, 33),
    ];

    /// `(name, visibility, value)` of the local-binding library's `External`
    /// `u64` data definitions.
    const BOUND_WORDS: [(&str, Visibility, u64); 3] = [
        ("lb_default_word", Visibility::Default, 0x1001),
        ("lb_protected_word", Visibility::Protected, 0x2002),
        ("lb_hidden_word", Visibility::Hidden, 0x3003),
    ];

    /// The definitions no reference from inside the library may reach
    /// through the GOT or a PLT stub.
    const LOCALLY_BOUND: [&str; 4] = [
        "lb_protected_fn",
        "lb_hidden_fn",
        "lb_protected_word",
        "lb_hidden_word",
    ];

    /// The preemptible twins: their references stay GOT/PLT-indirect.
    const PREEMPTIBLE: [&str; 2] = ["lb_default_fn", "lb_default_word"];

    fn push_function(
        module: &mut Module,
        name: String,
        sig: trust_ir::FuncTyId,
        body: Vec<InstrNode>,
    ) {
        let id = FuncId::new(module.functions.len() as u32);
        let mut function = Function::new(id, name, sig, BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.body = body;
        function.blocks.push(block);
        module.functions.push(function);
    }

    /// The local-binding library: each function of [`BOUND_FUNCTIONS`] with a
    /// default-visibility `call_<fn>` and `addr_<fn>` (its address as a data
    /// pointer), and each word of [`BOUND_WORDS`] with `load_<word>` and
    /// `addr_<word>`.
    fn local_binding_library() -> Module {
        let mut module = Module::new("local_binding_library");
        module.target_info = Some(linux_target_info());
        let ptr_sig = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::Ptr],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let u64_sig = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::U64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut leaves = Vec::new();
        for (name, visibility, value) in BOUND_FUNCTIONS {
            let id = constant_function(&mut module, name, Linkage::External, value);
            module.functions[id.index() as usize].visibility = visibility;
            leaves.push((name, id));
        }
        for (name, visibility, value) in BOUND_WORDS {
            module.globals.push(Global {
                name: name.into(),
                ty: Ty::U64,
                mutable: true,
                initializer: Some(Constant::Int(i128::from(value))),
                linkage: Linkage::External,
                tls: None,
                align: Some(8),
                section: None,
                visibility,
                retained: false,
            });
        }
        for (name, id) in leaves {
            calling_function(&mut module, &format!("call_{name}"), id);
            let leaf_sig = module.functions[id.index() as usize].ty;
            push_function(
                &mut module,
                format!("addr_{name}"),
                ptr_sig,
                vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::Func(leaf_sig),
                        value: Constant::FnDef(id),
                    })
                    .with_result(ValueId::new(0)),
                    InstrNode::new(Inst::Cast {
                        op: CastOp::ReifyFnPointer,
                        src_ty: Ty::Func(leaf_sig),
                        dst_ty: Ty::Ptr,
                        operand: ValueId::new(0),
                    })
                    .with_result(ValueId::new(1)),
                    InstrNode::new(Inst::Return {
                        values: vec![ValueId::new(1)],
                    }),
                ],
            );
        }
        for (index, (name, ..)) in BOUND_WORDS.iter().enumerate() {
            let global = GlobalId::new(index as u32);
            push_function(
                &mut module,
                format!("load_{name}"),
                u64_sig,
                vec![
                    InstrNode::new(Inst::GlobalAddr { global }).with_result(ValueId::new(0)),
                    InstrNode::new(Inst::Load {
                        ty: Ty::U64,
                        ptr: ValueId::new(0),
                        volatile: false,
                        align: Some(8),
                    })
                    .with_result(ValueId::new(1)),
                    InstrNode::new(Inst::Return {
                        values: vec![ValueId::new(1)],
                    }),
                ],
            );
            push_function(
                &mut module,
                format!("addr_{name}"),
                ptr_sig,
                vec![
                    InstrNode::new(Inst::GlobalAddr { global }).with_result(ValueId::new(0)),
                    InstrNode::new(Inst::Return {
                        values: vec![ValueId::new(0)],
                    }),
                ],
            );
        }
        module
    }

    /// The `cc` linker selections the local-binding control runs: GNU ld
    /// always, gold and LLD when present. `TCG_REQUIRE_GOLD` and
    /// `TCG_REQUIRE_LLD` turn a missing one into a failure.
    fn linkers() -> Vec<(&'static str, Vec<String>)> {
        let on_path = |tool: &str| {
            std::env::var_os("PATH").and_then(|paths| {
                std::env::split_paths(&paths).find(|dir| dir.join(tool).is_file())
            })
        };
        let mut linkers = vec![("bfd", Vec::new())];
        if on_path("ld.gold").is_some() || Path::new("/usr/bin/ld.gold").is_file() {
            linkers.push(("gold", vec!["-fuse-ld=gold".to_string()]));
        } else {
            assert!(
                std::env::var_os("TCG_REQUIRE_GOLD").is_none(),
                "TCG_REQUIRE_GOLD is set but no ld.gold was found"
            );
            eprintln!("SKIP: no ld.gold (PATH, /usr/bin); the gold legs did not run");
        }
        match std::env::var_os("TCG_LLD_DIR")
            .map(PathBuf::from)
            .or_else(|| std::env::var_os("HOME").map(|home| Path::new(&home).join(".local/bin")))
            .filter(|dir| dir.join("ld.lld").is_file())
            .or_else(|| on_path("ld.lld"))
        {
            Some(dir) => linkers.push((
                "lld",
                vec!["-fuse-ld=lld".to_string(), format!("-B{}/", dir.display())],
            )),
            None => {
                assert!(
                    std::env::var_os("TCG_REQUIRE_LLD").is_none(),
                    "TCG_REQUIRE_LLD is set but no ld.lld was found"
                );
                eprintln!(
                    "SKIP: no ld.lld (TCG_LLD_DIR, ~/.local/bin, PATH); the LLD legs did not run"
                );
            }
        }
        linkers
    }

    /// The names of the [`linkers`] legs a row runs, for its pass line.
    fn linker_names(linkers: &[(&'static str, Vec<String>)]) -> Vec<&'static str> {
        linkers.iter().map(|(name, _)| *name).collect()
    }

    /// One `readelf --relocs --wide` row: offset, type, symbol name (none for
    /// a symbol-less row such as `R_AARCH64_RELATIVE`) and addend.
    #[derive(Debug)]
    struct RelocRow {
        offset: u64,
        kind: String,
        symbol: Option<String>,
        addend: u64,
    }

    fn hex(text: &str) -> u64 {
        u64::from_str_radix(text.trim_start_matches("0x"), 16)
            .unwrap_or_else(|error| panic!("hex `{text}`: {error}"))
    }

    fn reloc_rows(text: &str) -> Vec<RelocRow> {
        text.lines()
            .filter_map(|line| {
                let columns: Vec<&str> = line.split_whitespace().collect();
                if columns.len() < 4 || !columns[2].starts_with("R_AARCH64_") {
                    return None;
                }
                Some(if columns.len() == 4 {
                    RelocRow {
                        offset: hex(columns[0]),
                        kind: columns[2].to_string(),
                        symbol: None,
                        addend: hex(columns[3]),
                    }
                } else {
                    // `value name + addend` (an addend below zero reads `- n`).
                    let addend = hex(columns.last().unwrap());
                    RelocRow {
                        offset: hex(columns[0]),
                        kind: columns[2].to_string(),
                        symbol: Some(columns[4].split('@').next().unwrap().to_string()),
                        addend: if columns[columns.len() - 2] == "-" {
                            addend.wrapping_neg()
                        } else {
                            addend
                        },
                    }
                })
            })
            .collect()
    }

    /// `[start, end)` of each section named in `names`, from `readelf -SW`.
    fn section_ranges(text: &str, names: &[&str]) -> Vec<(String, u64, u64)> {
        text.lines()
            .filter_map(|line| {
                let rest = &line[line.find(']')? + 1..];
                let columns: Vec<&str> = rest.split_whitespace().collect();
                (columns.len() >= 5 && names.contains(&columns[0])).then(|| {
                    let start = hex(columns[2]);
                    (columns[0].to_string(), start, start + hex(columns[4]))
                })
            })
            .collect()
    }

    /// `st_value` of `name` in `.symtab`/`.dynsym`, from `readelf -sW`.
    fn symbol_value(text: &str, name: &str) -> Option<u64> {
        text.lines().find_map(|line| {
            let columns: Vec<&str> = line.split_whitespace().collect();
            (columns.len() >= 8
                && columns[0].ends_with(':')
                && columns[7].split('@').next() == Some(name)
                && columns[6] != "UND")
                .then(|| hex(columns[1]))
        })
    }

    /// Every `b`/`bl` of `objdump -d`, as `(containing function, target)`.
    fn direct_branches(text: &str) -> Vec<(String, u64)> {
        let mut function = String::new();
        let mut branches = Vec::new();
        for line in text.lines() {
            if let Some(name) = line
                .strip_suffix(">:")
                .and_then(|head| head.split_once(" <"))
                .map(|(_, name)| name)
            {
                function = name.to_string();
                continue;
            }
            let columns: Vec<&str> = line.split_whitespace().collect();
            if columns.len() >= 3 && columns[0].ends_with(':') && matches!(columns[1], "b" | "bl") {
                branches.push((function.clone(), hex(columns[2])));
            }
        }
        branches
    }

    /// trust-ir hidden and protected functions AND data in a `pic` shared
    /// object bind every reference from inside the library locally, O0-O3,
    /// with GNU ld, gold and LLD:
    ///
    /// * the object addresses them PC-relatively (no `R_AARCH64_ADR_GOT_PAGE`
    ///   or `LD64_GOT_LO12_NC` names them); the default-visibility function
    ///   and word stay GOT-addressed and the default call stays a call;
    /// * the linked library exports the protected symbols as `PROTECTED` and
    ///   not the hidden ones, carries no dynamic relocation naming them, holds
    ///   none of their addresses in a GOT slot, and branches to a PLT stub
    ///   only from the default caller;
    /// * an `LD_PRELOAD` interposer defining all six names takes over the
    ///   library's default call, function pointer, load and data address and
    ///   the executable's own protected references, never the library's
    ///   references to its protected and hidden definitions (the default rows
    ///   are the near-twin negative);
    /// * a non-PIE executable copy-relocates the default word and the library
    ///   follows the copy through its GOT slot, while every linker refuses
    ///   the copy relocation a protected word would need. That refusal is why
    ///   PC-relative protected data is sound here (see
    ///   `RelocationModel::definition_is_preemptible`).
    ///
    /// Execution evidence for these linkers and the glibc loader on this
    /// host, not a linker or loader proof.
    #[test]
    fn trust_ir_hidden_and_protected_references_bind_locally_in_a_shared_object() {
        let module = local_binding_library();
        let linkers = linkers();
        for opt_level in OPT_LEVELS {
            let directory = scratch("local-binding");
            let object = Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level,
                    relocation_model: trust_cg_codegen::RelocationModel::Pic,
                    ..Default::default()
                },
                TargetSpec::parse(LINUX).expect("triple"),
            )
            .with_codegen_license(permit_unlicensed())
            .compile(&module)
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
            .object_code;
            let object = write(&directory, "library.o", object);
            let readelf = |flags: &[&str], path: &Path| {
                ok(
                    Command::new("readelf")
                        .env("LC_ALL", "C")
                        .arg("--wide")
                        .args(flags)
                        .arg(path),
                    &directory,
                )
            };
            let object_relocs = readelf(&["--relocs"], &object);
            write(&directory, "object-relocs.txt", &object_relocs);
            let object_rows = reloc_rows(&object_relocs);
            let kinds = |name: &str| -> BTreeSet<&str> {
                object_rows
                    .iter()
                    .filter(|row| row.symbol.as_deref() == Some(name))
                    .map(|row| row.kind.as_str())
                    .collect()
            };
            for name in LOCALLY_BOUND {
                let kinds = kinds(name);
                assert!(
                    kinds.contains("R_AARCH64_ADR_PREL_PG_HI21")
                        && kinds.iter().all(|kind| !kind.contains("GOT")),
                    "{opt_level:?}: `{name}` must be addressed PC-relatively: {kinds:?}\n{object_relocs}"
                );
            }
            for name in PREEMPTIBLE {
                let kinds = kinds(name);
                assert!(
                    kinds.contains("R_AARCH64_ADR_GOT_PAGE")
                        && kinds.contains("R_AARCH64_LD64_GOT_LO12_NC")
                        && !kinds.contains("R_AARCH64_ADR_PREL_PG_HI21"),
                    "{opt_level:?}: `{name}` is preemptible and must come from the GOT: {kinds:?}"
                );
            }
            assert!(
                kinds("lb_default_fn")
                    .iter()
                    .any(|kind| ["R_AARCH64_CALL26", "R_AARCH64_JUMP26"].contains(kind)),
                "{opt_level:?}: the preemptible call stays a relocated call"
            );

            for (linker, flags) in &linkers {
                let leg = directory.join(linker);
                fs::create_dir_all(&leg).unwrap();
                let cc = || {
                    let mut command = Command::new("cc");
                    command.env("LC_ALL", "C").args(flags);
                    command
                };
                let label = format!("{opt_level:?} {linker}");
                let library = leg.join("libtcglb.so");
                ok(
                    cc().args(["-shared", "-Wl,-z,defs,-z,text,-z,relro,-z,now"])
                        .arg(&object)
                        .arg("-o")
                        .arg(&library),
                    &leg,
                );
                let exported = BOUND_FUNCTIONS
                    .iter()
                    .map(|(name, visibility, _)| (*name, *visibility))
                    .chain(
                        BOUND_WORDS
                            .iter()
                            .map(|(name, visibility, _)| (*name, *visibility)),
                    );
                for (name, visibility) in exported {
                    let rows = readelf_rows(&library, &leg, "--dyn-syms", name);
                    if visibility == Visibility::Hidden {
                        assert!(rows.is_empty(), "{label}: `{name}` exported: {rows:?}");
                        continue;
                    }
                    assert_eq!(rows.len(), 1, "{label}: `{name}`: {rows:?}");
                    assert_eq!(
                        (rows[0].0.as_str(), rows[0].1.as_str()),
                        ("GLOBAL", visibility.to_string().to_uppercase().as_str()),
                        "{label}: `{name}`"
                    );
                    assert_ne!(rows[0].2, "UND", "{label}: `{name}` is defined");
                }

                let dynamic_relocs = readelf(&["--relocs"], &library);
                write(&leg, "library-relocs.txt", &dynamic_relocs);
                let dynamic_rows = reloc_rows(&dynamic_relocs);
                for row in &dynamic_rows {
                    assert!(
                        !row.symbol
                            .as_deref()
                            .is_some_and(|symbol| LOCALLY_BOUND.contains(&symbol)),
                        "{label}: a dynamic relocation names a locally bound symbol: {row:?}"
                    );
                }
                let sections = readelf(&["--section-headers"], &library);
                let gots = section_ranges(&sections, &[".got", ".got.plt"]);
                let plt = section_ranges(&sections, &[".plt"]);
                assert!(
                    !gots.is_empty() && plt.len() == 1,
                    "{label}: {gots:?} {plt:?}"
                );
                let in_got = |offset: u64| {
                    gots.iter()
                        .any(|(_, start, end)| (*start..*end).contains(&offset))
                };
                for (kind, name) in [
                    ("R_AARCH64_GLOB_DAT", "lb_default_fn"),
                    ("R_AARCH64_GLOB_DAT", "lb_default_word"),
                    ("R_AARCH64_JUMP_SLOT", "lb_default_fn"),
                ] {
                    assert!(
                        dynamic_rows.iter().any(|row| row.kind == kind
                            && row.symbol.as_deref() == Some(name)
                            && in_got(row.offset)),
                        "{label}: `{name}` needs a {kind} GOT slot\n{dynamic_relocs}"
                    );
                }
                let symbols = readelf(&["--syms"], &library);
                for name in LOCALLY_BOUND {
                    let value = symbol_value(&symbols, name)
                        .unwrap_or_else(|| panic!("{label}: `{name}` in .symtab"));
                    let slots: Vec<&RelocRow> = dynamic_rows
                        .iter()
                        .filter(|row| {
                            row.kind == "R_AARCH64_RELATIVE"
                                && in_got(row.offset)
                                && row.addend == value
                        })
                        .collect();
                    assert!(
                        slots.is_empty(),
                        "{label}: a GOT slot holds `{name}` ({value:#x}): {slots:?}"
                    );
                }
                let disassembly = ok(
                    Command::new("objdump")
                        .env("LC_ALL", "C")
                        .args(["-d", "--no-show-raw-insn"])
                        .arg(&library),
                    &leg,
                );
                write(&leg, "library-disassembly.txt", &disassembly);
                let (_, plt_start, plt_end) = plt[0].clone();
                let branches = direct_branches(&disassembly);
                assert!(
                    branches.iter().any(|(function, target)| {
                        function == "call_lb_default_fn" && (plt_start..plt_end).contains(target)
                    }),
                    "{label}: the default call goes through the PLT: {branches:?}"
                );
                for (name, _, _) in BOUND_FUNCTIONS {
                    if name == "lb_default_fn" {
                        continue;
                    }
                    let leaf = symbol_value(&symbols, name).expect("leaf in .symtab");
                    for (function, target) in &branches {
                        if function == &format!("call_{name}") {
                            assert_eq!(
                                *target, leaf,
                                "{label}: `{function}` must branch straight to `{name}`"
                            );
                        }
                    }
                }

                let interposer_source = write(
                    &leg,
                    "interposer.c",
                    "#include <stdint.h>\n\
                     uint64_t lb_default_fn(void) { return 111; }\n\
                     uint64_t lb_protected_fn(void) { return 222; }\n\
                     uint64_t lb_hidden_fn(void) { return 333; }\n\
                     uint64_t lb_default_word = 0xd1, lb_protected_word = 0xd2,\n\
                       lb_hidden_word = 0xd3;\n",
                );
                let interposer = leg.join("libinterpose.so");
                ok(
                    cc().args(["-shared", "-fPIC"])
                        .arg(&interposer_source)
                        .arg("-o")
                        .arg(&interposer),
                    &leg,
                );
                let driver = write(
                    &leg,
                    "driver.c",
                    "#include <stdint.h>\n#include <stdio.h>\n\
                     typedef uint64_t (*leaf)(void);\n\
                     extern uint64_t lb_default_fn(void), lb_protected_fn(void);\n\
                     extern uint64_t lb_default_word, lb_protected_word;\n\
                     uint64_t call_lb_default_fn(void), call_lb_protected_fn(void),\n\
                       call_lb_hidden_fn(void);\n\
                     void *addr_lb_default_fn(void), *addr_lb_protected_fn(void),\n\
                       *addr_lb_hidden_fn(void);\n\
                     uint64_t load_lb_default_word(void), load_lb_protected_word(void),\n\
                       load_lb_hidden_word(void);\n\
                     uint64_t *addr_lb_default_word(void), *addr_lb_protected_word(void),\n\
                       *addr_lb_hidden_word(void);\n\
                     int main(void) {\n\
                       printf(\"call %llu %llu %llu\\n\", (unsigned long long)call_lb_default_fn(),\n\
                         (unsigned long long)call_lb_protected_fn(),\n\
                         (unsigned long long)call_lb_hidden_fn());\n\
                       printf(\"pointer %llu %llu %llu\\n\",\n\
                         (unsigned long long)((leaf)addr_lb_default_fn())(),\n\
                         (unsigned long long)((leaf)addr_lb_protected_fn())(),\n\
                         (unsigned long long)((leaf)addr_lb_hidden_fn())());\n\
                       printf(\"load %llx %llx %llx\\n\", (unsigned long long)load_lb_default_word(),\n\
                         (unsigned long long)load_lb_protected_word(),\n\
                         (unsigned long long)load_lb_hidden_word());\n\
                       printf(\"deref %llx %llx %llx\\n\", (unsigned long long)*addr_lb_default_word(),\n\
                         (unsigned long long)*addr_lb_protected_word(),\n\
                         (unsigned long long)*addr_lb_hidden_word());\n\
                       printf(\"same %d %d %d %d\\n\", addr_lb_default_fn() == (void *)lb_default_fn,\n\
                         addr_lb_protected_fn() == (void *)lb_protected_fn,\n\
                         addr_lb_default_word() == &lb_default_word,\n\
                         addr_lb_protected_word() == &lb_protected_word);\n\
                       return 0;\n\
                     }\n",
                );
                let binary = leg.join("driver");
                let rpath = format!("-Wl,-rpath,{}", leg.display());
                ok(
                    cc().args(["-fPIE", "-pie"])
                        .arg(&driver)
                        .arg(format!("-L{}", leg.display()))
                        .arg("-ltcglb")
                        .arg(&rpath)
                        .arg("-o")
                        .arg(&binary),
                    &leg,
                );
                let plain = ok(&mut Command::new(&binary), &leg);
                write(&leg, "run-plain.txt", &plain);
                assert_eq!(
                    plain,
                    "call 11 22 33\npointer 11 22 33\nload 1001 2002 3003\n\
                     deref 1001 2002 3003\nsame 1 1 1 1\n",
                    "{label}"
                );
                let preloaded = ok(Command::new(&binary).env("LD_PRELOAD", &interposer), &leg);
                write(&leg, "run-preload.txt", &preloaded);
                assert_eq!(
                    preloaded,
                    "call 111 22 33\npointer 111 22 33\nload d1 2002 3003\n\
                     deref d1 2002 3003\nsame 1 0 1 0\n",
                    "{label}: only the default references interpose"
                );

                // Copy relocations: a non-PIE executable that stores to the
                // default word gets a copy the library must follow through
                // its GOT slot; the protected word cannot be copied at all.
                let copy_default = write(
                    &leg,
                    "copy_default.c",
                    "#include <stdint.h>\n\
                     extern uint64_t lb_default_word;\n\
                     uint64_t load_lb_default_word(void), *addr_lb_default_word(void);\n\
                     int main(void) {\n\
                       lb_default_word = 77;\n\
                       return !(load_lb_default_word() == 77\n\
                         && addr_lb_default_word() == &lb_default_word);\n\
                     }\n",
                );
                let copy_binary = leg.join("copy_default");
                ok(
                    cc().args(["-fno-PIE", "-no-pie"])
                        .arg(&copy_default)
                        .arg(format!("-L{}", leg.display()))
                        .arg("-ltcglb")
                        .arg(&rpath)
                        .arg("-o")
                        .arg(&copy_binary),
                    &leg,
                );
                assert!(
                    reloc_rows(&readelf(&["--relocs"], &copy_binary))
                        .iter()
                        .any(|row| {
                            row.kind == "R_AARCH64_COPY"
                                && row.symbol.as_deref() == Some("lb_default_word")
                        }),
                    "{label}: the non-PIE control must copy-relocate the default word"
                );
                ok(&mut Command::new(&copy_binary), &leg);
                let copy_protected = write(
                    &leg,
                    "copy_protected.c",
                    "#include <stdint.h>\n\
                     extern uint64_t lb_protected_word;\n\
                     uint64_t load_lb_protected_word(void);\n\
                     int main(void) {\n\
                       lb_protected_word = 77;\n\
                       return load_lb_protected_word() != 77;\n\
                     }\n",
                );
                let (success, _, stderr) = run(
                    cc().args(["-fno-PIE", "-no-pie"])
                        .arg(&copy_protected)
                        .arg(format!("-L{}", leg.display()))
                        .arg("-ltcglb")
                        .arg(&rpath)
                        .arg("-o")
                        .arg(leg.join("copy_protected")),
                    &leg,
                );
                write(&leg, "copy-protected-link.txt", &stderr);
                assert!(
                    !success && stderr.contains("lb_protected_word"),
                    "{label}: the linker must refuse to copy protected data: {stderr}"
                );
            }
            eprintln!(
                "hidden/protected local binding passed: {opt_level:?} {:?} {directory:?}",
                linker_names(&linkers)
            );
        }
    }

    // -------------------------------------------------------------------------
    // Module-local (Internal/Private) functions through Compiler::compile
    // -------------------------------------------------------------------------

    /// `(C compiler flag, executable link flag)` of each relocation model:
    /// objects for a position-dependent executable, a PIE and a shared object
    /// (whose objects this control links into a PIE).
    fn model_flags(model: trust_cg_codegen::RelocationModel) -> (&'static str, &'static str) {
        match model {
            trust_cg_codegen::RelocationModel::Static => ("-fno-PIE", "-no-pie"),
            trust_cg_codegen::RelocationModel::Pie => ("-fPIE", "-pie"),
            trust_cg_codegen::RelocationModel::Pic => ("-fPIC", "-pie"),
        }
    }

    /// The gcc twin of [`local_binding_module`]: a `static` helper and
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
    /// `global_helper` it also calls the executable's own global `helper`
    /// (`x + 300`, a third object) and checks that neither module's address
    /// taking yields it.
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
    /// taking reaches its own module's helper.
    fn local_binding_expected(global_helper: bool) -> String {
        format!(
            "calls 101 102 103 201 202 203\npointers 105 205 106 206\ncounts 5 5\n\
             same 1 1 1 1 1 1 1 1\ndistinct 1{}\n",
            if global_helper { " 1 1 global 304" } else { "" }
        )
    }

    /// `(type, bind, vis, ndx, value)` of every `readelf --wide --symbols`
    /// row named `name`.
    fn symbol_rows(text: &str, name: &str) -> Vec<(String, String, String, String, u64)> {
        text.lines()
            .filter_map(|line| {
                let columns: Vec<&str> = line.split_whitespace().collect();
                (columns.len() >= 8
                    && columns[0].ends_with(':')
                    && columns[7].split('@').next() == Some(name))
                .then(|| {
                    (
                        columns[3].to_string(),
                        columns[4].to_string(),
                        columns[5].to_string(),
                        columns[6].to_string(),
                        hex(columns[1]),
                    )
                })
            })
            .collect()
    }

    /// readelf's account of one relocatable object: `helper` is at most one
    /// symbol, a defined `LOCAL` `FUNC` one, so every relocation naming
    /// `helper` names that local definition (relocations against a section
    /// symbol are local by construction). Returns the kinds of the
    /// relocations naming `helper`.
    fn readelf_local_helper(object: &Path, directory: &Path, label: &str) -> BTreeSet<String> {
        let readelf = |flag: &str| {
            ok(
                Command::new("readelf")
                    .env("LC_ALL", "C")
                    .args(["--wide", flag])
                    .arg(object),
                directory,
            )
        };
        let symbols = readelf("--symbols");
        let relocs = readelf("--relocs");
        let stem = object.file_stem().unwrap().to_string_lossy().into_owned();
        write(directory, &format!("{stem}-symbols.txt"), &symbols);
        write(directory, &format!("{stem}-relocs.txt"), &relocs);
        let rows = symbol_rows(&symbols, "helper");
        assert!(
            rows.len() <= 1
                && rows.iter().all(|(kind, bind, _, ndx, _)| {
                    kind == "FUNC" && bind == "LOCAL" && ndx != "UND"
                }),
            "{label}: {object:?} must spell `helper` only as its local definition: {rows:?}"
        );
        let kinds: BTreeSet<String> = reloc_rows(&relocs)
            .into_iter()
            .filter(|row| row.symbol.as_deref() == Some("helper"))
            .map(|row| row.kind)
            .collect();
        assert!(
            kinds.is_empty() || rows.len() == 1,
            "{label}: {object:?} relocates against an undefined `helper`: {kinds:?}"
        );
        kinds
    }

    /// The one target of every `b`/`bl` in `function` of a linked image. It
    /// must be one of the `LOCAL` `helper` definitions and not the global one.
    fn direct_helper_target(
        branches: &[(String, u64)],
        local_helpers: &[u64],
        global_helper: u64,
        function: &str,
        label: &str,
    ) -> u64 {
        let targets: BTreeSet<u64> = branches
            .iter()
            .filter(|(name, _)| name == function)
            .map(|(_, target)| *target)
            .collect();
        assert!(
            targets.len() == 1
                && targets.iter().all(|target| local_helpers.contains(target))
                && !targets.contains(&global_helper),
            "{label}: `{function}` must branch only to one local helper {local_helpers:x?} \
             (global {global_helper:#x}): {targets:x?}"
        );
        *targets.first().unwrap()
    }

    /// Two trust-ir modules `a` and `b`, each with its own Internal (`a`) or
    /// Private (`b`) `helper`, compiled by `Compiler::compile` at O0-O3 under
    /// `static`, `pie` and `pic`, sequential and parallel, linked with a third
    /// C object defining a global `helper` into one executable by
    /// `run_link` (GNU ld) and by `cc` with gold and LLD. Every direct call,
    /// function pointer in a local, function pointer in a global and address
    /// taking in `a` and `b` reaches its own module's helper; the two
    /// takings in each module and its data slot agree; the three helpers are
    /// distinct. readelf reads each helper as a defined `LOCAL` `FUNC` symbol
    /// that every relocation naming it uses, and objdump shows `a_direct` and
    /// `b_direct` branching to two different local helpers, never the global
    /// one. The same program built from the gcc twin with `static` functions
    /// prints the same result. Execution evidence for these linkers on this
    /// host, not a linker proof.
    #[test]
    fn module_local_functions_bind_to_their_own_object_in_executables() {
        let modules = [
            ("a", local_binding_module("a", Linkage::Internal, 100)),
            ("b", local_binding_module("b", Linkage::Private, 200)),
        ];
        let linkers = linkers();
        let expected = local_binding_expected(true);
        for opt_level in OPT_LEVELS {
            let directory = scratch("module-local-exe");
            let o_flag = format!("-O{}", opt_level as u8);
            for model in RELOCATION_MODELS {
                let (cc_flag, link_flag) = model_flags(model);
                let model_dir = directory.join(model.to_string());
                fs::create_dir_all(&model_dir).unwrap();
                let cc_object = |source: &Path, object: &str| {
                    let path = model_dir.join(object);
                    ok(
                        Command::new("cc")
                            .args(["-c", &o_flag, cc_flag])
                            .arg(source)
                            .arg("-o")
                            .arg(&path),
                        &model_dir,
                    );
                    path
                };
                let driver = cc_object(
                    &write(&model_dir, "driver.c", local_binding_driver(true)),
                    "driver.o",
                );
                let global = cc_object(
                    &write(
                        &model_dir,
                        "global_helper.c",
                        "#include <stdint.h>\n\
                         uint64_t helper(uint64_t x) { return x + 300; }\n",
                    ),
                    "global_helper.o",
                );
                let mut gcc_objects = Vec::new();
                for (tag, offset) in [("a", 100), ("b", 200)] {
                    let source = write(
                        &model_dir,
                        &format!("gcc_{tag}.c"),
                        local_binding_c_source(tag, offset),
                    );
                    let object = cc_object(&source, &format!("gcc_{tag}.o"));
                    readelf_local_helper(&object, &model_dir, "gcc");
                    gcc_objects.push(object);
                }
                let gcc_binary = model_dir.join("gcc_program");
                ok(
                    Command::new("cc")
                        .arg(link_flag)
                        .arg(&driver)
                        .arg(&global)
                        .args(&gcc_objects)
                        .arg("-o")
                        .arg(&gcc_binary),
                    &model_dir,
                );
                let gcc_output = ok(&mut Command::new(&gcc_binary), &model_dir);
                assert_eq!(gcc_output, expected, "gcc {opt_level:?} {model}");

                for parallel in [false, true] {
                    let label = format!("{opt_level:?} {model} parallel={parallel}");
                    let leg_dir = model_dir.join(if parallel { "parallel" } else { "sequential" });
                    fs::create_dir_all(&leg_dir).unwrap();
                    let mut objects = Vec::new();
                    for (tag, module) in &modules {
                        let result = local_binding_compiler(LINUX, opt_level, model, parallel)
                            .compile(module)
                            .unwrap_or_else(|error| panic!("{label} {tag}: {error}"));
                        assert_emission_path(
                            &result,
                            parallel,
                            LOCAL_BINDING_CORE_FUNCTIONS + LOCAL_BINDING_PADDING,
                            &label,
                        );
                        let object = write(&leg_dir, &format!("{tag}.o"), &result.object_code);
                        let kinds = readelf_local_helper(&object, &leg_dir, &label);
                        for kind in [
                            "R_AARCH64_ADR_PREL_PG_HI21",
                            "R_AARCH64_ADD_ABS_LO12_NC",
                            "R_AARCH64_ABS64",
                        ] {
                            assert!(kinds.contains(kind), "{label} {tag}: {kind}: {kinds:?}");
                        }
                        assert!(
                            kinds.contains("R_AARCH64_CALL26")
                                || kinds.contains("R_AARCH64_JUMP26"),
                            "{label} {tag}: the direct call relocates against helper: {kinds:?}"
                        );
                        assert!(
                            kinds.iter().all(|kind| !kind.contains("GOT")),
                            "{label} {tag}: {kinds:?}"
                        );
                        objects.push(object);
                    }
                    for (linker, flags) in &linkers {
                        let binary = leg_dir.join(format!("program-{linker}"));
                        let mut inputs = vec![driver.clone(), global.clone()];
                        inputs.extend(objects.iter().cloned());
                        if *linker == "bfd" {
                            let mut request =
                                trust_cg_codegen::link_driver::LinkRequest::executable(
                                    TargetSpec::parse(LINUX).expect("triple"),
                                    inputs,
                                    binary.clone(),
                                );
                            request.position_independence = if link_flag == "-no-pie" {
                                trust_cg_codegen::link_driver::PositionIndependence::NoPie
                            } else {
                                trust_cg_codegen::link_driver::PositionIndependence::Pie
                            };
                            trust_cg_codegen::link_driver::run_link(&request, "cc")
                                .unwrap_or_else(|error| panic!("{label} run_link: {error}"));
                        } else {
                            ok(
                                Command::new("cc")
                                    .env("LC_ALL", "C")
                                    .args(flags)
                                    .arg(link_flag)
                                    .args(&inputs)
                                    .arg("-o")
                                    .arg(&binary),
                                &leg_dir,
                            );
                        }
                        let label = format!("{label} {linker}");
                        let output = ok(&mut Command::new(&binary), &leg_dir);
                        assert_eq!(output, expected, "{label}");
                        assert_eq!(output, gcc_output, "{label}: the gcc twin agrees");

                        let symbols = ok(
                            Command::new("readelf")
                                .env("LC_ALL", "C")
                                .args(["--wide", "--syms"])
                                .arg(&binary),
                            &leg_dir,
                        );
                        let helpers: Vec<_> = symbol_rows(&symbols, "helper")
                            .into_iter()
                            .filter(|(kind, _, _, ndx, _)| kind == "FUNC" && ndx != "UND")
                            .collect();
                        let values = |bind: &str| -> Vec<u64> {
                            helpers
                                .iter()
                                .filter(|row| row.1 == bind)
                                .map(|row| row.4)
                                .collect()
                        };
                        let (local_helpers, global_helpers) = (values("LOCAL"), values("GLOBAL"));
                        assert!(
                            local_helpers.len() == 2 && global_helpers.len() == 1,
                            "{label}: two local helpers and one global: {helpers:?}"
                        );
                        let disassembly = ok(
                            Command::new("objdump")
                                .env("LC_ALL", "C")
                                .args(["-d", "--no-show-raw-insn"])
                                .arg(&binary),
                            &leg_dir,
                        );
                        let branches = direct_branches(&disassembly);
                        let a = direct_helper_target(
                            &branches,
                            &local_helpers,
                            global_helpers[0],
                            "a_direct",
                            &label,
                        );
                        let b = direct_helper_target(
                            &branches,
                            &local_helpers,
                            global_helpers[0],
                            "b_direct",
                            &label,
                        );
                        assert_ne!(a, b, "{label}: each module calls its own helper");
                    }
                }
            }
            // Text placement: both modules with function sections, module
            // `a`'s helper in an explicit section, linked with --gc-sections.
            let sections_dir = directory.join("sections");
            fs::create_dir_all(&sections_dir).unwrap();
            let mut inputs = Vec::new();
            for (name, source) in [
                ("driver", local_binding_driver(true)),
                (
                    "global_helper",
                    "#include <stdint.h>\nuint64_t helper(uint64_t x) { return x + 300; }\n"
                        .to_string(),
                ),
            ] {
                let object = sections_dir.join(format!("{name}.o"));
                ok(
                    Command::new("cc")
                        .args(["-c", &o_flag, "-fno-PIE"])
                        .arg(write(&sections_dir, &format!("{name}.c"), source))
                        .arg("-o")
                        .arg(&object),
                    &sections_dir,
                );
                inputs.push(object);
            }
            for (tag, module) in &modules {
                let mut module = module.clone();
                if *tag == "a" {
                    module.functions[0].section = Some(".text.tcg_local".into());
                }
                let object = Compiler::new_for_target_spec(
                    CompilerConfig {
                        opt_level,
                        function_sections: true,
                        ..Default::default()
                    },
                    TargetSpec::parse(LINUX).expect("triple"),
                )
                .with_codegen_license(permit_unlicensed())
                .compile(&module)
                .unwrap_or_else(|error| panic!("{opt_level:?} sections {tag}: {error}"))
                .object_code;
                let object = write(&sections_dir, &format!("{tag}.o"), object);
                readelf_local_helper(&object, &sections_dir, "sections");
                inputs.push(object);
            }
            let binary = sections_dir.join("program");
            ok(
                Command::new("cc")
                    .args(["-no-pie", "-Wl,--gc-sections"])
                    .args(&inputs)
                    .arg("-o")
                    .arg(&binary),
                &sections_dir,
            );
            assert_eq!(
                ok(&mut Command::new(&binary), &sections_dir),
                expected,
                "{opt_level:?} function sections, --gc-sections"
            );
            eprintln!("module-local executable binding passed: {opt_level:?} {directory:?}");
            fs::remove_dir_all(&directory).ok();
        }
    }

    /// Modules `a` (Internal helper) and `b` (Private helper) compiled under
    /// `pic` at O0-O3 and linked by `run_link` into one shared library each,
    /// both loaded by one program. Neither library exports a helper or
    /// carries a dynamic relocation naming one, so neither library's calls,
    /// pointers or address takings reach the other's helper, and an
    /// `LD_PRELOAD` interposer defining `helper` reaches none of them. The
    /// gcc twins with `static` functions behave the same. Near-twin control:
    /// with `a`'s helper External its library exports it, and the interposer
    /// takes over `a`'s direct call, local pointer, data slot and takings.
    /// Execution evidence for GNU ld and the glibc loader on this host, not a
    /// loader proof.
    #[test]
    fn module_local_functions_resist_interposition_in_a_shared_object() {
        let expected = local_binding_expected(false);
        let pic = trust_cg_codegen::RelocationModel::Pic;
        for opt_level in OPT_LEVELS {
            let directory = scratch("module-local-shared");
            let o_flag = format!("-O{}", opt_level as u8);
            let interposer = directory.join("libinterpose.so");
            ok(
                Command::new("cc")
                    .args(["-shared", "-fPIC"])
                    .arg(write(
                        &directory,
                        "interposer.c",
                        "#include <stdint.h>\n\
                         uint64_t helper(uint64_t x) { return x + 900; }\n",
                    ))
                    .arg("-o")
                    .arg(&interposer),
                &directory,
            );
            let driver = write(&directory, "driver.c", local_binding_driver(false));
            // Link a program against `lib<prefix>a.so` and `lib<prefix>b.so`
            // in `library_dir` and run it without and with the interposer.
            let run_program = |library_dir: &Path, prefix: &str| -> (String, String) {
                let binary = library_dir.join("program");
                ok(
                    Command::new("cc")
                        .args(["-fPIE", "-pie"])
                        .arg(&driver)
                        .arg(format!("-L{}", library_dir.display()))
                        .arg(format!("-l{prefix}a"))
                        .arg(format!("-l{prefix}b"))
                        .arg(format!("-Wl,-rpath,{}", library_dir.display()))
                        .arg("-o")
                        .arg(&binary),
                    library_dir,
                );
                let plain = ok(&mut Command::new(&binary), library_dir);
                let preloaded = ok(
                    Command::new(&binary).env("LD_PRELOAD", &interposer),
                    library_dir,
                );
                write(library_dir, "run-plain.txt", &plain);
                write(library_dir, "run-preload.txt", &preloaded);
                (plain, preloaded)
            };

            // gcc twins: `static` helpers in two -fPIC shared objects.
            let gcc_dir = directory.join("gcc");
            fs::create_dir_all(&gcc_dir).unwrap();
            for (tag, offset) in [("a", 100), ("b", 200)] {
                ok(
                    Command::new("cc")
                        .args(["-shared", "-fPIC", &o_flag])
                        .arg(write(
                            &gcc_dir,
                            &format!("gcc_{tag}.c"),
                            local_binding_c_source(tag, offset),
                        ))
                        .arg("-o")
                        .arg(gcc_dir.join(format!("libgcc{tag}.so"))),
                    &gcc_dir,
                );
            }
            let gcc_run = run_program(&gcc_dir, "gcc");
            assert_eq!(
                gcc_run,
                (expected.clone(), expected.clone()),
                "gcc {opt_level:?}"
            );

            for (leg_name, a_linkage) in
                [("local", Linkage::Internal), ("control", Linkage::External)]
            {
                let leg = directory.join(leg_name);
                fs::create_dir_all(&leg).unwrap();
                let label = format!("{opt_level:?} {leg_name}");
                let mut objects = Vec::new();
                let mut exported = Vec::new();
                let mut dynamic_relocs = Vec::new();
                for (tag, linkage, offset) in [("a", a_linkage, 100), ("b", Linkage::Private, 200)]
                {
                    let module = local_binding_module(tag, linkage, offset);
                    let object = local_binding_compiler(LINUX, opt_level, pic, true)
                        .compile(&module)
                        .unwrap_or_else(|error| panic!("{label} {tag}: {error}"))
                        .object_code;
                    let object = write(&leg, &format!("{tag}.o"), object);
                    let library = leg.join(format!("libtcg{tag}.so"));
                    let mut request = trust_cg_codegen::link_driver::LinkRequest::executable(
                        TargetSpec::parse(LINUX).expect("triple"),
                        vec![object.clone()],
                        library.clone(),
                    );
                    request.kind = trust_cg_codegen::link_driver::LinkOutputKind::SharedLibrary;
                    trust_cg_codegen::link_driver::run_link(&request, "cc")
                        .unwrap_or_else(|error| panic!("{label} {tag} run_link: {error}"));
                    exported.extend(readelf_rows(&library, &leg, "--dyn-syms", "helper"));
                    let library_relocs = ok(
                        Command::new("readelf")
                            .env("LC_ALL", "C")
                            .args(["--wide", "--relocs"])
                            .arg(&library),
                        &leg,
                    );
                    write(&leg, &format!("lib{tag}-relocs.txt"), &library_relocs);
                    dynamic_relocs.extend(reloc_rows(&library_relocs));
                    objects.push(object);
                }
                let (plain, preloaded) = run_program(&leg, "tcg");
                assert_eq!(plain, expected, "{label}: without the interposer");
                if a_linkage == Linkage::Internal {
                    for object in &objects {
                        readelf_local_helper(object, &leg, &label);
                    }
                    assert!(
                        exported.is_empty(),
                        "{label}: helper exported: {exported:?}"
                    );
                    assert!(
                        dynamic_relocs
                            .iter()
                            .all(|row| row.symbol.as_deref() != Some("helper")),
                        "{label}: a dynamic relocation names helper: {dynamic_relocs:?}"
                    );
                    assert_eq!(preloaded, expected, "{label}: the interposer must not bind");
                    assert_eq!(
                        (plain, preloaded),
                        gcc_run.clone(),
                        "{label}: the gcc twin agrees"
                    );
                } else {
                    // The interposer is load-bearing: a default-visibility
                    // helper is preempted everywhere module `a` names it.
                    assert_eq!(exported.len(), 1, "{label}: helper exported: {exported:?}");
                    assert_eq!(
                        preloaded,
                        "calls 901 902 903 201 202 203\npointers 905 205 906 206\n\
                         counts 0 5\nsame 1 1 1 1 1 1 1 1\ndistinct 1\n",
                        "{label}: the interposer must take over the External helper"
                    );
                }
            }
            eprintln!("module-local shared-object binding passed: {opt_level:?} {directory:?}");
            fs::remove_dir_all(&directory).ok();
        }
    }

    /// Modules `a` and `b` each DEFINE an Internal (then Private)
    /// `rust_eh_personality` that counts its calls, and each run an invoke of
    /// a C thrower (`_Unwind_RaiseException` with no handler anywhere, so the
    /// search phase asks every frame's personality and the raise returns to
    /// the thrower). Linked into one executable at O0-O3 by
    /// `run_link` (GNU ld), gold and LLD, in both link orders, each module's
    /// frame runs its OWN personality: after `a_run` the counts are `1 0`,
    /// after `b_run` `1 1`. With a shared weak `DW.ref.rust_eh_personality`
    /// slot the linker keeps one object's cell and the other object's frame
    /// runs the wrong personality (`2 0` or `0 2`). Execution evidence for
    /// these linkers and libgcc's unwinder on this host.
    #[test]
    fn module_local_personality_runs_for_its_own_objects_frames() {
        let linkers = linkers();
        for opt_level in OPT_LEVELS {
            let directory = scratch("module-local-personality");
            let thrower = directory.join("thrower.o");
            ok(
                Command::new("cc")
                    .args(["-c", "-O1", "-fexceptions"])
                    .arg(write(
                        &directory,
                        "thrower.c",
                        "#include <stdint.h>\n#include <string.h>\n#include <unwind.h>\n\
                         static void drop_exception(_Unwind_Reason_Code c,\n\
                           struct _Unwind_Exception *e) { (void)c; (void)e; }\n\
                         int32_t thrower(int32_t x) {\n\
                           static struct _Unwind_Exception exception;\n\
                           memset(&exception, 0, sizeof exception);\n\
                           exception.exception_class = 0x5443472d4c4f434cULL;\n\
                           exception.exception_cleanup = drop_exception;\n\
                           /* The return code is not read: libgcc on this host returns\n\
                              garbage from a search phase that finds no handler. */\n\
                           (void)_Unwind_RaiseException(&exception);\n\
                           return x + 100;\n\
                         }\n",
                    ))
                    .arg("-o")
                    .arg(&thrower),
                &directory,
            );
            let driver = directory.join("driver.o");
            ok(
                Command::new("cc")
                    .args(["-c", "-O1"])
                    .arg(write(
                        &directory,
                        "driver.c",
                        "#include <stdint.h>\n#include <stdio.h>\n\
                         int32_t a_run(int32_t), b_run(int32_t);\n\
                         uint64_t a_personality_calls(void), b_personality_calls(void);\n\
                         int main(void) {\n\
                           int32_t a = a_run(1);\n\
                           printf(\"a_run %d: %llu %llu\\n\", a,\n\
                             (unsigned long long)a_personality_calls(),\n\
                             (unsigned long long)b_personality_calls());\n\
                           int32_t b = b_run(2);\n\
                           printf(\"b_run %d: %llu %llu\\n\", b,\n\
                             (unsigned long long)a_personality_calls(),\n\
                             (unsigned long long)b_personality_calls());\n\
                           return 0;\n\
                         }\n",
                    ))
                    .arg("-o")
                    .arg(&driver),
                &directory,
            );
            for linkage in [Linkage::Internal, Linkage::Private] {
                let leg = directory.join(linkage.to_string());
                fs::create_dir_all(&leg).unwrap();
                let objects: Vec<PathBuf> = ["a", "b"]
                    .iter()
                    .map(|tag| {
                        let object = compiler(LINUX, opt_level, false)
                            .compile(&local_personality_module(tag, Some(linkage)))
                            .unwrap_or_else(|error| panic!("{opt_level:?} {tag}: {error}"))
                            .object_code;
                        let path = write(&leg, &format!("{tag}.o"), object);
                        let rows =
                            readelf_rows(&path, &leg, "--symbols", "DW.ref.rust_eh_personality");
                        assert_eq!(
                            rows,
                            [("LOCAL".into(), "DEFAULT".into(), rows[0].2.clone())],
                            "{opt_level:?} {tag}: the slot is object-local"
                        );
                        path
                    })
                    .collect();
                for order in [[0, 1], [1, 0]] {
                    for (linker, flags) in &linkers {
                        let binary = leg.join(format!("program-{linker}-{}{}", order[0], order[1]));
                        let inputs = vec![
                            driver.clone(),
                            thrower.clone(),
                            objects[order[0]].clone(),
                            objects[order[1]].clone(),
                        ];
                        if *linker == "bfd" {
                            let request = trust_cg_codegen::link_driver::LinkRequest::executable(
                                TargetSpec::parse(LINUX).expect("triple"),
                                inputs,
                                binary.clone(),
                            );
                            trust_cg_codegen::link_driver::run_link(&request, "cc")
                                .unwrap_or_else(|error| panic!("{opt_level:?} run_link: {error}"));
                        } else {
                            ok(
                                Command::new("cc")
                                    .env("LC_ALL", "C")
                                    .args(flags)
                                    .args(&inputs)
                                    .arg("-o")
                                    .arg(&binary),
                                &leg,
                            );
                        }
                        assert_eq!(
                            ok(&mut Command::new(&binary), &leg),
                            "a_run 101: 1 0\nb_run 102: 1 1\n",
                            "{opt_level:?} {linkage} {linker} order {order:?}: each frame runs \
                             its own object's personality"
                        );
                    }
                }
            }
            eprintln!("module-local personality passed: {opt_level:?} {directory:?}");
            fs::remove_dir_all(&directory).ok();
        }
    }

    /// The objects of `a` and `b` compiled separately, and of their merge in
    /// both input orders: `(label, objects)`.
    fn separate_and_merged_objects(
        a: &Module,
        b: &Module,
        opt_level: OptLevel,
        directory: &Path,
        tag: &str,
    ) -> Vec<(String, Vec<PathBuf>)> {
        let object = |module: &Module, name: String| {
            let bytes = compiler(LINUX, opt_level, false)
                .compile(module)
                .unwrap_or_else(|error| panic!("{opt_level:?} {name}: {error}"))
                .object_code;
            write(directory, &name, bytes)
        };
        let mut legs = vec![(
            "separate".to_string(),
            vec![
                object(a, format!("{tag}-a.o")),
                object(b, format!("{tag}-b.o")),
            ],
        )];
        for (order, inputs) in [
            ("ab", [a.clone(), b.clone()]),
            ("ba", [b.clone(), a.clone()]),
        ] {
            let merged = trust_cg_codegen::module_merge::merge_modules(&inputs)
                .unwrap_or_else(|error| panic!("{tag} merge {order}: {error}"));
            legs.push((
                format!("merged-{order}"),
                vec![object(&merged, format!("{tag}-merged-{order}.o"))],
            ));
        }
        legs
    }

    /// A module DECLARING `helper` and a module DEFINING a module-local
    /// `helper`, compiled separately and merged in both orders (the merge
    /// renames the local definition apart): linked with a C object defining
    /// a global `helper` (`x + 300`), the declaration binds to the global one
    /// and the local definition only to its own module's calls, O0-O3.
    #[test]
    fn separately_compiled_declaration_binds_to_the_global_helper() {
        for opt_level in OPT_LEVELS {
            let directory = scratch("declaration-local-pair");
            let driver = write(
                &directory,
                "driver.c",
                "#include <stdint.h>\n#include <stdio.h>\n\
                 uint64_t a_call(uint64_t), b_call(uint64_t);\n\
                 uint64_t helper(uint64_t x) { return x + 300; }\n\
                 int main(void) {\n\
                   printf(\"%llu %llu\\n\", (unsigned long long)a_call(1),\n\
                     (unsigned long long)b_call(1));\n\
                   return 0;\n\
                 }\n",
            );
            for linkage in [Linkage::Internal, Linkage::Private] {
                let (a, b) = declaration_and_local_definition_modules(linkage);
                for (leg, objects) in separate_and_merged_objects(
                    &a,
                    &b,
                    opt_level,
                    &directory,
                    &format!("{linkage}"),
                ) {
                    let binary = directory.join(format!("program-{linkage}-{leg}"));
                    ok(
                        Command::new("cc")
                            .arg(&driver)
                            .args(&objects)
                            .arg("-o")
                            .arg(&binary),
                        &directory,
                    );
                    assert_eq!(
                        ok(&mut Command::new(&binary), &directory),
                        "301 201\n",
                        "{opt_level:?} {linkage} {leg}"
                    );
                }
            }
            fs::remove_dir_all(&directory).ok();
        }
    }

    /// Module `a`'s module-local `helper` (`x + 200`) and module `b`'s
    /// `SymbolAddr` references to `helper` (in a function body, an indirect
    /// call and a global initializer), compiled separately and merged in
    /// both orders, linked by GNU ld, gold and LLD with a C object defining
    /// a global `helper` (`x + 300`), O0-O3: `a` reaches its own body and
    /// every `b` reference the global one, as under separate compilation.
    #[test]
    fn merged_symbol_addresses_bind_like_separate_objects() {
        for opt_level in OPT_LEVELS {
            let directory = scratch("symbol-address-merge");
            let driver = write(
                &directory,
                "driver.c",
                "#include <stdint.h>\n#include <stdio.h>\n\
                 typedef int64_t (*fn)(int64_t);\n\
                 int64_t a_call(int64_t), b_callp(int64_t), b_tbl_call(int64_t);\n\
                 fn a_ptr(void), b_ptr(void);\n\
                 extern fn b_tbl;\n\
                 int64_t helper(int64_t x) { return x + 300; }\n\
                 int main(void) {\n\
                   printf(\"a_call=%lld a_ptr=%lld b_ptr=%lld b_callp=%lld b_tbl=%lld \"\n\
                     \"b_tbl_call=%lld\\n\", (long long)a_call(1), (long long)a_ptr()(1),\n\
                     (long long)b_ptr()(1), (long long)b_callp(1), (long long)b_tbl(1),\n\
                     (long long)b_tbl_call(1));\n\
                   return 0;\n\
                 }\n",
            );
            for linkage in ["internal", "private"] {
                let (a, b) = symbol_address_and_local_definition_modules(linkage);
                for (leg, objects) in
                    separate_and_merged_objects(&a, &b, opt_level, &directory, linkage)
                {
                    for (linker, flags) in linkers() {
                        let binary = directory.join(format!("program-{linkage}-{leg}-{linker}"));
                        ok(
                            Command::new("cc")
                                .args(&flags)
                                .arg(&driver)
                                .args(&objects)
                                .arg("-o")
                                .arg(&binary),
                            &directory,
                        );
                        assert_eq!(
                            ok(&mut Command::new(&binary), &directory),
                            "a_call=201 a_ptr=201 b_ptr=301 b_callp=301 b_tbl=301 \
                             b_tbl_call=301\n",
                            "{opt_level:?} {linkage} {leg} {linker}"
                        );
                    }
                }
            }
            fs::remove_dir_all(&directory).ok();
        }
    }

    /// The verifier's personality-scope pair ([`personality_scope_modules`]
    /// with `a`'s module-local counting personality), linked with a C
    /// `thrower` that raises once (the search phase finds no handler, so it
    /// returns `x + 100`) through GNU ld, gold and LLD at O0-O3. Compiled
    /// separately, only `a_run`'s frame runs `a`'s personality:
    /// `a_run 202: personality calls 1`. Each merge order must either be
    /// refused or print exactly that; the merge refuses both, and the row
    /// runs the merged program if a change ever admits it.
    #[test]
    fn module_local_personality_runs_only_for_its_own_inputs_frames() {
        let (a, b) = personality_scope_modules(true);
        for opt_level in OPT_LEVELS {
            let directory = scratch("personality-scope");
            let thrower = directory.join("thrower.o");
            ok(
                Command::new("cc")
                    .args(["-c", "-O1", "-fexceptions"])
                    .arg(write(
                        &directory,
                        "thrower.c",
                        "#include <stdint.h>\n#include <string.h>\n#include <unwind.h>\n\
                         static void drop_exception(_Unwind_Reason_Code c,\n\
                           struct _Unwind_Exception *e) { (void)c; (void)e; }\n\
                         static int thrown = 0;\n\
                         int32_t thrower(int32_t x) {\n\
                           static struct _Unwind_Exception exception;\n\
                           if (!thrown) {\n\
                             thrown = 1;\n\
                             memset(&exception, 0, sizeof exception);\n\
                             exception.exception_class = 0x5443472d4c4f434cULL;\n\
                             exception.exception_cleanup = drop_exception;\n\
                             (void)_Unwind_RaiseException(&exception);\n\
                           }\n\
                           return x + 100;\n\
                         }\n",
                    ))
                    .arg("-o")
                    .arg(&thrower),
                &directory,
            );
            let driver = write(
                &directory,
                "driver.c",
                "#include <stdint.h>\n#include <stdio.h>\n\
                 int32_t a_run(int32_t);\n\
                 uint64_t a_personality_calls(void);\n\
                 int main(void) {\n\
                   int32_t a = a_run(1);\n\
                   printf(\"a_run %d: personality calls %llu\\n\", a,\n\
                     (unsigned long long)a_personality_calls());\n\
                   return 0;\n\
                 }\n",
            );
            let object = |module: &Module, name: &str| {
                let bytes = compiler(LINUX, opt_level, false)
                    .compile(module)
                    .unwrap_or_else(|error| panic!("{opt_level:?} {name}: {error}"))
                    .object_code;
                write(&directory, name, bytes)
            };
            let mut legs = vec![(
                "separate".to_string(),
                vec![object(&a, "a.o"), object(&b, "b.o")],
            )];
            for (order, inputs) in [
                ("ab", [a.clone(), b.clone()]),
                ("ba", [b.clone(), a.clone()]),
            ] {
                match trust_cg_codegen::module_merge::merge_modules(&inputs) {
                    Ok(merged) => legs.push((
                        format!("merged-{order}"),
                        vec![object(&merged, &format!("merged-{order}.o"))],
                    )),
                    Err(error) => assert!(
                        error.contains("module-local personality `rust_eh_personality`"),
                        "{order}: {error}"
                    ),
                }
            }
            for (leg, objects) in &legs {
                for (linker, flags) in linkers() {
                    let binary = directory.join(format!("program-{leg}-{linker}"));
                    ok(
                        Command::new("cc")
                            .env("LC_ALL", "C")
                            .args(&flags)
                            .arg(&driver)
                            .arg(&thrower)
                            .args(objects)
                            .arg("-o")
                            .arg(&binary),
                        &directory,
                    );
                    assert_eq!(
                        ok(&mut Command::new(&binary), &directory),
                        "a_run 202: personality calls 1\n",
                        "{opt_level:?} {leg} {linker}"
                    );
                }
            }
            fs::remove_dir_all(&directory).ok();
        }
    }

    /// The public translation routes feed `Pipeline` directly: the strict
    /// entries (raw module and validation report), the compatibility entry
    /// and the per-function entry. Each module either is refused at
    /// translation with `BackendSymbolShadowed`, or its object (built by
    /// `Pipeline::compile_module`, O0 and O2) is linked with a C driver and
    /// runs correctly: `frem` beside an Internal `fmod` gives
    /// `my_rem(5,3)=2`, and an i128 `sdiv` beside an Internal `__divti3` gives
    /// `my_div(100,7)=14`. Every route refuses both; the row runs any object a
    /// change lets through (the verifier's objects printed 42).
    #[test]
    fn public_translation_routes_never_bind_a_backend_call_to_a_module_body() {
        let parse = |text: &str| {
            let mut module = trust_ir::parser::parse_module(text)
                .unwrap_or_else(|error| panic!("fixture parses: {error:?}"));
            module.target_info = Some(linux_target_info());
            module
        };
        let cases = [
            (
                "fmod",
                parse(
                    "module \"sp_fmod\"\nfuncty.0 = (f64, f64) -> (f64)\n\
                     internal fn @fmod(functy.0) {\nbb0(%0: f64, %1: f64):\n    %2 = const f64 42.0\n    ret %2\n}\n\
                     fn @my_rem(functy.0) {\nbb0(%0: f64, %1: f64):\n    %2 = frem f64 %0, %1\n    ret %2\n}\n",
                ),
                "#include <stdio.h>\ndouble my_rem(double, double);\n\
                 int main(void) { printf(\"my_rem(5,3)=%g\\n\", my_rem(5.0, 3.0)); return 0; }\n",
                "my_rem(5,3)=2\n",
            ),
            (
                "__divti3",
                parse(
                    "module \"sp_divti3\"\nfuncty.0 = (i128, i128) -> (i128)\n\
                     internal fn @__divti3(functy.0) {\nbb0(%0: i128, %1: i128):\n    %2 = const i128 42\n    ret %2\n}\n\
                     fn @my_div(functy.0) {\nbb0(%0: i128, %1: i128):\n    %2 = sdiv i128 %0, %1\n    ret %2\n}\n",
                ),
                "#include <stdio.h>\n__int128 my_div(__int128, __int128);\n\
                 int main(void) { printf(\"my_div(100,7)=%lld\\n\", (long long)my_div(100, 7)); return 0; }\n",
                "my_div(100,7)=14\n",
            ),
        ];
        let directory = scratch("public-translation-routes");
        for (name, module, driver_source, expected) in &cases {
            let driver = write(
                &directory,
                &format!("driver_{}.c", name.trim_start_matches('_')),
                driver_source,
            );
            let report = trust_ir_build::validate_module_report(module);
            type TranslationRoute = Result<
                Vec<(LirFunction, trust_cg_lower::ProofContext)>,
                trust_cg_lower::AdapterError,
            >;
            let routes: [(&str, TranslationRoute); 4] = [
                (
                    "strict",
                    trust_cg_lower::translate_module_strict_for_arch_with_tls_and_validation_with_license(
                        module,
                        trust_cg_lower::GuardCarrierArch::AArch64,
                        trust_cg_lower::TlsDialect::ElfLocalExec,
                    &permit_unlicensed(),)
                    .map(|(functions, _)| functions),
                ),
                (
                    "strict report",
                    trust_cg_lower::translate_validated_module_strict_for_arch_with_tls_and_validation_with_license(
                        &report,
                        trust_cg_lower::GuardCarrierArch::AArch64,
                        trust_cg_lower::TlsDialect::ElfLocalExec,
                    &permit_unlicensed(),)
                    .map(|(functions, _)| functions),
                ),
                (
                    "compatibility",
                    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                        module,
                        trust_cg_lower::GuardCarrierArch::AArch64,
                        trust_cg_lower::TlsDialect::ElfLocalExec,
                    &permit_unlicensed(),),
                ),
                (
                    "per function",
                    module
                        .functions
                        .iter()
                        .filter(|function| !function.blocks.is_empty())
                        .map(|function| trust_cg_lower::translate_function_with_license(function, module, &permit_unlicensed()))
                        .collect(),
                ),
            ];
            for (route, translated) in routes {
                let functions = match translated {
                    Err(trust_cg_lower::AdapterError::BackendSymbolShadowed {
                        name: shadowed,
                        ..
                    }) if shadowed == *name => {
                        continue;
                    }
                    Err(error) => panic!("{name} {route}: {error}"),
                    Ok(functions) => functions,
                };
                for opt_level in [OptLevel::O0, OptLevel::O2] {
                    let pipeline = pipeline(LINUX, opt_level);
                    let machines: Vec<trust_cg_ir::MachFunction> = functions
                        .iter()
                        .map(|(function, proofs)| {
                            pipeline
                                .prepare_function_with_proofs(function, Some(proofs))
                                .unwrap_or_else(|error| panic!("{name} {route}: {error}"))
                        })
                        .collect();
                    let object = pipeline
                        .compile_module(&machines)
                        .unwrap_or_else(|error| panic!("{name} {route} {opt_level:?}: {error}"));
                    let tag = format!(
                        "{}-{}-{opt_level:?}",
                        name.trim_start_matches('_'),
                        route.replace(' ', "-")
                    );
                    let object = write(&directory, &format!("{tag}.o"), object);
                    let binary = directory.join(&tag);
                    ok(
                        Command::new("cc")
                            .arg(&driver)
                            .arg(&object)
                            .args(["-lm"])
                            .arg("-o")
                            .arg(&binary),
                        &directory,
                    );
                    assert_eq!(
                        ok(&mut Command::new(&binary), &directory),
                        *expected,
                        "{name} {route} {opt_level:?}"
                    );
                }
            }
        }
        fs::remove_dir_all(&directory).ok();
    }

    /// Module-local data never receives a reference the backend makes by
    /// name, checked by execution. Each module below either fails to compile
    /// or links (GNU ld, gold, LLD) and runs correctly at O0-O3:
    ///
    /// * `frem` beside Internal data `fmod` (refused; the verifier's module
    ///   crashed with SIGSEGV), beside External data `fmod` (refused; the
    ///   program's every `fmod` call would branch into it) and beside Internal
    ///   data `printf` (compiles): `my_rem(5,3)=2`;
    /// * an EH module selecting `__gxx_personality_v0` beside Internal data of
    ///   that name (refused; its unwinding crashed) and beside Internal data
    ///   `rust_eh_personality` (compiles): `a_run` invokes a C `b_mid` whose
    ///   `thrower` raises once through it, so `a_run 101 data 0`.
    ///
    /// The refusals keep the first of each pair from ever running; the row
    /// runs it if a change ever lets it compile.
    #[test]
    fn module_local_data_never_receives_a_backend_reference() {
        let data = |name: &str| Global {
            name: name.into(),
            ty: Ty::I64,
            mutable: true,
            initializer: Some(Constant::Int(42)),
            linkage: Linkage::Internal,
            tls: None,
            align: Some(8),
            section: None,
            visibility: Visibility::Default,
            retained: false,
        };
        let rem_module = |name: &str| {
            let mut module = frem_module("unrelated_local", Linkage::Internal, Ty::F64);
            module.globals.push(data(name));
            module
        };
        for opt_level in OPT_LEVELS {
            let directory = scratch("data-backend-reference");
            let rem_driver = write(
                &directory,
                "rem_driver.c",
                "#include <stdio.h>\n\
                 double my_rem(double, double);\n\
                 int main(void) { printf(\"my_rem(5,3)=%g\\n\", my_rem(5.0, 3.0)); return 0; }\n",
            );
            let eh_driver = write(
                &directory,
                "eh_driver.c",
                "#include <stdint.h>\n#include <stdio.h>\n#include <string.h>\n\
                 #include <unwind.h>\n\
                 static void drop_exception(_Unwind_Reason_Code c,\n\
                   struct _Unwind_Exception *e) { (void)c; (void)e; }\n\
                 static int thrown = 0;\n\
                 __attribute__((noinline)) int32_t thrower(int32_t x) {\n\
                   static struct _Unwind_Exception exception;\n\
                   if (!thrown) {\n\
                     thrown = 1;\n\
                     memset(&exception, 0, sizeof exception);\n\
                     exception.exception_class = 0x5443472d4c4f434cULL;\n\
                     exception.exception_cleanup = drop_exception;\n\
                     (void)_Unwind_RaiseException(&exception);\n\
                   }\n\
                   return x + 100;\n\
                 }\n\
                 __attribute__((noinline)) int32_t b_mid(int32_t x) { return thrower(x); }\n\
                 int32_t a_run(int32_t);\n\
                 uint64_t data_value(void);\n\
                 int main(void) {\n\
                   int32_t a = a_run(1);\n\
                   printf(\"a_run %d data %llu\\n\", a, (unsigned long long)data_value());\n\
                   return 0;\n\
                 }\n",
            );
            let cases = [
                (
                    "fmod data",
                    rem_module("fmod"),
                    &rem_driver,
                    "my_rem(5,3)=2\n",
                    true,
                ),
                (
                    "external fmod data",
                    {
                        let mut module = rem_module("fmod");
                        module.globals[0].linkage = Linkage::External;
                        module
                    },
                    &rem_driver,
                    "my_rem(5,3)=2\n",
                    true,
                ),
                (
                    "printf data",
                    rem_module("printf"),
                    &rem_driver,
                    "my_rem(5,3)=2\n",
                    false,
                ),
                (
                    "gxx personality data",
                    eh_module_with_local_data("__gxx_personality_v0"),
                    &eh_driver,
                    "a_run 101 data 0\n",
                    true,
                ),
                (
                    "rust personality data",
                    eh_module_with_local_data("rust_eh_personality"),
                    &eh_driver,
                    "a_run 101 data 0\n",
                    false,
                ),
            ];
            for (label, module, driver, expected, refused) in cases {
                let object = match compiler(LINUX, opt_level, false).compile(&module) {
                    Ok(result) => write(
                        &directory,
                        &format!("{}.o", label.replace(' ', "-")),
                        result.object_code,
                    ),
                    Err(error) => {
                        assert!(refused, "{label} {opt_level:?}: {error}");
                        continue;
                    }
                };
                for (linker, flags) in linkers() {
                    let binary = directory.join(format!("{}-{linker}", label.replace(' ', "-")));
                    ok(
                        Command::new("cc")
                            .env("LC_ALL", "C")
                            .args(&flags)
                            .arg("-fexceptions")
                            .arg(driver)
                            .arg(&object)
                            .args(["-lm", "-lstdc++"])
                            .arg("-o")
                            .arg(&binary),
                        &directory,
                    );
                    assert_eq!(
                        ok(&mut Command::new(&binary), &directory),
                        expected,
                        "{label} {opt_level:?} {linker}"
                    );
                }
            }
            fs::remove_dir_all(&directory).ok();
        }
    }

    /// [`versioned_names_module`] linked by GNU ld, gold and LLD against a
    /// shared library whose `helper@VERS_1` returns 301 and a C object whose
    /// `probe` returns 601, O0-O3: the local `helper` and `probe@LOCAL` run
    /// their own bodies (201, 501) and the declarations the other objects'
    /// definitions (301, 601).
    #[test]
    fn versioned_reference_and_at_named_local_bind_like_their_names() {
        for opt_level in OPT_LEVELS {
            let directory = scratch("versioned-names");
            let library_source = write(
                &directory,
                "versioned.c",
                "#include <stdint.h>\n\
                 uint64_t helper_v1(void) { return 301; }\n\
                 uint64_t helper_v2(void) { return 302; }\n\
                 __asm__(\".symver helper_v1, helper@VERS_1\");\n\
                 __asm__(\".symver helper_v2, helper@@VERS_2\");\n",
            );
            let map = write(
                &directory,
                "versioned.map",
                "VERS_1 { global: helper; local: *; };\nVERS_2 { global: helper; } VERS_1;\n",
            );
            let library = directory.join("libversioned.so");
            ok(
                Command::new("cc")
                    .args(["-shared", "-fPIC"])
                    .arg(&library_source)
                    .arg(format!("-Wl,--version-script={}", map.display()))
                    .arg("-o")
                    .arg(&library),
                &directory,
            );
            let driver = write(
                &directory,
                "driver.c",
                "#include <stdint.h>\n#include <stdio.h>\n\
                 uint64_t call_local(void), call_versioned(void), call_at_local(void),\n\
                   call_probe(void);\n\
                 uint64_t probe(void) { return 601; }\n\
                 int main(void) {\n\
                   printf(\"%llu %llu %llu %llu\\n\", (unsigned long long)call_local(),\n\
                     (unsigned long long)call_versioned(), (unsigned long long)call_at_local(),\n\
                     (unsigned long long)call_probe());\n\
                   return 0;\n\
                 }\n",
            );
            let object = compile_object(
                &versioned_names_module(),
                opt_level,
                &directory,
                "versioned-names.o",
            );
            for (linker, flags) in linkers() {
                let binary = directory.join(format!("program-{linker}"));
                ok(
                    Command::new("cc")
                        .args(&flags)
                        .arg(&driver)
                        .arg(&object)
                        .arg(format!("-L{}", directory.display()))
                        .arg("-lversioned")
                        .arg(format!("-Wl,-rpath,{}", directory.display()))
                        .arg("-o")
                        .arg(&binary),
                    &directory,
                );
                assert_eq!(
                    ok(&mut Command::new(&binary), &directory),
                    "201 301 501 601\n",
                    "{opt_level:?} {linker}"
                );
            }
            fs::remove_dir_all(&directory).ok();
        }
    }

    // -------------------------------------------------------------------------
    // Hidden and protected function DECLARATIONS through Compiler::compile
    // -------------------------------------------------------------------------

    /// `module` compiled by `Compiler::compile` for AArch64 Linux under
    /// `relocation_model`, written to `directory/name`.
    fn compile_with_model(
        module: &Module,
        opt_level: OptLevel,
        relocation_model: trust_cg_codegen::RelocationModel,
        directory: &Path,
        name: &str,
    ) -> PathBuf {
        let object = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level,
                relocation_model,
                ..Default::default()
            },
            TargetSpec::parse(LINUX).expect("triple"),
        )
        .with_codegen_license(permit_unlicensed())
        .compile(module)
        .unwrap_or_else(|error| panic!("{name} {relocation_model} {opt_level:?}: {error}"))
        .object_code;
        write(directory, name, object)
    }

    /// The declarations a `pic` trust-ir library references and a C object in
    /// the same library defines, default-visible, returning `value`:
    /// `(name, linkage, visibility, bodied, value)`. Each
    /// `AvailableExternally` template has the same body as its C definition,
    /// satisfying the ordinary AOT inliner's same-body premise. The default one
    /// is preemptible under `pic`, so its body is withheld and its call goes
    /// through the PLT, where an `LD_PRELOAD` interposer takes it (L02-P6
    /// closure audit 6: splicing it, mutant K6, failed one object row only).
    const LIBRARY_DECLARATIONS: [(&str, Linkage, Visibility, bool, u64); 5] = [
        (
            "dl_default_fn",
            Linkage::External,
            Visibility::Default,
            false,
            11,
        ),
        (
            "dl_protected_fn",
            Linkage::External,
            Visibility::Protected,
            false,
            22,
        ),
        (
            "dl_hidden_fn",
            Linkage::External,
            Visibility::Hidden,
            false,
            33,
        ),
        (
            "dl_avail_hidden_fn",
            Linkage::AvailableExternally,
            Visibility::Hidden,
            true,
            44,
        ),
        (
            "dl_avail_default_fn",
            Linkage::AvailableExternally,
            Visibility::Default,
            true,
            55,
        ),
    ];

    /// Build the declaration library ([`push_declaration`] for each of
    /// [`LIBRARY_DECLARATIONS`]), print it as `.trust_ir` text (retained as
    /// `declarations.tir`) and return the module PARSED BACK, so the object
    /// comes from the `; #visibility:` directives on the declarations.
    fn declaration_library_from_text(directory: &Path) -> Module {
        let mut module = Module::new("v45_declaration_library");
        module.target_info = Some(linux_target_info());
        for (name, linkage, visibility, bodied, value) in LIBRARY_DECLARATIONS {
            let id = push_declaration(&mut module, name, linkage, visibility, bodied);
            if bodied {
                let Inst::Const {
                    value: body_value, ..
                } = &mut module.functions[id.index() as usize].blocks[0].body[0].inst
                else {
                    panic!("declaration template must start with its return constant");
                };
                *body_value = Constant::Int(value.into());
            }
        }
        let text = trust_cg_codegen::pipeline::encode_trust_ir_text(&module);
        assert!(
            text.contains("; #visibility: hidden") && text.contains("; #visibility: protected"),
            "{text}"
        );
        write(directory, "declarations.tir", &text);
        let parsed =
            trust_cg_codegen::pipeline::parse_trust_ir_text(&text).expect("the text form parses");
        assert_eq!(parsed.functions.len(), module.functions.len());
        for (built, reparsed) in module.functions.iter().zip(&parsed.functions) {
            assert_eq!(
                (
                    &built.name,
                    built.linkage,
                    built.visibility,
                    built.blocks.is_empty()
                ),
                (
                    &reparsed.name,
                    reparsed.linkage,
                    reparsed.visibility,
                    reparsed.blocks.is_empty()
                )
            );
        }
        parsed
    }

    /// `st_value` of the undefined `.dynsym` entry for `name` in `image`
    /// (the canonical PLT address a non-PIE executable gives an imported
    /// function whose address it takes), or `None` when there is none.
    fn dynamic_symbol_value(image: &Path, directory: &Path, name: &str) -> Option<u64> {
        let text = ok(
            Command::new("readelf")
                .env("LC_ALL", "C")
                .args(["--wide", "--dyn-syms"])
                .arg(image),
            directory,
        );
        text.lines().find_map(|line| {
            let columns: Vec<&str> = line.split_whitespace().collect();
            (columns.len() >= 8
                && columns[0].ends_with(':')
                && columns[6] == "UND"
                && columns[7].split('@').next() == Some(name))
            .then(|| hex(columns[1]))
        })
    }

    /// C definitions of `rows` (`name` returning `value`), each with a
    /// `c_addr_<name>` returning the address as this C object takes it.
    fn c_definitions(rows: &[(&str, u64)]) -> String {
        let mut source = String::from("#include <stdint.h>\n");
        for (name, value) in rows {
            source.push_str(&format!(
                "uint64_t {name}(void) {{ return {value}; }}\n\
                 void *c_addr_{name}(void) {{ return (void *){name}; }}\n"
            ));
        }
        source
    }

    /// trust-ir hidden and protected function DECLARATIONS in a `pic` CG
    /// object whose definitions a C object in the same shared library
    /// supplies (default-visible there), O0-O3, linked by GNU ld, gold and
    /// LLD:
    ///
    /// * the object spells each as an undefined `STB_GLOBAL` symbol with its
    ///   `STV_*`, addresses each through the GOT (`ADR_GOT_PAGE` +
    ///   `LD64_GOT_LO12_NC`, never a PC-relative page), and calls each with a
    ///   `CALL26`/`JUMP26`, except that at O1-O3 the hidden
    ///   `AvailableExternally` body is spliced into its call (the default one,
    ///   preemptible under `pic`, never is);
    /// * the library gives each definition the most constraining visibility:
    ///   the hidden ones are absent from `.dynsym` and the protected one is
    ///   `PROTECTED` there; only the two default calls (the import and the
    ///   `AvailableExternally` function) have a `JUMP_SLOT` and branch into
    ///   `.plt`, and every other call branches straight to its definition;
    /// * a PIE driver sees every call return the C definition's value and
    ///   every `SymbolAddr` and `FnDef` address reach the C definition (never
    ///   an `AvailableExternally` template), both CG
    ///   address forms equal the C object's, and the executable's own
    ///   addresses of the default and protected functions equal the
    ///   library's;
    /// * an `LD_PRELOAD` interposer defining all five names takes over the
    ///   two default calls and their addresses and the executable's protected
    ///   address, never the library's references to its protected and hidden
    ///   definitions, whose CG forms still equal the C object's GOT loads;
    /// * a non-PIE executable that takes the protected function's address
    ///   needs a canonical PLT entry: GNU ld and LLD refuse the link naming
    ///   it. They give the default function one, and its address agrees
    ///   across the images. gold links both without a canonical address (the
    ///   executable's `.dynsym` value is 0), so the addresses differ for the
    ///   default function too, for the CG GOT form and the C object's alike:
    ///   a gold defect no address form in the library avoids.
    ///
    /// Execution evidence for these linkers and the glibc loader on this
    /// host, not a linker or loader proof.
    #[test]
    fn trust_ir_hidden_and_protected_declarations_bind_inside_the_library() {
        let linkers = linkers();
        let values: Vec<(&str, u64)> = LIBRARY_DECLARATIONS
            .iter()
            .map(|(name, .., value)| (*name, *value))
            .collect();
        for opt_level in OPT_LEVELS {
            let directory = scratch("declaration-library");
            let module = declaration_library_from_text(&directory);
            let result = Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level,
                    relocation_model: trust_cg_codegen::RelocationModel::Pic,
                    ..Default::default()
                },
                TargetSpec::parse(LINUX).expect("triple"),
            )
            .with_codegen_license(permit_unlicensed())
            .compile(&module)
            .unwrap_or_else(|error| panic!("declaration library {opt_level:?}: {error}"));
            let expected_spliced: Vec<(String, usize)> = LIBRARY_DECLARATIONS
                .iter()
                .filter(|(_, linkage, visibility, _, _)| {
                    declaration_body_spliced(
                        *linkage,
                        *visibility,
                        trust_cg_codegen::RelocationModel::Pic,
                        opt_level,
                    )
                })
                .map(|(name, ..)| (name.to_string(), 1))
                .collect();
            let spliced: Vec<(String, usize)> = result
                .inline_only_bodies
                .spliced
                .iter()
                .map(|use_| (use_.name.clone(), use_.sites))
                .collect();
            assert_eq!(spliced, expected_spliced, "{opt_level:?}");
            let object = write(&directory, "declarations.o", result.object_code);
            let readelf = |flags: &[&str], path: &Path| {
                ok(
                    Command::new("readelf")
                        .env("LC_ALL", "C")
                        .arg("--wide")
                        .args(flags)
                        .arg(path),
                    &directory,
                )
            };
            let object_relocs = readelf(&["--relocs"], &object);
            write(&directory, "object-relocs.txt", &object_relocs);
            let object_rows = reloc_rows(&object_relocs);
            for (name, linkage, visibility, _, _) in LIBRARY_DECLARATIONS {
                assert_eq!(
                    readelf_rows(&object, &directory, "--symbols", name),
                    [(
                        "GLOBAL".to_string(),
                        visibility.to_string().to_uppercase(),
                        "UND".to_string()
                    )],
                    "{opt_level:?}: `{name}`"
                );
                let kinds: BTreeSet<&str> = object_rows
                    .iter()
                    .filter(|row| row.symbol.as_deref() == Some(name))
                    .map(|row| row.kind.as_str())
                    .collect();
                let addressed = kinds.contains("R_AARCH64_ADR_GOT_PAGE")
                    && kinds.contains("R_AARCH64_LD64_GOT_LO12_NC")
                    && !kinds.contains("R_AARCH64_ADR_PREL_PG_HI21")
                    && !kinds.contains("R_AARCH64_ADD_ABS_LO12_NC");
                assert!(
                    addressed,
                    "{opt_level:?}: `{name}`: {kinds:?}\n{object_relocs}"
                );
                let has_call = kinds
                    .iter()
                    .any(|kind| ["R_AARCH64_CALL26", "R_AARCH64_JUMP26"].contains(kind));
                assert_eq!(
                    has_call,
                    !declaration_body_spliced(
                        linkage,
                        visibility,
                        trust_cg_codegen::RelocationModel::Pic,
                        opt_level,
                    ),
                    "{opt_level:?}: `{name}` ({visibility}): {kinds:?}\n{object_relocs}"
                );
            }
            let definitions = directory.join("definitions.o");
            ok(
                Command::new("cc")
                    .args(["-fPIC", "-O2", "-c"])
                    .arg(write(&directory, "definitions.c", c_definitions(&values)))
                    .arg("-o")
                    .arg(&definitions),
                &directory,
            );
            let interposer_source = write(
                &directory,
                "interposer.c",
                "#include <stdint.h>\n\
                 uint64_t dl_default_fn(void) { return 111; }\n\
                 uint64_t dl_protected_fn(void) { return 222; }\n\
                 uint64_t dl_hidden_fn(void) { return 333; }\n\
                 uint64_t dl_avail_hidden_fn(void) { return 444; }\n\
                 uint64_t dl_avail_default_fn(void) { return 555; }\n",
            );
            let driver = write(
                &directory,
                "driver.c",
                "#include <stdint.h>\n#include <stdio.h>\n\
                 typedef uint64_t (*leaf)(void);\n\
                 #define EACH(X) X(dl_default_fn) X(dl_protected_fn) X(dl_hidden_fn) \\\n\
                   X(dl_avail_hidden_fn) X(dl_avail_default_fn)\n\
                 #define DECLARE(n) uint64_t call_##n(void); void *addr_##n(void), \\\n\
                   *fnaddr_##n(void), *c_addr_##n(void);\n\
                 EACH(DECLARE)\n\
                 extern uint64_t dl_default_fn(void), dl_protected_fn(void);\n\
                 #define CALL(n) printf(\" %llu\", (unsigned long long)call_##n());\n\
                 #define POINTER(n) printf(\" %llu\", (unsigned long long)((leaf)addr_##n())());\n\
                 #define FNPOINTER(n) printf(\" %llu\", (unsigned long long)((leaf)fnaddr_##n())());\n\
                 #define SAME(n) printf(\" %d\", addr_##n() == c_addr_##n() \\\n\
                   && fnaddr_##n() == c_addr_##n());\n\
                 int main(void) {\n\
                   printf(\"call\"); EACH(CALL) printf(\"\\n\");\n\
                   printf(\"pointer\"); EACH(POINTER) printf(\"\\n\");\n\
                   printf(\"fnpointer\"); EACH(FNPOINTER) printf(\"\\n\");\n\
                   printf(\"same-lib\"); EACH(SAME) printf(\"\\n\");\n\
                   printf(\"same-exe %d %d\\n\", addr_dl_default_fn() == (void *)dl_default_fn,\n\
                     addr_dl_protected_fn() == (void *)dl_protected_fn);\n\
                   return 0;\n\
                 }\n",
            );
            let non_pie_driver = |name: &str| {
                format!(
                    "#include <stdint.h>\n#include <stdio.h>\n\
                     extern uint64_t {name}(void);\n\
                     void *addr_{name}(void), *c_addr_{name}(void);\n\
                     int main(void) {{\n\
                       printf(\"same %d %d\\n\", addr_{name}() == (void *){name},\n\
                         c_addr_{name}() == (void *){name});\n\
                       return 0;\n\
                     }}\n"
                )
            };
            for (linker, flags) in &linkers {
                let leg = directory.join(linker);
                fs::create_dir_all(&leg).unwrap();
                let cc = || {
                    let mut command = Command::new("cc");
                    command.env("LC_ALL", "C").args(flags);
                    command
                };
                let label = format!("{opt_level:?} {linker}");
                let library = leg.join("libtcgdecl.so");
                ok(
                    cc().args(["-shared", "-Wl,-z,defs,-z,text,-z,relro,-z,now"])
                        .arg(&object)
                        .arg(&definitions)
                        .arg("-o")
                        .arg(&library),
                    &leg,
                );
                for (name, _, visibility, _, _) in LIBRARY_DECLARATIONS {
                    let rows = readelf_rows(&library, &leg, "--dyn-syms", name);
                    if visibility == Visibility::Hidden {
                        assert!(rows.is_empty(), "{label}: `{name}` exported: {rows:?}");
                        continue;
                    }
                    assert_eq!(rows.len(), 1, "{label}: `{name}`: {rows:?}");
                    assert_eq!(
                        (rows[0].0.as_str(), rows[0].1.as_str()),
                        ("GLOBAL", visibility.to_string().to_uppercase().as_str()),
                        "{label}: `{name}` takes the declaration's visibility"
                    );
                    assert_ne!(rows[0].2, "UND", "{label}: `{name}` is defined");
                }
                let dynamic_relocs = readelf(&["--relocs"], &library);
                write(&leg, "library-relocs.txt", &dynamic_relocs);
                let slots: BTreeSet<&str> = reloc_rows(&dynamic_relocs)
                    .into_iter()
                    .filter(|row| row.kind == "R_AARCH64_JUMP_SLOT")
                    .filter_map(|row| {
                        LIBRARY_DECLARATIONS
                            .iter()
                            .map(|(name, ..)| *name)
                            .find(|name| row.symbol.as_deref() == Some(*name))
                    })
                    .collect();
                assert_eq!(
                    slots,
                    BTreeSet::from(["dl_default_fn", "dl_avail_default_fn"]),
                    "{label}: only the default calls go through the PLT\n{dynamic_relocs}"
                );
                let sections = readelf(&["--section-headers"], &library);
                let plt = section_ranges(&sections, &[".plt"]);
                assert_eq!(plt.len(), 1, "{label}: {plt:?}");
                let (_, plt_start, plt_end) = plt[0].clone();
                let symbols = readelf(&["--syms"], &library);
                let disassembly = ok(
                    Command::new("objdump")
                        .env("LC_ALL", "C")
                        .args(["-d", "--no-show-raw-insn"])
                        .arg(&library),
                    &leg,
                );
                write(&leg, "library-disassembly.txt", &disassembly);
                let branches = direct_branches(&disassembly);
                for (name, linkage, visibility, _, _) in LIBRARY_DECLARATIONS {
                    let caller = format!("call_{name}");
                    let targets: Vec<u64> = branches
                        .iter()
                        .filter(|(function, _)| *function == caller)
                        .map(|(_, target)| *target)
                        .collect();
                    if visibility == Visibility::Default {
                        assert!(
                            !targets.is_empty()
                                && targets
                                    .iter()
                                    .all(|target| (plt_start..plt_end).contains(target)),
                            "{label}: `{caller}` branches into .plt: {targets:?}"
                        );
                    } else if declaration_body_spliced(
                        linkage,
                        visibility,
                        trust_cg_codegen::RelocationModel::Pic,
                        opt_level,
                    ) {
                        assert!(
                            targets.is_empty(),
                            "{label}: `{caller}` spliced: {targets:?}"
                        );
                    } else {
                        let definition = symbol_value(&symbols, name)
                            .unwrap_or_else(|| panic!("{label}: `{name}` in .symtab"));
                        assert!(
                            !targets.is_empty()
                                && targets.iter().all(|target| *target == definition),
                            "{label}: `{caller}` branches straight to `{name}` \
                             ({definition:#x}): {targets:?}"
                        );
                    }
                }

                let interposer = leg.join("libinterpose.so");
                ok(
                    cc().args(["-shared", "-fPIC"])
                        .arg(&interposer_source)
                        .arg("-o")
                        .arg(&interposer),
                    &leg,
                );
                let rpath = format!("-Wl,-rpath,{}", leg.display());
                let binary = leg.join("driver");
                ok(
                    cc().args(["-fPIE", "-pie"])
                        .arg(&driver)
                        .arg(format!("-L{}", leg.display()))
                        .arg("-ltcgdecl")
                        .arg(&rpath)
                        .arg("-o")
                        .arg(&binary),
                    &leg,
                );
                let plain = ok(&mut Command::new(&binary), &leg);
                write(&leg, "run-plain.txt", &plain);
                assert_eq!(
                    plain,
                    "call 11 22 33 44 55\npointer 11 22 33 44 55\nfnpointer 11 22 33 44 55\n\
                     same-lib 1 1 1 1 1\nsame-exe 1 1\n",
                    "{label}"
                );
                let preloaded = ok(Command::new(&binary).env("LD_PRELOAD", &interposer), &leg);
                write(&leg, "run-preload.txt", &preloaded);
                let lines: Vec<&str> = preloaded.lines().collect();
                assert_eq!(
                    lines,
                    [
                        "call 111 22 33 44 555",
                        "pointer 111 22 33 44 555",
                        "fnpointer 111 22 33 44 555",
                        "same-lib 1 1 1 1 1",
                        "same-exe 1 0"
                    ],
                    "{label}: only the default references interpose\n{preloaded}"
                );

                // A non-PIE executable taking a function's address needs a
                // canonical PLT entry, whose address the library's GOT slot
                // must follow. GNU ld and LLD give the default function one
                // and refuse it for the protected one. gold links both with
                // no canonical address (the executable's `.dynsym` entry has
                // value 0), so the executable and the library see different
                // addresses for either function, through the CG object's GOT
                // or PC-relative form and the C object's GOT form alike.
                for (name, protected) in [("dl_default_fn", false), ("dl_protected_fn", true)] {
                    let source = write(&leg, &format!("non-pie-{name}.c"), non_pie_driver(name));
                    let program = leg.join(format!("non-pie-{name}"));
                    let (success, _, stderr) = run(
                        cc().args(["-fno-PIE", "-no-pie"])
                            .arg(&source)
                            .arg(format!("-L{}", leg.display()))
                            .arg("-ltcgdecl")
                            .arg(&rpath)
                            .arg("-o")
                            .arg(&program),
                        &leg,
                    );
                    write(&leg, &format!("non-pie-{name}-link.txt"), &stderr);
                    let gold = *linker == "gold";
                    if protected && !gold {
                        assert!(
                            !success && stderr.contains(name),
                            "{label}: the linker must refuse the canonical PLT entry of \
                             `{name}`: {stderr}"
                        );
                        continue;
                    }
                    assert!(success, "{label}: `{name}`: {stderr}");
                    let canonical = dynamic_symbol_value(&program, &leg, name);
                    assert_eq!(
                        canonical != Some(0),
                        !gold,
                        "{label}: `{name}` canonical PLT address {canonical:?}"
                    );
                    let output = ok(&mut Command::new(&program), &leg);
                    write(&leg, &format!("non-pie-{name}-run.txt"), &output);
                    let expected = if gold { "same 0 0\n" } else { "same 1 1\n" };
                    assert_eq!(output, expected, "{label}: `{name}`");
                }
            }
            eprintln!("hidden/protected declarations passed: {opt_level:?} {directory:?}");
        }
    }

    /// A strong hidden or protected declaration binds only to a definition in
    /// the output being linked. A `pic` CG object referencing one, O0-O3, does
    /// not link with GNU ld, gold or LLD into a shared object without the
    /// definition, into a shared object that finds it only in another shared
    /// library, or (as `pie` code) into an executable that does; each failure
    /// is classified by `link_driver::classify_linker_stderr` as an undefined
    /// `dn_*` symbol. The default-visibility twin links in all three shapes
    /// and runs against the other library's definition, and with the
    /// definition in the same output every visibility links under
    /// `-z defs`.
    #[test]
    fn hidden_and_protected_declarations_need_their_definition_in_the_output() {
        use trust_cg_codegen::link_driver::{LinkDiagnosticKind, classify_linker_stderr};
        let linkers = linkers();
        let values = [
            ("dn_default_fn", 1),
            ("dn_hidden_fn", 2),
            ("dn_protected_fn", 3),
        ];
        for opt_level in OPT_LEVELS {
            let directory = scratch("declaration-undefined");
            let other = directory.join("libother.so");
            ok(
                Command::new("cc")
                    .args(["-shared", "-fPIC"])
                    .arg(write(&directory, "other.c", c_definitions(&values)))
                    .arg("-o")
                    .arg(&other),
                &directory,
            );
            let definitions = directory.join("definitions.o");
            ok(
                Command::new("cc")
                    .args(["-fPIC", "-c"])
                    .arg(directory.join("other.c"))
                    .arg("-o")
                    .arg(&definitions),
                &directory,
            );
            for visibility in VISIBILITIES {
                let name = format!("dn_{visibility}_fn");
                let mut module = Module::new(format!("declares_{name}"));
                module.target_info = Some(linux_target_info());
                push_declaration(&mut module, &name, Linkage::External, visibility, false);
                let pic_object = compile_with_model(
                    &module,
                    opt_level,
                    trust_cg_codegen::RelocationModel::Pic,
                    &directory,
                    &format!("{name}-pic.o"),
                );
                let pie_object = compile_with_model(
                    &module,
                    opt_level,
                    trust_cg_codegen::RelocationModel::Pie,
                    &directory,
                    &format!("{name}-pie.o"),
                );
                let driver = write(
                    &directory,
                    &format!("driver-{name}.c"),
                    format!(
                        "#include <stdint.h>\n#include <stdio.h>\n\
                         uint64_t call_{name}(void);\n\
                         int main(void) {{\n\
                           printf(\"%llu\\n\", (unsigned long long)call_{name}());\n\
                           return 0;\n\
                         }}\n"
                    ),
                );
                for (linker, flags) in &linkers {
                    let label = format!("{opt_level:?} {linker} {visibility}");
                    let leg = directory.join(format!("{linker}-{visibility}"));
                    fs::create_dir_all(&leg).unwrap();
                    let cc = || {
                        let mut command = Command::new("cc");
                        command.env("LC_ALL", "C").args(flags);
                        command
                    };
                    let library_path = format!("-L{}", directory.display());
                    let rpath = format!("-Wl,-rpath,{}", directory.display());
                    let program = leg.join("program");
                    let mut shapes = [
                        ("missing", {
                            let mut command = cc();
                            command
                                .arg("-shared")
                                .arg(&pic_object)
                                .arg("-o")
                                .arg(leg.join("missing.so"));
                            command
                        }),
                        ("other-library", {
                            let mut command = cc();
                            command
                                .arg("-shared")
                                .arg(&pic_object)
                                .arg(&library_path)
                                .arg("-lother")
                                .arg("-o")
                                .arg(leg.join("other.so"));
                            command
                        }),
                        ("executable", {
                            let mut command = cc();
                            command
                                .args(["-fPIE", "-pie"])
                                .arg(&driver)
                                .arg(&pie_object)
                                .arg(&library_path)
                                .arg("-lother")
                                .arg(&rpath)
                                .arg("-o")
                                .arg(&program);
                            command
                        }),
                    ];
                    for (shape, command) in &mut shapes {
                        let (success, _, stderr) = run(command, &leg);
                        write(&leg, &format!("{shape}-link.txt"), &stderr);
                        if visibility == Visibility::Default {
                            assert!(success, "{label} {shape}: the default twin links: {stderr}");
                            continue;
                        }
                        assert!(!success, "{label} {shape}: the link must fail");
                        let diagnostics = classify_linker_stderr(&stderr);
                        assert!(
                            diagnostics.iter().any(|diagnostic| {
                                diagnostic.kind == LinkDiagnosticKind::UndefinedSymbol
                                    && diagnostic.subject.as_deref() == Some(name.as_str())
                            }),
                            "{label} {shape}: {diagnostics:?}\n{stderr}"
                        );
                    }
                    if visibility == Visibility::Default {
                        assert_eq!(
                            ok(&mut Command::new(&program), &leg),
                            "1\n",
                            "{label}: the default twin binds to the other library"
                        );
                    }
                    ok(
                        cc().args(["-shared", "-Wl,-z,defs"])
                            .arg(&pic_object)
                            .arg(&definitions)
                            .arg("-o")
                            .arg(leg.join("defined.so")),
                        &leg,
                    );
                }
            }
            eprintln!("declarations without a definition passed: {opt_level:?} {directory:?}");
        }
    }

    /// The `ExternalWeak` declarations the weak rows reference, with the value
    /// a C definition returns in the present legs: `(name, visibility,
    /// value)`.
    const WEAK_DECLARATIONS: [(&str, Visibility, u64); 3] = [
        ("wn_default_fn", Visibility::Default, 111),
        ("wn_protected_fn", Visibility::Protected, 222),
        ("wn_hidden_fn", Visibility::Hidden, 333),
    ];

    /// trust-ir `ExternalWeak` declarations, default, protected and hidden,
    /// through `Compiler::compile` at O0-O3 under `static` (a non-PIE
    /// executable), `pie` (a PIE) and `pic` (a shared library a PIE loads),
    /// linked by GNU ld, gold and LLD. Each is addressed through the GOT
    /// (the host-neutral rows pin the relocations), so:
    ///
    /// * absent, every address reads 0 and each null-guarded call returns 7
    ///   instead of calling, except with gold in a PIE or a shared library,
    ///   where the hidden address reads the image's load base: gold 2.42
    ///   exports the absent hidden reference to `.dynsym` (`WEAK HIDDEN
    ///   UND`, with a `GLOB_DAT`) in every shape, and the glibc loader
    ///   resolves a hidden symbol to its own image, which only a non-PIE
    ///   executable loads at 0. A GCC object reading the same weak hidden
    ///   declaration in the same image reads the same nonzero value, so the
    ///   row pins it as a gold defect and does not call through it;
    /// * present (a C object in the same output defines each), every call
    ///   returns the definition's value and both address forms agree;
    /// * defined only in another shared library the image needs
    ///   (`--no-as-needed`), the default reference binds to it (111), while
    ///   GNU ld and LLD link the hidden and protected references as absent:
    ///   their addresses read 0 and their guarded calls return 7. gold refuses
    ///   the link instead (`hidden symbol 'wn_hidden_fn' is not defined
    ///   locally`, and the same for `wn_protected_fn`), which
    ///   `classify_linker_stderr` reports as undefined symbols. A strong hidden
    ///   or protected reference fails that link with every linker (see
    ///   `hidden_and_protected_declarations_need_their_definition_in_the_output`).
    #[test]
    fn weak_hidden_and_protected_declarations_read_null_when_absent() {
        use trust_cg_codegen::link_driver::{LinkDiagnosticKind, classify_linker_stderr};
        let linkers = linkers();
        let mut module = Module::new("v45_weak_declarations");
        module.target_info = Some(linux_target_info());
        for (name, visibility, _) in WEAK_DECLARATIONS {
            push_declaration(&mut module, name, Linkage::ExternalWeak, visibility, false);
        }
        let values: Vec<(&str, u64)> = WEAK_DECLARATIONS
            .iter()
            .map(|(name, _, value)| (*name, *value))
            .collect();
        for opt_level in OPT_LEVELS {
            let directory = scratch("weak-declarations");
            let definitions_source = write(&directory, "definitions.c", c_definitions(&values));
            let gcc_source = write(
                &directory,
                "gcc_weak.c",
                "#include <stdint.h>\n\
                 extern uint64_t wn_hidden_fn(void) __attribute__((weak, visibility(\"hidden\")));\n\
                 int gcc_hidden_is_set(void) { return (void *)wn_hidden_fn != 0; }\n",
            );
            let absent_driver = write(
                &directory,
                "absent.c",
                "#include <stdint.h>\n#include <stdio.h>\n\
                 void *addr_wn_default_fn(void), *addr_wn_protected_fn(void),\n\
                   *addr_wn_hidden_fn(void);\n\
                 uint64_t call_wn_default_fn(void), call_wn_protected_fn(void),\n\
                   call_wn_hidden_fn(void);\n\
                 int gcc_hidden_is_set(void);\n\
                 int main(int argc, char **argv) {\n\
                   (void)argv;\n\
                   printf(\"addr %d %d %d\\n\", addr_wn_default_fn() != 0,\n\
                     addr_wn_protected_fn() != 0, addr_wn_hidden_fn() != 0);\n\
                   printf(\"gcc %d\\n\", gcc_hidden_is_set());\n\
                   printf(\"call %llu %llu\", (unsigned long long)call_wn_default_fn(),\n\
                     (unsigned long long)call_wn_protected_fn());\n\
                   if (argc == 1) printf(\" %llu\", (unsigned long long)call_wn_hidden_fn());\n\
                   printf(\"\\n\");\n\
                   return 0;\n\
                 }\n",
            );
            let library_only_driver = write(
                &directory,
                "library_only.c",
                "#include <stdint.h>\n#include <stdio.h>\n\
                 void *addr_wn_default_fn(void), *addr_wn_protected_fn(void),\n\
                   *addr_wn_hidden_fn(void);\n\
                 uint64_t call_wn_default_fn(void), call_wn_protected_fn(void),\n\
                   call_wn_hidden_fn(void);\n\
                 int main(void) {\n\
                   printf(\"addr %d %d %d\\n\", addr_wn_default_fn() != 0,\n\
                     addr_wn_protected_fn() != 0, addr_wn_hidden_fn() != 0);\n\
                   printf(\"call %llu %llu %llu\\n\", (unsigned long long)call_wn_default_fn(),\n\
                     (unsigned long long)call_wn_protected_fn(),\n\
                     (unsigned long long)call_wn_hidden_fn());\n\
                   return 0;\n\
                 }\n",
            );
            let definitions_library = directory.join("libwndefs.so");
            ok(
                Command::new("cc")
                    .args(["-shared", "-fPIC"])
                    .arg(&definitions_source)
                    .arg("-o")
                    .arg(&definitions_library),
                &directory,
            );
            let present_driver = write(
                &directory,
                "present.c",
                "#include <stdint.h>\n#include <stdio.h>\n\
                 #define EACH(X) X(wn_default_fn) X(wn_protected_fn) X(wn_hidden_fn)\n\
                 #define DECLARE(n) uint64_t call_##n(void); void *addr_##n(void), \\\n\
                   *c_addr_##n(void);\n\
                 EACH(DECLARE)\n\
                 #define CALL(n) printf(\" %llu\", (unsigned long long)call_##n());\n\
                 #define SAME(n) printf(\" %d\", addr_##n() == c_addr_##n());\n\
                 int main(void) {\n\
                   printf(\"call\"); EACH(CALL) printf(\"\\n\");\n\
                   printf(\"same\"); EACH(SAME) printf(\"\\n\");\n\
                   return 0;\n\
                 }\n",
            );
            for relocation_model in RELOCATION_MODELS {
                let object = compile_with_model(
                    &module,
                    opt_level,
                    relocation_model,
                    &directory,
                    &format!("weak-{relocation_model}.o"),
                );
                let (code_flag, _) = model_flags(relocation_model);
                let c_object = |source: &Path, name: &str| {
                    let path = directory.join(format!("{name}-{relocation_model}.o"));
                    ok(
                        Command::new("cc")
                            .args([code_flag, "-O2", "-c"])
                            .arg(source)
                            .arg("-o")
                            .arg(&path),
                        &directory,
                    );
                    path
                };
                let definitions = c_object(&definitions_source, "definitions");
                let gcc_object = c_object(&gcc_source, "gcc-weak");
                for (linker, flags) in &linkers {
                    let label = format!("{opt_level:?} {relocation_model} {linker}");
                    let leg = directory.join(format!("{relocation_model}-{linker}"));
                    fs::create_dir_all(&leg).unwrap();
                    let cc = || {
                        let mut command = Command::new("cc");
                        command.env("LC_ALL", "C").args(flags);
                        command
                    };
                    // The image holding the CG object: the executable itself,
                    // or the shared library the PIE driver loads.
                    let link = |driver: &Path, extra: &[&Path], tag: &str| -> (PathBuf, PathBuf) {
                        let program = leg.join(tag);
                        match relocation_model {
                            trust_cg_codegen::RelocationModel::Pic => {
                                let library = leg.join(format!("lib{tag}.so"));
                                let mut command = cc();
                                command.arg("-shared").arg(&object);
                                for path in extra {
                                    command.arg(path);
                                }
                                ok(command.arg("-o").arg(&library), &leg);
                                ok(
                                    cc().args(["-fPIE", "-pie"])
                                        .arg(driver)
                                        .arg(&library)
                                        .arg(format!("-Wl,-rpath,{}", leg.display()))
                                        .arg("-o")
                                        .arg(&program),
                                    &leg,
                                );
                                (program, library)
                            }
                            model => {
                                let (code, link) = model_flags(model);
                                let mut command = cc();
                                command.args([code, link]).arg(driver).arg(&object);
                                for path in extra {
                                    command.arg(path);
                                }
                                ok(command.arg("-o").arg(&program), &leg);
                                (program.clone(), program)
                            }
                        }
                    };
                    let (absent, absent_image) =
                        link(&absent_driver, &[gcc_object.as_path()], "absent");
                    // gold exports the absent hidden reference in every
                    // shape; the loader's image-relative value is 0 only in
                    // a non-PIE executable, loaded at its link address.
                    let gold = *linker == "gold";
                    let gold_defect =
                        gold && relocation_model != trust_cg_codegen::RelocationModel::Static;
                    let dynamic = readelf_rows(&absent_image, &leg, "--dyn-syms", "wn_hidden_fn");
                    if gold {
                        assert_eq!(
                            dynamic,
                            [("WEAK".into(), "HIDDEN".into(), "UND".into())],
                            "{label}: gold exports the absent hidden reference"
                        );
                    } else {
                        assert!(dynamic.is_empty(), "{label}: {dynamic:?}");
                    }
                    let mut command = Command::new(&absent);
                    if gold_defect {
                        command.arg("skip-hidden-call");
                    }
                    let output = ok(&mut command, &leg);
                    write(&leg, "run-absent.txt", &output);
                    let expected = if gold_defect {
                        "addr 0 0 1\ngcc 1\ncall 7 7\n"
                    } else {
                        "addr 0 0 0\ngcc 0\ncall 7 7 7\n"
                    };
                    assert_eq!(output, expected, "{label}: absent");

                    let (present, _) = link(
                        &present_driver,
                        &[definitions.as_path(), gcc_object.as_path()],
                        "present",
                    );
                    let output = ok(&mut Command::new(&present), &leg);
                    write(&leg, "run-present.txt", &output);
                    assert_eq!(output, "call 111 222 333\nsame 1 1 1\n", "{label}: present");

                    // The definitions only in another shared library.
                    let needs_definitions = [
                        "-Wl,--no-as-needed".to_string(),
                        format!("-L{}", directory.display()),
                        "-lwndefs".to_string(),
                        format!("-Wl,-rpath,{}", directory.display()),
                    ];
                    let program = leg.join("library-only");
                    let (success, _, stderr) = match relocation_model {
                        trust_cg_codegen::RelocationModel::Pic => {
                            let library = leg.join("liblibrary-only.so");
                            let linked = run(
                                cc().arg("-shared")
                                    .arg(&object)
                                    .args(&needs_definitions)
                                    .arg("-o")
                                    .arg(&library),
                                &leg,
                            );
                            if linked.0 {
                                ok(
                                    cc().args(["-fPIE", "-pie"])
                                        .arg(&library_only_driver)
                                        .arg(&library)
                                        .args(&needs_definitions)
                                        .arg(format!("-Wl,-rpath,{}", leg.display()))
                                        .arg("-o")
                                        .arg(&program),
                                    &leg,
                                );
                            }
                            linked
                        }
                        model => {
                            let (code, link) = model_flags(model);
                            run(
                                cc().args([code, link])
                                    .arg(&library_only_driver)
                                    .arg(&object)
                                    .args(&needs_definitions)
                                    .arg("-o")
                                    .arg(&program),
                                &leg,
                            )
                        }
                    };
                    write(&leg, "library-only-link.txt", &stderr);
                    if gold {
                        assert!(!success, "{label}: gold must refuse the library-only link");
                        for name in ["wn_hidden_fn", "wn_protected_fn"] {
                            assert!(
                                classify_linker_stderr(&stderr).iter().any(|diagnostic| {
                                    diagnostic.kind == LinkDiagnosticKind::UndefinedSymbol
                                        && diagnostic.subject.as_deref() == Some(name)
                                }) && stderr.contains("is not defined locally"),
                                "{label}: `{name}`: {stderr}"
                            );
                        }
                        continue;
                    }
                    assert!(success, "{label}: library-only link: {stderr}");
                    let output = ok(&mut Command::new(&program), &leg);
                    write(&leg, "run-library-only.txt", &output);
                    assert_eq!(
                        output, "addr 1 0 0\ncall 111 7 7\n",
                        "{label}: only the default reference binds to another library"
                    );
                }
            }
            eprintln!("weak hidden/protected declarations passed: {opt_level:?} {directory:?}");
        }
    }

    /// The strong declarations the IFUNC row references, with the value each
    /// IFUNC's implementation returns: `(name, visibility, value)`.
    const IFUNC_DECLARATIONS: [(&str, Visibility, u64); 3] = [
        ("if_default_fn", Visibility::Default, 41),
        ("if_protected_fn", Visibility::Protected, 42),
        ("if_hidden_fn", Visibility::Hidden, 43),
    ];

    /// The IFUNC row's module: each of [`IFUNC_DECLARATIONS`] with its
    /// `addr_`/`fnaddr_`/`call_` accessors ([`push_declaration`]), a
    /// read-only data word `tbl_<name>` initialized with its `SymbolAddr`
    /// (an `R_AARCH64_ABS64`) and a `load_tbl_<name>` that loads it.
    fn ifunc_declaration_module() -> Module {
        let mut module = Module::new("v45_ifunc_declarations");
        module.target_info = Some(linux_target_info());
        let ptr_sig = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::Ptr],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        for (name, visibility, _) in IFUNC_DECLARATIONS {
            push_declaration(&mut module, name, Linkage::External, visibility, false);
            let global = GlobalId::new(module.globals.len() as u32);
            module.globals.push(Global {
                name: format!("tbl_{name}"),
                ty: Ty::Ptr,
                mutable: false,
                initializer: Some(Constant::SymbolAddr {
                    symbol: name.into(),
                    addend: 0,
                }),
                linkage: Linkage::External,
                tls: None,
                align: Some(8),
                section: None,
                visibility: Visibility::Default,
                retained: false,
            });
            push_function(
                &mut module,
                format!("load_tbl_{name}"),
                ptr_sig,
                vec![
                    InstrNode::new(Inst::GlobalAddr { global }).with_result(ValueId::new(0)),
                    InstrNode::new(Inst::Load {
                        ty: Ty::Ptr,
                        ptr: ValueId::new(0),
                        volatile: false,
                        align: Some(8),
                    })
                    .with_result(ValueId::new(1)),
                    InstrNode::new(Inst::Return {
                        values: vec![ValueId::new(1)],
                    }),
                ],
            );
        }
        module
    }

    /// trust-ir declarations, default, protected and hidden, whose
    /// definitions in the same output are GNU IFUNCs (a C object's
    /// `__attribute__((ifunc))` functions), O0-O3, linked by GNU ld, gold
    /// and LLD into a non-PIE executable (`static` code), a `-static`
    /// executable (`static` code), a PIE (`pie` code), a static PIE (`pie`
    /// code) and a shared library a PIE loads (`pic` code). In every image
    /// each CG `SymbolAddr` address, `FnDef` address and `ABS64` data word
    /// equals the C object's own address of the function, and each call
    /// returns the implementation's value.
    ///
    /// A declaration's address comes from the GOT whatever its visibility.
    /// A PC-relative reference to an IFUNC reads its PLT stub with GNU ld (a
    /// PIE, a static PIE, a shared library) and gold (a PIE, a shared
    /// library) while every GOT slot and data word holds the resolved
    /// function: this row fails if a hidden or protected declaration is
    /// addressed PC-relatively. gold does not link a static PIE
    /// (`--no-dynamic-linker: unknown option`), which the row pins.
    #[test]
    fn declarations_of_ifunc_definitions_take_one_address() {
        let linkers = linkers();
        let module = ifunc_declaration_module();
        let mut definitions = String::from("#include <stdint.h>\n");
        for (name, _, value) in IFUNC_DECLARATIONS {
            definitions.push_str(&format!(
                "static uint64_t impl_{name}(void) {{ return {value}; }}\n\
                 static void *resolve_{name}(void) {{ return (void *)impl_{name}; }}\n\
                 uint64_t {name}(void) __attribute__((ifunc(\"resolve_{name}\")));\n\
                 void *c_addr_{name}(void) {{ return (void *){name}; }}\n"
            ));
        }
        let driver_source = "#include <stdint.h>\n#include <stdio.h>\n\
             #define EACH(X) X(if_default_fn) X(if_protected_fn) X(if_hidden_fn)\n\
             #define DECLARE(n) uint64_t call_##n(void); void *addr_##n(void), \\\n\
               *fnaddr_##n(void), *load_tbl_##n(void), *c_addr_##n(void);\n\
             EACH(DECLARE)\n\
             #define ROW(n) printf(\"%s %llu %d %d %d\\n\", #n, \\\n\
               (unsigned long long)call_##n(), addr_##n() == c_addr_##n(), \\\n\
               fnaddr_##n() == c_addr_##n(), load_tbl_##n() == c_addr_##n());\n\
             int main(void) { EACH(ROW) return 0; }\n";
        let expected = "if_default_fn 41 1 1 1\nif_protected_fn 42 1 1 1\nif_hidden_fn 43 1 1 1\n";
        // (image kind, CG relocation model, C code flag, link flags); `None`
        // links the CG and C objects into a shared library a PIE loads.
        let shapes: [(
            &str,
            trust_cg_codegen::RelocationModel,
            &str,
            Option<&[&str]>,
        ); 5] = [
            (
                "nopie",
                trust_cg_codegen::RelocationModel::Static,
                "-fno-PIE",
                Some(&["-no-pie"]),
            ),
            (
                "static",
                trust_cg_codegen::RelocationModel::Static,
                "-fno-PIE",
                Some(&["-static"]),
            ),
            (
                "pie",
                trust_cg_codegen::RelocationModel::Pie,
                "-fPIE",
                Some(&["-pie"]),
            ),
            (
                "static-pie",
                trust_cg_codegen::RelocationModel::Pie,
                "-fPIE",
                Some(&["-static-pie"]),
            ),
            (
                "shared",
                trust_cg_codegen::RelocationModel::Pic,
                "-fPIC",
                None,
            ),
        ];
        for opt_level in OPT_LEVELS {
            let directory = scratch("ifunc-declarations");
            let definitions_source = write(&directory, "definitions.c", &definitions);
            let driver = write(&directory, "driver.c", driver_source);
            for (kind, relocation_model, code_flag, link_flags) in shapes {
                let object = compile_with_model(
                    &module,
                    opt_level,
                    relocation_model,
                    &directory,
                    &format!("ifunc-{kind}.o"),
                );
                let c_object = |source: &Path, name: &str| {
                    let path = directory.join(format!("{name}-{kind}.o"));
                    ok(
                        Command::new("cc")
                            .args([code_flag, "-O1", "-c"])
                            .arg(source)
                            .arg("-o")
                            .arg(&path),
                        &directory,
                    );
                    path
                };
                let definitions_object = c_object(&definitions_source, "definitions");
                for (linker, flags) in &linkers {
                    let label = format!("{opt_level:?} {kind} {linker}");
                    let leg = directory.join(format!("{kind}-{linker}"));
                    fs::create_dir_all(&leg).unwrap();
                    let cc = || {
                        let mut command = Command::new("cc");
                        command.env("LC_ALL", "C").args(flags);
                        command
                    };
                    let program = leg.join("program");
                    match link_flags {
                        Some(link_flags) => {
                            let (success, _, stderr) = run(
                                cc().arg(code_flag)
                                    .args(link_flags)
                                    .arg(&driver)
                                    .arg(&object)
                                    .arg(&definitions_object)
                                    .arg("-o")
                                    .arg(&program),
                                &leg,
                            );
                            write(&leg, "link.txt", &stderr);
                            if kind == "static-pie" && *linker == "gold" {
                                assert!(
                                    !success && stderr.contains("--no-dynamic-linker"),
                                    "{label}: gold 2.42 links no static PIE: {stderr}"
                                );
                                continue;
                            }
                            assert!(success, "{label}: {stderr}");
                        }
                        None => {
                            let library = leg.join("libtcgifunc.so");
                            ok(
                                cc().args(["-shared", "-Wl,-z,defs,-z,text,-z,relro,-z,now"])
                                    .arg(&object)
                                    .arg(&definitions_object)
                                    .arg("-o")
                                    .arg(&library),
                                &leg,
                            );
                            ok(
                                cc().args(["-fPIE", "-pie"])
                                    .arg(&driver)
                                    .arg(&library)
                                    .arg(format!("-Wl,-rpath,{}", leg.display()))
                                    .arg("-o")
                                    .arg(&program),
                                &leg,
                            );
                        }
                    }
                    let output = ok(&mut Command::new(&program), &leg);
                    write(&leg, "run.txt", &output);
                    assert_eq!(output, expected, "{label}");
                }
            }
            eprintln!("IFUNC declarations passed: {opt_level:?} {directory:?}");
        }
    }

    // =========================================================================
    // L02-P6 closure-audit residuals (2026-09-24): data declarations, merged
    // data visibility, the DW.ref personality slot and hidden thread-locals
    // =========================================================================

    /// A `cc` command carrying one linker's flags (see [`linkers`]).
    fn cc_with(flags: &[String]) -> Command {
        let mut command = Command::new("cc");
        command.env("LC_ALL", "C").args(flags);
        command
    }

    /// `readelf --wide <flags> <path>`.
    fn readelf_text(flags: &[&str], path: &Path, directory: &Path) -> String {
        ok(
            Command::new("readelf")
                .env("LC_ALL", "C")
                .arg("--wide")
                .args(flags)
                .arg(path),
            directory,
        )
    }

    /// Names of the dynamic relocations of `image` that name any of `names`.
    fn dynamic_relocations_naming(
        image: &Path,
        directory: &Path,
        names: &[&str],
    ) -> Vec<(String, String)> {
        reloc_rows(&readelf_text(&["--relocs"], image, directory))
            .into_iter()
            .filter_map(|row| {
                let symbol = row.symbol?;
                names
                    .contains(&symbol.as_str())
                    .then_some((row.kind, symbol))
            })
            .collect()
    }

    /// L02-P6 residual 1: `merge_modules` gives a data definition the most
    /// constraining visibility of the imports it satisfies. A consumer with
    /// hidden, protected and default imports of `pw_*` and `load_pw_*`
    /// accessors, and a provider with default definitions (5, 6, 7) and a
    /// PROTECTED definition of the hidden import `pw_hidden_over_protected`
    /// (8), are merged in both orders, and also compiled separately (the
    /// consumer's hidden and protected imports compile on their own now),
    /// under `pic` at O0-O3, then linked by GNU ld, gold and LLD into a
    /// `-z defs` shared library that a PIE loads. The library never exports
    /// `pw_hidden` or `pw_hidden_over_protected` (the linker makes the
    /// latter hidden when linked separately, and the merge must too),
    /// exports `pw_protected` as `PROTECTED`, and names none of them in a
    /// dynamic relocation of the merged object. An `LD_PRELOAD` interposer
    /// defining all four words (905-908) takes over only the default load:
    /// the program prints `5 6 7 8` plain and `5 6 907 8` preloaded. At the
    /// base the merged library exported and GOT-addressed `pw_hidden`, and
    /// the interposer took it over; a merge that let the protected definition
    /// keep its own visibility would export `pw_hidden_over_protected`.
    #[test]
    fn merged_hidden_and_protected_data_imports_are_not_interposed() {
        let linkers = linkers();
        // `pw_hidden_over_protected`: a hidden import of a PROTECTED
        // definition, which the merge (and the linker, separately) makes hidden.
        let rows = [
            ("pw_hidden", "external", Visibility::Hidden, false),
            ("pw_protected", "external", Visibility::Protected, false),
            ("pw_default", "external", Visibility::Default, false),
            (
                "pw_hidden_over_protected",
                "external",
                Visibility::Hidden,
                false,
            ),
        ];
        let consumer = parse_linux(&data_declaration_text("consumer", &rows));
        let provider = parse_linux(
            "module \"provider\"\nfuncty.0 = () -> (u64)\n\
             global external mut @pw_hidden u64 = 5\n\
             global external mut @pw_protected u64 = 6\n\
             global external mut @pw_default u64 = 7\n\
             global external mut visibility(protected) @pw_hidden_over_protected u64 = 8\n\
             fn @provider_zero(functy.0) {\nbb0:\n    %0 = const u64 0\n    ret %0\n}\n",
        );
        let merge = |inputs: &[Module]| {
            trust_cg_codegen::module_merge::merge_modules(inputs)
                .unwrap_or_else(|error| panic!("merge: {error}"))
        };
        let consumer_first = merge(&[consumer.clone(), provider.clone()]);
        let provider_first = merge(&[provider.clone(), consumer.clone()]);
        for opt_level in OPT_LEVELS {
            let directory = scratch("merged-data-visibility");
            let pic = trust_cg_codegen::RelocationModel::Pic;
            let legs: [(&str, Vec<PathBuf>); 3] = [
                (
                    "consumer-first",
                    vec![compile_with_model(
                        &consumer_first,
                        opt_level,
                        pic,
                        &directory,
                        "consumer-first.o",
                    )],
                ),
                (
                    "provider-first",
                    vec![compile_with_model(
                        &provider_first,
                        opt_level,
                        pic,
                        &directory,
                        "provider-first.o",
                    )],
                ),
                (
                    "separate",
                    vec![
                        compile_with_model(&consumer, opt_level, pic, &directory, "consumer.o"),
                        compile_with_model(&provider, opt_level, pic, &directory, "provider.o"),
                    ],
                ),
            ];
            let interposer_source = write(
                &directory,
                "interposer.c",
                "#include <stdint.h>\n\
                 uint64_t pw_hidden = 905, pw_protected = 906, pw_default = 907,\n\
                   pw_hidden_over_protected = 908;\n",
            );
            let driver = write(
                &directory,
                "driver.c",
                "#include <stdint.h>\n#include <stdio.h>\n\
                 uint64_t load_pw_hidden(void), load_pw_protected(void), load_pw_default(void),\n\
                   load_pw_hidden_over_protected(void);\n\
                 int main(void) {\n\
                   printf(\"%llu %llu %llu %llu\\n\", (unsigned long long)load_pw_hidden(),\n\
                     (unsigned long long)load_pw_protected(),\n\
                     (unsigned long long)load_pw_default(),\n\
                     (unsigned long long)load_pw_hidden_over_protected());\n\
                   return 0;\n\
                 }\n",
            );
            for (leg_name, objects) in &legs {
                for (linker, flags) in &linkers {
                    let label = format!("{opt_level:?} {leg_name} {linker}");
                    let leg = directory.join(format!("{leg_name}-{linker}"));
                    fs::create_dir_all(&leg).unwrap();
                    let library = leg.join("libmdv.so");
                    ok(
                        cc_with(flags)
                            .args(["-shared", "-Wl,-z,defs,-z,text,-z,relro,-z,now"])
                            .args(objects)
                            .arg("-o")
                            .arg(&library),
                        &leg,
                    );
                    for hidden in ["pw_hidden", "pw_hidden_over_protected"] {
                        let rows = readelf_rows(&library, &leg, "--dyn-syms", hidden);
                        assert!(rows.is_empty(), "{label}: `{hidden}` is exported: {rows:?}");
                    }
                    for (name, visibility) in
                        [("pw_protected", "PROTECTED"), ("pw_default", "DEFAULT")]
                    {
                        let rows = readelf_rows(&library, &leg, "--dyn-syms", name);
                        assert!(
                            matches!(rows.as_slice(), [(bind, vis, ndx)]
                                if bind == "GLOBAL" && vis == visibility && ndx != "UND"),
                            "{label}: `{name}`: {rows:?}"
                        );
                    }
                    let hidden_relocs = dynamic_relocations_naming(
                        &library,
                        &leg,
                        &["pw_hidden", "pw_hidden_over_protected"],
                    );
                    assert!(hidden_relocs.is_empty(), "{label}: {hidden_relocs:?}");
                    if *leg_name != "separate" {
                        let protected_relocs =
                            dynamic_relocations_naming(&library, &leg, &["pw_protected"]);
                        assert!(
                            protected_relocs.is_empty(),
                            "{label}: the merged definition is addressed PC-relatively: \
                             {protected_relocs:?}"
                        );
                    }
                    let interposer = leg.join("libinterpose.so");
                    ok(
                        cc_with(flags)
                            .args(["-shared", "-fPIC"])
                            .arg(&interposer_source)
                            .arg("-o")
                            .arg(&interposer),
                        &leg,
                    );
                    let binary = leg.join("driver");
                    ok(
                        cc_with(flags)
                            .args(["-fPIE", "-pie"])
                            .arg(&driver)
                            .arg(format!("-L{}", leg.display()))
                            .arg("-lmdv")
                            .arg(format!("-Wl,-rpath,{}", leg.display()))
                            .arg("-o")
                            .arg(&binary),
                        &leg,
                    );
                    let plain = ok(&mut Command::new(&binary), &leg);
                    assert_eq!(plain, "5 6 7 8\n", "{label}");
                    let preloaded = ok(Command::new(&binary).env("LD_PRELOAD", &interposer), &leg);
                    assert_eq!(
                        preloaded, "5 6 907 8\n",
                        "{label}: only the default load interposes"
                    );
                }
            }
        }
    }

    // -------------------------------------------------------------------------
    // L02-P6 closure audit 5: declaration-only and identical-input merges, and
    // the `SymbolAddr` and stub forms of data addresses, in a shared object
    // -------------------------------------------------------------------------

    /// Fail with every problem an audit-5 row collected at one optimization
    /// level, and a count per `[tag]` (the check that found it: `[merge]`,
    /// `[object]`, `[dynsym]`, `[dynrel]`, `[got]`, `[plain]`, `[preload]`),
    /// so a failure shows every check a defect reaches, not only the first.
    fn assert_no_problems(problems: &[String], label: &str) {
        if problems.is_empty() {
            return;
        }
        let mut tags: std::collections::BTreeMap<&str, usize> = Default::default();
        for problem in problems {
            let tag = problem
                .strip_prefix('[')
                .and_then(|rest| rest.split_once(']'))
                .map_or("untagged", |(tag, _)| tag);
            *tags.entry(tag).or_default() += 1;
        }
        panic!(
            "{label}: {} problems {tags:?}:\n{}",
            problems.len(),
            problems.join("\n")
        );
    }

    /// The PIE that reads every name of the audit-5 merge rows through the
    /// accessors of both inputs (`a_*`, `b_*`; see [`merge_unit_text`]):
    /// one line per input (the call, the function address called, the word
    /// load and each identical definition read through its address), then
    /// whether the two inputs' addresses of each name agree.
    fn merge_unit_driver() -> String {
        let mut driver = String::from(
            "#include <stdint.h>\n#include <stdio.h>\ntypedef uint64_t (*leaf)(void);\n",
        );
        for tag in ["a", "b"] {
            driver.push_str(&format!(
                "uint64_t {tag}_call_mu_fn(void), {tag}_load_mu_word(void);\n\
                 void *{tag}_addr_mu_fn(void);\n"
            ));
            for (name, ..) in MERGE_UNIT_DEFINITIONS {
                driver.push_str(&format!("const uint64_t *{tag}_addr_{name}(void);\n"));
            }
        }
        driver.push_str("int main(void) {\n");
        for tag in ["a", "b"] {
            driver.push_str(&format!(
                "  printf(\"{tag} %llu %llu %llu\", (unsigned long long){tag}_call_mu_fn(),\n    \
                 (unsigned long long)((leaf){tag}_addr_mu_fn())(),\n    \
                 (unsigned long long){tag}_load_mu_word());\n"
            ));
            for (name, ..) in MERGE_UNIT_DEFINITIONS {
                driver.push_str(&format!(
                    "  printf(\" %llu\", (unsigned long long)*{tag}_addr_{name}());\n"
                ));
            }
            driver.push_str("  printf(\"\\n\");\n");
        }
        driver.push_str("  printf(\"same %d\", a_addr_mu_fn() == b_addr_mu_fn());\n");
        for (name, ..) in MERGE_UNIT_DEFINITIONS {
            driver.push_str(&format!(
                "  printf(\" %d\", a_addr_{name}() == b_addr_{name}());\n"
            ));
        }
        driver.push_str("  printf(\"\\n\");\n  return 0;\n}\n");
        driver
    }

    /// L02-P6 closure audit 5: a merge in which NO input defines a name, or
    /// every input defines it identically, gives the name the visibility the
    /// linker gives it under separate compilation, in a `pic` shared library
    /// linked by GNU ld, gold and LLD at O0-O3. Two inputs of
    /// [`merge_unit_text`] state every name with the `first` and `second`
    /// visibility of (default, default) and each of [`VISIBILITY_PAIRS`].
    /// Each pair is compiled merged and separately and linked with a C object
    /// that defines the declared function (5) and word (7):
    ///
    /// * the merged object spells the most constraining visibility on every
    ///   undefined symbol and definition (`readelf --syms`);
    /// * the library does not export a name that is hidden, and exports each
    ///   as `PROTECTED` when it is protected;
    /// * a PIE prints the library's values plain; under an `LD_PRELOAD`
    ///   interposer that defines every name (905, 907, 917-920) only the
    ///   (default, default) pair's reads move; the merged and the separate
    ///   library of a pair print the same.
    ///
    /// Every check runs at each level before the row fails, so a failure
    /// names each check the defect reaches ([`assert_no_problems`]). The
    /// mutant log is on
    /// [`data_symbol_and_stub_addresses_bind_like_global_addr_in_a_shared_object`].
    ///
    /// Execution evidence for these linkers and the glibc loader on this
    /// host, not a linker or loader proof.
    #[test]
    fn merged_declarations_and_identical_definitions_keep_their_visibility_in_a_shared_object() {
        let linkers = linkers();
        let pic = trust_cg_codegen::RelocationModel::Pic;
        let pairs: Vec<(Visibility, Visibility)> =
            std::iter::once((Visibility::Default, Visibility::Default))
                .chain(VISIBILITY_PAIRS)
                .collect();
        let own = "5 5 7 17 18 19 20";
        let interposed = "905 905 907 917 918 919 920";
        let expected = |values: &str| format!("a {values}\nb {values}\nsame 1 1 1 1 1\n");
        for opt_level in OPT_LEVELS {
            let directory = scratch("merge-unit-visibility");
            let definitions_source = write(
                &directory,
                "definitions.c",
                "#include <stdint.h>\n\
                 uint64_t mu_fn(void) { return 5; }\n\
                 uint64_t mu_word = 7;\n",
            );
            let definitions = directory.join("definitions.o");
            ok(
                Command::new("cc")
                    .env("LC_ALL", "C")
                    .args(["-fPIC", "-c"])
                    .arg(&definitions_source)
                    .arg("-o")
                    .arg(&definitions),
                &directory,
            );
            let interposer_source = write(
                &directory,
                "interposer.c",
                "#include <stdint.h>\n\
                 uint64_t mu_fn(void) { return 905; }\n\
                 uint64_t mu_word = 907;\n\
                 const uint64_t mu_odr = 917, mu_weak_const = 918, mu_lo = 919, mu_wodr = 920;\n",
            );
            let driver = write(&directory, "driver.c", merge_unit_driver());
            let mut problems = Vec::new();
            for (first, second) in &pairs {
                let visibility = most_constraining(*first, *second);
                let pair = format!("{first}-{second}");
                let a = parse_linux(&merge_unit_text("a", *first));
                let b = parse_linux(&merge_unit_text("b", *second));
                let merged =
                    match trust_cg_codegen::module_merge::merge_modules(&[a.clone(), b.clone()]) {
                        Ok(merged) => merged,
                        Err(error) => {
                            problems.push(format!("[merge] {pair}: {error}"));
                            continue;
                        }
                    };
                let merged_object = compile_with_model(
                    &merged,
                    opt_level,
                    pic,
                    &directory,
                    &format!("{pair}-merged.o"),
                );
                let upper = visibility.to_string().to_uppercase();
                for (name, bind, _, defined) in MERGE_UNIT_SYMBOLS {
                    let bind = if bind == STB_WEAK { "WEAK" } else { "GLOBAL" };
                    let rows = readelf_rows(&merged_object, &directory, "--syms", name);
                    if !matches!(rows.as_slice(), [(row_bind, row_visibility, ndx)]
                        if row_bind == bind
                            && *row_visibility == upper
                            && (ndx == "UND") != defined)
                    {
                        problems.push(format!(
                            "[object] {pair}: the merged object's `{name}` must be {bind} \
                             {upper}: {rows:?}"
                        ));
                    }
                }
                let legs = [
                    ("merged", vec![merged_object]),
                    (
                        "separate",
                        vec![
                            compile_with_model(
                                &a,
                                opt_level,
                                pic,
                                &directory,
                                &format!("{pair}-a.o"),
                            ),
                            compile_with_model(
                                &b,
                                opt_level,
                                pic,
                                &directory,
                                &format!("{pair}-b.o"),
                            ),
                        ],
                    ),
                ];
                for (leg_name, objects) in &legs {
                    for (linker, flags) in &linkers {
                        let label = format!("{opt_level:?} {pair} {leg_name} {linker}");
                        let leg = directory.join(format!("{pair}-{leg_name}-{linker}"));
                        fs::create_dir_all(&leg).unwrap();
                        let library = leg.join("libmu.so");
                        ok(
                            cc_with(flags)
                                .args(["-shared", "-Wl,-z,defs,-z,text,-z,relro,-z,now"])
                                .args(objects)
                                .arg(&definitions)
                                .arg("-o")
                                .arg(&library),
                            &leg,
                        );
                        for (name, ..) in MERGE_UNIT_SYMBOLS {
                            let rows = readelf_rows(&library, &leg, "--dyn-syms", name);
                            if visibility == Visibility::Hidden {
                                if !rows.is_empty() {
                                    problems.push(format!(
                                        "[dynsym] {label}: `{name}` is exported: {rows:?}"
                                    ));
                                }
                            } else if !matches!(rows.as_slice(), [(_, row_visibility, ndx)]
                                if *row_visibility == upper && ndx != "UND")
                            {
                                problems.push(format!(
                                    "[dynsym] {label}: `{name}` must be exported {upper}: {rows:?}"
                                ));
                            }
                        }
                        let interposer = leg.join("libinterpose.so");
                        ok(
                            cc_with(flags)
                                .args(["-shared", "-fPIC"])
                                .arg(&interposer_source)
                                .arg("-o")
                                .arg(&interposer),
                            &leg,
                        );
                        let binary = leg.join("driver");
                        ok(
                            cc_with(flags)
                                .args(["-fPIE", "-pie"])
                                .arg(&driver)
                                .arg(format!("-L{}", leg.display()))
                                .arg("-lmu")
                                .arg(format!("-Wl,-rpath,{}", leg.display()))
                                .arg("-o")
                                .arg(&binary),
                            &leg,
                        );
                        let plain = ok(&mut Command::new(&binary), &leg);
                        if plain != expected(own) {
                            problems.push(format!("[plain] {label}: {plain:?}"));
                        }
                        let preloaded =
                            ok(Command::new(&binary).env("LD_PRELOAD", &interposer), &leg);
                        let want = expected(if visibility == Visibility::Default {
                            interposed
                        } else {
                            own
                        });
                        if preloaded != want {
                            problems.push(format!(
                                "[preload] {label}: only a default name interposes: \
                                 {preloaded:?}, not {want:?}"
                            ));
                        }
                    }
                }
            }
            assert_no_problems(&problems, &format!("{opt_level:?} {directory:?}"));
            eprintln!(
                "declaration-only and identical merges passed: {opt_level:?} {} pairs {:?} \
                 {directory:?}",
                pairs.len(),
                linker_names(&linkers)
            );
        }
    }

    /// L02-P6 closure audit 5: every address form of a data definition binds
    /// like `Inst::GlobalAddr` in a `pic` shared library linked by GNU ld,
    /// gold and LLD at O0-O3. [`address_form_module`] gives each strong,
    /// read-only, `weak` and `linkonce_odr` word, default, hidden and
    /// protected, a `GlobalAddr`, a function-body `SymbolAddr` and an
    /// importer global-address stub accessor, the last two also at offset 8:
    ///
    /// * the library does not export the hidden words and exports the
    ///   protected ones as `PROTECTED`; no dynamic relocation names a hidden
    ///   or protected word, no GOT slot holds one's address, and each default
    ///   word has a `GLOB_DAT` GOT slot;
    /// * a PIE reads every form of every word and checks every address
    ///   against the `GlobalAddr` one (plus 8 for the offset forms); under an
    ///   `LD_PRELOAD` interposer that defines every word, exactly the default
    ///   words move, every form together.
    ///
    /// Every check runs at each level before the row fails
    /// ([`assert_no_problems`]).
    ///
    /// Mutation evidence (L02-P6 fifth closure audit, `159f53415`). Each
    /// mutant below was applied alone to the sources of `063b6c49a` with
    /// these rows (at `17df3d66d`); the seven floor targets
    /// `aarch64_elf_symbol_binding`, `e2e_aarch64_elf_relocation_model`,
    /// `v41_abi_residue_objects`, `e2e_aarch64_globals_linux`,
    /// `e2e_aarch64_elf_sections`, `e2e_aarch64_elf_link` and
    /// `e2e_aarch64_elf_tlsie` were rebuilt and run with
    /// `TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1`, and the source was restored.
    /// Unmutated, they passed 81/21/18/15/26/11/13 with no `SKIP` line. Every
    /// mutant was killed; each of the audit's seven only by the two rows of
    /// its class added here. The problem counts are those of the native
    /// row's first level (O0).
    ///
    /// * S01 (`trust-cg-lower` `adapter.rs`, `decode_imported_global_addr`):
    ///   `self.global_address_is_got_indirect(global)` ->
    ///   `global_is_external_data_import(global) ||
    ///   self.definition_is_preemptible(global.linkage,
    ///   trust_ir::Visibility::Default)`. Killed by both address-form rows:
    ///   under `pic` the object named each hidden and protected word with
    ///   the GOT pair; in the library a GOT slot held each one (20 `[got]`)
    ///   and gold named the protected ones in `GLOB_DAT` relocations (1
    ///   `[dynrel]`). The plain and preloaded runs printed the expected
    ///   values: the slots held the library's own addresses.
    /// * S02 (`translate_symbol_addr_const`, `is_local_global`): the same
    ///   substitution in `global.name == symbol &&
    ///   !self.global_address_is_got_indirect(global)`. Killed as S01.
    /// * S06 (`module_merge.rs`, the identical-global branch): after
    ///   `comparable.visibility = w.visibility;`, `let s06_dedup =
    ///   &comparable == w;`, and the update `visibilities[d as usize] =
    ///   most_constraining_visibility(visibilities[d as usize],
    ///   g.visibility);` runs only `if !s06_dedup`. Killed by both merge
    ///   rows: where the second input was more constraining, `mu_word` and
    ///   the four words kept the first input's visibility, the merged
    ///   library exported them with it (default in place of hidden or
    ///   protected, protected in place of hidden) and the interposer took
    ///   the default-first pairs' reads (15 `[object]`, 45 `[dynsym]`, 6
    ///   `[preload]`).
    /// * S06a and S06b: as S06 with `s06_dedup` also requiring
    ///   `global_is_import(g)` (identical imports) or
    ///   `!global_is_import(g)` (identical definitions). Killed by both
    ///   merge rows (3, 9, 6 and 12, 36, 6 problems).
    /// * S07: `comparable.visibility = w.visibility;` deleted. Killed by
    ///   both merge rows: the merge refused every pair of distinct
    ///   visibilities (6 `[merge]`).
    /// * S21 (`merge_modules`, step 12): `f.visibility =
    ///   visibilities[dense];` -> `if orig.has_body() { f.visibility =
    ///   visibilities[dense]; }`. Killed by both merge rows: where the
    ///   second input was more constraining, `mu_fn` kept the first
    ///   input's visibility (`GLOBAL DEFAULT UND` in the default-first
    ///   merges), the library exported it and the interposer took the
    ///   default-first merges' call and address (3 `[object]`, 9
    ///   `[dynsym]`, 6 `[preload]`).
    /// * N1 (the first input naming a global): `visibilities.push(
    ///   g.visibility);` -> `visibilities.push(
    ///   trust_ir::Visibility::Default);`. Killed by both merge rows,
    ///   `merged_data_import_visibility_restricts_the_definition` and
    ///   `native::merged_hidden_and_protected_data_imports_are_not_interposed`.
    /// * N2 (a function's accumulated visibility): a bodyless input resets
    ///   it to its own (`if f.has_body() { most_constraining_visibility(..)
    ///   } else { f.visibility }`). Killed by both merge rows and
    ///   `merged_declaration_visibility_restricts_the_definition`.
    /// * N3 (a global's accumulated visibility): the last input wins
    ///   (`visibilities[d as usize] = g.visibility;`). Killed as N1.
    /// * N4 (`decode_imported_global_addr`): the import-only predicate
    ///   `global_is_external_data_import(global)`. Killed by both
    ///   address-form rows: the emitters' `pic` backstop refused the
    ///   PC-relative page of each default word.
    /// * N5 (`is_local_global`): `!global_is_external_data_import(global)`.
    ///   Killed as N4 and by `e2e_aarch64_globals_linux`'s
    ///   `body_symbol_addr_naming_a_thread_local_is_refused_by_name_on_elf_and_macho`.
    /// * N6 (the stub's nonzero-offset path): its base `opcode:
    ///   base_opcode` rewritten from `ExternRef { name }` to `GlobalRef {
    ///   name }`. Killed as N4.
    /// * N7 (`translate_symbol_addr_const`): `is_local_function ||
    ///   is_local_global` -> `is_local_function || (is_local_global &&
    ///   addend == 0)`. Killed by both address-form rows (20 `[got]`, 1
    ///   `[dynrel]`) and by `e2e_aarch64_globals_linux`'s
    ///   `native::jit_reads_and_writes_module_globals_and_string_constant_at_o0_through_o3`.
    ///
    /// Execution evidence for these linkers and the glibc loader on this
    /// host, not a linker or loader proof.
    #[test]
    fn data_symbol_and_stub_addresses_bind_like_global_addr_in_a_shared_object() {
        let linkers = linkers();
        let module = address_form_module(&AddressForm::ALL);
        let rows = address_form_rows();
        let interposed_value = |index: usize| 0x9000 + 0x10 * index as u64;
        let mut interposer_source = String::from("#include <stdint.h>\n");
        let mut driver_source = String::from("#include <stdint.h>\n#include <stdio.h>\n");
        for (index, (name, _, mutable, _, _)) in rows.iter().enumerate() {
            let value = interposed_value(index);
            interposer_source.push_str(&format!(
                "{}uint64_t {name}[2] = {{{value}, {}}};\n",
                if *mutable { "" } else { "const " },
                value + 1
            ));
            driver_source.push_str(&format!(
                "uint64_t *ga_{name}(void), *sym_{name}(void), *symoff_{name}(void),\n  \
                 *stub_{name}(void), *stuboff_{name}(void);\n"
            ));
        }
        driver_source.push_str("int main(void) {\n");
        for (name, ..) in &rows {
            driver_source.push_str(&format!(
                "  printf(\"{name} %llu %llu %llu %llu %llu %d\\n\",\n    \
                 (unsigned long long)*ga_{name}(), (unsigned long long)*sym_{name}(),\n    \
                 (unsigned long long)*symoff_{name}(), (unsigned long long)*stub_{name}(),\n    \
                 (unsigned long long)*stuboff_{name}(),\n    \
                 sym_{name}() == ga_{name}() && stub_{name}() == ga_{name}()\n    \
                 && symoff_{name}() == ga_{name}() + 1 && stuboff_{name}() == ga_{name}() + 1);\n"
            ));
        }
        driver_source.push_str("  return 0;\n}\n");
        let expected = |preloaded: bool| -> String {
            rows.iter()
                .enumerate()
                .map(|(index, (name, _, _, visibility, value))| {
                    let value = if preloaded && *visibility == Visibility::Default {
                        interposed_value(index)
                    } else {
                        *value
                    };
                    format!(
                        "{name} {value} {value} {} {value} {} 1\n",
                        value + 1,
                        value + 1
                    )
                })
                .collect()
        };
        let bound: Vec<&str> = rows
            .iter()
            .filter(|(.., visibility, _)| *visibility != Visibility::Default)
            .map(|(name, ..)| name.as_str())
            .collect();
        for opt_level in OPT_LEVELS {
            let directory = scratch("data-address-forms");
            let object = compile_with_model(
                &module,
                opt_level,
                trust_cg_codegen::RelocationModel::Pic,
                &directory,
                "address_forms.o",
            );
            let interposer_source = write(&directory, "interposer.c", &interposer_source);
            let driver = write(&directory, "driver.c", &driver_source);
            let mut problems = Vec::new();
            for (linker, flags) in &linkers {
                let label = format!("{opt_level:?} {linker}");
                let leg = directory.join(linker);
                fs::create_dir_all(&leg).unwrap();
                let library = leg.join("libaf.so");
                ok(
                    cc_with(flags)
                        .args(["-shared", "-Wl,-z,defs,-z,text,-z,relro,-z,now"])
                        .arg(&object)
                        .arg("-o")
                        .arg(&library),
                    &leg,
                );
                for (name, _, _, visibility, _) in &rows {
                    let dynamic = readelf_rows(&library, &leg, "--dyn-syms", name);
                    let upper = visibility.to_string().to_uppercase();
                    if *visibility == Visibility::Hidden {
                        if !dynamic.is_empty() {
                            problems
                                .push(format!("[dynsym] {label}: `{name}` exported: {dynamic:?}"));
                        }
                    } else if !matches!(dynamic.as_slice(), [(_, row_visibility, ndx)]
                        if *row_visibility == upper && ndx != "UND")
                    {
                        problems.push(format!(
                            "[dynsym] {label}: `{name}` must be exported {upper}: {dynamic:?}"
                        ));
                    }
                }
                let dynamic_relocs = readelf_text(&["--relocs"], &library, &leg);
                write(&leg, "library-relocs.txt", &dynamic_relocs);
                let dynamic_rows = reloc_rows(&dynamic_relocs);
                let naming_bound: Vec<&RelocRow> = dynamic_rows
                    .iter()
                    .filter(|row| {
                        row.symbol
                            .as_deref()
                            .is_some_and(|symbol| bound.contains(&symbol))
                    })
                    .collect();
                if !naming_bound.is_empty() {
                    problems.push(format!(
                        "[dynrel] {label}: a dynamic relocation names a hidden or protected \
                         word: {naming_bound:?}"
                    ));
                }
                let sections = readelf_text(&["--section-headers"], &library, &leg);
                let gots = section_ranges(&sections, &[".got", ".got.plt"]);
                let in_got = |offset: u64| {
                    gots.iter()
                        .any(|(_, start, end)| (*start..*end).contains(&offset))
                };
                let symbols = readelf_text(&["--syms"], &library, &leg);
                for (name, _, _, visibility, _) in &rows {
                    if *visibility == Visibility::Default {
                        if !dynamic_rows.iter().any(|row| {
                            row.kind == "R_AARCH64_GLOB_DAT"
                                && row.symbol.as_deref() == Some(name.as_str())
                                && in_got(row.offset)
                        }) {
                            problems.push(format!(
                                "[got] {label}: the default `{name}` needs a GLOB_DAT GOT slot"
                            ));
                        }
                        continue;
                    }
                    let value = symbol_value(&symbols, name)
                        .unwrap_or_else(|| panic!("{label}: `{name}` in .symtab"));
                    let slots: Vec<&RelocRow> = dynamic_rows
                        .iter()
                        .filter(|row| {
                            row.kind == "R_AARCH64_RELATIVE"
                                && in_got(row.offset)
                                && (row.addend == value || row.addend == value + 8)
                        })
                        .collect();
                    if !slots.is_empty() {
                        problems.push(format!(
                            "[got] {label}: a GOT slot holds `{name}` ({value:#x}): {slots:?}"
                        ));
                    }
                }
                let interposer = leg.join("libinterpose.so");
                ok(
                    cc_with(flags)
                        .args(["-shared", "-fPIC"])
                        .arg(&interposer_source)
                        .arg("-o")
                        .arg(&interposer),
                    &leg,
                );
                let binary = leg.join("driver");
                ok(
                    cc_with(flags)
                        .args(["-fPIE", "-pie"])
                        .arg(&driver)
                        .arg(format!("-L{}", leg.display()))
                        .arg("-laf")
                        .arg(format!("-Wl,-rpath,{}", leg.display()))
                        .arg("-o")
                        .arg(&binary),
                    &leg,
                );
                let plain = ok(&mut Command::new(&binary), &leg);
                if plain != expected(false) {
                    problems.push(format!("[plain] {label}: {plain:?}"));
                }
                let preloaded = ok(Command::new(&binary).env("LD_PRELOAD", &interposer), &leg);
                if preloaded != expected(true) {
                    problems.push(format!(
                        "[preload] {label}: only the default words interpose: {preloaded:?}"
                    ));
                }
            }
            assert_no_problems(&problems, &format!("{opt_level:?} {directory:?}"));
            eprintln!(
                "data address forms passed: {opt_level:?} {} words {:?} {directory:?}",
                rows.len(),
                linker_names(&linkers)
            );
        }
    }

    /// The strong data declarations of the L02-P6 data rows, all resolved by
    /// a C object in the same output: default, protected and hidden
    /// `External` imports and a hidden `AvailableExternally` one (whose own
    /// initializer is never emitted), plus `dd_ifunc_hidden`, a hidden data
    /// declaration whose name the C object defines as a GNU IFUNC function.
    const STRONG_DATA_DECLARATIONS: [(&str, &str, Visibility, bool); 5] = [
        ("dd_default", "external", Visibility::Default, false),
        ("dd_protected", "external", Visibility::Protected, false),
        ("dd_hidden", "external", Visibility::Hidden, false),
        (
            "dd_avail_hidden",
            "available_externally",
            Visibility::Hidden,
            false,
        ),
        ("dd_ifunc_hidden", "external", Visibility::Hidden, false),
    ];

    /// L02-P6 residual 2: trust-ir hidden and protected DATA declarations
    /// ([`STRONG_DATA_DECLARATIONS`]) compile and bind inside the output,
    /// O0-O3, with GNU ld, gold and LLD, into a non-PIE executable (`static`
    /// code), a `-static` executable, a PIE, a static PIE (`pie` code) and a
    /// `-z defs` shared library a PIE loads (`pic` code):
    ///
    /// * each CG load reads the C object's value (11, 22, 33, 44: never the
    ///   `AvailableExternally` initializer), each CG store is what the C
    ///   object reads back, and each CG address equals the C object's own;
    /// * the CG address of `dd_ifunc_hidden` equals the C object's address of
    ///   the IFUNC function in every image. The declaration's address comes
    ///   from the GOT; a PC-relative form reads the IFUNC's PLT stub with GNU
    ///   ld (PIE, static PIE, shared) and gold (PIE, shared), as a GCC
    ///   `extern char x[] __attribute__((visibility("hidden")))` does;
    /// * gold links no static PIE (`--no-dynamic-linker`), which is pinned;
    /// * in the library the hidden words are absent from `.dynsym` and the
    ///   protected one is `PROTECTED`; an `LD_PRELOAD` interposer defining
    ///   the four words takes over only the default one;
    /// * a non-PIE executable reading the library's default word gets an
    ///   `R_AARCH64_COPY` that the library's CG GOT load follows, while every
    ///   linker refuses the copy relocation the protected word would need;
    /// * a hidden or protected declaration does not link into a `-z defs`
    ///   shared library whose only definition is in another shared library
    ///   (the default twin does).
    ///
    /// Execution evidence for these linkers and the glibc loader on this
    /// host, not a linker or loader proof.
    #[test]
    fn hidden_and_protected_data_declarations_bind_inside_the_output() {
        let linkers = linkers();
        let module = data_declaration_module(&STRONG_DATA_DECLARATIONS);
        let definitions = "#include <stdint.h>\n\
             uint64_t dd_default = 11, dd_protected = 22, dd_hidden = 33, dd_avail_hidden = 44;\n\
             #define ADDR(n) void *c_addr_##n(void) { return &n; }\n\
             ADDR(dd_default) ADDR(dd_protected) ADDR(dd_hidden) ADDR(dd_avail_hidden)\n\
             static uint64_t impl_ifunc(void) { return 77; }\n\
             static void *resolve_ifunc(void) { return (void *)impl_ifunc; }\n\
             uint64_t dd_ifunc_hidden(void) __attribute__((ifunc(\"resolve_ifunc\")));\n\
             void *c_addr_dd_ifunc_hidden(void) { return (void *)dd_ifunc_hidden; }\n";
        let driver_source = "#include <stdint.h>\n#include <stdio.h>\n\
             #define EACH(X) X(dd_default) X(dd_protected) X(dd_hidden) X(dd_avail_hidden)\n\
             #define DECLARE(n) uint64_t load_##n(void); void *addr_##n(void), \\\n\
               *c_addr_##n(void); void store_##n(uint64_t);\n\
             EACH(DECLARE)\n\
             void *addr_dd_ifunc_hidden(void), *c_addr_dd_ifunc_hidden(void);\n\
             #define ROW(n) { unsigned long long before = load_##n(); \\\n\
               store_##n(before + 100); \\\n\
               printf(\"%s %llu %d %llu\\n\", #n, before, addr_##n() == c_addr_##n(), \\\n\
                 (unsigned long long)*(uint64_t *)c_addr_##n()); }\n\
             int main(void) {\n\
               EACH(ROW)\n\
               printf(\"ifunc %d\\n\", addr_dd_ifunc_hidden() == c_addr_dd_ifunc_hidden());\n\
               return 0;\n\
             }\n";
        let expected = "dd_default 11 1 111\ndd_protected 22 1 122\ndd_hidden 33 1 133\n\
                        dd_avail_hidden 44 1 144\nifunc 1\n";
        // (image kind, CG relocation model, C code flag, link flags); `None`
        // links the CG and C objects into a shared library a PIE loads.
        let shapes: [(
            &str,
            trust_cg_codegen::RelocationModel,
            &str,
            Option<&[&str]>,
        ); 5] = [
            (
                "nopie",
                trust_cg_codegen::RelocationModel::Static,
                "-fno-PIE",
                Some(&["-no-pie"]),
            ),
            (
                "static",
                trust_cg_codegen::RelocationModel::Static,
                "-fno-PIE",
                Some(&["-static"]),
            ),
            (
                "pie",
                trust_cg_codegen::RelocationModel::Pie,
                "-fPIE",
                Some(&["-pie"]),
            ),
            (
                "static-pie",
                trust_cg_codegen::RelocationModel::Pie,
                "-fPIE",
                Some(&["-static-pie"]),
            ),
            (
                "shared",
                trust_cg_codegen::RelocationModel::Pic,
                "-fPIC",
                None,
            ),
        ];
        for opt_level in OPT_LEVELS {
            let directory = scratch("data-declarations");
            let definitions_source = write(&directory, "definitions.c", definitions);
            let driver = write(&directory, "driver.c", driver_source);
            let interposer_source = write(
                &directory,
                "interposer.c",
                "#include <stdint.h>\n\
                 uint64_t dd_default = 901, dd_protected = 902, dd_hidden = 903, \
                 dd_avail_hidden = 904;\n",
            );
            for (kind, relocation_model, code_flag, link_flags) in shapes {
                let object = compile_with_model(
                    &module,
                    opt_level,
                    relocation_model,
                    &directory,
                    &format!("declarations-{kind}.o"),
                );
                let definitions_object = directory.join(format!("definitions-{kind}.o"));
                ok(
                    Command::new("cc")
                        .args([code_flag, "-O1", "-c"])
                        .arg(&definitions_source)
                        .arg("-o")
                        .arg(&definitions_object),
                    &directory,
                );
                for (linker, flags) in &linkers {
                    let label = format!("{opt_level:?} {kind} {linker}");
                    let leg = directory.join(format!("{kind}-{linker}"));
                    fs::create_dir_all(&leg).unwrap();
                    let program = leg.join("program");
                    let Some(link_flags) = link_flags else {
                        let library = leg.join("libtcgdata.so");
                        ok(
                            cc_with(flags)
                                .args(["-shared", "-Wl,-z,defs,-z,text,-z,relro,-z,now"])
                                .arg(&object)
                                .arg(&definitions_object)
                                .arg("-o")
                                .arg(&library),
                            &leg,
                        );
                        for (name, _, visibility, _) in STRONG_DATA_DECLARATIONS {
                            let rows = readelf_rows(&library, &leg, "--dyn-syms", name);
                            if visibility == Visibility::Hidden {
                                // gold lists the hidden IFUNC `LOCAL` for the
                                // `GLOB_DAT` that fills its GOT slot (GNU ld
                                // and LLD write an `IRELATIVE`); never exported.
                                let gold_ifunc = *linker == "gold" && name == "dd_ifunc_hidden";
                                assert!(
                                    rows.iter()
                                        .all(|(bind, vis, _)| bind == "LOCAL" && vis == "HIDDEN")
                                        && (gold_ifunc || rows.is_empty()),
                                    "{label}: `{name}` exported: {rows:?}"
                                );
                            } else {
                                assert!(
                                    matches!(rows.as_slice(), [(bind, vis, ndx)]
                                        if bind == "GLOBAL"
                                            && *vis == visibility.to_string().to_uppercase()
                                            && ndx != "UND"),
                                    "{label}: `{name}`: {rows:?}"
                                );
                            }
                        }
                        ok(
                            cc_with(flags)
                                .args(["-fPIE", "-pie"])
                                .arg(&driver)
                                .arg(&library)
                                .arg(format!("-Wl,-rpath,{}", leg.display()))
                                .arg("-o")
                                .arg(&program),
                            &leg,
                        );
                        let output = ok(&mut Command::new(&program), &leg);
                        write(&leg, "run.txt", &output);
                        assert_eq!(output, expected, "{label}");
                        let interposer = leg.join("libinterpose.so");
                        ok(
                            cc_with(flags)
                                .args(["-shared", "-fPIC"])
                                .arg(&interposer_source)
                                .arg("-o")
                                .arg(&interposer),
                            &leg,
                        );
                        let preloaded =
                            ok(Command::new(&program).env("LD_PRELOAD", &interposer), &leg);
                        write(&leg, "run-preload.txt", &preloaded);
                        assert_eq!(
                            preloaded,
                            "dd_default 901 1 1001\ndd_protected 22 1 122\ndd_hidden 33 1 133\n\
                             dd_avail_hidden 44 1 144\nifunc 1\n",
                            "{label}: only the default word interposes"
                        );
                        // A non-PIE executable copy-relocates the default
                        // word, and the library's GOT load follows the copy;
                        // no linker copies the protected word.
                        for (name, protected) in [("dd_default", false), ("dd_protected", true)] {
                            let source = write(
                                &leg,
                                &format!("copy-{name}.c"),
                                format!(
                                    "#include <stdint.h>\n#include <stdio.h>\n\
                                     extern uint64_t {name};\nvoid *addr_{name}(void);\n\
                                     int main(void) {{\n\
                                       printf(\"copy %d %llu\\n\", addr_{name}() == (void *)&{name},\n\
                                         (unsigned long long){name});\n\
                                       return 0;\n\
                                     }}\n"
                                ),
                            );
                            let executable = leg.join(format!("copy-{name}"));
                            let (success, _, stderr) = run(
                                cc_with(flags)
                                    .args(["-fno-PIE", "-no-pie", "-O1"])
                                    .arg(&source)
                                    .arg(&library)
                                    .arg(format!("-Wl,-rpath,{}", leg.display()))
                                    .arg("-o")
                                    .arg(&executable),
                                &leg,
                            );
                            if protected {
                                assert!(
                                    !success && stderr.contains(name),
                                    "{label}: a copy of the protected word must be refused: \
                                     {stderr}"
                                );
                                continue;
                            }
                            assert!(success, "{label}: {stderr}");
                            let copies: Vec<(String, String)> =
                                dynamic_relocations_naming(&executable, &leg, &[name])
                                    .into_iter()
                                    .filter(|(kind, _)| kind == "R_AARCH64_COPY")
                                    .collect();
                            assert_eq!(copies.len(), 1, "{label}: {copies:?}");
                            let output = ok(&mut Command::new(&executable), &leg);
                            assert_eq!(output, "copy 1 11\n", "{label}: the GOT follows the copy");
                        }
                        continue;
                    };
                    let (success, _, stderr) = run(
                        cc_with(flags)
                            .arg(code_flag)
                            .args(link_flags)
                            .arg(&driver)
                            .arg(&object)
                            .arg(&definitions_object)
                            .arg("-o")
                            .arg(&program),
                        &leg,
                    );
                    if kind == "static-pie" && *linker == "gold" {
                        assert!(
                            !success && stderr.contains("--no-dynamic-linker"),
                            "{label}: gold 2.42 links no static PIE: {stderr}"
                        );
                        continue;
                    }
                    assert!(success, "{label}: {stderr}");
                    let output = ok(&mut Command::new(&program), &leg);
                    write(&leg, "run.txt", &output);
                    assert_eq!(output, expected, "{label}");
                }
            }
            // A strong hidden or protected declaration needs its definition
            // in the output: a library that finds it only in another shared
            // library does not link. The default twin does.
            let definitions_library = directory.join("libdddefs.so");
            ok(
                Command::new("cc")
                    .args(["-shared", "-fPIC", "-O1"])
                    .arg(&definitions_source)
                    .arg("-o")
                    .arg(&definitions_library),
                &directory,
            );
            for (name, visibility) in [
                ("dd_default", Visibility::Default),
                ("dd_protected", Visibility::Protected),
                ("dd_hidden", Visibility::Hidden),
            ] {
                let single = data_declaration_module(&[(name, "external", visibility, false)]);
                let object = compile_with_model(
                    &single,
                    opt_level,
                    trust_cg_codegen::RelocationModel::Pic,
                    &directory,
                    &format!("single-{name}.o"),
                );
                for (linker, flags) in &linkers {
                    let label = format!("{opt_level:?} {linker} {name} elsewhere");
                    let (success, _, stderr) = run(
                        cc_with(flags)
                            .args(["-shared", "-Wl,-z,defs"])
                            .arg(&object)
                            .arg(&definitions_library)
                            .arg("-o")
                            .arg(directory.join(format!("libsingle-{name}-{linker}.so"))),
                        &directory,
                    );
                    if visibility == Visibility::Default {
                        assert!(success, "{label}: {stderr}");
                    } else {
                        assert!(
                            !success && stderr.contains(name),
                            "{label}: must be refused: {stderr}"
                        );
                    }
                }
            }
        }
    }

    /// L02-P6 residual 2, weak: `ExternalWeak` data declarations, default,
    /// protected and hidden, read 0 when no definition is linked and bind to
    /// a C definition in the same output when one is, O0-O3, with GNU ld,
    /// gold and LLD, in a non-PIE executable, a `-static` executable, a PIE
    /// and a shared library a PIE loads. Absent, every CG address is 0 (a
    /// weak declaration is GOT-addressed), except the gold defect the
    /// function row pins: gold exports an absent weak HIDDEN reference as
    /// `WEAK HIDDEN UND` with a `GLOB_DAT` in a PIE or a shared library, and
    /// glibc then gives it a nonzero address, for the CG object and a GCC
    /// object alike. Present, each CG address equals the C object's and each
    /// load reads its value (61, 62, 63).
    #[test]
    fn weak_hidden_and_protected_data_declarations_read_null_when_absent() {
        let linkers = linkers();
        let rows = [
            ("dw_default", "external_weak", Visibility::Default, false),
            (
                "dw_protected",
                "external_weak",
                Visibility::Protected,
                false,
            ),
            ("dw_hidden", "external_weak", Visibility::Hidden, false),
        ];
        let module = data_declaration_module(&rows);
        let definitions = "#include <stdint.h>\n\
             uint64_t dw_default = 61, dw_protected = 62, dw_hidden = 63;\n\
             void *c_addr_dw_default(void) { return &dw_default; }\n\
             void *c_addr_dw_protected(void) { return &dw_protected; }\n\
             void *c_addr_dw_hidden(void) { return &dw_hidden; }\n";
        // The GCC twin of the hidden reference, for gold's absent-weak leg.
        let gcc_twin = "extern char dw_hidden[] __attribute__((weak, visibility(\"hidden\")));\n\
             void *gcc_addr_dw_hidden(void) { return dw_hidden; }\n";
        let absent_driver = "#include <stdio.h>\n\
             void *addr_dw_default(void), *addr_dw_protected(void), *addr_dw_hidden(void),\n\
               *gcc_addr_dw_hidden(void);\n\
             int main(void) {\n\
               printf(\"absent %d %d %d %d\\n\", addr_dw_default() == 0,\n\
                 addr_dw_protected() == 0, addr_dw_hidden() == 0, gcc_addr_dw_hidden() == 0);\n\
               return 0;\n\
             }\n";
        let present_driver = "#include <stdint.h>\n#include <stdio.h>\n\
             #define EACH(X) X(dw_default) X(dw_protected) X(dw_hidden)\n\
             #define DECLARE(n) uint64_t load_##n(void); void *addr_##n(void), *c_addr_##n(void);\n\
             EACH(DECLARE)\n\
             #define ROW(n) printf(\" %llu %d\", (unsigned long long)load_##n(), \\\n\
               addr_##n() == c_addr_##n());\n\
             int main(void) { printf(\"present\"); EACH(ROW) printf(\"\\n\"); return 0; }\n";
        let shapes: [(
            &str,
            trust_cg_codegen::RelocationModel,
            &str,
            Option<&[&str]>,
        ); 4] = [
            (
                "nopie",
                trust_cg_codegen::RelocationModel::Static,
                "-fno-PIE",
                Some(&["-no-pie"]),
            ),
            (
                "static",
                trust_cg_codegen::RelocationModel::Static,
                "-fno-PIE",
                Some(&["-static"]),
            ),
            (
                "pie",
                trust_cg_codegen::RelocationModel::Pie,
                "-fPIE",
                Some(&["-pie"]),
            ),
            (
                "shared",
                trust_cg_codegen::RelocationModel::Pic,
                "-fPIC",
                None,
            ),
        ];
        for opt_level in OPT_LEVELS {
            let directory = scratch("weak-data-declarations");
            let definitions_source = write(&directory, "definitions.c", definitions);
            let twin_source = write(&directory, "gcc-twin.c", gcc_twin);
            let absent_source = write(&directory, "absent.c", absent_driver);
            let present_source = write(&directory, "present.c", present_driver);
            for (kind, relocation_model, code_flag, link_flags) in shapes {
                let object = compile_with_model(
                    &module,
                    opt_level,
                    relocation_model,
                    &directory,
                    &format!("weak-{kind}.o"),
                );
                let c_object = |source: &Path, name: &str| {
                    let path = directory.join(format!("{name}-{kind}.o"));
                    ok(
                        Command::new("cc")
                            .args([code_flag, "-O1", "-c"])
                            .arg(source)
                            .arg("-o")
                            .arg(&path),
                        &directory,
                    );
                    path
                };
                let definitions_object = c_object(&definitions_source, "definitions");
                let twin_object = c_object(&twin_source, "gcc-twin");
                for (linker, flags) in &linkers {
                    let label = format!("{opt_level:?} {kind} {linker}");
                    let leg = directory.join(format!("{kind}-{linker}"));
                    fs::create_dir_all(&leg).unwrap();
                    // (driver, objects beside the CG object, expected output)
                    let gold_hidden_quirk = *linker == "gold" && matches!(kind, "pie" | "shared");
                    let absent_expected = if gold_hidden_quirk {
                        "absent 1 1 0 0\n"
                    } else {
                        "absent 1 1 1 1\n"
                    };
                    for (name, driver, extra, expected) in [
                        ("absent", &absent_source, &twin_object, absent_expected),
                        (
                            "present",
                            &present_source,
                            &definitions_object,
                            "present 61 1 62 1 63 1\n",
                        ),
                    ] {
                        let program = leg.join(name);
                        let image = match link_flags {
                            Some(link_flags) => {
                                ok(
                                    cc_with(flags)
                                        .arg(code_flag)
                                        .args(link_flags)
                                        .arg(driver)
                                        .arg(&object)
                                        .arg(extra)
                                        .arg("-o")
                                        .arg(&program),
                                    &leg,
                                );
                                program.clone()
                            }
                            None => {
                                let library = leg.join(format!("libweak{name}.so"));
                                ok(
                                    cc_with(flags)
                                        .args(["-shared", "-Wl,-z,text,-z,relro,-z,now"])
                                        .arg(&object)
                                        .arg(extra)
                                        .arg("-o")
                                        .arg(&library),
                                    &leg,
                                );
                                ok(
                                    cc_with(flags)
                                        .args(["-fPIE", "-pie"])
                                        .arg(driver)
                                        .arg(&library)
                                        .arg(format!("-Wl,-rpath,{}", leg.display()))
                                        .arg("-o")
                                        .arg(&program),
                                    &leg,
                                );
                                library
                            }
                        };
                        let output = ok(&mut Command::new(&program), &leg);
                        write(&leg, &format!("{name}.txt"), &output);
                        assert_eq!(output, expected, "{label} {name}");
                        if name == "absent" && gold_hidden_quirk {
                            let rows = readelf_rows(&image, &leg, "--dyn-syms", "dw_hidden");
                            assert!(
                                matches!(rows.as_slice(), [(bind, vis, ndx)]
                                    if bind == "WEAK" && vis == "HIDDEN" && ndx == "UND"),
                                "{label}: gold's absent weak hidden export: {rows:?}"
                            );
                        }
                    }
                }
            }
        }
    }

    /// The EH module the `DW.ref` rows compile: `<tag>_run(x)` invokes the
    /// declared `<tag>_mid(x)` with a cleanup pad that calls the declared
    /// `note_cleanup()` and resumes. No function is named
    /// `rust_eh_personality`, so its frames use `__gxx_personality_v0`
    /// through a `DW.ref.__gxx_personality_v0` slot.
    fn cleanup_eh_module(tag: &str) -> Module {
        parse_linux(
            &"\
module \"eh_TAG\"
functy.0 = (i32) -> (i32)
functy.1 = () -> ()
fn @TAG_mid(functy.0) {
}
fn @note_cleanup(functy.1) {
}
fn @TAG_run(functy.0) {
bb0(%0: i32):
    br bb3
bb3:
    %2 = invoke @func.0(%0) to bb1() unwind bb2
bb1:
    ret %2
bb2:
    %20, %21 = landingpad cleanup
    call @func.1()
    resume %20
}
"
            .replace("TAG", tag),
        )
    }

    /// L02-P6 residual 3: the `DW.ref.<personality>` slot of an external
    /// personality is GCC's WEAK HIDDEN symbol in a COMDAT group, so a `pic`
    /// EH module links into a shared object with every linker. At O0-O3, CG
    /// modules `a` and `b` (each `<tag>_run` invokes a C++ thrower through a
    /// cleanup pad, see [`cleanup_eh_module`]) are compiled under `pic` and
    /// linked by `run_link` (GNU ld, the product driver with its `.eh_frame`
    /// checks) and by `g++` with GNU ld, gold and LLD into three
    /// `-z defs,text,now` libraries: `a` alone, `a` with `b` (two CG objects
    /// sharing one slot), and `a` with a g++ `-fPIC` object whose own cleanup
    /// frame uses GCC's slot (a mixed library). The C++ throwers live in a
    /// separate library. In every library:
    ///
    /// * no `DW.ref.` symbol is in `.dynsym` (at the base gold exported the
    ///   weak default slot, and GNU ld and LLD refused the link);
    /// * exactly one `R_AARCH64_ABS64`/`GLOB_DAT` dynamic relocation names
    ///   `__gxx_personality_v0` (GNU ld also gives it a `JUMP_SLOT`, which is
    ///   not a slot cell): one slot cell survives however many objects
    ///   carried one, CG or GCC (without the COMDAT group each object's cell
    ///   and relocation would remain);
    /// * a C++ PIE driver catches each throw that crossed a frame of the
    ///   library, after that frame's cleanup ran: `a 8 1` for `a` alone,
    ///   `a 8 1` and `b 9 2` for `a` with `b`, `a 8 1` and `g 10 2` for the
    ///   mixed library (the last number counts the cleanups run so far).
    #[test]
    fn pic_eh_modules_link_into_shared_objects_with_one_hidden_personality_slot() {
        let linkers = linkers();
        let modules = [("a", cleanup_eh_module("a")), ("b", cleanup_eh_module("b"))];
        let throwers = "static int cleanups;\n\
             extern \"C\" void note_cleanup(void) { cleanups++; }\n\
             extern \"C\" int cleanup_count(void) { return cleanups; }\n\
             extern \"C\" int a_mid(int x) { throw x + 1; }\n\
             extern \"C\" int b_mid(int x) { throw x + 1; }\n\
             extern \"C\" int g_mid(int x) { throw x + 1; }\n";
        let gxx_frame = "extern \"C\" int g_mid(int);\nextern \"C\" void note_cleanup(void);\n\
             struct Cleanup { ~Cleanup() { note_cleanup(); } };\n\
             extern \"C\" int g_run(int x) { Cleanup c; return g_mid(x); }\n";
        let driver_source = "#include <cstdio>\n\
             extern \"C\" int a_run(int), cleanup_count(void);\n\
             extern \"C\" int b_run(int) __attribute__((weak));\n\
             extern \"C\" int g_run(int) __attribute__((weak));\n\
             static void probe(const char *tag, int (*run)(int), int x) {\n\
               if (!run) return;\n\
               try { run(x); std::printf(\"%s returned\\n\", tag); }\n\
               catch (int caught) {\n\
                 std::printf(\"%s %d %d\\n\", tag, caught, cleanup_count());\n\
               }\n\
             }\n\
             int main() {\n\
               probe(\"a\", a_run, 7);\n\
               probe(\"b\", b_run, 8);\n\
               probe(\"g\", g_run, 9);\n\
               return 0;\n\
             }\n";
        for opt_level in OPT_LEVELS {
            let directory = scratch("dw-ref-slot");
            let objects: Vec<(&str, PathBuf)> = modules
                .iter()
                .map(|(tag, module)| {
                    (
                        *tag,
                        compile_with_model(
                            module,
                            opt_level,
                            trust_cg_codegen::RelocationModel::Pic,
                            &directory,
                            &format!("{tag}.o"),
                        ),
                    )
                })
                .collect();
            for (tag, object) in &objects {
                let rows = readelf_rows(
                    object,
                    &directory,
                    "--symbols",
                    "DW.ref.__gxx_personality_v0",
                );
                assert!(
                    matches!(rows.as_slice(), [(bind, vis, ndx)]
                        if bind == "WEAK" && vis == "HIDDEN" && ndx != "UND"),
                    "{opt_level:?} {tag}: the slot is WEAK HIDDEN: {rows:?}"
                );
            }
            let throwers_source = write(&directory, "throwers.cc", throwers);
            let gxx_source = write(&directory, "gxx_frame.cc", gxx_frame);
            let gxx_object = directory.join("gxx_frame.o");
            ok(
                Command::new("g++")
                    .args(["-fPIC", "-O2", "-c"])
                    .arg(&gxx_source)
                    .arg("-o")
                    .arg(&gxx_object),
                &directory,
            );
            let driver = write(&directory, "driver.cc", driver_source);
            // (library tag, objects, expected output)
            let libraries: [(&str, Vec<&Path>, &str); 3] = [
                ("one", vec![objects[0].1.as_path()], "a 8 1\n"),
                (
                    "two",
                    vec![objects[0].1.as_path(), objects[1].1.as_path()],
                    "a 8 1\nb 9 2\n",
                ),
                (
                    "mixed",
                    vec![objects[0].1.as_path(), gxx_object.as_path()],
                    "a 8 1\ng 10 2\n",
                ),
            ];
            let mut legs: Vec<(String, Vec<String>)> = linkers
                .iter()
                .map(|(linker, flags)| (linker.to_string(), flags.clone()))
                .collect();
            legs.push(("run_link".to_string(), Vec::new()));
            for (linker, flags) in &legs {
                let leg = directory.join(linker);
                fs::create_dir_all(&leg).unwrap();
                let throwers_library = leg.join("libthrowers.so");
                ok(
                    Command::new("g++")
                        .env("LC_ALL", "C")
                        .args(flags)
                        .args(["-shared", "-fPIC", "-O2"])
                        .arg(&throwers_source)
                        .arg("-o")
                        .arg(&throwers_library),
                    &leg,
                );
                for (library_tag, inputs, expected) in &libraries {
                    // `run_link` links the CG-only libraries (its GNU ld
                    // leg); the mixed one goes through g++ with each linker.
                    if linker == "run_link" && *library_tag == "mixed" {
                        continue;
                    }
                    let label = format!("{opt_level:?} {linker} {library_tag}");
                    let library = leg.join(format!("libeh{library_tag}.so"));
                    if linker == "run_link" {
                        let mut request = trust_cg_codegen::link_driver::LinkRequest::executable(
                            TargetSpec::parse(LINUX).expect("triple"),
                            inputs.iter().map(|input| input.to_path_buf()).collect(),
                            library.clone(),
                        );
                        request.kind = trust_cg_codegen::link_driver::LinkOutputKind::SharedLibrary;
                        request.lib_paths = vec![leg.clone()];
                        request.rpaths = vec![leg.display().to_string()];
                        request.libs = vec!["throwers".to_string(), "stdc++".to_string()];
                        request.linker_arg_groups = vec![vec![
                            "-z".to_string(),
                            "defs".to_string(),
                            "-z".to_string(),
                            "text".to_string(),
                            "-z".to_string(),
                            "now".to_string(),
                        ]];
                        trust_cg_codegen::link_driver::run_link(&request, "cc")
                            .unwrap_or_else(|error| panic!("{label} run_link: {error}"));
                    } else {
                        ok(
                            Command::new("g++")
                                .env("LC_ALL", "C")
                                .args(flags)
                                .args(["-shared", "-Wl,-z,defs,-z,text,-z,now"])
                                .args(inputs)
                                .arg(format!("-L{}", leg.display()))
                                .arg("-lthrowers")
                                .arg(format!("-Wl,-rpath,{}", leg.display()))
                                .arg("-o")
                                .arg(&library),
                            &leg,
                        );
                    }
                    let dynsym = readelf_text(&["--dyn-syms"], &library, &leg);
                    assert!(
                        !dynsym.contains("DW.ref."),
                        "{label}: a personality slot is exported:\n{dynsym}"
                    );
                    // The slot cell's word (GNU ld also gives the
                    // personality a `JUMP_SLOT`, which is not a slot cell).
                    let personality_relocs: Vec<(String, String)> =
                        dynamic_relocations_naming(&library, &leg, &["__gxx_personality_v0"])
                            .into_iter()
                            .filter(|(kind, _)| {
                                matches!(kind.as_str(), "R_AARCH64_ABS64" | "R_AARCH64_GLOB_DAT")
                            })
                            .collect();
                    assert_eq!(
                        personality_relocs.len(),
                        1,
                        "{label}: one slot cell survives: {personality_relocs:?}"
                    );
                    let program = leg.join(format!("driver-{library_tag}"));
                    ok(
                        Command::new("g++")
                            .env("LC_ALL", "C")
                            .args(flags)
                            .args(["-fPIE", "-pie", "-O1"])
                            .arg(&driver)
                            .arg(&library)
                            .arg(&throwers_library)
                            .arg(format!("-Wl,-rpath,{}", leg.display()))
                            .arg("-o")
                            .arg(&program),
                        &leg,
                    );
                    let output = ok(&mut Command::new(&program), &leg);
                    write(&leg, &format!("run-{library_tag}.txt"), &output);
                    assert_eq!(output, *expected, "{label}");
                }
            }
        }
    }

    /// The thread-locals of
    /// [`hidden_and_protected_thread_locals_bind_inside_a_shared_object`]:
    /// `(name, trust-ir linkage, visibility, explicit section, initializer)`.
    /// The three strong hidden definitions, which the library anchors, lie at
    /// NONZERO offsets of `.tdata` (after `tt_default` and `tt_protected`),
    /// `.tbss` (after `tt_zero`) and the explicit `.tdata.tt_sec` (after
    /// `tt_sec0`).
    type TlsLibraryRow = (
        &'static str,
        &'static str,
        &'static str,
        Option<&'static str>,
        Option<u64>,
    );
    const TLS_LIBRARY_ROWS: [TlsLibraryRow; 9] = [
        ("tt_default", "external", "default", None, Some(3)),
        ("tt_protected", "external", "protected", None, Some(2)),
        ("tt_hidden", "external", "hidden", None, Some(1)),
        ("tt_weak_hidden", "weak", "hidden", None, Some(4)),
        ("tt_decl_hidden", "external", "hidden", None, None),
        ("tt_zero", "external", "default", None, Some(0)),
        ("tt_bss_hidden", "external", "hidden", None, Some(0)),
        (
            "tt_sec0",
            "external",
            "default",
            Some(".tdata.tt_sec"),
            Some(6),
        ),
        (
            "tt_sec_hidden",
            "external",
            "hidden",
            Some(".tdata.tt_sec"),
            Some(7),
        ),
    ];

    /// The anchored rows of [`TLS_LIBRARY_ROWS`] and their sections.
    const TLS_LIBRARY_ANCHORED: [(&str, &str); 3] = [
        ("tt_hidden", ".tdata"),
        ("tt_bss_hidden", ".tbss"),
        ("tt_sec_hidden", ".tdata.tt_sec"),
    ];

    /// `readelf --wide --syms` row of `name` in `text`: `(value, section
    /// index)`, or `None`.
    fn symbol_value_and_section(text: &str, name: &str) -> Option<(u64, String)> {
        text.lines().find_map(|line| {
            let columns: Vec<&str> = line.split_whitespace().collect();
            (columns.len() >= 8 && columns[0].ends_with(':') && columns[7] == name)
                .then(|| (hex(columns[1]), columns[6].to_string()))
        })
    }

    /// L02-P6 residual 4: hidden and protected thread-locals in a `pic` CG
    /// library, O0-O3, linked by GNU ld, gold and LLD
    /// ([`TLS_LIBRARY_ROWS`]). The library defines default, protected and
    /// hidden thread-locals in `.tdata`, `.tbss` and an explicit TLS section,
    /// a WEAK hidden `tt_weak_hidden` (4) that a C object's strong hidden
    /// definition (40) replaces, and declares a hidden `tt_decl_hidden` that
    /// the C object defines (5). A PIE driver runs three threads besides the
    /// main one: each reads the initial values through the CG accessors,
    /// checks that every CG address equals the C object's address of the same
    /// variable in that thread, writes a distinct value to every variable and
    /// reads them all back (so two accessors reaching one storage cell fail).
    ///
    /// * The object anchors the three strong hidden definitions, each at a
    ///   nonzero offset: the anchor's section index and value are the
    ///   variable's, and the descriptor relocations name the anchor.
    /// * The library exports only the protected and default thread-locals.
    ///   GNU ld and LLD list no hidden name in `.dynsym` and name none in a
    ///   dynamic relocation. gold lists a hidden thread-local that any object
    ///   relocates by its global symbol as `TLS LOCAL HIDDEN` (not
    ///   exported): the weak definition and the declaration, which the CG
    ///   object names by symbol, and the anchored ones, which the C object's
    ///   `extern` declarations name.
    /// * Linked with a C object that does not reference the anchored
    ///   variables, no linker, gold included, lists them in `.dynsym` or
    ///   names them in a dynamic relocation (naming the global hidden symbol
    ///   made gold list it `TLS LOCAL HIDDEN`).
    /// * An `LD_PRELOAD` interposer defining every thread-local takes over
    ///   only the default ones (the near-twin negative).
    /// * The weak hidden definition reads the C object's 40: it is not
    ///   anchored, because a strong definition elsewhere replaces it.
    #[test]
    fn hidden_and_protected_thread_locals_bind_inside_a_shared_object() {
        let linkers = linkers();
        let names: Vec<&str> = TLS_LIBRARY_ROWS.iter().map(|(name, ..)| *name).collect();
        let anchored: Vec<&str> = TLS_LIBRARY_ANCHORED.iter().map(|(name, _)| *name).collect();
        let mut text = String::from(
            "module \"tls_visibility\"\nfuncty.0 = () -> (u64)\nfuncty.1 = () -> (ptr)\n\
             functy.2 = (u64) -> ()\n",
        );
        for (name, linkage, visibility, section, initializer) in TLS_LIBRARY_ROWS {
            let section = section
                .map(|section| format!(" section(\"{section}\")"))
                .unwrap_or_default();
            let initializer = initializer
                .map(|value| format!(" = {value}"))
                .unwrap_or_default();
            text.push_str(&format!(
                "global {linkage} tls(general_dynamic) mut visibility({visibility}){section} \
                 @{name} u64{initializer}\n"
            ));
        }
        for (index, name) in names.iter().enumerate() {
            text.push_str(&format!(
                "fn @load_{name}(functy.0) {{\nbb0:\n    %0 = global_addr @global.{index}\n    \
                 %1 = load u64, ptr %0\n    ret %1\n}}\n\
                 fn @addr_{name}(functy.1) {{\nbb0:\n    %0 = global_addr @global.{index}\n    \
                 ret %0\n}}\n\
                 fn @store_{name}(functy.2) {{\nbb0(%0: u64):\n    \
                 %1 = global_addr @global.{index}\n    store u64 %0, ptr %1\n    ret\n}}\n"
            ));
        }
        let module = parse_linux(&text);
        // The C object: the strong hidden `tt_weak_hidden` and the
        // `tt_decl_hidden` definition, and every variable's address as C
        // takes it; with `anchored_refs` false, no reference to the anchored
        // variables at all.
        let definitions = |anchored_refs: bool| {
            let mut source = String::from(
                "#include <stdint.h>\n\
                 __attribute__((visibility(\"hidden\"))) __thread uint64_t tt_weak_hidden = 40;\n\
                 __thread uint64_t tt_decl_hidden = 5;\n",
            );
            for (name, _, visibility, ..) in TLS_LIBRARY_ROWS {
                if matches!(name, "tt_weak_hidden" | "tt_decl_hidden")
                    || (!anchored_refs && anchored.contains(&name))
                {
                    continue;
                }
                source.push_str(&format!(
                    "extern __thread uint64_t {name} __attribute__((visibility(\"{visibility}\")));\n"
                ));
            }
            for name in &names {
                if anchored_refs || !anchored.contains(name) {
                    source.push_str(&format!(
                        "void *c_addr_{name}(void) {{ return &{name}; }}\n"
                    ));
                }
            }
            source
        };
        let count = names.len();
        let mut driver_source = String::from(
            "#include <pthread.h>\n#include <stdint.h>\n#include <stdio.h>\n\
             typedef uint64_t (*load_fn)(void);\n\
             typedef void *(*addr_fn)(void);\n\
             typedef void (*store_fn)(uint64_t);\n",
        );
        for name in &names {
            driver_source.push_str(&format!(
                "uint64_t load_{name}(void); void *addr_{name}(void), *c_addr_{name}(void);\n\
                 void store_{name}(uint64_t);\n"
            ));
        }
        let table = |prefix: &str| {
            names
                .iter()
                .map(|name| format!("{prefix}_{name}"))
                .collect::<Vec<_>>()
                .join(", ")
        };
        driver_source.push_str(&format!(
            "static const load_fn loads[{count}] = {{ {} }};\n\
             static const addr_fn addrs[{count}] = {{ {} }};\n\
             static const addr_fn c_addrs[{count}] = {{ {} }};\n\
             static const store_fn stores[{count}] = {{ {} }};\n\
             static uint64_t initial[{count}];\n\
             static int check(uintptr_t key) {{\n\
               int good = 1;\n\
               for (int i = 0; i < {count}; i++)\n\
                 good &= loads[i]() == initial[i] && addrs[i]() == c_addrs[i]();\n\
               for (int i = 0; i < {count}; i++) stores[i](key * 100 + i);\n\
               for (int i = 0; i < {count}; i++) good &= loads[i]() == key * 100 + i;\n\
               return good;\n\
             }}\n\
             static void *worker(void *key) {{ return (void *)(uintptr_t)check((uintptr_t)key); }}\n\
             int main(void) {{\n\
               printf(\"main\");\n\
               for (int i = 0; i < {count}; i++) {{\n\
                 initial[i] = loads[i]();\n\
                 printf(\" %llu\", (unsigned long long)initial[i]);\n\
               }}\n\
               printf(\"\\n\");\n\
               pthread_t threads[3];\n\
               int good = 0;\n\
               for (uintptr_t key = 0; key < 3; key++)\n\
                 pthread_create(&threads[key], 0, worker, (void *)(key + 1));\n\
               for (int thread = 0; thread < 3; thread++) {{\n\
                 void *result;\n\
                 pthread_join(threads[thread], &result);\n\
                 good += (int)(uintptr_t)result;\n\
               }}\n\
               printf(\"threads %d/3 main %d\\n\", good, check(9));\n\
               return 0;\n\
             }}\n",
            table("load"),
            table("addr"),
            table("c_addr"),
            table("store"),
        ));
        let interposer_source = std::iter::once("#include <stdint.h>\n".to_string())
            .chain(
                names
                    .iter()
                    .enumerate()
                    .map(|(index, name)| format!("__thread uint64_t {name} = {};\n", 901 + index)),
            )
            .collect::<String>();
        let hidden_names: Vec<&str> = anchored
            .iter()
            .copied()
            .chain(["tt_weak_hidden", "tt_decl_hidden"])
            .collect();
        for opt_level in OPT_LEVELS {
            let directory = scratch("tls-visibility");
            let object = compile_with_model(
                &module,
                opt_level,
                trust_cg_codegen::RelocationModel::Pic,
                &directory,
                "tls.o",
            );
            // Each anchored definition lies at a nonzero offset, and its
            // anchor names exactly its section and offset.
            let object_symbols = readelf_text(&["--syms"], &object, &directory);
            let object_relocs = reloc_rows(&readelf_text(&["--relocs"], &object, &directory));
            let section_headers = readelf_text(&["--section-headers"], &object, &directory);
            for (name, section) in TLS_LIBRARY_ANCHORED {
                let label = format!("{opt_level:?} `{name}`");
                let (value, index) = symbol_value_and_section(&object_symbols, name)
                    .unwrap_or_else(|| panic!("{label} in .symtab"));
                let anchor = symbol_value_and_section(&object_symbols, &format!(".Ltls.{name}"))
                    .unwrap_or_else(|| panic!("{label}: its anchor in .symtab"));
                assert_ne!(value, 0, "{label}: at a nonzero offset");
                assert_eq!(
                    anchor,
                    (value, index.clone()),
                    "{label}: the anchor's place"
                );
                assert!(
                    section_headers.contains(&format!("[{index:>2}] {section} "))
                        || section_headers.contains(&format!("[{index}] {section} ")),
                    "{label}: section {index} is `{section}`\n{section_headers}"
                );
                assert!(
                    object_relocs
                        .iter()
                        .all(|row| row.symbol.as_deref() != Some(name)),
                    "{label}: relocated through its anchor"
                );
                assert_eq!(
                    object_relocs
                        .iter()
                        .filter(|row| row.symbol.as_deref() == Some(&format!(".Ltls.{name}")))
                        .count(),
                    12,
                    "{label}: the three accessors' descriptor relocations name the anchor"
                );
            }
            let c_object = |name: &str, source: &str| {
                let source = write(&directory, &format!("{name}.c"), source);
                let object = directory.join(format!("{name}.o"));
                ok(
                    Command::new("cc")
                        .args(["-fPIC", "-O2", "-c"])
                        .arg(&source)
                        .arg("-o")
                        .arg(&object),
                    &directory,
                );
                object
            };
            let definitions_object = c_object("definitions", &definitions(true));
            let anchor_object = c_object("definitions-anchor", &definitions(false));
            let driver = write(&directory, "driver.c", &driver_source);
            let interposer_source = write(&directory, "interposer.c", &interposer_source);
            for (linker, flags) in &linkers {
                let label = format!("{opt_level:?} {linker}");
                let leg = directory.join(linker);
                fs::create_dir_all(&leg).unwrap();
                let library = leg.join("libtcgtls.so");
                ok(
                    cc_with(flags)
                        .args(["-shared", "-Wl,-z,defs,-z,text,-z,relro,-z,now"])
                        .arg(&object)
                        .arg(&definitions_object)
                        .arg("-o")
                        .arg(&library),
                    &leg,
                );
                let anchor_library = leg.join("libtcgtlsanchor.so");
                ok(
                    cc_with(flags)
                        .args(["-shared", "-Wl,-z,defs,-z,text,-z,relro,-z,now"])
                        .arg(&object)
                        .arg(&anchor_object)
                        .arg("-o")
                        .arg(&anchor_library),
                    &leg,
                );
                for (image, anchored_only) in [(&library, false), (&anchor_library, true)] {
                    for name in &hidden_names {
                        let rows = readelf_rows(image, &leg, "--dyn-syms", name);
                        let listed_locally =
                            *linker == "gold" && !(anchored_only && anchored.contains(name));
                        assert!(
                            rows.iter()
                                .all(|(bind, vis, _)| bind == "LOCAL" && vis == "HIDDEN")
                                && (listed_locally || rows.is_empty()),
                            "{label} {image:?}: `{name}` in .dynsym: {rows:?}"
                        );
                    }
                    if *linker != "gold" {
                        let named = dynamic_relocations_naming(image, &leg, &hidden_names);
                        assert!(named.is_empty(), "{label} {image:?}: {named:?}");
                    }
                }
                let named = dynamic_relocations_naming(&anchor_library, &leg, &anchored);
                assert!(named.is_empty(), "{label}: {named:?}");
                for (name, _, visibility, ..) in TLS_LIBRARY_ROWS {
                    if visibility == "hidden" {
                        continue;
                    }
                    let rows = readelf_rows(&library, &leg, "--dyn-syms", name);
                    let visibility = visibility.to_uppercase();
                    assert!(
                        matches!(rows.as_slice(), [(bind, vis, ndx)]
                            if bind == "GLOBAL" && *vis == visibility && ndx != "UND"),
                        "{label}: `{name}`: {rows:?}"
                    );
                }
                let program = leg.join("driver");
                ok(
                    cc_with(flags)
                        .args(["-fPIE", "-pie"])
                        .arg(&driver)
                        .arg(&library)
                        .arg("-pthread")
                        .arg(format!("-Wl,-rpath,{}", leg.display()))
                        .arg("-o")
                        .arg(&program),
                    &leg,
                );
                let plain = ok(&mut Command::new(&program), &leg);
                assert_eq!(
                    plain, "main 3 2 1 40 5 0 0 6 7\nthreads 3/3 main 1\n",
                    "{label}"
                );
                let interposer = leg.join("libinterpose.so");
                ok(
                    cc_with(flags)
                        .args(["-shared", "-fPIC"])
                        .arg(&interposer_source)
                        .arg("-o")
                        .arg(&interposer),
                    &leg,
                );
                let preloaded = ok(Command::new(&program).env("LD_PRELOAD", &interposer), &leg);
                assert_eq!(
                    preloaded, "main 901 2 1 40 5 906 0 908 7\nthreads 3/3 main 1\n",
                    "{label}: only the default thread-locals interpose"
                );
            }
        }
    }

    // -------------------------------------------------------------------------
    // L02-P6 closure audit 2: weak and COMDAT data definitions, and the
    // Pipeline route's hidden thread-local anchors, at link time
    // -------------------------------------------------------------------------

    /// Compile `source` with `compiler` (`cc` or `g++`) and `flags` into
    /// `directory/<name>.o`.
    fn c_object_with(
        compiler: &str,
        directory: &Path,
        name: &str,
        source: &str,
        flags: &[&str],
    ) -> PathBuf {
        let extension = if compiler == "g++" { "cc" } else { "c" };
        let source = write(directory, &format!("{name}.{extension}"), source);
        let object = directory.join(format!("{name}.o"));
        ok(
            Command::new(compiler)
                .env("LC_ALL", "C")
                .args(flags)
                .arg("-c")
                .arg(&source)
                .arg("-o")
                .arg(&object),
            directory,
        );
        object
    }

    /// The `readelf` spelling of `visibility` (`DEFAULT`, `HIDDEN`,
    /// `PROTECTED`).
    fn readelf_visibility(visibility: Visibility) -> String {
        visibility.to_string().to_uppercase()
    }

    /// The diagnostic `linker` refuses a non-PIE executable's store to a
    /// shared library's `visibility` data definition `name` with: an
    /// undefined reference for a hidden one (the library does not export
    /// it), a refused copy relocation for a protected one; `None` for a
    /// default one, which the executable copy-relocates.
    fn outsider_refusal(linker: &str, visibility: Visibility, name: &str) -> Option<String> {
        Some(match (visibility, linker) {
            (Visibility::Default, _) => return None,
            (Visibility::Hidden, "gold") => format!("undefined reference to '{name}'"),
            (Visibility::Hidden, "lld") => format!("undefined symbol: {name}"),
            (Visibility::Hidden, _) => format!("undefined reference to `{name}'"),
            (Visibility::Protected, "gold") => {
                format!("cannot make copy relocation for protected symbol '{name}'")
            }
            (Visibility::Protected, "lld") => format!("cannot preempt symbol: {name}"),
            (Visibility::Protected, _) => {
                format!("copy relocation against non-copyable protected symbol `{name}'")
            }
        })
    }

    /// L02-P6 closure audit 2: the weak and COMDAT data definitions of
    /// [`WEAK_DATA_ROWS`] (plain `weak` in `.data`, `.bss` and an explicit
    /// section; `linkonce`, `linkonce_odr` and `weak_odr` in their own COMDAT
    /// groups; each default, hidden and protected) in a `pic` library built
    /// through `Compiler::compile`, O0-O3, linked by GNU ld, gold and LLD.
    ///
    /// * The object spells every definition `WEAK` with its own visibility.
    /// * The library lists no hidden definition in `.dynsym`, exports the
    ///   default and protected ones `WEAK` with their visibility, and names
    ///   no hidden or protected one in a dynamic relocation.
    /// * A PIE driver reads every definition through its `load_<name>` and
    ///   `addr_<name>` accessors. An `LD_PRELOAD` interposer defining every
    ///   name takes over only the default definitions (the near-twin
    ///   negative).
    /// * A non-PIE outsider that stores to a hidden definition does not link
    ///   (the library does not export it), and one that stores to a protected
    ///   definition is refused the copy relocation. One that stores to a
    ///   default definition copy-relocates it and the library follows the
    ///   copy through its GOT slot (`exe=77 lib=77`).
    ///
    /// At the audited base, spelling these definitions `STV_DEFAULT` passed
    /// every suite: gold then linked the library exporting the hidden words
    /// `WEAK DEFAULT`, and a non-PIE outsider copy-relocated one into a split
    /// (`exe=77 lib=22`). Execution evidence for these linkers and the glibc
    /// loader on this host, not a linker or loader proof.
    #[test]
    fn weak_and_comdat_hidden_and_protected_data_bind_inside_a_shared_object() {
        let linkers = linkers();
        let module = weak_data_module();
        let directory = scratch("weak-data");
        let mut driver = String::from("#include <stdint.h>\n#include <stdio.h>\n");
        for (name, ..) in WEAK_DATA_ROWS {
            driver.push_str(&format!(
                "uint64_t load_{name}(void), *addr_{name}(void);\n"
            ));
        }
        driver.push_str("int main(void) {\n  printf(\"load\");\n");
        for (name, ..) in WEAK_DATA_ROWS {
            driver.push_str(&format!(
                "  printf(\" %llx\", (unsigned long long)load_{name}());\n"
            ));
        }
        driver.push_str("  printf(\"\\nderef\");\n");
        for (name, ..) in WEAK_DATA_ROWS {
            driver.push_str(&format!(
                "  printf(\" %llx\", (unsigned long long)*addr_{name}());\n"
            ));
        }
        driver.push_str("  printf(\"\\n\");\n  return 0;\n}\n");
        let interposed = |index: usize| 0x9000 + index as u64;
        let mut interposer = String::from("#include <stdint.h>\n");
        for (index, (name, ..)) in WEAK_DATA_ROWS.iter().enumerate() {
            interposer.push_str(&format!("uint64_t {name} = {:#x};\n", interposed(index)));
        }
        let expected = |preloaded: bool| {
            let values: String = WEAK_DATA_ROWS
                .iter()
                .enumerate()
                .map(|(index, (_, _, visibility, _, value))| {
                    let value = if preloaded && *visibility == Visibility::Default {
                        interposed(index)
                    } else {
                        *value
                    };
                    format!(" {value:x}")
                })
                .collect();
            format!("load{values}\nderef{values}\n")
        };
        let driver_object = c_object_with("cc", &directory, "driver", &driver, &["-fPIE"]);
        let interposer_object =
            c_object_with("cc", &directory, "interposer", &interposer, &["-fPIC"]);
        let outsiders: Vec<(&str, Visibility, PathBuf)> = WEAK_DATA_ROWS
            .iter()
            .enumerate()
            .map(|(index, &(name, _, visibility, ..))| {
                let source = format!(
                    "#include <stdint.h>\n#include <stdio.h>\n\
                     extern uint64_t {name};\nuint64_t load_{name}(void);\n\
                     int main(void) {{\n  {name} = 0x77;\n\
                       printf(\"exe=%llx lib=%llx\\n\", (unsigned long long){name},\n\
                         (unsigned long long)load_{name}());\n  return 0;\n}}\n"
                );
                // Named by index, so no path in a diagnostic spells `name`.
                let object = c_object_with(
                    "cc",
                    &directory,
                    &format!("outsider{index}"),
                    &source,
                    &["-fno-PIE"],
                );
                (name, visibility, object)
            })
            .collect();
        let bound: Vec<&str> = WEAK_DATA_ROWS
            .iter()
            .filter(|(.., visibility, _, _)| *visibility != Visibility::Default)
            .map(|(name, ..)| *name)
            .collect();
        for opt_level in OPT_LEVELS {
            let level = directory.join(format!("{opt_level:?}"));
            fs::create_dir_all(&level).unwrap();
            let object = compile_with_model(
                &module,
                opt_level,
                trust_cg_codegen::RelocationModel::Pic,
                &level,
                "weak_data.o",
            );
            for (name, linkage, visibility, ..) in WEAK_DATA_ROWS {
                let rows = readelf_rows(&object, &level, "--symbols", name);
                assert!(
                    matches!(rows.as_slice(), [(bind, vis, ndx)]
                        if bind == "WEAK" && *vis == readelf_visibility(visibility) && ndx != "UND"),
                    "{opt_level:?}: `{name}` ({linkage} {visibility}) in the object: {rows:?}"
                );
            }
            for (linker, flags) in &linkers {
                let label = format!("{opt_level:?} {linker}");
                let leg = level.join(linker);
                fs::create_dir_all(&leg).unwrap();
                let library = leg.join("libtcgweakdata.so");
                ok(
                    cc_with(flags)
                        .args(["-shared", "-Wl,-z,defs,-z,text,-z,relro,-z,now"])
                        .arg(&object)
                        .arg("-o")
                        .arg(&library),
                    &leg,
                );
                write(
                    &leg,
                    "dynsym.txt",
                    readelf_text(&["--dyn-syms"], &library, &leg),
                );
                for (name, linkage, visibility, ..) in WEAK_DATA_ROWS {
                    let rows = readelf_rows(&library, &leg, "--dyn-syms", name);
                    if visibility == Visibility::Hidden {
                        assert!(
                            rows.is_empty(),
                            "{label}: hidden `{name}` ({linkage}) in .dynsym: {rows:?}"
                        );
                        continue;
                    }
                    assert!(
                        matches!(rows.as_slice(), [(bind, vis, ndx)]
                            if bind == "WEAK" && *vis == readelf_visibility(visibility) && ndx != "UND"),
                        "{label}: `{name}` ({linkage} {visibility}) exported: {rows:?}"
                    );
                }
                let named = dynamic_relocations_naming(&library, &leg, &bound);
                assert!(named.is_empty(), "{label}: {named:?}");

                let rpath = format!("-Wl,-rpath,{}", leg.display());
                let program = leg.join("driver");
                ok(
                    cc_with(flags)
                        .args(["-fPIE", "-pie"])
                        .arg(&driver_object)
                        .arg(&library)
                        .arg(&rpath)
                        .arg("-o")
                        .arg(&program),
                    &leg,
                );
                let plain = ok(&mut Command::new(&program), &leg);
                assert_eq!(plain, expected(false), "{label}");
                let interposer = leg.join("libinterpose.so");
                ok(
                    cc_with(flags)
                        .arg("-shared")
                        .arg(&interposer_object)
                        .arg("-o")
                        .arg(&interposer),
                    &leg,
                );
                let preloaded = ok(Command::new(&program).env("LD_PRELOAD", &interposer), &leg);
                assert_eq!(
                    preloaded,
                    expected(true),
                    "{label}: only the default definitions interpose"
                );

                for (index, (name, visibility, outsider)) in outsiders.iter().enumerate() {
                    let binary = leg.join(format!("outsider{index}"));
                    let (success, _, stderr) = run(
                        cc_with(flags)
                            .arg("-no-pie")
                            .arg(outsider)
                            .arg(&library)
                            .arg(&rpath)
                            .arg("-o")
                            .arg(&binary),
                        &leg,
                    );
                    if let Some(refusal) = outsider_refusal(linker, *visibility, name) {
                        write(&leg, &format!("{name}-outsider-link.txt"), &stderr);
                        assert!(
                            !success && stderr.contains(&refusal),
                            "{label}: a non-PIE store to {visibility} `{name}` must fail with \
                             `{refusal}`: {stderr}"
                        );
                        continue;
                    }
                    assert!(success, "{label}: `{name}`: {stderr}");
                    assert!(
                        reloc_rows(&readelf_text(&["--relocs"], &binary, &leg))
                            .iter()
                            .any(|row| {
                                row.kind == "R_AARCH64_COPY" && row.symbol.as_deref() == Some(name)
                            }),
                        "{label}: the non-PIE control must copy-relocate `{name}`"
                    );
                    assert_eq!(
                        ok(&mut Command::new(&binary), &leg),
                        "exe=77 lib=77\n",
                        "{label}: the library follows `{name}`'s copy"
                    );
                }
            }
            eprintln!(
                "weak/COMDAT hidden/protected data passed: {opt_level:?} {:?} {directory:?}",
                linker_names(&linkers)
            );
        }
    }

    /// L02-P6 closure audit 2: the definitions of [`WEAK_DATA_ROWS`] meet a
    /// g++ twin in one `pic` library, O0-O3, linked by GNU ld, gold and LLD
    /// in both input orders. The twin (`-std=c++17 -fno-gnu-unique`) defines
    /// each COMDAT name as a C++ `inline` variable with the same visibility,
    /// which g++ places in a `GRP_COMDAT` group signed by the same name, and
    /// each plain `weak` name as a strong definition; every twin value is the
    /// CG value plus `0x10000`. The linker keeps the first input's COMDAT
    /// group and the strong definition, so the CG and twin accessors read one
    /// storage cell: the first input's value for a COMDAT name and the twin's
    /// for a weak one, at one address. No hidden name reaches `.dynsym`. A
    /// relocation against a discarded CG COMDAT section, rather than the
    /// symbol, would fail the twin-first link.
    #[test]
    fn weak_and_comdat_data_coalesce_with_gcc_definitions_in_a_shared_object() {
        let linkers = linkers();
        let module = weak_data_module();
        let directory = scratch("weak-data-twin");
        let twin_value = |value: u64| value + 0x10000;
        let mut twin = String::from("#include <stdint.h>\n");
        for (name, linkage, visibility, _, value) in WEAK_DATA_ROWS {
            let inline = if linkage == "weak" { "" } else { "inline " };
            twin.push_str(&format!(
                "__attribute__((visibility(\"{visibility}\"))) {inline}uint64_t {name} = {:#x};\n\
                 extern \"C\" uint64_t twin_load_{name}(void) {{ return {name}; }}\n\
                 extern \"C\" uint64_t *twin_addr_{name}(void) {{ return &{name}; }}\n",
                twin_value(value)
            ));
        }
        let twin_object = c_object_with(
            "g++",
            &directory,
            "twin",
            &twin,
            &["-std=c++17", "-fPIC", "-O2", "-fno-gnu-unique"],
        );
        let twin_groups = comdat_groups(&fs::read(&twin_object).unwrap());
        for (name, linkage, ..) in WEAK_DATA_ROWS {
            assert_eq!(
                twin_groups
                    .iter()
                    .any(|(signature, _)| signature.as_str() == name),
                linkage != "weak",
                "the twin's `{name}` ({linkage}) group: {twin_groups:?}"
            );
        }
        let mut driver = String::from("#include <stdint.h>\n#include <stdio.h>\n");
        for (name, ..) in WEAK_DATA_ROWS {
            driver.push_str(&format!(
                "uint64_t load_{name}(void), *addr_{name}(void);\n\
                 uint64_t twin_load_{name}(void), *twin_addr_{name}(void);\n"
            ));
        }
        driver.push_str("int main(void) {\n  printf(\"cg\");\n");
        for (name, ..) in WEAK_DATA_ROWS {
            driver.push_str(&format!(
                "  printf(\" %llx\", (unsigned long long)load_{name}());\n"
            ));
        }
        driver.push_str("  printf(\"\\ntwin\");\n");
        for (name, ..) in WEAK_DATA_ROWS {
            driver.push_str(&format!(
                "  printf(\" %llx\", (unsigned long long)twin_load_{name}());\n"
            ));
        }
        driver.push_str("  printf(\"\\nsame\");\n");
        for (name, ..) in WEAK_DATA_ROWS {
            driver.push_str(&format!(
                "  printf(\" %d\", addr_{name}() == twin_addr_{name}());\n"
            ));
        }
        driver.push_str("  printf(\"\\n\");\n  return 0;\n}\n");
        let driver_object = c_object_with("cc", &directory, "driver", &driver, &["-fPIE"]);
        let expected = |cg_first: bool| {
            let values: String = WEAK_DATA_ROWS
                .iter()
                .map(|(_, linkage, _, _, value)| {
                    let kept = if *linkage != "weak" && cg_first {
                        *value
                    } else {
                        twin_value(*value)
                    };
                    format!(" {kept:x}")
                })
                .collect();
            let same = " 1".repeat(WEAK_DATA_ROWS.len());
            format!("cg{values}\ntwin{values}\nsame{same}\n")
        };
        for opt_level in OPT_LEVELS {
            let level = directory.join(format!("{opt_level:?}"));
            fs::create_dir_all(&level).unwrap();
            let object = compile_with_model(
                &module,
                opt_level,
                trust_cg_codegen::RelocationModel::Pic,
                &level,
                "weak_data.o",
            );
            for (linker, flags) in &linkers {
                for cg_first in [true, false] {
                    let order = if cg_first { "cg-first" } else { "twin-first" };
                    let label = format!("{opt_level:?} {linker} {order}");
                    let leg = level.join(format!("{linker}-{order}"));
                    fs::create_dir_all(&leg).unwrap();
                    let library = leg.join("libtcgweaktwin.so");
                    let (first, second) = if cg_first {
                        (&object, &twin_object)
                    } else {
                        (&twin_object, &object)
                    };
                    ok(
                        cc_with(flags)
                            .args(["-shared", "-Wl,-z,defs,-z,text,-z,relro,-z,now"])
                            .arg(first)
                            .arg(second)
                            .arg("-o")
                            .arg(&library),
                        &leg,
                    );
                    for (name, _, visibility, ..) in WEAK_DATA_ROWS {
                        if visibility == Visibility::Hidden {
                            let rows = readelf_rows(&library, &leg, "--dyn-syms", name);
                            assert!(rows.is_empty(), "{label}: `{name}` in .dynsym: {rows:?}");
                        }
                    }
                    let program = leg.join("driver");
                    ok(
                        cc_with(flags)
                            .args(["-fPIE", "-pie"])
                            .arg(&driver_object)
                            .arg(&library)
                            .arg(format!("-Wl,-rpath,{}", leg.display()))
                            .arg("-o")
                            .arg(&program),
                        &leg,
                    );
                    assert_eq!(
                        ok(&mut Command::new(&program), &leg),
                        expected(cg_first),
                        "{label}"
                    );
                }
            }
            eprintln!(
                "weak/COMDAT data g++ coalescing passed: {opt_level:?} {:?} {directory:?}",
                linker_names(&linkers)
            );
        }
    }

    /// L02-P6 closure audit 2: the objects of
    /// [`pipeline_hidden_tls_descriptor_references_name_an_object_local_anchor`]'s
    /// layout-less route (`Pipeline::compile_module_with_globals`, `pic`,
    /// O0-O3) in a shared library linked by GNU ld, gold and LLD. No linker
    /// lists an anchored hidden thread-local (`pt_hidden`, `pt_bss_hidden`)
    /// in `.dynsym`, gold included, or names one in a dynamic relocation; the
    /// weak hidden one, which the object names by its symbol, may appear in
    /// gold's `.dynsym` only as `TLS LOCAL HIDDEN`; the default and protected
    /// ones are exported. A PIE driver reads every variable in the main
    /// thread and a second thread, which sees the initial values and then
    /// its own stores; an `LD_PRELOAD` interposer defining every name takes
    /// over only the default ones. At the audited base, dropping the
    /// layout-less emitter's anchor listed `LOCAL HIDDEN pt_hidden` in gold's
    /// `.dynsym` and passed every suite.
    #[test]
    fn pipeline_hidden_thread_locals_stay_out_of_every_linkers_dynsym() {
        let linkers = linkers();
        let directory = scratch("pipeline-tls");
        let names: Vec<&str> = PIPELINE_TLS_ROWS.iter().map(|(name, ..)| *name).collect();
        let anchored: Vec<&str> = PIPELINE_TLS_ANCHORED
            .iter()
            .map(|(name, _)| *name)
            .collect();
        let mut driver =
            String::from("#include <pthread.h>\n#include <stdint.h>\n#include <stdio.h>\n");
        for name in &names {
            driver.push_str(&format!("uint64_t *addr_{name}(void);\n"));
        }
        driver.push_str("static void print(const char *who) {\n  printf(\"%s\", who);\n");
        for name in &names {
            driver.push_str(&format!(
                "  printf(\" %llu\", (unsigned long long)*addr_{name}());\n"
            ));
        }
        driver.push_str("  printf(\"\\n\");\n}\nstatic void *worker(void *unused) {\n");
        driver.push_str("  (void)unused;\n  print(\"thread\");\n");
        for name in &names {
            driver.push_str(&format!("  *addr_{name}() += 100;\n"));
        }
        driver.push_str(
            "  print(\"thread\");\n  return 0;\n}\n\
             int main(void) {\n  pthread_t thread;\n  print(\"main\");\n\
               pthread_create(&thread, 0, worker, 0);\n  pthread_join(thread, 0);\n\
               print(\"main\");\n  return 0;\n}\n",
        );
        let interposed = |index: usize| 900 + index as u64;
        let mut interposer = String::from("#include <stdint.h>\n");
        for (index, name) in names.iter().enumerate() {
            interposer.push_str(&format!(
                "__thread uint64_t {name} = {};\n",
                interposed(index)
            ));
        }
        let expected = |preloaded: bool| {
            let initial: Vec<u64> = PIPELINE_TLS_ROWS
                .iter()
                .enumerate()
                .map(|(index, (_, visibility, _, value))| {
                    if preloaded && *visibility == Visibility::Default {
                        interposed(index)
                    } else {
                        *value
                    }
                })
                .collect();
            let row = |who: &str, add: u64| {
                let values: String = initial
                    .iter()
                    .map(|value| format!(" {}", value + add))
                    .collect();
                format!("{who}{values}\n")
            };
            [
                row("main", 0),
                row("thread", 0),
                row("thread", 100),
                row("main", 0),
            ]
            .concat()
        };
        let driver_object = c_object_with("cc", &directory, "driver", &driver, &["-fPIE"]);
        let interposer_object =
            c_object_with("cc", &directory, "interposer", &interposer, &["-fPIC"]);
        for opt_level in OPT_LEVELS {
            let level = directory.join(format!("{opt_level:?}"));
            fs::create_dir_all(&level).unwrap();
            let (pipeline, (functions, _), globals) = pipeline_tls_input(opt_level);
            let object = write(
                &level,
                "pipeline_tls.o",
                pipeline
                    .compile_module_with_globals(&functions, &globals)
                    .unwrap_or_else(|error| panic!("{opt_level:?}: {error}")),
            );
            let object_relocs = reloc_rows(&readelf_text(&["--relocs"], &object, &level));
            for name in &anchored {
                assert!(
                    object_relocs
                        .iter()
                        .all(|row| row.symbol.as_deref() != Some(name)),
                    "{opt_level:?}: `{name}` is relocated through its anchor"
                );
            }
            for (linker, flags) in &linkers {
                let label = format!("{opt_level:?} {linker}");
                let leg = level.join(linker);
                fs::create_dir_all(&leg).unwrap();
                let library = leg.join("libtcgpipelinetls.so");
                ok(
                    cc_with(flags)
                        .args(["-shared", "-Wl,-z,defs,-z,text,-z,relro,-z,now"])
                        .arg(&object)
                        .arg("-o")
                        .arg(&library),
                    &leg,
                );
                write(
                    &leg,
                    "dynsym.txt",
                    readelf_text(&["--dyn-syms"], &library, &leg),
                );
                for (name, visibility, ..) in PIPELINE_TLS_ROWS {
                    let rows = readelf_rows(&library, &leg, "--dyn-syms", name);
                    if anchored.contains(&name) {
                        assert!(rows.is_empty(), "{label}: `{name}` in .dynsym: {rows:?}");
                    } else if visibility == Visibility::Hidden {
                        assert!(
                            rows.iter()
                                .all(|(bind, vis, _)| bind == "LOCAL" && vis == "HIDDEN")
                                && (*linker == "gold" || rows.is_empty()),
                            "{label}: `{name}` in .dynsym: {rows:?}"
                        );
                    } else {
                        assert!(
                            matches!(rows.as_slice(), [(bind, vis, ndx)]
                                if bind == "GLOBAL" && *vis == readelf_visibility(visibility)
                                    && ndx != "UND"),
                            "{label}: `{name}` exported: {rows:?}"
                        );
                    }
                }
                let named = dynamic_relocations_naming(&library, &leg, &anchored);
                assert!(named.is_empty(), "{label}: {named:?}");
                let program = leg.join("driver");
                ok(
                    cc_with(flags)
                        .args(["-fPIE", "-pie"])
                        .arg(&driver_object)
                        .arg(&library)
                        .arg("-pthread")
                        .arg(format!("-Wl,-rpath,{}", leg.display()))
                        .arg("-o")
                        .arg(&program),
                    &leg,
                );
                assert_eq!(
                    ok(&mut Command::new(&program), &leg),
                    expected(false),
                    "{label}"
                );
                let interposer = leg.join("libinterpose.so");
                ok(
                    cc_with(flags)
                        .arg("-shared")
                        .arg(&interposer_object)
                        .arg("-o")
                        .arg(&interposer),
                    &leg,
                );
                assert_eq!(
                    ok(Command::new(&program).env("LD_PRELOAD", &interposer), &leg),
                    expected(true),
                    "{label}: only the default thread-locals interpose"
                );
            }
            eprintln!(
                "Pipeline-route hidden TLS anchors passed: {opt_level:?} {:?} {directory:?}",
                linker_names(&linkers)
            );
        }
    }

    /// L02-P6 closure audit 2, verifier round: the weak and COMDAT
    /// thread-local definitions of [`WEAK_TLS_ROWS`] (plain `weak` in
    /// `.tdata`, `.tbss` and an explicit section; `linkonce`, `linkonce_odr`
    /// and `weak_odr` in their own COMDAT groups; each default, hidden and
    /// protected) in a `pic` library built through `Compiler::compile`,
    /// O0-O3, linked by GNU ld, gold and LLD.
    ///
    /// * The object spells every definition `WEAK` `TLS` with its own
    ///   visibility.
    /// * The library exports the default and protected ones `WEAK` with their
    ///   visibility. No hidden one is exported: GNU ld and LLD list none in
    ///   `.dynsym` and name none in a dynamic relocation; gold may list one
    ///   only as `LOCAL HIDDEN` (the object names it by its symbol).
    /// * A PIE driver declares every exported name `extern __thread` and
    ///   reads each variable through the library's accessors and, for the
    ///   exported ones, directly, in the main thread and a second thread
    ///   that then adds 100 to each through the library's address: the
    ///   executable and the library share each exported variable's cell,
    ///   and each thread has its own.
    /// * An `LD_PRELOAD` interposer defining every name takes over the
    ///   library's default variables and the executable's references to the
    ///   default and protected ones, never the library's own protected and
    ///   hidden ones (the near-twin negative).
    /// * A PIE that names a hidden one does not link, with each linker's own
    ///   undefined-symbol diagnostic.
    ///
    /// The verifier found that spelling a COMDAT thread-local `STV_DEFAULT`
    /// exported every hidden COMDAT name `WEAK DEFAULT` with every linker
    /// and let `LD_PRELOAD` interpose it, and that spelling a weak protected
    /// thread-local `STV_HIDDEN` dropped it from `.dynsym`, so a PIE naming
    /// it no longer linked; both passed every suite. Execution evidence for
    /// these linkers and the glibc loader on this host, not a linker or
    /// loader proof.
    #[test]
    fn weak_and_comdat_hidden_and_protected_thread_locals_bind_inside_a_shared_object() {
        let linkers = linkers();
        let module = weak_tls_module();
        let directory = scratch("weak-tls");
        let exported: Vec<&str> = WEAK_TLS_ROWS
            .iter()
            .filter(|(.., visibility, _, _)| *visibility != Visibility::Hidden)
            .map(|(name, ..)| *name)
            .collect();
        let hidden: Vec<&str> = WEAK_TLS_ROWS
            .iter()
            .filter(|(.., visibility, _, _)| *visibility == Visibility::Hidden)
            .map(|(name, ..)| *name)
            .collect();
        let mut driver =
            String::from("#include <pthread.h>\n#include <stdint.h>\n#include <stdio.h>\n");
        for (name, ..) in WEAK_TLS_ROWS {
            driver.push_str(&format!(
                "uint64_t load_{name}(void), *addr_{name}(void);\n"
            ));
        }
        for name in &exported {
            driver.push_str(&format!("extern __thread uint64_t {name};\n"));
        }
        driver.push_str("static void report(const char *who) {\n  printf(\"%s lib\", who);\n");
        for (name, ..) in WEAK_TLS_ROWS {
            driver.push_str(&format!(
                "  printf(\" %llu\", (unsigned long long)load_{name}());\n"
            ));
        }
        driver.push_str("  printf(\" exe\");\n");
        for name in &exported {
            driver.push_str(&format!(
                "  printf(\" %llu\", (unsigned long long){name});\n"
            ));
        }
        driver.push_str("  printf(\" same\");\n");
        for name in &exported {
            driver.push_str(&format!("  printf(\" %d\", addr_{name}() == &{name});\n"));
        }
        driver.push_str("  printf(\"\\n\");\n}\nstatic void *worker(void *unused) {\n");
        driver.push_str("  (void)unused;\n  report(\"thread\");\n");
        for (name, ..) in WEAK_TLS_ROWS {
            driver.push_str(&format!("  *addr_{name}() += 100;\n"));
        }
        driver.push_str(
            "  report(\"thread\");\n  return 0;\n}\n\
             int main(void) {\n  pthread_t thread;\n  report(\"main\");\n\
               pthread_create(&thread, 0, worker, 0);\n  pthread_join(thread, 0);\n\
               report(\"main\");\n  return 0;\n}\n",
        );
        let interposed = |index: usize| 900 + index as u64;
        let mut interposer = String::from("#include <stdint.h>\n");
        for (index, (name, ..)) in WEAK_TLS_ROWS.iter().enumerate() {
            interposer.push_str(&format!(
                "__thread uint64_t {name} = {};\n",
                interposed(index)
            ));
        }
        // Each thread's view: the library's value of every variable, the
        // executable's value of every exported one, and whether the two
        // share a cell; `added` after the worker's `+= 100` through the
        // library's address.
        let expected = |preloaded: bool| {
            let row = |who: &str, added: bool| {
                let mut lib = String::new();
                let mut exe = String::new();
                let mut same = String::new();
                for (index, (_, _, visibility, _, value)) in WEAK_TLS_ROWS.iter().enumerate() {
                    let interposes = preloaded && *visibility == Visibility::Default;
                    let library_value = if interposes {
                        interposed(index)
                    } else {
                        *value
                    };
                    let bump = if added { 100 } else { 0 };
                    lib.push_str(&format!(" {}", library_value + bump));
                    if *visibility == Visibility::Hidden {
                        continue;
                    }
                    // With the interposer loaded the executable's reference
                    // binds to it; the library's own protected accesses do
                    // not follow.
                    let shared = !(preloaded && *visibility == Visibility::Protected);
                    let executable_value = if preloaded { interposed(index) } else { *value };
                    exe.push_str(&format!(
                        " {}",
                        executable_value + if shared { bump } else { 0 }
                    ));
                    same.push_str(if shared { " 1" } else { " 0" });
                }
                format!("{who} lib{lib} exe{exe} same{same}\n")
            };
            [
                row("main", false),
                row("thread", false),
                row("thread", true),
                row("main", false),
            ]
            .concat()
        };
        let driver_object = c_object_with("cc", &directory, "driver", &driver, &["-fPIE"]);
        let interposer_object =
            c_object_with("cc", &directory, "interposer", &interposer, &["-fPIC"]);
        // Named by index, so no path in a diagnostic spells the variable.
        let outsiders: Vec<(&str, PathBuf)> = hidden
            .iter()
            .enumerate()
            .map(|(index, name)| {
                let source = format!(
                    "#include <stdint.h>\nextern __thread uint64_t {name};\n\
                     int main(void) {{ return {name} != 0; }}\n"
                );
                let object = c_object_with(
                    "cc",
                    &directory,
                    &format!("tls_outsider{index}"),
                    &source,
                    &["-fPIE"],
                );
                (*name, object)
            })
            .collect();
        for opt_level in OPT_LEVELS {
            let level = directory.join(format!("{opt_level:?}"));
            fs::create_dir_all(&level).unwrap();
            let object = compile_with_model(
                &module,
                opt_level,
                trust_cg_codegen::RelocationModel::Pic,
                &level,
                "weak_tls.o",
            );
            let object_symbols = readelf_text(&["--syms"], &object, &level);
            for (name, linkage, visibility, ..) in WEAK_TLS_ROWS {
                let rows: Vec<Vec<&str>> = object_symbols
                    .lines()
                    .map(|line| line.split_whitespace().collect::<Vec<&str>>())
                    .filter(|columns| columns.len() >= 8 && columns[7] == name)
                    .collect();
                assert!(
                    matches!(rows.as_slice(), [columns]
                        if columns[3] == "TLS" && columns[4] == "WEAK"
                            && columns[5] == readelf_visibility(visibility)
                            && columns[6] != "UND"),
                    "{opt_level:?}: `{name}` ({linkage} {visibility}) in the object: {rows:?}"
                );
            }
            for (linker, flags) in &linkers {
                let label = format!("{opt_level:?} {linker}");
                let leg = level.join(linker);
                fs::create_dir_all(&leg).unwrap();
                let library = leg.join("libtcgweaktls.so");
                ok(
                    cc_with(flags)
                        .args(["-shared", "-Wl,-z,defs,-z,text,-z,relro,-z,now"])
                        .arg(&object)
                        .arg("-o")
                        .arg(&library),
                    &leg,
                );
                write(
                    &leg,
                    "dynsym.txt",
                    readelf_text(&["--dyn-syms"], &library, &leg),
                );
                for (name, linkage, visibility, ..) in WEAK_TLS_ROWS {
                    let rows = readelf_rows(&library, &leg, "--dyn-syms", name);
                    if visibility == Visibility::Hidden {
                        assert!(
                            rows.iter()
                                .all(|(bind, vis, _)| bind == "LOCAL" && vis == "HIDDEN")
                                && (*linker == "gold" || rows.is_empty()),
                            "{label}: hidden `{name}` ({linkage}) in .dynsym: {rows:?}"
                        );
                        continue;
                    }
                    assert!(
                        matches!(rows.as_slice(), [(bind, vis, ndx)]
                            if bind == "WEAK" && *vis == readelf_visibility(visibility)
                                && ndx != "UND"),
                        "{label}: `{name}` ({linkage} {visibility}) exported: {rows:?}"
                    );
                }
                if *linker != "gold" {
                    let named = dynamic_relocations_naming(&library, &leg, &hidden);
                    assert!(named.is_empty(), "{label}: {named:?}");
                }
                let program = leg.join("driver");
                ok(
                    cc_with(flags)
                        .args(["-fPIE", "-pie"])
                        .arg(&driver_object)
                        .arg(&library)
                        .arg("-pthread")
                        .arg(format!("-Wl,-rpath,{}", leg.display()))
                        .arg("-o")
                        .arg(&program),
                    &leg,
                );
                assert_eq!(
                    ok(&mut Command::new(&program), &leg),
                    expected(false),
                    "{label}"
                );
                let interposer = leg.join("libinterpose.so");
                ok(
                    cc_with(flags)
                        .arg("-shared")
                        .arg(&interposer_object)
                        .arg("-o")
                        .arg(&interposer),
                    &leg,
                );
                assert_eq!(
                    ok(Command::new(&program).env("LD_PRELOAD", &interposer), &leg),
                    expected(true),
                    "{label}: only the default variables interpose in the library"
                );
                for (index, (name, outsider)) in outsiders.iter().enumerate() {
                    let (success, _, stderr) = run(
                        cc_with(flags)
                            .args(["-fPIE", "-pie"])
                            .arg(outsider)
                            .arg(&library)
                            .arg(format!("-Wl,-rpath,{}", leg.display()))
                            .arg("-o")
                            .arg(leg.join(format!("tls_outsider{index}"))),
                        &leg,
                    );
                    let refusal = outsider_refusal(linker, Visibility::Hidden, name)
                        .expect("a hidden name is refused");
                    write(&leg, &format!("{name}-outsider-link.txt"), &stderr);
                    assert!(
                        !success && stderr.contains(&refusal),
                        "{label}: a PIE naming hidden `{name}` must fail with `{refusal}`: \
                         {stderr}"
                    );
                }
            }
            eprintln!(
                "weak/COMDAT hidden/protected thread-locals passed: {opt_level:?} {:?} \
                 {directory:?}",
                linker_names(&linkers)
            );
        }
    }

    /// L02-P6 closure audit 2, verifier round: the thread-locals of
    /// [`WEAK_TLS_ROWS`] meet a g++ twin in one `pic` library, O0-O3, linked
    /// by GNU ld, gold and LLD in both input orders. The twin
    /// (`-std=c++17 -fPIC -O2 -fno-gnu-unique`) defines each COMDAT name as a
    /// C++ `inline thread_local` variable with the same visibility, in a
    /// `GRP_COMDAT` group of the same signature (the row checks the twin's
    /// groups), and each plain `weak` name as a strong `thread_local`, every
    /// value the CG value plus 1000. In the main thread and a second one the
    /// CG and twin accessors read one cell at one address: the first input's
    /// value for a COMDAT name and the twin's strong value for a weak one, and
    /// a store through the CG address in the second thread is what the twin
    /// reads back there. No hidden name is exported.
    #[test]
    fn weak_and_comdat_thread_locals_coalesce_with_gcc_definitions_in_a_shared_object() {
        let linkers = linkers();
        let module = weak_tls_module();
        let directory = scratch("weak-tls-twin");
        let twin_value = |value: u64| value + 1000;
        let mut twin = String::from("#include <cstdint>\n");
        for (name, linkage, visibility, _, value) in WEAK_TLS_ROWS {
            let inline = if linkage == "weak" { "" } else { "inline " };
            twin.push_str(&format!(
                "__attribute__((visibility(\"{visibility}\"))) {inline}thread_local uint64_t \
                 {name} = {};\n\
                 extern \"C\" uint64_t twin_load_{name}(void) {{ return {name}; }}\n\
                 extern \"C\" uint64_t *twin_addr_{name}(void) {{ return &{name}; }}\n",
                twin_value(value)
            ));
        }
        let twin_object = c_object_with(
            "g++",
            &directory,
            "twin",
            &twin,
            &["-std=c++17", "-fPIC", "-O2", "-fno-gnu-unique"],
        );
        let twin_groups = comdat_groups(&fs::read(&twin_object).unwrap());
        for (name, linkage, ..) in WEAK_TLS_ROWS {
            assert_eq!(
                twin_groups
                    .iter()
                    .any(|(signature, _)| signature.as_str() == name),
                linkage != "weak",
                "the twin's `{name}` ({linkage}) group: {twin_groups:?}"
            );
        }
        let mut driver =
            String::from("#include <pthread.h>\n#include <stdint.h>\n#include <stdio.h>\n");
        for (name, ..) in WEAK_TLS_ROWS {
            driver.push_str(&format!(
                "uint64_t load_{name}(void), *addr_{name}(void);\n\
                 uint64_t twin_load_{name}(void), *twin_addr_{name}(void);\n"
            ));
        }
        driver.push_str("static void report(const char *who) {\n  printf(\"%s cg\", who);\n");
        for (name, ..) in WEAK_TLS_ROWS {
            driver.push_str(&format!(
                "  printf(\" %llu\", (unsigned long long)load_{name}());\n"
            ));
        }
        driver.push_str("  printf(\" twin\");\n");
        for (name, ..) in WEAK_TLS_ROWS {
            driver.push_str(&format!(
                "  printf(\" %llu\", (unsigned long long)twin_load_{name}());\n"
            ));
        }
        driver.push_str("  printf(\" same\");\n");
        for (name, ..) in WEAK_TLS_ROWS {
            driver.push_str(&format!(
                "  printf(\" %d\", addr_{name}() == twin_addr_{name}());\n"
            ));
        }
        driver.push_str("  printf(\"\\n\");\n}\nstatic void *worker(void *unused) {\n");
        driver.push_str("  (void)unused;\n  report(\"thread\");\n");
        for (index, (name, ..)) in WEAK_TLS_ROWS.iter().enumerate() {
            driver.push_str(&format!("  *addr_{name}() = {};\n", 5000 + index));
        }
        driver.push_str(
            "  report(\"thread\");\n  return 0;\n}\n\
             int main(void) {\n  pthread_t thread;\n  report(\"main\");\n\
               pthread_create(&thread, 0, worker, 0);\n  pthread_join(thread, 0);\n\
               report(\"main\");\n  return 0;\n}\n",
        );
        let driver_object = c_object_with("cc", &directory, "driver", &driver, &["-fPIE"]);
        let expected = |cg_first: bool| {
            let row = |who: &str, stored: bool| {
                let values: String = WEAK_TLS_ROWS
                    .iter()
                    .enumerate()
                    .map(|(index, (_, linkage, _, _, value))| {
                        let kept = if stored {
                            5000 + index as u64
                        } else if *linkage != "weak" && cg_first {
                            *value
                        } else {
                            twin_value(*value)
                        };
                        format!(" {kept}")
                    })
                    .collect();
                let same = " 1".repeat(WEAK_TLS_ROWS.len());
                format!("{who} cg{values} twin{values} same{same}\n")
            };
            [
                row("main", false),
                row("thread", false),
                row("thread", true),
                row("main", false),
            ]
            .concat()
        };
        for opt_level in OPT_LEVELS {
            let level = directory.join(format!("{opt_level:?}"));
            fs::create_dir_all(&level).unwrap();
            let object = compile_with_model(
                &module,
                opt_level,
                trust_cg_codegen::RelocationModel::Pic,
                &level,
                "weak_tls.o",
            );
            for (linker, flags) in &linkers {
                for cg_first in [true, false] {
                    let order = if cg_first { "cg-first" } else { "twin-first" };
                    let label = format!("{opt_level:?} {linker} {order}");
                    let leg = level.join(format!("{linker}-{order}"));
                    fs::create_dir_all(&leg).unwrap();
                    let library = leg.join("libtcgweaktlstwin.so");
                    let (first, second) = if cg_first {
                        (&object, &twin_object)
                    } else {
                        (&twin_object, &object)
                    };
                    ok(
                        cc_with(flags)
                            .args(["-shared", "-Wl,-z,defs,-z,text,-z,relro,-z,now"])
                            .arg(first)
                            .arg(second)
                            .arg("-o")
                            .arg(&library),
                        &leg,
                    );
                    for (name, _, visibility, ..) in WEAK_TLS_ROWS {
                        if visibility == Visibility::Hidden {
                            let rows = readelf_rows(&library, &leg, "--dyn-syms", name);
                            assert!(
                                rows.iter().all(|(bind, _, _)| bind == "LOCAL"),
                                "{label}: `{name}` exported: {rows:?}"
                            );
                        }
                    }
                    let program = leg.join("driver");
                    ok(
                        cc_with(flags)
                            .args(["-fPIE", "-pie"])
                            .arg(&driver_object)
                            .arg(&library)
                            .arg("-pthread")
                            .arg(format!("-Wl,-rpath,{}", leg.display()))
                            .arg("-o")
                            .arg(&program),
                        &leg,
                    );
                    assert_eq!(
                        ok(&mut Command::new(&program), &leg),
                        expected(cg_first),
                        "{label}"
                    );
                }
            }
            eprintln!(
                "weak/COMDAT thread-local g++ coalescing passed: {opt_level:?} {:?} {directory:?}",
                linker_names(&linkers)
            );
        }
    }

    // -------------------------------------------------------------------------
    // L02-P6 closure audit 3: strong hidden and protected data definitions in
    // every implicit section, at link time
    // -------------------------------------------------------------------------

    /// The C prototypes of [`strong_data_module`]'s accessors for `name`.
    fn strong_data_prototypes(name: &str, section: &str, pointer: bool) -> String {
        let mut prototypes = if pointer {
            format!("uint64_t *load_{name}(void), **addr_{name}(void);\n")
        } else {
            format!("uint64_t load_{name}(void), *addr_{name}(void);\n")
        };
        if strong_data_is_mutable(section) {
            prototypes.push_str(&format!("void store_{name}(uint64_t);\n"));
        }
        prototypes
    }

    /// L02-P6 closure audit 3: the strong (`External`) definitions of
    /// [`STRONG_DATA_ROWS`] (hidden, protected and default in `.data`,
    /// `.bss`, `.rodata` and `.data.rel.ro`) in a `pic` library built through
    /// `Compiler::compile`, O0-O3, linked by GNU ld, gold and LLD with
    /// `-z defs,-z text`.
    ///
    /// * The object spells every definition `GLOBAL` with its own
    ///   visibility.
    /// * The library lists no hidden definition in `.dynsym` (its `.symtab`
    ///   keeps each one `LOCAL`), exports the default and protected
    ///   ones `GLOBAL` with their visibility, names no hidden or protected
    ///   one in a dynamic relocation, holds none of their addresses in a GOT
    ///   slot, and gives each default one a `GLOB_DAT` GOT slot.
    /// * A PIE driver reads every definition through `load_<name>` and
    ///   `addr_<name>` (a pointer row through its target), stores through
    ///   `store_<name>` to every mutable one and reads it back, then reads
    ///   each mutable name's global-scope definition with `dlsym`. An
    ///   `LD_PRELOAD` interposer defining every name takes over only the
    ///   default definitions: the library's stores to its hidden and
    ///   protected definitions leave the interposer's copies untouched.
    /// * A non-PIE outsider that references a hidden definition does not
    ///   link, and one that references a protected definition is refused the
    ///   copy relocation, in every section. One that references a default
    ///   definition copy-relocates it and the library follows the copy (a
    ///   mutable one: `exe=77 lib=77`).
    ///
    /// At the audited base, spelling the strong `.bss`, `.rodata` or
    /// `.data.rel.ro` hidden or protected definitions `STV_DEFAULT` passed
    /// every floor suite: GNU ld and LLD then refused the library and gold
    /// linked it exporting them `DEFAULT`. Execution evidence for these
    /// linkers and the glibc loader on this host, not a linker or loader
    /// proof.
    #[test]
    fn strong_hidden_and_protected_data_bind_inside_a_shared_object_in_every_implicit_section() {
        let linkers = linkers();
        let module = strong_data_module();
        let directory = scratch("strong-data");
        let stored = |index: usize| 0x5000 + index as u64;
        let interposed = |index: usize| 0x9000 + index as u64;
        let mutable: Vec<(usize, &str, Visibility)> = STRONG_DATA_ROWS
            .iter()
            .enumerate()
            .filter(|(_, (_, section, ..))| strong_data_is_mutable(section))
            .map(|(index, (name, _, visibility, ..))| (index, *name, *visibility))
            .collect();
        let mut driver = String::from(
            "#define _GNU_SOURCE\n#include <dlfcn.h>\n#include <stdint.h>\n#include <stdio.h>\n",
        );
        for (name, section, _, _, target) in STRONG_DATA_ROWS {
            driver.push_str(&strong_data_prototypes(name, section, target.is_some()));
        }
        driver.push_str("int main(void) {\n  printf(\"load\");\n");
        for (name, _, _, _, target) in STRONG_DATA_ROWS {
            let star = if target.is_some() { "*" } else { "" };
            driver.push_str(&format!(
                "  printf(\" %llx\", (unsigned long long){star}load_{name}());\n"
            ));
        }
        driver.push_str("  printf(\"\\nderef\");\n");
        for (name, _, _, _, target) in STRONG_DATA_ROWS {
            let star = if target.is_some() { "**" } else { "*" };
            driver.push_str(&format!(
                "  printf(\" %llx\", (unsigned long long){star}addr_{name}());\n"
            ));
        }
        driver.push_str("  printf(\"\\nstored\");\n");
        for (index, name, _) in &mutable {
            driver.push_str(&format!(
                "  store_{name}({:#x});\n  printf(\" %llx/%llx\", (unsigned long long)load_{name}(),\n\
                 \x20   (unsigned long long)*addr_{name}());\n",
                stored(*index)
            ));
        }
        driver.push_str("  printf(\"\\nglobal\");\n");
        for (_, name, _) in &mutable {
            driver.push_str(&format!(
                "  {{\n    uint64_t *p = dlsym(RTLD_DEFAULT, \"{name}\");\n\
                 \x20   if (p) printf(\" %llx\", (unsigned long long)*p); else printf(\" -\");\n  }}\n"
            ));
        }
        driver.push_str("  printf(\"\\n\");\n  return 0;\n}\n");
        let mut interposer = String::from("#include <stdint.h>\n");
        for (index, (name, _, _, _, target)) in STRONG_DATA_ROWS.iter().enumerate() {
            let value = interposed(index);
            if target.is_some() {
                interposer.push_str(&format!(
                    "static uint64_t cell_{name} = {value:#x};\nuint64_t *{name} = &cell_{name};\n"
                ));
            } else {
                interposer.push_str(&format!("uint64_t {name} = {value:#x};\n"));
            }
        }
        let expected = |preloaded: bool| {
            let read: String = STRONG_DATA_ROWS
                .iter()
                .enumerate()
                .map(|(index, (_, _, visibility, value, _))| {
                    let value = if preloaded && *visibility == Visibility::Default {
                        interposed(index)
                    } else {
                        *value
                    };
                    format!(" {value:x}")
                })
                .collect();
            let written: String = mutable
                .iter()
                .map(|(index, ..)| format!(" {0:x}/{0:x}", stored(*index)))
                .collect();
            let global: String = mutable
                .iter()
                .map(|(index, _, visibility)| match (preloaded, visibility) {
                    // Without the interposer nothing exports a hidden name.
                    (false, Visibility::Hidden) => " -".to_string(),
                    (false, _) | (true, Visibility::Default) => format!(" {:x}", stored(*index)),
                    // The library's stores never reached the interposer's
                    // hidden and protected copies.
                    (true, _) => format!(" {:x}", interposed(*index)),
                })
                .collect();
            format!("load{read}\nderef{read}\nstored{written}\nglobal{global}\n")
        };
        let driver_object = c_object_with("cc", &directory, "driver", &driver, &["-fPIE"]);
        let interposer_object =
            c_object_with("cc", &directory, "interposer", &interposer, &["-fPIC"]);
        let outsiders: Vec<(&str, Visibility, u64, bool, PathBuf)> = STRONG_DATA_ROWS
            .iter()
            .enumerate()
            .map(|(index, &(name, section, visibility, value, target))| {
                let mutable = strong_data_is_mutable(section);
                let (declaration, read) = match (target.is_some(), mutable) {
                    (true, _) => (
                        format!("extern uint64_t *const {name};"),
                        format!("*{name}, (unsigned long long)*load_{name}()"),
                    ),
                    (false, true) => (
                        format!("extern uint64_t {name};"),
                        format!("{name}, (unsigned long long)load_{name}()"),
                    ),
                    (false, false) => (
                        format!("extern const uint64_t {name};"),
                        format!("{name}, (unsigned long long)load_{name}()"),
                    ),
                };
                let store = if mutable {
                    format!("  {name} = 0x77;\n")
                } else {
                    String::new()
                };
                let source = format!(
                    "#include <stdint.h>\n#include <stdio.h>\n{declaration}\n{}\
                     int main(void) {{\n{store}  printf(\"exe=%llx lib=%llx\\n\", \
                     (unsigned long long){read});\n  return 0;\n}}\n",
                    strong_data_prototypes(name, section, target.is_some())
                );
                // Named by index, so no path in a diagnostic spells `name`.
                let object = c_object_with(
                    "cc",
                    &directory,
                    &format!("outsider{index}"),
                    &source,
                    &["-fno-PIE"],
                );
                let seen = if mutable { 0x77 } else { value };
                (name, visibility, seen, mutable, object)
            })
            .collect();
        let bound: Vec<&str> = STRONG_DATA_ROWS
            .iter()
            .filter(|(_, _, visibility, ..)| *visibility != Visibility::Default)
            .map(|(name, ..)| *name)
            .collect();
        for opt_level in OPT_LEVELS {
            let level = directory.join(format!("{opt_level:?}"));
            fs::create_dir_all(&level).unwrap();
            let object = compile_with_model(
                &module,
                opt_level,
                trust_cg_codegen::RelocationModel::Pic,
                &level,
                "strong_data.o",
            );
            for (name, section, visibility, ..) in STRONG_DATA_ROWS {
                let rows = readelf_rows(&object, &level, "--symbols", name);
                assert!(
                    matches!(rows.as_slice(), [(bind, vis, ndx)]
                        if bind == "GLOBAL" && *vis == readelf_visibility(visibility) && ndx != "UND"),
                    "{opt_level:?}: `{name}` ({section} {visibility}) in the object: {rows:?}"
                );
            }
            for (linker, flags) in &linkers {
                let label = format!("{opt_level:?} {linker}");
                let leg = level.join(linker);
                fs::create_dir_all(&leg).unwrap();
                let library = leg.join("libtcgstrongdata.so");
                ok(
                    cc_with(flags)
                        .args(["-shared", "-Wl,-z,defs,-z,text,-z,relro,-z,now"])
                        .arg(&object)
                        .arg("-o")
                        .arg(&library),
                    &leg,
                );
                write(
                    &leg,
                    "dynsym.txt",
                    readelf_text(&["--dyn-syms"], &library, &leg),
                );
                let symbols = readelf_text(&["--syms"], &library, &leg);
                write(&leg, "symbols.txt", &symbols);
                for (name, section, visibility, ..) in STRONG_DATA_ROWS {
                    let rows = readelf_rows(&library, &leg, "--dyn-syms", name);
                    if visibility == Visibility::Hidden {
                        assert!(
                            rows.is_empty(),
                            "{label}: hidden `{name}` ({section}) in .dynsym: {rows:?}"
                        );
                        let rows = readelf_rows(&library, &leg, "--syms", name);
                        assert!(
                            matches!(rows.as_slice(), [(bind, _, ndx)]
                                if bind == "LOCAL" && ndx != "UND"),
                            "{label}: hidden `{name}` ({section}) in .symtab: {rows:?}"
                        );
                        continue;
                    }
                    assert!(
                        matches!(rows.as_slice(), [(bind, vis, ndx)]
                            if bind == "GLOBAL" && *vis == readelf_visibility(visibility) && ndx != "UND"),
                        "{label}: `{name}` ({section} {visibility}) exported: {rows:?}"
                    );
                }
                let relocations = readelf_text(&["--relocs"], &library, &leg);
                write(&leg, "library-relocs.txt", &relocations);
                let named = dynamic_relocations_naming(&library, &leg, &bound);
                assert!(named.is_empty(), "{label}: {named:?}");
                let dynamic_rows = reloc_rows(&relocations);
                let sections = readelf_text(&["--section-headers"], &library, &leg);
                let gots = section_ranges(&sections, &[".got", ".got.plt"]);
                assert!(!gots.is_empty(), "{label}: {gots:?}");
                let in_got = |offset: u64| {
                    gots.iter()
                        .any(|(_, start, end)| (*start..*end).contains(&offset))
                };
                for (name, _, visibility, ..) in STRONG_DATA_ROWS {
                    if visibility == Visibility::Default {
                        assert!(
                            dynamic_rows
                                .iter()
                                .any(|row| row.kind == "R_AARCH64_GLOB_DAT"
                                    && row.symbol.as_deref() == Some(name)
                                    && in_got(row.offset)),
                            "{label}: default `{name}` needs a GLOB_DAT GOT slot\n{relocations}"
                        );
                        continue;
                    }
                    let value = symbol_value(&symbols, name)
                        .unwrap_or_else(|| panic!("{label}: `{name}` in .symtab"));
                    let slots: Vec<&RelocRow> = dynamic_rows
                        .iter()
                        .filter(|row| {
                            row.kind == "R_AARCH64_RELATIVE"
                                && in_got(row.offset)
                                && row.addend == value
                        })
                        .collect();
                    assert!(
                        slots.is_empty(),
                        "{label}: a GOT slot holds `{name}` ({value:#x}): {slots:?}"
                    );
                }

                let rpath = format!("-Wl,-rpath,{}", leg.display());
                let program = leg.join("driver");
                ok(
                    cc_with(flags)
                        .args(["-fPIE", "-pie"])
                        .arg(&driver_object)
                        .arg(&library)
                        .arg(&rpath)
                        .arg("-o")
                        .arg(&program),
                    &leg,
                );
                let plain = ok(&mut Command::new(&program), &leg);
                write(&leg, "run-plain.txt", &plain);
                assert_eq!(plain, expected(false), "{label}");
                let interposer = leg.join("libinterpose.so");
                ok(
                    cc_with(flags)
                        .arg("-shared")
                        .arg(&interposer_object)
                        .arg("-o")
                        .arg(&interposer),
                    &leg,
                );
                let preloaded = ok(Command::new(&program).env("LD_PRELOAD", &interposer), &leg);
                write(&leg, "run-preload.txt", &preloaded);
                assert_eq!(
                    preloaded,
                    expected(true),
                    "{label}: only the default definitions interpose"
                );

                for (index, (name, visibility, seen, mutable, outsider)) in
                    outsiders.iter().enumerate()
                {
                    let binary = leg.join(format!("outsider{index}"));
                    let (success, _, stderr) = run(
                        cc_with(flags)
                            .arg("-no-pie")
                            .arg(outsider)
                            .arg(&library)
                            .arg(&rpath)
                            .arg("-o")
                            .arg(&binary),
                        &leg,
                    );
                    if let Some(refusal) = outsider_refusal(linker, *visibility, name) {
                        write(&leg, &format!("outsider{index}-link.txt"), &stderr);
                        assert!(
                            !success && stderr.contains(&refusal),
                            "{label}: a non-PIE reference to {visibility} `{name}` must fail \
                             with `{refusal}`: {stderr}"
                        );
                        continue;
                    }
                    assert!(success, "{label}: `{name}`: {stderr}");
                    assert!(
                        reloc_rows(&readelf_text(&["--relocs"], &binary, &leg))
                            .iter()
                            .any(|row| {
                                row.kind == "R_AARCH64_COPY" && row.symbol.as_deref() == Some(name)
                            }),
                        "{label}: the non-PIE control must copy-relocate `{name}`"
                    );
                    assert_eq!(
                        ok(&mut Command::new(&binary), &leg),
                        format!("exe={seen:x} lib={seen:x}\n"),
                        "{label}: the library follows `{name}`'s copy (mutable: {mutable})"
                    );
                }
            }
            eprintln!(
                "strong hidden/protected data in every implicit section passed: {opt_level:?} \
                 {:?} {directory:?}",
                linker_names(&linkers)
            );
        }
    }

    // -------------------------------------------------------------------------
    // L02-P6 closure audit 4: the visibility cross-product table, at link time
    // -------------------------------------------------------------------------

    use super::visibility_table::{
        Case, Kind, Link, Role, Route, SLOT_TARGET_VALUE, anchored, call_kept, callable,
        case_value, pipeline_input, pipeline_object, table_compiler, table_module,
    };

    /// The four table routes, each with its own symbol prefix.
    const TABLE_ROUTES: [Route; 4] = [
        Route::Compiler,
        Route::PipelineUnwind,
        Route::PipelineLayoutLess,
        Route::PipelineRelocationFree,
    ];

    /// The value the C `definitions` object gives declaration `ordinal` of
    /// route `route_index`, and the one the interposer gives any name.
    fn declared_value(route_index: usize, ordinal: usize) -> u64 {
        0x7_0000 + 0x1000 * route_index as u64 + ordinal as u64
    }

    fn interposed_value(route_index: usize, ordinal: usize) -> u64 {
        0x9_0000 + 0x1000 * route_index as u64 + ordinal as u64
    }

    /// One printed read of the table driver: its label and every value it
    /// may print without the interposer and with it. A set holds two values
    /// only where the module inliner may fold a preemptible
    /// one-definition-rule function's call (its copies are equivalent), so
    /// the call reaches either the library's copy or the interposer's.
    struct TableRead {
        label: String,
        plain: Vec<u64>,
        preloaded: Vec<u64>,
    }

    /// The reads the driver makes of `case` on `route`, plus the C source
    /// that makes them (a relocation-free route has no CG accessor: its reads
    /// go through C accessors compiled into the library).
    fn table_reads(
        route: Route,
        route_index: usize,
        ordinal: usize,
        case: Case,
    ) -> Vec<(TableRead, String)> {
        let name = case.name(route.prefix());
        let own = if case.role == Role::Declaration {
            declared_value(route_index, ordinal)
        } else {
            match case.kind {
                Kind::RelRo => SLOT_TARGET_VALUE,
                Kind::Bss | Kind::Tbss => 0,
                _ => case_value(ordinal),
            }
        };
        let interposed = interposed_value(route_index, ordinal);
        let interposable = case.exported() && case.visibility == Visibility::Default;
        let preloaded = if interposable { interposed } else { own };
        let read = |what: &str, preloaded: Vec<u64>, expression: String| {
            (
                TableRead {
                    label: format!("{name}.{what}"),
                    plain: vec![own],
                    preloaded,
                },
                format!(
                    "  printf(\"{name}.{what} %llx\\n\", (unsigned long long)({expression}));\n"
                ),
            )
        };
        let mut reads = Vec::new();
        let relocation_free = route == Route::PipelineRelocationFree;
        if relocation_free && !case.exported() {
            return reads;
        }
        let accessor = |kind: &str| {
            if relocation_free {
                format!("c{kind}_{name}")
            } else {
                format!("{kind}_{name}")
            }
        };
        match case.kind {
            Kind::Function => {
                // An `available_externally` body may be inlined in place of
                // the call, so only its address is read.
                if callable(case) && case.link != Link::AvailableExternally {
                    let folds = !call_kept(case, trust_cg_codegen::RelocationModel::Pic, route)
                        && interposable;
                    let preloaded = if folds {
                        vec![own, interposed]
                    } else {
                        vec![preloaded]
                    };
                    reads.push(read("call", preloaded, format!("{}()", accessor("call"))));
                }
                reads.push(read(
                    "addr",
                    vec![preloaded],
                    format!("((uint64_t (*)(void)){}())()", accessor("addr")),
                ));
            }
            Kind::RelRo if case.role == Role::Definition => reads.push(read(
                "addr",
                vec![preloaded],
                format!("**(uint64_t **){}()", accessor("addr")),
            )),
            _ => reads.push(read(
                "addr",
                vec![preloaded],
                format!("*(uint64_t *){}()", accessor("addr")),
            )),
        }
        reads
    }

    /// L02-P6 closure audit 4: every admitted case of the visibility table,
    /// from all four routes (`Compiler::compile` and the three Pipeline
    /// module emitters, each with its own symbol prefix), in ONE `pic` shared
    /// library linked by GNU ld, gold and LLD with `-z defs,-z text`, at
    /// O0-O3, with and without function sections. A C object in the
    /// library defines every declared name at default visibility, and C
    /// accessors read the relocation-free route's symbols, which no CG code
    /// references.
    ///
    /// * `.dynsym`: no hidden or module-local name is exported (gold may list
    ///   a hidden thread-local its own object names by symbol, never an
    ///   anchored one, as `TLS LOCAL HIDDEN`); every protected name is
    ///   exported `PROTECTED` and every default one `DEFAULT`, `WEAK` for a
    ///   weak or COMDAT definition; no dynamic relocation names a hidden name
    ///   (gold's `LOCAL HIDDEN` thread-locals excepted).
    /// * A PIE driver reads every case through its accessors (a function
    ///   through `call_<symbol>` and through its address). An `LD_PRELOAD`
    ///   interposer defining every name takes over exactly the
    ///   default-visibility definitions and declarations.
    ///
    /// This covers every class the fourth closure audit's surviving mutants
    /// broke natively: weak and COMDAT read-only data, COMDAT data with an
    /// explicit name, explicit-section protected data and thread-locals,
    /// functions in named text or function sections, COMDAT functions with an
    /// explicit name, the relocation-free route's data and the layout-less
    /// route's thread-local imports. Execution evidence for these linkers and
    /// the glibc loader on this host, not a linker or loader proof.
    #[test]
    fn visibility_table_binds_every_class_inside_a_shared_object() {
        let model = trust_cg_codegen::RelocationModel::Pic;
        let linkers = linkers();
        let directory = scratch("visibility-table");
        let routes: Vec<(Route, Vec<Case>)> = TABLE_ROUTES
            .iter()
            .map(|route| (*route, route.cases()))
            .collect();

        let mut definitions = String::from("#include <stdint.h>\n");
        let mut accessors = String::from("#include <stdint.h>\n");
        let mut interposer = String::from("#include <stdint.h>\n");
        let mut driver = String::from("#include <stdint.h>\n#include <stdio.h>\n");
        let mut body = String::from("int main(void) {\n");
        let mut reads = Vec::new();
        // The relocation-free route references nothing, so its declarations
        // emit no symbol (the object rows check that) and are not linked.
        let linked = |route: Route, case: &Case| {
            route != Route::PipelineRelocationFree || case.role == Role::Definition
        };
        for (route_index, (route, cases)) in routes.iter().enumerate() {
            for (ordinal, case) in cases.iter().enumerate() {
                if !linked(*route, case) {
                    continue;
                }
                let name = case.name(route.prefix());
                let declared = declared_value(route_index, ordinal);
                let interposed = interposed_value(route_index, ordinal);
                let thread = if case.kind.tls() { "__thread " } else { "" };
                if case.role == Role::Declaration {
                    if case.kind == Kind::Function {
                        // An `available_externally` body promises the one the
                        // library defines: it returns the declared value too.
                        definitions.push_str(&format!(
                            "uint64_t {name}(void) {{ return {declared:#x}; }}\n"
                        ));
                    } else {
                        definitions
                            .push_str(&format!("{thread}uint64_t {name} = {declared:#x};\n"));
                    }
                }
                if case.exported() {
                    match case.kind {
                        Kind::Function => interposer.push_str(&format!(
                            "uint64_t {name}(void) {{ return {interposed:#x}; }}\n"
                        )),
                        Kind::RelRo if case.role == Role::Definition => {
                            interposer.push_str(&format!(
                                "static uint64_t cell_{name} = {interposed:#x};\n\
                                 uint64_t *{name} = &cell_{name};\n"
                            ));
                        }
                        _ => interposer
                            .push_str(&format!("{thread}uint64_t {name} = {interposed:#x};\n")),
                    }
                }
                if *route == Route::PipelineRelocationFree && case.exported() {
                    if case.kind == Kind::Function {
                        accessors.push_str(&format!(
                            "extern uint64_t {name}(void);\n\
                             uint64_t ccall_{name}(void) {{ return {name}(); }}\n\
                             void *caddr_{name}(void) {{ return (void *){name}; }}\n"
                        ));
                        driver.push_str(&format!(
                            "uint64_t ccall_{name}(void);\nvoid *caddr_{name}(void);\n"
                        ));
                    } else {
                        accessors.push_str(&format!(
                            "extern {thread}uint64_t {name};\n\
                             void *caddr_{name}(void) {{ return (void *)&{name}; }}\n"
                        ));
                        driver.push_str(&format!("void *caddr_{name}(void);\n"));
                    }
                } else if *route != Route::PipelineRelocationFree {
                    if callable(*case) {
                        driver.push_str(&format!("uint64_t call_{name}(void);\n"));
                    }
                    driver.push_str(&format!("void *addr_{name}(void);\n"));
                }
                for (read, source) in table_reads(*route, route_index, ordinal, *case) {
                    body.push_str(&source);
                    reads.push(read);
                }
            }
        }
        body.push_str("  return 0;\n}\n");
        driver.push_str(&body);
        let expected = |preloaded: bool| -> Vec<(String, Vec<u64>)> {
            reads
                .iter()
                .map(|read| {
                    (
                        read.label.clone(),
                        if preloaded {
                            read.preloaded.clone()
                        } else {
                            read.plain.clone()
                        },
                    )
                })
                .collect()
        };
        let check_run = |output: &str, preloaded: bool, label: &str| {
            let lines: Vec<&str> = output.lines().collect();
            let expected = expected(preloaded);
            assert_eq!(lines.len(), expected.len(), "{label}: printed reads");
            let wrong: Vec<String> = lines
                .iter()
                .zip(&expected)
                .filter_map(|(line, (read, values))| {
                    let (printed, value) = line.split_once(' ')?;
                    let value = u64::from_str_radix(value, 16).ok()?;
                    (printed != read || !values.contains(&value))
                        .then(|| format!("{line} (expected {read} in {values:x?})"))
                })
                .collect();
            assert!(
                wrong.is_empty(),
                "{label}: {} wrong read(s), preloaded={preloaded}:\n{}",
                wrong.len(),
                wrong.join("\n")
            );
        };

        let definitions_object =
            c_object_with("cc", &directory, "definitions", &definitions, &["-fPIC"]);
        let accessors_object = c_object_with("cc", &directory, "accessors", &accessors, &["-fPIC"]);
        let interposer_object =
            c_object_with("cc", &directory, "interposer", &interposer, &["-fPIC"]);
        let driver_object = c_object_with("cc", &directory, "driver", &driver, &["-fPIE"]);
        let interposers: Vec<PathBuf> = linkers
            .iter()
            .map(|(linker, flags)| {
                let library = directory.join(format!("libinterpose-{linker}.so"));
                ok(
                    cc_with(flags)
                        .arg("-shared")
                        .arg(&interposer_object)
                        .arg("-o")
                        .arg(&library),
                    &directory,
                );
                library
            })
            .collect();

        for function_sections in [false, true] {
            for opt_level in OPT_LEVELS {
                let level =
                    directory.join(format!("fs{}-{opt_level:?}", u8::from(function_sections)));
                fs::create_dir_all(&level).unwrap();
                let mut objects = vec![definitions_object.clone(), accessors_object.clone()];
                for (route, cases) in &routes {
                    let bytes = if *route == Route::Compiler {
                        table_compiler(opt_level, model, function_sections, true)
                            .compile(&table_module(cases))
                            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
                            .object_code
                    } else {
                        pipeline_object(
                            *route,
                            model,
                            function_sections,
                            opt_level,
                            &pipeline_input(*route, model),
                        )
                    };
                    objects.push(write(&level, &format!("{}.o", route.prefix()), bytes));
                }
                for ((linker, flags), interposer) in linkers.iter().zip(&interposers) {
                    let label = format!("fs={function_sections} {opt_level:?} {linker}");
                    let leg = level.join(linker);
                    fs::create_dir_all(&leg).unwrap();
                    let library = leg.join("libtcgvistable.so");
                    ok(
                        cc_with(flags)
                            .args(["-shared", "-Wl,-z,defs,-z,text,-z,relro,-z,now"])
                            .args(&objects)
                            .arg("-o")
                            .arg(&library),
                        &leg,
                    );
                    let dynsym = readelf_text(&["--dyn-syms"], &library, &leg);
                    write(&leg, "dynsym.txt", &dynsym);
                    // `.dynsym` rows `(bind, vis, ndx)` by name.
                    let mut by_name: std::collections::HashMap<
                        &str,
                        Vec<(String, String, String)>,
                    > = std::collections::HashMap::new();
                    for line in dynsym.lines() {
                        let columns: Vec<&str> = line.split_whitespace().collect();
                        if columns.len() >= 8 && columns[0].ends_with(':') {
                            let name = columns[7].split('@').next().unwrap_or_default();
                            by_name.entry(name).or_default().push((
                                columns[4].to_string(),
                                columns[5].to_string(),
                                columns[6].to_string(),
                            ));
                        }
                    }
                    let rows = |name: &str| by_name.get(name).cloned().unwrap_or_default();
                    let mut wrong = Vec::new();
                    let mut hidden_names = Vec::new();
                    for (route, cases) in &routes {
                        for case in cases.iter().filter(|case| linked(*route, case)) {
                            let name = case.name(route.prefix());
                            let rows = rows(&name);
                            let visibility = if case.exported() {
                                case.visibility
                            } else {
                                Visibility::Hidden
                            };
                            // Gold lists a hidden or module-local
                            // thread-local that some object of the library
                            // names by symbol in `.dynsym` as `LOCAL`: all but
                            // the anchored ones (the relocation-free route
                            // has no anchor; C accessors name its symbols).
                            let gold_local = *linker == "gold"
                                && case.kind.tls()
                                && !(anchored(*case, model)
                                    && *route != Route::PipelineRelocationFree);
                            let fine = match visibility {
                                Visibility::Hidden => {
                                    if !gold_local {
                                        hidden_names.push(name.clone());
                                    }
                                    rows.iter().all(|(bind, vis, _)| {
                                        bind == "LOCAL" && (vis == "HIDDEN" || !case.exported())
                                    }) && (gold_local || rows.is_empty())
                                }
                                _ => {
                                    let bind = if case.role == Role::Definition
                                        && case.link != Link::External
                                    {
                                        "WEAK"
                                    } else {
                                        "GLOBAL"
                                    };
                                    matches!(rows.as_slice(), [(b, v, ndx)]
                                        if b == bind
                                            && *v == readelf_visibility(visibility)
                                            && ndx != "UND")
                                }
                            };
                            if !fine {
                                wrong.push(format!("{name} ({case:?}): {rows:?}"));
                            }
                        }
                    }
                    assert!(
                        wrong.is_empty(),
                        "{label}: {} `.dynsym` mismatch(es):\n{}",
                        wrong.len(),
                        wrong.join("\n")
                    );
                    let hidden: Vec<&str> = hidden_names.iter().map(String::as_str).collect();
                    let named = dynamic_relocations_naming(&library, &leg, &hidden);
                    assert!(named.is_empty(), "{label}: {named:?}");

                    let program = leg.join("driver");
                    ok(
                        cc_with(flags)
                            .args(["-fPIE", "-pie"])
                            .arg(&driver_object)
                            .arg(&library)
                            .arg(format!("-Wl,-rpath,{}", leg.display()))
                            .arg("-o")
                            .arg(&program),
                        &leg,
                    );
                    let plain = ok(&mut Command::new(&program), &leg);
                    write(&leg, "run-plain.txt", &plain);
                    check_run(&plain, false, &label);
                    let preloaded = ok(Command::new(&program).env("LD_PRELOAD", interposer), &leg);
                    write(&leg, "run-preload.txt", &preloaded);
                    check_run(&preloaded, true, &label);
                }
                eprintln!(
                    "visibility table in a shared object passed: fs={function_sections} \
                     {opt_level:?} {} reads {:?} {directory:?}",
                    reads.len(),
                    linker_names(&linkers)
                );
            }
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
