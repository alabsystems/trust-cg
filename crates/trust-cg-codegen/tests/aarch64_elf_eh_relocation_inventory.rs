// AArch64 ELF relocation inventory of exception-handling objects.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Ledger row L03-P13. The certified-object relocation inventory used to refuse
// every module carrying exception-handling metadata. On AArch64 ELF it now
// enumerates the unwind-table rows the module emitter writes:
//
// * `.eh_frame` @ the zPLR CIE personality field: `R_AARCH64_PREL32` against
//   `DW.ref.<personality>`, addend 0;
// * `.eh_frame` @ each FDE pc-begin: `R_AARCH64_PREL32` against the function's
//   text-section anchor, addend the body's offset in that section;
// * `.eh_frame` @ each FDE LSDA pointer: `R_AARCH64_PREL32` against the
//   `.gcc_except_table` anchor, addend the LSDA's offset;
// * `.data.DW.ref.<personality>` @ 0: `R_AARCH64_ABS64` against the
//   personality, addend 0.
//
// These tests compile EH modules (cleanup-only, catch-all, EH functions mixed
// with functions that have no personality, several EH functions per module, a
// module-local personality, COMDAT text, two COMDAT functions in one explicit
// section name, function sections) at O0-O3 under the static, PIE and PIC
// relocation models, and require the inventory's mirrored rows to equal the
// relocation records of the emitted object exactly in both directions, keyed
// by section and symbol INDEX (a section name two sections can share never
// identifies one). The object is read by the ELF reparse gate's independent
// reader, by this file's own section and `.eh_frame` walker (which locates the
// personality, pc-begin and LSDA fields from the bytes), and on Linux GNU by
// GNU readelf. The whole report's relocation kinds must equal the object's. A
// data global in a section named like a personality slot stays a data row,
// and a data global in `.eh_frame` or `.gcc_except_table` is refused alike by
// the inventory and the emitter. The rows-less report APIs never report an EH
// module as promotable. Refusals stay named: Mach-O EH, a second personality,
// a typed catch, and an EH module without frame layouts. The exact row
// cross-check that `Compiler::compile` runs after emission must fail on any
// dropped, added or altered row. A certified compile of an EH module is
// refused at promotion because exception tables carry no proof obligation
// (`[TCG-EH-UNPROVED]`).
//
// Evidence boundary: object readback of these fixtures. It shows the inventory
// names the rows the emitter wrote; it does not prove the unwind tables
// describe the frames.

#![cfg(feature = "verify")]

use std::collections::{BTreeMap, BTreeSet};

#[path = "common/pinned_target.rs"]
mod pinned_target;

use trust_cg_codegen::frame::FrameLayout;
use trust_cg_codegen::pipeline::{
    AArch64ElfRelocationKey, AArch64ElfRelocationSymbol, AArch64ElfRelocationTarget,
    AArch64ElfSectionIdentity, AArch64ElfUnwindRelocationRole, AArch64ElfUnwindRelocationRow,
    FunctionSymbolBinding, ModuleSymbolLinkage, ObjectGlobal, OptLevel, Pipeline, PipelineConfig,
    PipelineError, aarch64_elf_unwind_relocation_keys,
    crosscheck_aarch64_elf_unwind_relocation_rows,
};
use trust_cg_codegen::{CompileError, Compiler, CompilerConfig, RelocationModel};
use trust_cg_ir::MachFunction;
use trust_ir::{
    BinOp, Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Linkage, Module,
    Ty, ValueId,
};

const LINUX: &str = "aarch64-unknown-linux-gnu";
const DARWIN: &str = "aarch64-apple-darwin";
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const MODELS: [RelocationModel; 3] = [
    RelocationModel::Static,
    RelocationModel::Pie,
    RelocationModel::Pic,
];
const CXX_PERSONALITY: &str = "__gxx_personality_v0";
const RUST_PERSONALITY: &str = "rust_eh_personality";

const R_AARCH64_ABS64: u32 = 257;
const R_AARCH64_PREL32: u32 = 261;

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn b(index: u32) -> BlockId {
    BlockId::new(index)
}

fn declare(module: &mut Module, id: u32, name: &str, params: Vec<Ty>, returns: Vec<Ty>) {
    let signature = module
        .add_func_type(FuncTy {
            params,
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(id), name, signature, b(0));
    function.linkage = Linkage::External;
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

fn define(module: &mut Module, id: u32, name: &str, blocks: Vec<Block>) {
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(id), name, signature, b(0));
    function.blocks = blocks;
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

fn block(id: u32, params: Vec<(ValueId, Ty)>, body: Vec<InstrNode>) -> Block {
    Block {
        id: b(id),
        params,
        body,
    }
}

fn i32_const(value: i128, result: u32) -> InstrNode {
    InstrNode::new(Inst::Const {
        ty: Ty::I32,
        value: Constant::Int(value),
    })
    .with_result(v(result))
}

fn ret(value: u32) -> InstrNode {
    InstrNode::new(Inst::Return {
        values: vec![v(value)],
    })
}

/// `b0: r = invoke callee(x) to b1 unwind b2`, `b1: return r`.
fn invoke_blocks(callee: u32) -> [Block; 2] {
    let invoke = InstrNode::new(Inst::Invoke {
        callee: FuncId::new(callee),
        args: vec![v(0)],
        normal_dest: b(1),
        normal_args: vec![],
        unwind_dest: b(2),
    })
    .with_result(v(2));
    [
        block(0, vec![(v(0), Ty::I32)], vec![invoke]),
        block(1, vec![], vec![ret(2)]),
    ]
}

/// `x -> invoke callee(x)`, cleanup pad `{ cleanup(x); resume }`.
fn cleanup_function(module: &mut Module, id: u32, name: &str, callee: u32, cleanup: u32) {
    let pad = vec![
        InstrNode::new(Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        })
        .with_results(vec![v(20), v(21)]),
        InstrNode::new(Inst::Call {
            callee: FuncId::new(cleanup),
            args: vec![v(0)],
        }),
        InstrNode::new(Inst::Resume { exn: v(20) }),
    ];
    let mut blocks = invoke_blocks(callee).to_vec();
    blocks.push(block(2, vec![], pad));
    define(module, id, name, blocks);
}

/// `x -> invoke callee(x)`, catch-all pad `{ caught(x); return 7 }`.
fn catch_all_function(module: &mut Module, id: u32, name: &str, callee: u32, caught: u32) {
    let pad = vec![
        InstrNode::new(Inst::LandingPad {
            is_cleanup: false,
            catch_type_indices: vec![0],
        })
        .with_results(vec![v(20), v(21)]),
        InstrNode::new(Inst::Call {
            callee: FuncId::new(caught),
            args: vec![v(0)],
        }),
        i32_const(7, 22),
        ret(22),
    ];
    let mut blocks = invoke_blocks(callee).to_vec();
    blocks.push(block(2, vec![], pad));
    define(module, id, name, blocks);
}

/// A frame with no handler: `x -> callee(x)`.
fn plain_function(module: &mut Module, id: u32, name: &str, callee: u32) {
    let body = vec![
        InstrNode::new(Inst::Call {
            callee: FuncId::new(callee),
            args: vec![v(0)],
        })
        .with_result(v(1)),
        ret(1),
    ];
    define(
        module,
        id,
        name,
        vec![block(0, vec![(v(0), Ty::I32)], body)],
    );
}

/// A zero-frame leaf: `x -> x + 1`.
fn leaf_function(module: &mut Module, id: u32, name: &str) {
    let body = vec![
        i32_const(1, 1),
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(2)),
        ret(2),
    ];
    define(
        module,
        id,
        name,
        vec![block(0, vec![(v(0), Ty::I32)], body)],
    );
}

/// Cleanup pads only, under the Rust personality, with a plain frame and a
/// leaf that carry no personality of their own.
fn rust_cleanup_module() -> Module {
    let mut module = Module::new("eh_inventory_rust_cleanup");
    declare(&mut module, 0, "rs_callee", vec![Ty::I32], vec![Ty::I32]);
    declare(&mut module, 1, "rs_cleanup", vec![Ty::I32], vec![]);
    declare(&mut module, 2, RUST_PERSONALITY, vec![], vec![]);
    cleanup_function(&mut module, 3, "tr_cleanup", 0, 1);
    cleanup_function(&mut module, 4, "tr_nested", 3, 1);
    plain_function(&mut module, 5, "tr_plain", 0);
    leaf_function(&mut module, 6, "tr_leaf");
    module
}

/// Catch-all pads only, under the C++ personality.
fn cxx_catch_module() -> Module {
    let mut module = Module::new("eh_inventory_cxx_catch");
    declare(&mut module, 0, "cxx_callee", vec![Ty::I32], vec![Ty::I32]);
    declare(&mut module, 1, "cxx_caught", vec![Ty::I32], vec![]);
    catch_all_function(&mut module, 2, "tc_catch", 0, 1);
    catch_all_function(&mut module, 3, "tc_catch_nested", 2, 1);
    catch_all_function(&mut module, 4, "tc_catch_third", 3, 1);
    module
}

/// Catch-all and cleanup pads mixed with functions without a personality.
fn cxx_mixed_module() -> Module {
    let mut module = Module::new("eh_inventory_cxx_mixed");
    declare(&mut module, 0, "cxx_callee", vec![Ty::I32], vec![Ty::I32]);
    declare(&mut module, 1, "cxx_caught", vec![Ty::I32], vec![]);
    leaf_function(&mut module, 2, "tm_leaf");
    catch_all_function(&mut module, 3, "tm_catch", 0, 1);
    plain_function(&mut module, 4, "tm_plain", 0);
    cleanup_function(&mut module, 5, "tm_cleanup", 3, 1);
    module
}

/// One EH function alone.
fn single_eh_module() -> Module {
    let mut module = Module::new("eh_inventory_single");
    declare(&mut module, 0, "cxx_callee", vec![Ty::I32], vec![Ty::I32]);
    declare(&mut module, 1, "cxx_cleanup", vec![Ty::I32], vec![]);
    cleanup_function(&mut module, 2, "ts_cleanup", 0, 1);
    module
}

/// Control: no EH, so only FDE pc-begin rows.
fn no_eh_module() -> Module {
    let mut module = Module::new("eh_inventory_none");
    declare(&mut module, 0, "cxx_callee", vec![Ty::I32], vec![Ty::I32]);
    plain_function(&mut module, 1, "tn_plain", 0);
    leaf_function(&mut module, 2, "tn_leaf");
    module
}

struct Fixture {
    module: Module,
    /// The personality every EH function carries, or `None` without EH.
    personality: Option<&'static str>,
    /// Functions carrying their own EH structure.
    eh_functions: &'static [&'static str],
}

fn fixtures() -> Vec<Fixture> {
    vec![
        Fixture {
            module: rust_cleanup_module(),
            personality: Some(RUST_PERSONALITY),
            eh_functions: &["tr_cleanup", "tr_nested"],
        },
        Fixture {
            module: cxx_catch_module(),
            personality: Some(CXX_PERSONALITY),
            eh_functions: &["tc_catch", "tc_catch_nested", "tc_catch_third"],
        },
        Fixture {
            module: cxx_mixed_module(),
            personality: Some(CXX_PERSONALITY),
            eh_functions: &["tm_catch", "tm_cleanup"],
        },
        Fixture {
            module: single_eh_module(),
            personality: Some(CXX_PERSONALITY),
            eh_functions: &["ts_cleanup"],
        },
        Fixture {
            module: no_eh_module(),
            personality: None,
            eh_functions: &[],
        },
    ]
}

fn pipeline(triple: &str, level: OptLevel, model: RelocationModel) -> Pipeline {
    Pipeline::new(PipelineConfig {
        target_triple: triple.to_string(),
        opt_level: level,
        relocation_model: model,
        ..PipelineConfig::default()
    })
}

/// Lower and prepare every defined function, keeping its frame layout.
fn prepare(pipeline: &Pipeline, module: &Module) -> (Vec<MachFunction>, Vec<Option<FrameLayout>>) {
    let defined: BTreeSet<&str> = module
        .functions
        .iter()
        .filter(|function| !function.blocks.is_empty())
        .map(|function| function.name.as_str())
        .collect();
    permit_translate_module(module)
        .unwrap_or_else(|error| panic!("{}: lowering: {error:?}", module.name))
        .iter()
        .filter(|(function, _)| defined.contains(function.name.as_str()))
        .map(|(function, context)| {
            let (prepared, metrics) = pipeline
                .prepare_function_with_metrics(function, Some(context))
                .unwrap_or_else(|error| panic!("{}: prepare: {error}", function.name));
            (prepared, metrics.frame_layout)
        })
        .unzip()
}

// ---------------------------------------------------------------------------
// Independent readers
// ---------------------------------------------------------------------------

fn u16_at(bytes: &[u8], at: usize) -> u16 {
    u16::from_le_bytes(bytes[at..at + 2].try_into().unwrap())
}

fn u32_at(bytes: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap())
}

fn u64_at(bytes: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap())
}

#[derive(Debug, Clone)]
struct Section {
    name: String,
    sh_type: u32,
    flags: u64,
    offset: usize,
    size: usize,
    info: u32,
}

#[derive(Debug, Clone)]
struct Symbol {
    name: String,
    binding: u8,
    kind: u8,
    visibility: u8,
    section: u16,
    value: u64,
    size: u64,
}

/// A minimal ELF64 reader: section headers and the symbol table.
struct Elf<'a> {
    bytes: &'a [u8],
    sections: Vec<Section>,
    symbols: Vec<Symbol>,
}

fn c_string(bytes: &[u8], at: usize) -> String {
    let end = bytes[at..].iter().position(|&byte| byte == 0).unwrap() + at;
    String::from_utf8(bytes[at..end].to_vec()).unwrap()
}

fn parse_elf(bytes: &[u8]) -> Elf<'_> {
    assert_eq!(&bytes[..4], b"\x7fELF");
    assert_eq!(u16_at(bytes, 18), 183, "EM_AARCH64");
    let shoff = u64_at(bytes, 0x28) as usize;
    let shentsize = usize::from(u16_at(bytes, 0x3a));
    let shnum = usize::from(u16_at(bytes, 0x3c));
    let shstrndx = usize::from(u16_at(bytes, 0x3e));
    let header = |index: usize| shoff + index * shentsize;
    let strtab = u64_at(bytes, header(shstrndx) + 0x18) as usize;
    let mut sections = Vec::with_capacity(shnum);
    let mut links = Vec::with_capacity(shnum);
    for index in 0..shnum {
        let at = header(index);
        sections.push(Section {
            name: c_string(bytes, strtab + u32_at(bytes, at) as usize),
            sh_type: u32_at(bytes, at + 4),
            flags: u64_at(bytes, at + 8),
            offset: u64_at(bytes, at + 0x18) as usize,
            size: u64_at(bytes, at + 0x20) as usize,
            info: u32_at(bytes, at + 0x2c),
        });
        links.push(u32_at(bytes, at + 0x28) as usize);
    }
    let symtab = sections
        .iter()
        .position(|section| section.sh_type == 2)
        .expect("symtab");
    let names = sections[links[symtab]].offset;
    let symbols = (0..sections[symtab].size / 24)
        .map(|index| {
            let at = sections[symtab].offset + index * 24;
            Symbol {
                name: c_string(bytes, names + u32_at(bytes, at) as usize),
                binding: bytes[at + 4] >> 4,
                kind: bytes[at + 4] & 0xf,
                visibility: bytes[at + 5] & 3,
                section: u16_at(bytes, at + 6),
                value: u64_at(bytes, at + 8),
                size: u64_at(bytes, at + 16),
            }
        })
        .collect();
    Elf {
        bytes,
        sections,
        symbols,
    }
}

impl Elf<'_> {
    fn section(&self, name: &str) -> Option<(usize, &Section)> {
        self.sections
            .iter()
            .enumerate()
            .find(|(_, section)| section.name == name)
    }

    fn data(&self, name: &str) -> &[u8] {
        let (_, section) = self.section(name).unwrap_or_else(|| panic!("no {name}"));
        &self.bytes[section.offset..section.offset + section.size]
    }

    fn symbol(&self, name: &str) -> &Symbol {
        self.symbols
            .iter()
            .find(|symbol| symbol.name == name)
            .unwrap_or_else(|| panic!("no symbol {name}"))
    }

    /// Every `Elf64_Rela` record keyed by index: patched section, offset,
    /// type, target (an `STT_SECTION` symbol by the section it anchors),
    /// addend.
    fn relocations(&self) -> Vec<AArch64ElfRelocationKey> {
        let mut records = Vec::new();
        for section in self.sections.iter().filter(|section| section.sh_type == 4) {
            for index in 0..section.size / 24 {
                let at = section.offset + index * 24;
                let info = u64_at(self.bytes, at + 8);
                let symbol_index = (info >> 32) as usize;
                let symbol = &self.symbols[symbol_index];
                records.push(AArch64ElfRelocationKey {
                    section: section.info as usize,
                    offset: u64_at(self.bytes, at),
                    r_type: info as u32,
                    target: if symbol.kind == 3 {
                        AArch64ElfRelocationTarget::Section(usize::from(symbol.section))
                    } else {
                        AArch64ElfRelocationTarget::Symbol(symbol_index)
                    },
                    addend: u64_at(self.bytes, at + 16) as i64,
                });
            }
        }
        records
    }

    fn executable(&self, section: usize) -> bool {
        self.sections[section].flags & 0x4 != 0
    }

    /// The one non-section symbol named `name`, by index.
    fn named(&self, name: &str) -> usize {
        let found: Vec<usize> = self
            .symbols
            .iter()
            .enumerate()
            .filter(|(_, symbol)| symbol.kind != 3 && symbol.name == name)
            .map(|(index, _)| index)
            .collect();
        assert_eq!(found.len(), 1, "exactly one symbol named {name}: {found:?}");
        found[0]
    }

    /// This reader's own resolution of a row's section identity.
    fn resolve_section(&self, identity: &AArch64ElfSectionIdentity) -> usize {
        match identity {
            AArch64ElfSectionIdentity::Unique(name) => {
                let found: Vec<usize> = self
                    .sections
                    .iter()
                    .enumerate()
                    .filter(|(_, section)| section.name == *name)
                    .map(|(index, _)| index)
                    .collect();
                assert_eq!(found.len(), 1, "exactly one section named {name}");
                found[0]
            }
            AArch64ElfSectionIdentity::Defining(name) => {
                usize::from(self.symbols[self.named(name)].section)
            }
        }
    }

    /// A mirrored row resolved into this object by this reader.
    fn resolve(&self, row: &AArch64ElfUnwindRelocationRow) -> AArch64ElfRelocationKey {
        AArch64ElfRelocationKey {
            section: self.resolve_section(&row.section),
            offset: row.offset,
            r_type: row.r_type,
            target: match &row.symbol {
                AArch64ElfRelocationSymbol::Named(name) => {
                    AArch64ElfRelocationTarget::Symbol(self.named(name))
                }
                AArch64ElfRelocationSymbol::SectionAnchor(identity) => {
                    AArch64ElfRelocationTarget::Section(self.resolve_section(identity))
                }
            },
            addend: row.addend,
        }
    }
}

fn uleb(bytes: &[u8], at: &mut usize) -> u64 {
    let (mut value, mut shift) = (0u64, 0);
    loop {
        let byte = bytes[*at];
        *at += 1;
        value |= u64::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            return value;
        }
        shift += 7;
    }
}

/// The relocatable fields of an `.eh_frame` section, located from its bytes:
/// the CIE personality field, and each FDE's pc-begin and LSDA fields.
#[derive(Debug, Default)]
struct EhFrameFields {
    augmentation: String,
    personality_encoding: Option<u8>,
    lsda_encoding: Option<u8>,
    fde_encoding: Option<u8>,
    personality: Option<u64>,
    pc_begin: Vec<u64>,
    lsda: Vec<u64>,
}

fn eh_frame_fields(eh_frame: &[u8]) -> EhFrameFields {
    let mut fields = EhFrameFields::default();
    let mut at = 0usize;
    while at < eh_frame.len() {
        let length = u32_at(eh_frame, at) as usize;
        assert!(length != 0 && length != 0xffff_ffff, "record at {at}");
        let id = u32_at(eh_frame, at + 4);
        if id == 0 {
            assert!(fields.augmentation.is_empty(), "one CIE per object");
            let mut cursor = at + 9;
            fields.augmentation = c_string(eh_frame, cursor);
            cursor += fields.augmentation.len() + 1;
            uleb(eh_frame, &mut cursor); // code alignment
            uleb(eh_frame, &mut cursor); // data alignment (SLEB, one byte here)
            uleb(eh_frame, &mut cursor); // return address register
            assert!(fields.augmentation.starts_with('z'));
            uleb(eh_frame, &mut cursor); // augmentation data length
            for letter in fields.augmentation.chars().skip(1) {
                let encoding = eh_frame[cursor];
                cursor += 1;
                match letter {
                    'P' => {
                        fields.personality_encoding = Some(encoding);
                        fields.personality = Some(cursor as u64);
                        cursor += 4;
                    }
                    'L' => fields.lsda_encoding = Some(encoding),
                    'R' => fields.fde_encoding = Some(encoding),
                    other => panic!("unexpected augmentation {other}"),
                }
            }
        } else {
            fields.pc_begin.push((at + 8) as u64);
            let mut cursor = at + 16;
            let augmentation_length = uleb(eh_frame, &mut cursor);
            if fields.augmentation.contains('L') {
                assert_eq!(augmentation_length, 4, "sdata4 LSDA pointer");
                fields.lsda.push(cursor as u64);
            } else {
                assert_eq!(augmentation_length, 0);
            }
        }
        at += 4 + length;
    }
    fields
}

fn sorted(mut records: Vec<AArch64ElfRelocationKey>) -> Vec<AArch64ElfRelocationKey> {
    records.sort();
    records
}

/// Name a relocation type the fixtures emit.
fn type_name(r_type: u32) -> &'static str {
    match r_type {
        257 => "R_AARCH64_ABS64",
        261 => "R_AARCH64_PREL32",
        275 => "R_AARCH64_ADR_PREL_PG_HI21",
        277 => "R_AARCH64_ADD_ABS_LO12_NC",
        282 => "R_AARCH64_JUMP26",
        283 => "R_AARCH64_CALL26",
        311 => "R_AARCH64_ADR_GOT_PAGE",
        312 => "R_AARCH64_LD64_GOT_LO12_NC",
        other => panic!("unexpected relocation type {other}"),
    }
}

// ---------------------------------------------------------------------------
// The mirror-equals-object check
// ---------------------------------------------------------------------------

/// What one module emission contributed to the evidence line.
#[derive(Default)]
struct Tally {
    emissions: usize,
    unwind_rows: usize,
    eh_rows: usize,
    all_rows: usize,
}

/// Require the inventory's unwind rows to equal the emitted object's records
/// exactly, both directions, keyed by section and symbol index, and the
/// report's kinds to equal every record's.
#[allow(clippy::too_many_arguments)]
fn check_emission(
    label: &str,
    pipeline: &Pipeline,
    functions: &[MachFunction],
    globals: &[ObjectGlobal],
    layouts: &[Option<FrameLayout>],
    linkage: &ModuleSymbolLinkage,
    personality: Option<&str>,
    local_personality: bool,
    tally: &mut Tally,
) -> Vec<u8> {
    let inventory = pipeline
        .module_relocation_inventory_with_symbol_linkage(
            functions,
            globals,
            layouts,
            linkage,
            format!("{label}.o"),
        )
        .unwrap_or_else(|error| panic!("{label}: inventory refused: {error}"))
        .unwrap_or_else(|| panic!("{label}: no ELF inventory"));
    let object = pipeline
        .compile_module_emission_with_symbol_linkage(functions, globals, layouts, linkage)
        .unwrap_or_else(|error| panic!("{label}: emission: {error}"))
        .into_emission()
        .object;
    let rows = &inventory.elf_unwind_rows;
    let elf = parse_elf(&object);

    // 1. Mirror == object, both directions, by index: the gate's reader and
    //    resolution, then this file's reader and resolution over every record
    //    that patches a non-executable section other than a data global's.
    let mirrored = sorted(rows.iter().map(|row| elf.resolve(row)).collect());
    let keys = aarch64_elf_unwind_relocation_keys(&object, rows)
        .unwrap_or_else(|error| panic!("{label}: readback: {error}"));
    assert_eq!(keys.mirrored, mirrored, "{label}: resolutions disagree");
    assert_eq!(
        keys.mirrored, keys.emitted,
        "{label}: mirrored unwind rows (left) != object records (right)"
    );
    let global_sections: BTreeSet<usize> = globals
        .iter()
        .filter(|global| !global.is_import)
        .map(|global| usize::from(elf.symbol(&global.name).section))
        .collect();
    let all_records = elf.relocations();
    let own_read = sorted(
        all_records
            .iter()
            .filter(|record| {
                !elf.executable(record.section) && !global_sections.contains(&record.section)
            })
            .copied()
            .collect(),
    );
    assert_eq!(mirrored, own_read, "{label}: this file's reader disagrees");
    crosscheck_aarch64_elf_unwind_relocation_rows(&object, rows)
        .unwrap_or_else(|error| panic!("{label}: cross-check: {error}"));

    // 2. The report's kinds are exactly the object's relocation types.
    let report_kinds: BTreeMap<String, usize> =
        inventory
            .report
            .entries
            .iter()
            .fold(BTreeMap::new(), |mut counts, entry| {
                *counts
                    .entry(entry.kind.to_string().replace("AArch64 ELF ", ""))
                    .or_default() += 1;
                counts
            });
    let object_kinds: BTreeMap<String, usize> =
        all_records
            .iter()
            .fold(BTreeMap::new(), |mut counts, record| {
                *counts
                    .entry(type_name(record.r_type).to_string())
                    .or_default() += 1;
                counts
            });
    assert_eq!(
        report_kinds, object_kinds,
        "{label}: report kinds != object"
    );
    // Every kind has a registered proof and the reparse binding; only the
    // exception-table rows are Unverified (the tables carry no proof
    // obligation), so exactly an EH module's report is not promotable.
    let uncovered: Vec<usize> = inventory
        .report
        .uncovered_relocations()
        .iter()
        .map(|entry| entry.index)
        .collect();
    let first_unwind = inventory.report.entries.len() - rows.len();
    let eh_indices: Vec<usize> = rows
        .iter()
        .enumerate()
        .filter(|(_, row)| row.is_exception_table_row())
        .map(|(offset, _)| first_unwind + offset)
        .collect();
    assert_eq!(
        uncovered, eh_indices,
        "{label}: only exception-table rows are uncovered"
    );
    assert_eq!(
        inventory.report.is_promotable(),
        personality.is_none(),
        "{label}: {:?}",
        inventory.report.promotion_rejection_reason()
    );
    assert_eq!(
        inventory.trusted_unwind_tables,
        Some(format!(
            "unwind CFI of {} .eh_frame FDE(s) (trusted base TB-12: decode round trip and \
             native tests, no proof obligation)",
            functions.len()
        )),
        "{label}"
    );

    // 3. `.rela.eh_frame` is ascending (GNU ld's cursor) and the mirror lists
    //    the `.eh_frame` rows in the same order.
    let (eh_frame, _) = elf.section(".eh_frame").expect(".eh_frame");
    let eh_records: Vec<u64> = all_records
        .iter()
        .filter(|record| record.section == eh_frame)
        .map(|record| record.offset)
        .collect();
    assert!(
        eh_records.windows(2).all(|pair| pair[0] < pair[1]),
        "{label}: .rela.eh_frame must be sorted by r_offset"
    );
    let eh_rows: Vec<u64> = rows
        .iter()
        .filter(|row| row.section == AArch64ElfSectionIdentity::Unique(".eh_frame".into()))
        .map(|row| row.offset)
        .collect();
    assert_eq!(eh_rows, eh_records, "{label}: .eh_frame row order");

    // 4. Every row names what it claims, read from the bytes.
    let fields = eh_frame_fields(elf.data(".eh_frame"));
    assert_eq!(
        fields.fde_encoding,
        Some(0x1b),
        "{label}: pcrel|sdata4 FDEs"
    );
    assert_eq!(fields.pc_begin.len(), functions.len(), "{label}: FDE count");
    let by_role = |pick: &dyn Fn(&AArch64ElfUnwindRelocationRole) -> bool| {
        rows.iter()
            .filter(|row| pick(&row.role))
            .collect::<Vec<&AArch64ElfUnwindRelocationRow>>()
    };
    let pc_begin =
        by_role(&|role| matches!(role, AArch64ElfUnwindRelocationRole::FdePcBegin { .. }));
    assert_eq!(pc_begin.len(), functions.len());
    for ((row, field), function) in pc_begin.iter().zip(&fields.pc_begin).zip(functions) {
        assert_eq!(
            row.role,
            AArch64ElfUnwindRelocationRole::FdePcBegin {
                function: function.name.clone()
            }
        );
        assert_eq!(
            row.offset, *field,
            "{label}: {} pc-begin field",
            function.name
        );
        assert_eq!(row.r_type, R_AARCH64_PREL32);
        assert_eq!(row.formula(), "S + A - P");
        assert!(!row.is_exception_table_row());
        // The anchor is the section holding the body; the addend its offset.
        assert_eq!(
            row.symbol,
            AArch64ElfRelocationSymbol::SectionAnchor(AArch64ElfSectionIdentity::Defining(
                function.name.clone()
            )),
            "{label}: {} pc-begin anchor",
            function.name
        );
        let symbol = elf.symbol(&function.name);
        assert!(elf.executable(usize::from(symbol.section)));
        assert_eq!(
            symbol.value as i64, row.addend,
            "{label}: {} body offset",
            function.name
        );
    }
    let lsda = by_role(&|role| matches!(role, AArch64ElfUnwindRelocationRole::FdeLsda { .. }));
    let cie = by_role(&|role| *role == AArch64ElfUnwindRelocationRole::CiePersonality);
    let slot = by_role(&|role| *role == AArch64ElfUnwindRelocationRole::PersonalitySlot);
    if let Some((table, _)) = elf.section(".gcc_except_table") {
        assert!(
            !all_records.iter().any(|record| record.section == table),
            "{label}: .gcc_except_table carries no relocation"
        );
    }
    match personality {
        None => {
            assert_eq!(fields.augmentation, "zR", "{label}");
            assert!(
                lsda.is_empty() && cie.is_empty() && slot.is_empty(),
                "{label}"
            );
            assert!(fields.personality.is_none() && fields.lsda.is_empty());
            assert!(elf.section(".gcc_except_table").is_none());
            assert_eq!(rows.len(), functions.len());
        }
        Some(personality) => {
            assert_eq!(fields.augmentation, "zPLR", "{label}");
            assert_eq!(
                fields.personality_encoding,
                Some(0x9b),
                "indirect|pcrel|sdata4"
            );
            assert_eq!(fields.lsda_encoding, Some(0x1b), "pcrel|sdata4");
            assert_eq!(rows.len(), 2 * functions.len() + 2, "{label}: row count");
            let slot_symbol = format!("DW.ref.{personality}");
            let slot_section = format!(".data.DW.ref.{personality}");
            let [cie] = cie.as_slice() else {
                panic!("{label}: one CIE personality row")
            };
            assert_eq!(Some(cie.offset), fields.personality);
            assert_eq!(
                (&cie.section, cie.r_type, &cie.symbol, cie.addend),
                (
                    &AArch64ElfSectionIdentity::Unique(".eh_frame".into()),
                    R_AARCH64_PREL32,
                    &AArch64ElfRelocationSymbol::Named(slot_symbol.clone()),
                    0
                )
            );
            let [slot] = slot.as_slice() else {
                panic!("{label}: one slot row")
            };
            assert_eq!(
                (
                    &slot.section,
                    slot.offset,
                    slot.r_type,
                    &slot.symbol,
                    slot.addend
                ),
                (
                    &AArch64ElfSectionIdentity::Defining(slot_symbol.clone()),
                    0,
                    R_AARCH64_ABS64,
                    &AArch64ElfRelocationSymbol::Named(personality.to_string()),
                    0
                )
            );
            assert_eq!(slot.formula(), "S + A");
            assert_eq!(
                elf.data(&slot_section),
                &[0u8; 8],
                "{label}: RELA slot content"
            );
            // The slot symbol: weak hidden in its own COMDAT group for an
            // external personality, object-local for a local one.
            let slot_def = elf.symbol(&slot_symbol);
            let (slot_index, slot_header) = elf.section(&slot_section).unwrap();
            assert_eq!(usize::from(slot_def.section), slot_index);
            assert_eq!((slot_def.kind, slot_def.size, slot_def.value), (1, 8, 0));
            let group = elf.sections.iter().find(|section| {
                section.sh_type == 17 && elf.symbols[section.info as usize].name == slot_symbol
            });
            if local_personality {
                assert_eq!((slot_def.binding, slot_def.visibility), (0, 0), "{label}");
                assert!(group.is_none() && slot_header.flags & 0x200 == 0, "{label}");
            } else {
                assert_eq!((slot_def.binding, slot_def.visibility), (2, 2), "{label}");
                let group = group.unwrap_or_else(|| panic!("{label}: slot group"));
                let words: Vec<u32> = (0..group.size / 4)
                    .map(|word| u32_at(elf.bytes, group.offset + 4 * word))
                    .collect();
                assert_eq!(words[0], 1, "GRP_COMDAT");
                let members: BTreeSet<&str> = words[1..]
                    .iter()
                    .map(|&index| elf.sections[index as usize].name.as_str())
                    .collect();
                assert_eq!(
                    members,
                    BTreeSet::from([
                        slot_section.as_str(),
                        format!(".rela{slot_section}").as_str()
                    ]),
                    "{label}: slot group members"
                );
                assert!(slot_header.flags & 0x200 != 0, "SHF_GROUP");
            }
            // One LSDA field per FDE; each points at an LSDA (LPStart omit)
            // inside `.gcc_except_table`, 4-aligned, in function order.
            assert_eq!(lsda.len(), functions.len());
            assert_eq!(fields.lsda.len(), functions.len());
            let table = elf.data(".gcc_except_table");
            let mut previous = -1i64;
            for ((row, field), function) in lsda.iter().zip(&fields.lsda).zip(functions) {
                assert_eq!(
                    row.role,
                    AArch64ElfUnwindRelocationRole::FdeLsda {
                        function: function.name.clone()
                    }
                );
                assert_eq!(row.offset, *field, "{label}: {} LSDA field", function.name);
                assert_eq!(
                    (row.r_type, &row.symbol),
                    (
                        R_AARCH64_PREL32,
                        &AArch64ElfRelocationSymbol::SectionAnchor(
                            AArch64ElfSectionIdentity::Unique(".gcc_except_table".into())
                        )
                    )
                );
                let at = row.addend;
                assert!(at > previous && at % 4 == 0, "{label}: LSDA offsets ascend");
                assert_eq!(
                    table[at as usize], 0xff,
                    "{label}: LSDA at {at} (LPStart omit)"
                );
                previous = at;
            }
        }
    }

    #[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
    readelf::check(
        label,
        &object,
        &mirrored,
        &global_sections,
        personality,
        local_personality,
    );

    tally.emissions += 1;
    tally.unwind_rows += rows.len();
    tally.eh_rows += rows.len() - functions.len();
    tally.all_rows += all_records.len();
    object
}

/// GNU readelf, a reader shared with nothing in this crate, must list the
/// same unwind rows (by section and symbol index), symbol and group.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
mod readelf {
    use super::*;
    use std::process::Command;

    fn run(args: &[&str], object: &[u8], label: &str) -> String {
        let directory = std::env::temp_dir().join(format!(
            "tcg-eh-inventory-{}-{}",
            std::process::id(),
            label.replace([' ', '/'], "_")
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let path = directory.join("module.o");
        std::fs::write(&path, object).unwrap();
        let output = Command::new("readelf")
            .args(args)
            .arg(&path)
            .output()
            .unwrap_or_else(|error| panic!("readelf is required on Linux GNU: {error}"));
        std::fs::remove_dir_all(&directory).ok();
        assert!(output.status.success(), "{label}: readelf {args:?} failed");
        String::from_utf8(output.stdout).unwrap()
    }

    /// `-S`: index -> (type, file offset, flags, sh_info).
    fn section_table(object: &[u8], label: &str) -> BTreeMap<usize, (String, u64, String, usize)> {
        let text = run(&["-SW"], object, label);
        let mut sections = BTreeMap::new();
        for line in text.lines() {
            let Some(open) = line.find('[') else {
                continue;
            };
            let Some(close) = line[open..].find(']') else {
                continue;
            };
            let Ok(index) = line[open + 1..open + close].trim().parse::<usize>() else {
                continue;
            };
            let fields: Vec<&str> = line[open + close + 1..].split_whitespace().collect();
            // Name Type Address Off Size ES [Flg] Lk Inf Al
            let (kind, offset, flags, info) = match fields.len() {
                10 => (fields[1], fields[3], fields[6], fields[8]),
                9 => (fields[1], fields[3], "", fields[7]),
                _ => continue,
            };
            sections.insert(
                index,
                (
                    kind.to_string(),
                    u64::from_str_radix(offset, 16).unwrap(),
                    flags.to_string(),
                    info.parse().unwrap(),
                ),
            );
        }
        sections
    }

    pub(super) fn check(
        label: &str,
        object: &[u8],
        mirrored: &[AArch64ElfRelocationKey],
        global_sections: &BTreeSet<usize>,
        personality: Option<&str>,
        local_personality: bool,
    ) {
        let sections = section_table(object, label);
        // `-s`: index -> STT_SECTION's Ndx, or None for any other symbol.
        let symbol_table = run(&["-sW"], object, label);
        let mut section_symbols = BTreeMap::new();
        for line in symbol_table.lines() {
            let fields: Vec<&str> = line.split_whitespace().collect();
            let Some(index) = fields
                .first()
                .and_then(|field| field.strip_suffix(':'))
                .and_then(|field| field.parse::<usize>().ok())
            else {
                continue;
            };
            let ndx =
                (fields.get(3) == Some(&"SECTION")).then(|| fields[6].parse::<usize>().unwrap());
            section_symbols.insert(index, ndx);
        }
        // `-r`: each `.rela` section by its file offset, then its records.
        let relocations = run(&["-rW"], object, label);
        let mut target = None;
        let mut read = Vec::new();
        for line in relocations.lines() {
            if let Some(rest) = line.strip_prefix("Relocation section '") {
                let offset = rest
                    .split(" at offset 0x")
                    .nth(1)
                    .and_then(|tail| tail.split_whitespace().next())
                    .map(|hex| u64::from_str_radix(hex, 16).unwrap())
                    .expect("rela section offset");
                let (_, (_, _, _, info)) = sections
                    .iter()
                    .find(|(_, (kind, at, _, _))| kind == "RELA" && *at == offset)
                    .expect("rela section by offset");
                target = Some(*info);
                continue;
            }
            let Some(section) = target else {
                continue;
            };
            if sections[&section].2.contains('X') || global_sections.contains(&section) {
                continue;
            }
            let fields: Vec<&str> = line.split_whitespace().collect();
            let (Some(offset), Some(info)) = (
                fields
                    .first()
                    .and_then(|field| u64::from_str_radix(field, 16).ok()),
                fields
                    .get(1)
                    .and_then(|field| u64::from_str_radix(field, 16).ok()),
            ) else {
                continue;
            };
            let (sign, magnitude) = (fields[fields.len() - 2], fields[fields.len() - 1]);
            let magnitude = i64::from_str_radix(magnitude, 16).unwrap();
            let symbol = (info >> 32) as usize;
            read.push(AArch64ElfRelocationKey {
                section,
                offset,
                r_type: info as u32,
                target: match section_symbols[&symbol] {
                    Some(ndx) => AArch64ElfRelocationTarget::Section(ndx),
                    None => AArch64ElfRelocationTarget::Symbol(symbol),
                },
                addend: if sign == "-" { -magnitude } else { magnitude },
            });
        }
        assert_eq!(
            sorted(read),
            mirrored,
            "{label}: GNU readelf rows:\n{relocations}"
        );
        let Some(personality) = personality else {
            return;
        };
        let slot = format!("DW.ref.{personality}");
        let line = symbol_table
            .lines()
            .find(|line| line.split_whitespace().last() == Some(slot.as_str()))
            .unwrap_or_else(|| panic!("{label}: readelf lists {slot}"));
        let fields: Vec<&str> = line.split_whitespace().collect();
        let expected = if local_personality {
            ["8", "OBJECT", "LOCAL", "DEFAULT"]
        } else {
            ["8", "OBJECT", "WEAK", "HIDDEN"]
        };
        assert_eq!(&fields[2..6], expected, "{label}: {line}");
        let groups = run(&["-gW"], object, label);
        assert_eq!(
            groups.contains(&format!("[{slot}]")),
            !local_personality,
            "{label}: COMDAT group signed by {slot}: {groups}"
        );
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// Every fixture at O0-O3 under the static, PIE and PIC models, with the
/// default single `.text` and with `-ffunction-sections`: the inventory's
/// unwind rows are the object's unwind records, exactly.
#[test]
fn eh_inventory_rows_equal_the_emitted_elf_records() {
    let mut tally = Tally::default();
    let mut eh_modules = BTreeSet::new();
    for fixture in fixtures() {
        for level in LEVELS {
            for model in MODELS {
                for function_sections in [false, true] {
                    let pipeline =
                        pipeline(LINUX, level, model).with_function_sections(function_sections);
                    let (functions, layouts) = prepare(&pipeline, &fixture.module);
                    let with_eh: BTreeSet<&str> = functions
                        .iter()
                        .filter(|function| function.eh_metadata.has_eh_info())
                        .map(|function| function.name.as_str())
                        .collect();
                    assert_eq!(
                        with_eh,
                        fixture.eh_functions.iter().copied().collect(),
                        "{}: EH functions",
                        fixture.module.name
                    );
                    let label = format!(
                        "{} {level:?} {model} fs={function_sections}",
                        fixture.module.name
                    );
                    check_emission(
                        &label,
                        &pipeline,
                        &functions,
                        &[],
                        &layouts,
                        &ModuleSymbolLinkage::default(),
                        fixture.personality,
                        false,
                        &mut tally,
                    );
                    if fixture.personality.is_some() {
                        eh_modules.insert(fixture.module.name.clone());
                    }
                }
            }
        }
    }
    assert_eq!(eh_modules.len(), 4);
    assert_eq!(tally.emissions, 5 * 4 * 3 * 2);
    println!(
        "EH_RELOC_INVENTORY emissions={} unwind_rows={} eh_only_rows={} object_rows={}",
        tally.emissions, tally.unwind_rows, tally.eh_rows, tally.all_rows
    );
}

/// Bindings that make `weak` weak definitions (a COMDAT definition must be
/// weak) and every other function global.
fn weak_bindings(functions: &[MachFunction], weak: &[&str]) -> Vec<FunctionSymbolBinding> {
    functions
        .iter()
        .map(|function| {
            if weak.contains(&function.name.as_str()) {
                FunctionSymbolBinding::WEAK
            } else {
                FunctionSymbolBinding::GLOBAL
            }
        })
        .collect()
}

/// A COMDAT EH function (its own grouped `.text.<symbol>`), two COMDAT EH
/// functions in ONE explicit section name (two distinct sections both named
/// `probe_text`), and a module-local personality (an object-local `DW.ref`
/// slot outside any group) keep the mirror exact. For the shared name, each
/// FDE must be anchored to its own function's section: the rows are matched
/// by section index, never by name.
#[test]
fn comdat_text_and_a_local_personality_keep_the_mirror_exact() {
    let mut tally = Tally::default();
    let mut shared_name_emissions = 0;
    for level in LEVELS {
        for model in MODELS {
            let pipeline = pipeline(LINUX, level, model);
            let (functions, layouts) = prepare(&pipeline, &cxx_mixed_module());
            let comdat =
                ModuleSymbolLinkage::new(weak_bindings(&functions, &["tm_catch"]), BTreeSet::new())
                    .with_comdat_functions(BTreeSet::from(["tm_catch".to_string()]));
            let object = check_emission(
                &format!("comdat {level:?} {model}"),
                &pipeline,
                &functions,
                &[],
                &layouts,
                &comdat,
                Some(CXX_PERSONALITY),
                false,
                &mut tally,
            );
            let elf = parse_elf(&object);
            assert_eq!(
                elf.sections[usize::from(elf.symbol("tm_catch").section)].name,
                ".text.tm_catch"
            );

            // Two COMDAT EH functions whose explicit section is the same name.
            let pair = ["tm_catch", "tm_cleanup"];
            let shared =
                ModuleSymbolLinkage::new(weak_bindings(&functions, &pair), BTreeSet::new())
                    .with_comdat_functions(pair.iter().map(|name| name.to_string()).collect())
                    .with_explicit_function_sections(
                        pair.iter()
                            .map(|name| (name.to_string(), "probe_text".to_string()))
                            .collect(),
                    );
            let label = format!("shared-name {level:?} {model}");
            let object = check_emission(
                &label,
                &pipeline,
                &functions,
                &[],
                &layouts,
                &shared,
                Some(CXX_PERSONALITY),
                false,
                &mut tally,
            );
            let elf = parse_elf(&object);
            let homes: Vec<usize> = pair
                .iter()
                .map(|name| usize::from(elf.symbol(name).section))
                .collect();
            assert_ne!(homes[0], homes[1], "{label}: two COMDAT sections");
            for home in &homes {
                assert_eq!(elf.sections[*home].name, "probe_text", "{label}");
            }
            // Each function's FDE pc-begin names ITS section's anchor.
            let (eh_frame, _) = elf.section(".eh_frame").unwrap();
            let fields = eh_frame_fields(elf.data(".eh_frame"));
            let records = elf.relocations();
            for (name, home) in pair.iter().zip(&homes) {
                let index = functions
                    .iter()
                    .position(|function| function.name == *name)
                    .unwrap();
                let record = records
                    .iter()
                    .find(|record| {
                        record.section == eh_frame && record.offset == fields.pc_begin[index]
                    })
                    .unwrap_or_else(|| panic!("{label}: {name} pc-begin record"));
                assert_eq!(
                    record.target,
                    AArch64ElfRelocationTarget::Section(*home),
                    "{label}: {name} FDE anchored to its own section"
                );
            }
            shared_name_emissions += 1;

            // The personality becomes `tm_plain`, bound STB_LOCAL.
            let mut local = functions.clone();
            for function in &mut local {
                if function.eh_metadata.has_eh_info() {
                    function.eh_metadata.personality = Some("tm_plain".to_string());
                }
            }
            let bindings = local
                .iter()
                .map(|function| {
                    if function.name == "tm_plain" {
                        FunctionSymbolBinding::LOCAL
                    } else {
                        FunctionSymbolBinding::GLOBAL
                    }
                })
                .collect();
            check_emission(
                &format!("local-personality {level:?} {model}"),
                &pipeline,
                &local,
                &[],
                &layouts,
                &ModuleSymbolLinkage::new(bindings, BTreeSet::new()),
                Some("tm_plain"),
                true,
                &mut tally,
            );
        }
    }
    assert_eq!(shared_name_emissions, 12);
    println!(
        "EH_RELOC_INVENTORY_LINKAGE emissions={} unwind_rows={} shared_section_name={}",
        tally.emissions, tally.unwind_rows, shared_name_emissions
    );
}

/// A pointer-slot data global.
fn slot_global(name: &str, section: Option<&str>, target: &str) -> ObjectGlobal {
    ObjectGlobal {
        name: name.to_string(),
        data: vec![0; 16],
        mutable: true,
        is_external: true,
        symbol_refs: vec![trust_cg_codegen::pipeline::GlobalSymbolRef {
            offset: 8,
            symbol: target.to_string(),
            addend: 4,
        }],
        is_thread_local: false,
        is_import: false,
        is_weak: false,
        align: 8,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        section: section.map(str::to_string),
        comdat: false,
    }
}

/// A data global in an explicit section named like a personality slot
/// (`.data.DW.ref.probe`) is data, not an unwind row: with and without EH,
/// the cross-check matches the slot through the CIE's relocation and its
/// symbol, and the global's `R_AARCH64_ABS64` stays a data row.
#[test]
fn a_data_section_named_like_a_slot_is_not_an_unwind_row() {
    let mut tally = Tally::default();
    for (module, personality) in [
        (cxx_mixed_module(), Some(CXX_PERSONALITY)),
        (no_eh_module(), None),
    ] {
        for level in [OptLevel::O0, OptLevel::O2] {
            for model in MODELS {
                let pipeline = pipeline(LINUX, level, model);
                let (functions, layouts) = prepare(&pipeline, &module);
                let target = functions[0].name.clone();
                let globals = vec![slot_global(
                    "probe_table",
                    Some(".data.DW.ref.probe"),
                    &target,
                )];
                let label = format!("dw-ref-named data {} {level:?} {model}", module.name);
                let object = check_emission(
                    &label,
                    &pipeline,
                    &functions,
                    &globals,
                    &layouts,
                    &ModuleSymbolLinkage::default(),
                    personality,
                    false,
                    &mut tally,
                );
                let elf = parse_elf(&object);
                let home = usize::from(elf.symbol("probe_table").section);
                assert_eq!(elf.sections[home].name, ".data.DW.ref.probe", "{label}");
                let data_rows: Vec<_> = elf
                    .relocations()
                    .into_iter()
                    .filter(|record| record.section == home)
                    .collect();
                assert_eq!(data_rows.len(), 1, "{label}: the global's slot");
                assert_eq!(
                    (
                        data_rows[0].r_type,
                        data_rows[0].offset,
                        data_rows[0].addend
                    ),
                    (R_AARCH64_ABS64, 8, 4)
                );
            }
        }
    }
    println!("EH_RELOC_DWREF_NAMED_DATA emissions={}", tally.emissions);
}

/// The relocation inventory refuses a data global in a section the ELF
/// emitters own exactly as the emitter does (`[TCG-SECTION-RESERVED]`):
/// one placement classification serves both.
#[test]
fn reserved_unwind_sections_are_refused_alike_by_inventory_and_emitter() {
    let pipeline = pipeline(LINUX, OptLevel::O0, RelocationModel::Pie);
    for module in [cxx_mixed_module(), no_eh_module()] {
        let (functions, layouts) = prepare(&pipeline, &module);
        for section in [".eh_frame", ".gcc_except_table"] {
            let globals = vec![slot_global(
                "probe_table",
                Some(section),
                &functions[0].name,
            )];
            let emitted = pipeline
                .compile_module_with_globals_and_layouts(&functions, &globals, &layouts)
                .expect_err("the emitter refuses a reserved section")
                .to_string();
            let inventoried = pipeline
                .module_relocation_inventory_with_symbol_linkage(
                    &functions,
                    &globals,
                    &layouts,
                    &ModuleSymbolLinkage::default(),
                    "reserved.o",
                )
                .expect_err("the inventory refuses a reserved section")
                .to_string();
            assert_eq!(inventoried, emitted, "{section}");
            assert!(
                emitted.contains("TCG-SECTION-RESERVED") && emitted.contains(section),
                "{section}: {emitted}"
            );
        }
    }
}

/// No inventory report of an EH module is promotable, with or without its
/// rows: every exception-table row is `Unverified` (the tables carry no
/// proof obligation). A module without EH is reported as before.
#[test]
fn inventory_reports_never_promote_exception_tables() {
    let pipeline = pipeline(LINUX, OptLevel::O2, RelocationModel::Pie);
    for (module, has_eh) in [(cxx_mixed_module(), true), (no_eh_module(), false)] {
        let (functions, layouts) = prepare(&pipeline, &module);
        let full = pipeline
            .module_relocation_inventory_with_symbol_linkage(
                &functions,
                &[],
                &layouts,
                &ModuleSymbolLinkage::default(),
                "full.o",
            )
            .unwrap()
            .unwrap();
        let rows_less = pipeline
            .module_relocation_inventory_report_with_object_state(&functions, &[], &layouts, "r.o")
            .unwrap()
            .unwrap();
        let eh_rows = full
            .elf_unwind_rows
            .iter()
            .filter(|row| row.is_exception_table_row())
            .count();
        assert_eq!(eh_rows > 0, has_eh, "{}", module.name);
        for report in [&full.report, &rows_less] {
            let unverified = report.uncovered_relocations();
            assert_eq!(unverified.len(), eh_rows, "{}", module.name);
            assert_eq!(report.is_promotable(), !has_eh, "{}", module.name);
            for entry in unverified {
                assert!(
                    entry
                        .detail
                        .contains("exception tables carry no proof obligation"),
                    "{}",
                    entry.detail
                );
            }
        }
    }
}

/// The exact row cross-check `Compiler::compile` runs after emission fails
/// closed on every single-row disagreement, in either direction.
#[test]
fn unwind_row_crosscheck_fails_closed_on_any_disagreement() {
    let pipeline = pipeline(LINUX, OptLevel::O2, RelocationModel::Pie);
    let (functions, layouts) = prepare(&pipeline, &cxx_mixed_module());
    let rows = pipeline
        .module_relocation_inventory_with_symbol_linkage(
            &functions,
            &[],
            &layouts,
            &ModuleSymbolLinkage::default(),
            "crosscheck.o",
        )
        .unwrap()
        .unwrap()
        .elf_unwind_rows;
    let object = pipeline
        .compile_module_with_globals_and_layouts(&functions, &[], &layouts)
        .unwrap();
    crosscheck_aarch64_elf_unwind_relocation_rows(&object, &rows).expect("exact rows pass");
    let refused = |mutated: &[AArch64ElfUnwindRelocationRow], what: &str| {
        let error = crosscheck_aarch64_elf_unwind_relocation_rows(&object, mutated)
            .expect_err(what)
            .to_string();
        assert!(
            error.contains("inventory's mirrored rows"),
            "{what}: {error}"
        );
    };
    let mut mutants = 0;
    for index in 0..rows.len() {
        let mut dropped = rows.clone();
        dropped.remove(index);
        refused(&dropped, "a dropped row");
        let mut added = rows.clone();
        added.push(rows[index].clone());
        refused(&added, "a duplicated row");
        for alter in 0..4 {
            let mut altered = rows.clone();
            let row = &mut altered[index];
            match alter {
                0 => row.addend += 4,
                1 => row.offset += 4,
                2 => {
                    row.symbol = match &row.symbol {
                        AArch64ElfRelocationSymbol::Named(name) => {
                            AArch64ElfRelocationSymbol::Named(format!("{name}x"))
                        }
                        AArch64ElfRelocationSymbol::SectionAnchor(_) => {
                            AArch64ElfRelocationSymbol::SectionAnchor(
                                AArch64ElfSectionIdentity::Unique(".eh_frame".into()),
                            )
                        }
                    }
                }
                _ => row.r_type ^= 1,
            }
            refused(&altered, "an altered row");
        }
        mutants += 6;
    }
    // The object side: one record's addend changed.
    let elf = parse_elf(&object);
    let (_, rela) = elf.section(".rela.eh_frame").unwrap();
    let mut patched = object.clone();
    patched[rela.offset + 16] ^= 4;
    let error = crosscheck_aarch64_elf_unwind_relocation_rows(&patched, &rows)
        .expect_err("a changed emitted addend");
    assert!(error.to_string().contains("emitted but not inventoried"));
    // A mirror without the slot row still reads the slot the CIE points at.
    let without_slot: Vec<_> = rows
        .iter()
        .filter(|row| row.role != AArch64ElfUnwindRelocationRole::PersonalitySlot)
        .cloned()
        .collect();
    let error = crosscheck_aarch64_elf_unwind_relocation_rows(&object, &without_slot)
        .expect_err("an uninventoried DW.ref slot record")
        .to_string();
    let slot_section = usize::from(elf.symbol(&format!("DW.ref.{CXX_PERSONALITY}")).section);
    assert!(
        error.contains("emitted but not inventoried")
            && error.contains(&format!("section: {slot_section},")),
        "{error}"
    );
    println!(
        "EH_RELOC_CROSSCHECK rows={} mutants={} refused={}",
        rows.len(),
        mutants + 2,
        mutants + 2
    );
}

fn expect_eh_refusal(
    result: Result<impl std::fmt::Debug, PipelineError>,
    needle: &str,
    label: &str,
) {
    match result {
        Err(PipelineError::EhSidecarUnsupported {
            api: "module_relocation_inventory_report",
            reason,
            ..
        }) => assert!(reason.contains(needle), "{label}: {reason}"),
        other => panic!("{label}: expected a named EH inventory refusal, got {other:?}"),
    }
}

/// Mach-O EH stays refused by name ([TCG-REGALLOC-063]); a Mach-O module
/// without EH still gets its report.
#[test]
fn darwin_eh_inventory_stays_refused_by_name() {
    for level in LEVELS {
        let pipeline = pipeline(DARWIN, level, RelocationModel::Static);
        for module in [rust_cleanup_module(), cxx_catch_module()] {
            let (functions, layouts) = prepare(&pipeline, &module);
            expect_eh_refusal(
                pipeline.module_relocation_inventory_with_symbol_linkage(
                    &functions,
                    &[],
                    &layouts,
                    &ModuleSymbolLinkage::default(),
                    "darwin.o",
                ),
                "Mach-O (Darwin) EH object emission",
                &format!("{} {level:?}", module.name),
            );
        }
        let (functions, layouts) = prepare(&pipeline, &no_eh_module());
        pipeline
            .module_relocation_inventory_report_with_object_state(&functions, &[], &layouts, "d.o")
            .expect("a Mach-O module without EH is inventoried")
            .expect("report");
    }
}

/// Shapes outside the enumeration are refused by name, and the emitter
/// refuses the same modules.
#[test]
#[allow(clippy::result_large_err)] // Test helper returns the compiler's own error type unchanged.
fn unenumerated_eh_shapes_are_refused_by_name() {
    for level in LEVELS {
        let pipeline = pipeline(LINUX, level, RelocationModel::Pie);
        let (functions, layouts) = prepare(&pipeline, &cxx_mixed_module());
        let inventory = |functions: &[MachFunction], layouts: &[Option<FrameLayout>]| {
            pipeline.module_relocation_inventory_with_symbol_linkage(
                functions,
                &[],
                layouts,
                &ModuleSymbolLinkage::default(),
                "refused.o",
            )
        };

        // A second personality needs a second CIE and slot.
        let mut mixed = functions.clone();
        let cleanup = mixed
            .iter_mut()
            .find(|function| function.name == "tm_cleanup")
            .unwrap();
        cleanup.eh_metadata.personality = Some(RUST_PERSONALITY.to_string());
        expect_eh_refusal(
            inventory(&mixed, &layouts),
            "differs from",
            "two personalities",
        );
        assert!(
            pipeline
                .compile_module_with_globals_and_layouts(&mixed, &[], &layouts)
                .is_err()
        );

        // A typed catch needs a typeinfo relocation.
        let mut typed = functions.clone();
        let catch = typed
            .iter_mut()
            .find(|function| function.name == "tm_catch")
            .unwrap();
        catch.eh_metadata.landing_pads[0].catch_type_indices = vec![3];
        expect_eh_refusal(inventory(&typed, &layouts), "typed catch", "typed catch");
        assert!(
            pipeline
                .compile_module_with_globals_and_layouts(&typed, &[], &layouts)
                .is_err()
        );

        // Every function of an EH module needs an FDE, so a frame layout.
        let mut partial = layouts.clone();
        partial[0] = None;
        for missing in [&partial[..], &[][..]] {
            expect_eh_refusal(inventory(&functions, missing), "frame layout", "no layouts");
            assert!(
                pipeline
                    .compile_module_with_globals_and_layouts(&functions, &[], missing)
                    .is_err()
            );
        }
    }
}

/// A certified (proof-required) compile of a module with exception-handling
/// structure is refused at the promotion gate by name — exception tables
/// carry no proof obligation (TB-12) — before any certificate check, at every
/// level and model, on AArch64 ELF and x86-64 Mach-O. The relocation inventory itself no longer refuses it.
/// This does not depend on the frame's pair opcodes (L07-P2): the refusal
/// comes first, so it stays when they gain proofs. Without a proof request
/// the same modules compile.
#[test]
fn eh_module_with_certificates_is_refused_for_unproved_exception_tables() {
    let spec = trust_cg_codegen::target::TargetSpec::parse(LINUX).expect("triple");
    let mut refusals = 0;
    for (module, first) in [
        (single_eh_module(), "ts_cleanup"),
        (rust_cleanup_module(), "tr_cleanup"),
        (cxx_mixed_module(), "tm_catch"),
    ] {
        let module = pinned_target::pinned(&module, LINUX);
        for level in [OptLevel::O0, OptLevel::O2] {
            for model in MODELS {
                let compiler = |emit_proofs| {
                    Compiler::new_for_target_spec(
                        CompilerConfig {
                            opt_level: level,
                            relocation_model: model,
                            emit_proofs,
                            ..CompilerConfig::default()
                        },
                        spec,
                    )
                    .with_codegen_license(permit_unlicensed())
                };
                let label = format!("{} {level:?} {model}", module.name);
                match compiler(true).compile(&module) {
                    Err(CompileError::ExceptionTablesUnproved { function, .. }) => {
                        assert_eq!(function, first, "{label}")
                    }
                    Err(other) => panic!("{label}: expected the EH-evidence refusal, got {other}"),
                    Ok(_) => panic!("{label}: an object with exception tables promoted"),
                }
                compiler(false)
                    .compile(&module)
                    .unwrap_or_else(|error| panic!("{label} without proofs: {error}"));
                refusals += 1;
            }
        }
    }
    // The x86-64 Mach-O object route (whose inventory enumerates its EH
    // rows) goes through the same gate.
    let darwin_x86 = trust_cg_codegen::target::TargetSpec::parse("x86_64-apple-darwin")
        .expect("x86-64 Mach-O triple");
    for module in [single_eh_module(), rust_cleanup_module()] {
        let module = pinned_target::pinned(&module, "x86_64-apple-darwin");
        let x86 = |emit_proofs| {
            Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level: OptLevel::O0,
                    target: trust_cg_codegen::Target::X86_64,
                    emit_proofs,
                    ..CompilerConfig::default()
                },
                darwin_x86,
            )
            .with_codegen_license(permit_unlicensed())
        };
        match x86(true).compile(&module) {
            Err(CompileError::ExceptionTablesUnproved { target, .. }) => {
                assert_eq!(target, trust_cg_codegen::Target::X86_64)
            }
            Err(other) => panic!(
                "x86-64 {}: expected the EH-evidence refusal, got {other}",
                module.name
            ),
            Ok(_) => panic!(
                "x86-64 {}: an object with exception tables promoted",
                module.name
            ),
        }
        x86(false)
            .compile(&module)
            .unwrap_or_else(|error| panic!("x86-64 {} without proofs: {error}", module.name));
        refusals += 1;
    }
    let message = CompileError::ExceptionTablesUnproved {
        target: trust_cg_codegen::Target::Aarch64,
        function: "f".to_string(),
        walk_through: false,
    }
    .to_string();
    assert!(
        message.contains("[TCG-EH-UNPROVED]")
            && message.contains("exception tables carry no proof obligation"),
        "{message}"
    );
    println!("EH_PROOF_PROMOTION refusals={refusals} diagnostic=[TCG-EH-UNPROVED]");
}

/// `x -> cxx_callee(x)`: a framed function with no EH structure of its own.
fn pass_through_module() -> Module {
    let mut module = Module::new("eh_inventory_pass_through");
    declare(&mut module, 0, "cxx_callee", vec![Ty::I32], vec![Ty::I32]);
    plain_function(&mut module, 1, "tp_pass_through", 0);
    module
}

/// A single leaf (`x + 1`, no call): frameless on AArch64, but the x86-64
/// object pipeline lowers every function with a frame.
fn leaf_module() -> Module {
    let mut module = Module::new("eh_inventory_leaf");
    leaf_function(&mut module, 0, "tl_leaf");
    module
}

/// Whether an object carries exception tables: an LSDA section (ELF
/// `.gcc_except_table`, Mach-O `__gcc_except_tab`) or a personality name.
fn carries_exception_tables(object: &[u8]) -> bool {
    [
        &b".gcc_except_table"[..],
        b"__gcc_except_tab",
        b"rust_eh_personality",
        b"__gxx_personality_v0",
    ]
    .iter()
    .any(|needle| object.windows(needle.len()).any(|window| window == *needle))
}

fn object_compiler(
    triple: &str,
    level: OptLevel,
    emit_proofs: bool,
    panic_unwind: bool,
) -> Compiler {
    let target = if triple.starts_with("x86_64") {
        trust_cg_codegen::Target::X86_64
    } else {
        trust_cg_codegen::Target::Aarch64
    };
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: level,
            target,
            emit_proofs,
            panic_unwind,
            ..CompilerConfig::default()
        },
        trust_cg_codegen::target::TargetSpec::parse(triple).expect("triple"),
    )
    .with_codegen_license(permit_unlicensed())
}

/// A certified compile is refused with `[TCG-EH-UNPROVED]` exactly when the
/// object the same compile emits without certificates carries exception
/// tables — including the x86-64 walk-through filler tables that
/// `panic=unwind` gives every framed function with no EH of its own (Mach-O)
/// or every function of the module (ELF) — and
/// otherwise never on their account. On AArch64 (ELF and Mach-O) the object
/// emitters do not read `panic_unwind`: the object is byte-identical with and
/// without it and carries no exception table, so a change that starts
/// emitting filler tables there must also teach the census about them.
#[test]
fn certified_refusal_matches_the_exception_tables_the_object_carries() {
    let mut refused = BTreeSet::new();
    let mut admitted = BTreeSet::new();
    for triple in [
        "x86_64-apple-darwin",
        "x86_64-unknown-linux-gnu",
        "aarch64-apple-darwin",
        "aarch64-unknown-linux-gnu",
    ] {
        for module in [pass_through_module(), leaf_module(), single_eh_module()] {
            let module = pinned_target::pinned(&module, triple);
            for level in [OptLevel::O0, OptLevel::O2] {
                let mut plain_objects = Vec::new();
                for panic_unwind in [false, true] {
                    let label = format!(
                        "{triple} {} {level:?} panic_unwind={panic_unwind}",
                        module.name
                    );
                    let object = object_compiler(triple, level, false, panic_unwind)
                        .compile(&module)
                        .unwrap_or_else(|error| panic!("{label} without proofs: {error}"))
                        .object_code;
                    let tables = carries_exception_tables(&object);
                    let certified =
                        object_compiler(triple, level, true, panic_unwind).compile(&module);
                    match (tables, certified) {
                        (
                            true,
                            Err(
                                error @ CompileError::ExceptionTablesUnproved {
                                    walk_through, ..
                                },
                            ),
                        ) => {
                            // A module without EH structure of its own gets
                            // only walk-through tables, and the refusal says so.
                            let own_eh = module.name == "eh_inventory_single";
                            assert_eq!(walk_through, !own_eh, "{label}: {error}");
                            assert_eq!(
                                error.to_string().contains("walk-through exception tables"),
                                !own_eh,
                                "{label}: {error}"
                            );
                            refused.insert(label);
                        }
                        (true, other) => panic!(
                            "{label}: the object carries exception tables but the certified \
                             compile returned {:?}",
                            other.map(|_| "a promoted object")
                        ),
                        (false, Err(CompileError::ExceptionTablesUnproved { function, .. })) => {
                            panic!("{label}: refused `{function}` without exception tables")
                        }
                        (false, _) => {
                            admitted.insert(label);
                        }
                    }
                    plain_objects.push(object);
                }
                if triple.starts_with("aarch64") {
                    assert_eq!(
                        plain_objects[0], plain_objects[1],
                        "{triple} {} {level:?}: AArch64 objects must not depend on panic_unwind",
                        module.name
                    );
                }
            }
        }
    }
    // The x86-64 pass-through under panic=unwind is the walk-through filler
    // case (Mach-O filler pass, ELF unwind planner); without panic=unwind the
    // same object carries no table.
    for triple in ["x86_64-apple-darwin", "x86_64-unknown-linux-gnu"] {
        for level in ["O0", "O2"] {
            assert!(refused.contains(&format!(
                "{triple} eh_inventory_pass_through {level} panic_unwind=true"
            )));
            assert!(admitted.contains(&format!(
                "{triple} eh_inventory_pass_through {level} panic_unwind=false"
            )));
        }
    }
    println!(
        "EH_CENSUS_MATCHES_OBJECTS refused={} admitted={}",
        refused.len(),
        admitted.len()
    );
}

/// Certified compiles with exception-handling structure are refused by the
/// census before the relocation inventory runs: on AArch64 Mach-O (whose
/// inventory refuses EH by name) and for a typed catch on ELF (which the
/// inventory also refuses), the diagnostic is `[TCG-EH-UNPROVED]`, not the
/// inventory's `EhSidecarUnsupported`. The typed catch is bound through the
/// module's EH type table, so lowering admits it and the census, not the
/// adapter's unbound-index refusal (`[TCG-EH-TTYPE]`), answers first.
#[test]
fn the_census_gate_runs_before_the_inventory() {
    let mut typed = Module::new("eh_inventory_typed_catch");
    declare(&mut typed, 0, "cxx_callee", vec![Ty::I32], vec![Ty::I32]);
    declare(&mut typed, 1, "cxx_caught", vec![Ty::I32], vec![]);
    catch_all_function(&mut typed, 2, "tt_typed", 0, 1);
    let pointer = typed
        .add_type(Ty::Ptr)
        .expect("Module::add_type: test fixture");
    typed.globals.push(trust_ir::Global {
        name: trust_cg_lower::function::EH_TYPE_TABLE_GLOBAL.to_string(),
        ty: Ty::Array(pointer, 3),
        mutable: false,
        initializer: Some(Constant::Array(
            ["_ZTIi", "_ZTId", "_ZTIc"]
                .into_iter()
                .map(|symbol| Constant::SymbolAddr {
                    symbol: symbol.to_string(),
                    addend: 0,
                })
                .collect(),
        )),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    for function in &mut typed.functions {
        for block in &mut function.blocks {
            for node in &mut block.body {
                if let Inst::LandingPad {
                    catch_type_indices, ..
                } = &mut node.inst
                {
                    *catch_type_indices = vec![3];
                }
            }
        }
    }
    for (triple, module, first) in [
        ("aarch64-apple-darwin", single_eh_module(), "ts_cleanup"),
        ("aarch64-apple-darwin", cxx_mixed_module(), "tm_catch"),
        ("aarch64-unknown-linux-gnu", typed, "tt_typed"),
    ] {
        let module = pinned_target::pinned(&module, triple);
        for level in LEVELS {
            match object_compiler(triple, level, true, false).compile(&module) {
                Err(CompileError::ExceptionTablesUnproved { function, .. }) => {
                    assert_eq!(function, first, "{triple} {} {level:?}", module.name)
                }
                other => panic!(
                    "{triple} {} {level:?}: expected [TCG-EH-UNPROVED], got {:?}",
                    module.name,
                    other.map(|_| "a promoted object")
                ),
            }
        }
    }
}

/// The inventory of an AArch64 object with unwind tables states that their
/// content is trusted, not proven — the `.eh_frame` FDEs on ELF, the
/// compact-unwind entries (and DWARF-fallback FDEs) on Mach-O — and the
/// relocation-inventory certificate repeats that sentence (the certificate
/// builder is pinned by `inventory_certificate_discloses_trusted_unwind_cfi`
/// in the library tests: no AArch64 function with a frame promotes today, so
/// no certified object carries it end to end yet).
#[test]
fn aarch64_inventories_disclose_trusted_unwind_tables() {
    for (triple, expected) in [
        (
            "aarch64-unknown-linux-gnu",
            [
                "unwind CFI of 1 .eh_frame FDE(s)",
                "unwind CFI of 2 .eh_frame FDE(s)",
            ],
        ),
        (
            "aarch64-apple-darwin",
            [
                "compact unwind of 1 function(s), 0 with a DWARF-fallback",
                "compact unwind of 2 function(s), 0 with a DWARF-fallback",
            ],
        ),
    ] {
        for (module, expected) in [leaf_module(), no_eh_module()].into_iter().zip(expected) {
            let pipeline = pipeline(triple, OptLevel::O2, RelocationModel::Static);
            let (functions, layouts) = prepare(&pipeline, &module);
            let inventory = pipeline
                .module_relocation_inventory_with_symbol_linkage(
                    &functions,
                    &[],
                    &layouts,
                    &ModuleSymbolLinkage::default(),
                    "disclosure.o",
                )
                .unwrap()
                .unwrap();
            let disclosure = inventory.trusted_unwind_tables.expect("unwind tables");
            assert!(
                disclosure.starts_with(expected)
                    && disclosure.contains("TB-12")
                    && disclosure.contains("no proof obligation"),
                "{triple} {}: {disclosure}",
                module.name
            );
            // Without frame layouts there are no unwind tables to disclose.
            let bare = pipeline
                .module_relocation_inventory_with_symbol_linkage(
                    &functions,
                    &[],
                    &[],
                    &ModuleSymbolLinkage::default(),
                    "bare.o",
                )
                .unwrap()
                .unwrap();
            assert_eq!(bare.trusted_unwind_tables, None, "{triple} {}", module.name);
        }
    }
}

/// Malformed exception-handling structure keeps its structural diagnostic
/// under certificates, never hidden behind `[TCG-EH-UNPROVED]`: the
/// structural validation refuses it with the same message whether or not
/// proofs are requested. Two shapes: a landing pad that no invoke reaches,
/// and a well-formed EH function beside a function whose `Resume` has no EH
/// metadata (the census would otherwise name the well-formed function).
///
/// Since WS7.3 that structural diagnostic is trust-ir's own: ingestion
/// admission refuses both modules before lowering, naming the
/// `MisplacedLandingPad` finding (trust-ir's unwind-structure rule), with the
/// same text under certificates.
#[test]
fn malformed_eh_structure_keeps_its_diagnostic_when_certified() {
    let mut orphan = Module::new("eh_inventory_orphan_pad");
    declare(&mut orphan, 0, "cxx_callee", vec![Ty::I32], vec![Ty::I32]);
    declare(&mut orphan, 1, "cxx_cleanup", vec![Ty::I32], vec![]);
    let orphan_pad = vec![
        InstrNode::new(Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        })
        .with_results(vec![v(20), v(21)]),
        InstrNode::new(Inst::Resume { exn: v(20) }),
    ];
    define(
        &mut orphan,
        2,
        "to_orphan",
        vec![
            block(0, vec![(v(0), Ty::I32)], vec![ret(0)]),
            block(2, vec![], orphan_pad),
        ],
    );
    let mut resume_only = Module::new("eh_inventory_good_eh_plus_resume_only");
    declare(
        &mut resume_only,
        0,
        "cxx_callee",
        vec![Ty::I32],
        vec![Ty::I32],
    );
    declare(&mut resume_only, 1, "cxx_cleanup", vec![Ty::I32], vec![]);
    cleanup_function(&mut resume_only, 2, "ta_good_eh", 0, 1);
    define(
        &mut resume_only,
        3,
        "tb_resume_only",
        vec![block(
            0,
            vec![(v(0), Ty::I32)],
            vec![InstrNode::new(Inst::Resume { exn: v(0) })],
        )],
    );
    for module in [&mut orphan, &mut resume_only] {
        module.target_info = Some(trust_ir::TargetInfo {
            triple: "aarch64-unknown-linux-gnu".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        });
    }
    let mut checked = 0;
    for module in [&orphan, &resume_only] {
        for triple in [
            "aarch64-unknown-linux-gnu",
            "aarch64-apple-darwin",
            "x86_64-apple-darwin",
            "x86_64-unknown-linux-gnu",
        ] {
            let plain = object_compiler(triple, OptLevel::O0, false, false)
                .compile(module)
                .map(|_| ())
                .expect_err("malformed EH structure");
            let certified = object_compiler(triple, OptLevel::O0, true, false)
                .compile(module)
                .map(|_| ())
                .expect_err("malformed EH structure");
            assert!(
                !matches!(certified, CompileError::ExceptionTablesUnproved { .. }),
                "{triple}: {certified}"
            );
            match &plain {
                CompileError::InvalidTrustIr(refusal) => assert!(
                    refusal.any(|finding| matches!(
                        finding,
                        trust_ir_build::ValidationError::MisplacedLandingPad { .. }
                    )),
                    "{triple}: {plain}"
                ),
                other => panic!("{triple}: expected trust-ir's structural refusal, got {other}"),
            }
            assert_eq!(certified.to_string(), plain.to_string(), "{triple}");
            checked += 1;
        }
    }
    println!("EH_MALFORMED_KEEPS_DIAGNOSTIC cases={checked}");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

/// `translate_module` under [`permit_unlicensed`].
fn permit_translate_module(
    module: &trust_ir::Module,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}
