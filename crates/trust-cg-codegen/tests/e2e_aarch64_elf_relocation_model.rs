// trust-cg-codegen/tests/e2e_aarch64_elf_relocation_model.rs - AArch64 ELF
// relocation models: preemptible-definition GOT access and TLS model selection.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Ground truth (clang --target=aarch64-linux-gnu -fPIC -O1 -c, llvm-objdump -dr):
//
//   __thread long tv = 5;       long *addr_tv(void) { return &tv; }
//     adrp x0, 0            R_AARCH64_TLSDESC_ADR_PAGE21 tv   90000000
//     ldr  x1, [x0]         R_AARCH64_TLSDESC_LD64_LO12  tv   f9400001
//     add  x0, x0, #0x0     R_AARCH64_TLSDESC_ADD_LO12   tv   91000000
//     blr  x1               R_AARCH64_TLSDESC_CALL       tv   d63f0020
//     mrs  x8, TPIDR_EL0                                      d53bd048
//     add  x0, x8, x0                                         8b000100
//   long g = 7;                 long *addr_g(void) { return &g; }
//     adrp x0, 0            R_AARCH64_ADR_GOT_PAGE      g
//     ldr  x0, [x0]         R_AARCH64_LD64_GOT_LO12_NC  g
//   __attribute__((visibility("hidden"))) long h;  &h
//     adrp x0, 0            R_AARCH64_ADR_PREL_PG_HI21  h
//     add  x0, x0, #0x0     R_AARCH64_ADD_ABS_LO12_NC   h
//   long f(long);               &f  -> ADR_GOT_PAGE / LD64_GOT_LO12_NC f
//
// The object tests below run on every host with an independent ELF64 reader
// and independent instruction-word decoding (no production relocation enums
// or encoder helpers). The Linux-native tests (cfg linux/gnu) build a CG
// shared object with preemptible data, functions and TLS, `dlopen` it from a
// C driver, exercise it from several threads, and check interposition by the
// executable at O0-O3. They are bounded runtime checks, not a dynamic-linker
// or concurrency proof.

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use trust_cg_codegen::pipeline::{
    FunctionSymbolBinding, FunctionSymbolLinkage, GlobalSymbolRef, ObjectGlobal, OptLevel,
    Pipeline, PipelineConfig,
};
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{CompileError, Compiler, CompilerConfig, RelocationModel};
use trust_ir::value::GlobalId;
use trust_ir::{
    BinOp, Block, BlockId, Constant, Endianness, FuncId, FuncTy, Function, Global, Inst, InstrNode,
    Linkage, Module, StructPassingPolicy, TargetInfo, TlsModel, Ty, ValueId, Visibility,
};

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const LINUX: &str = "aarch64-unknown-linux-gnu";

// ELF for the Arm 64-bit Architecture (IHI 0056), relocation codes.
const R_CALL26: u32 = 283;
const R_JUMP26: u32 = 282;
const R_ADR_PREL_PG_HI21: u32 = 275;
const R_ADD_ABS_LO12_NC: u32 = 277;
const R_ADR_GOT_PAGE: u32 = 311;
const R_LD64_GOT_LO12_NC: u32 = 312;
const R_TLSIE_ADR_GOTTPREL_PAGE21: u32 = 0x21d;
const R_TLSIE_LD64_GOTTPREL_LO12_NC: u32 = 0x21e;
const R_TLSLE_ADD_TPREL_HI12: u32 = 0x225;
const R_TLSLE_ADD_TPREL_LO12_NC: u32 = 0x227;
const R_TLSDESC_ADR_PAGE21: u32 = 0x232;
const R_TLSDESC_LD64_LO12: u32 = 0x233;
const R_TLSDESC_ADD_LO12: u32 = 0x234;
const R_TLSDESC_CALL: u32 = 0x239;

const STT_TLS: u8 = 6;
const STV_DEFAULT: u8 = 0;
const STV_HIDDEN: u8 = 2;
const STV_PROTECTED: u8 = 3;

// Canonical TLSDESC words (clang ground truth above).
const TLSDESC_WORDS: [u32; 4] = [0x9000_0000, 0xf940_0001, 0x9100_0000, 0xd63f_0020];
const TLSDESC_KINDS: [u32; 4] = [
    R_TLSDESC_ADR_PAGE21,
    R_TLSDESC_LD64_LO12,
    R_TLSDESC_ADD_LO12,
    R_TLSDESC_CALL,
];

// ---------------------------------------------------------------------------
// Fixture module
// ---------------------------------------------------------------------------

/// Global table of the fixture: `(name, linkage, visibility, defined, tls)`.
const GLOBALS: [(&str, Linkage, Visibility, bool, bool); 7] = [
    (
        "rm_pub_data",
        Linkage::External,
        Visibility::Default,
        true,
        false,
    ),
    (
        "rm_hid_data",
        Linkage::External,
        Visibility::Hidden,
        true,
        false,
    ),
    (
        "rm_prot_data",
        Linkage::External,
        Visibility::Protected,
        true,
        false,
    ),
    (
        "rm_loc_data",
        Linkage::Internal,
        Visibility::Default,
        true,
        false,
    ),
    (
        "rm_ext_data",
        Linkage::External,
        Visibility::Default,
        false,
        false,
    ),
    (
        "rm_tls_def",
        Linkage::External,
        Visibility::Default,
        true,
        true,
    ),
    (
        "rm_tls_imp",
        Linkage::External,
        Visibility::Default,
        false,
        true,
    ),
];

/// Initial value of the defined global at `index` (distinct per global).
fn initial_value(index: usize) -> u64 {
    0x5eed_0000_0000_0000 | ((index as u64 + 1) * 0x1111)
}

fn u64_value(value: u64) -> Constant {
    Constant::Int(value.into())
}

/// ```c
/// uint64_t rm_pub_data = ..., rm_hid_data (hidden), rm_prot_data (protected);
/// static uint64_t rm_loc_data = ...;  extern uint64_t rm_ext_data;
/// __thread uint64_t rm_tls_def = ...; extern __thread uint64_t rm_tls_imp;
/// uint64_t rm_pub_fn(uint64_t x) { return x * 3 + 7; }
/// uint64_t rm_call_pub_fn(uint64_t x) { return rm_pub_fn(x); }
/// uint64_t (*rm_addr_pub_fn(void))(uint64_t) { return rm_pub_fn; }
/// uint64_t *rm_addr_<global>(void) { return &<global>; }   // every global
/// ```
fn fixture() -> Module {
    let mut module = Module::new("relocation_model");
    module.target_info = Some(TargetInfo {
        triple: LINUX.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    module.globals = GLOBALS
        .iter()
        .enumerate()
        .map(
            |(index, &(name, linkage, visibility, defined, tls))| Global {
                section: None,
                visibility,
                retained: false,
                name: name.into(),
                ty: Ty::U64,
                mutable: true,
                initializer: defined.then(|| u64_value(initial_value(index))),
                linkage,
                tls: tls.then_some(TlsModel::GeneralDynamic),
                align: Some(8),
            },
        )
        .collect();

    let unary = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let pub_fn_id = FuncId::new(0);
    let mut pub_fn = Function::new(pub_fn_id, "rm_pub_fn", unary, BlockId::new(0));
    pub_fn.linkage = Linkage::External;
    pub_fn.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::U64)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(3),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::U64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(7),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U64,
                lhs: ValueId::new(2),
                rhs: ValueId::new(3),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(4)],
            }),
        ],
    }];
    module
        .try_add_function(pub_fn)
        .expect("Module::try_add_function: test fixture");

    let mut call = Function::new(FuncId::new(1), "rm_call_pub_fn", unary, BlockId::new(0));
    call.linkage = Linkage::External;
    call.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::U64)],
        body: vec![
            InstrNode::new(Inst::Call {
                callee: pub_fn_id,
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module
        .try_add_function(call)
        .expect("Module::try_add_function: test fixture");

    let nullary_ptr = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let nullary_fn = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Func(unary)],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut addr_fn = Function::new(
        FuncId::new(2),
        "rm_addr_pub_fn",
        nullary_fn,
        BlockId::new(0),
    );
    addr_fn.linkage = Linkage::External;
    addr_fn.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Func(unary),
                value: Constant::FnDef(pub_fn_id),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }),
        ],
    }];
    module
        .try_add_function(addr_fn)
        .expect("Module::try_add_function: test fixture");

    for (index, (name, ..)) in GLOBALS.iter().enumerate() {
        let id = FuncId::new(module.functions.len() as u32);
        let mut getter = Function::new(
            id,
            format!("rm_addr_{}", &name[3..]),
            nullary_ptr,
            BlockId::new(0),
        );
        getter.linkage = Linkage::External;
        getter.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::GlobalAddr {
                    global: GlobalId::new(index as u32),
                })
                .with_result(ValueId::new(0)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(0)],
                }),
            ],
        }];
        module
            .try_add_function(getter)
            .expect("Module::try_add_function: test fixture");
    }
    module
}

fn compiler(opt_level: OptLevel, relocation_model: RelocationModel, triple: &str) -> Compiler {
    let target_spec = TargetSpec::parse(triple).expect("supported target triple");
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            target: target_spec.architecture,
            parallel: false,
            relocation_model,
            ..CompilerConfig::default()
        },
        target_spec,
    )
    .with_codegen_license(permit_unlicensed())
}

fn compile(opt_level: OptLevel, relocation_model: RelocationModel) -> Vec<u8> {
    compiler(opt_level, relocation_model, LINUX)
        .compile(&fixture())
        .unwrap_or_else(|error| panic!("{relocation_model} {opt_level:?}: {error}"))
        .object_code
}

// ---------------------------------------------------------------------------
// Independent ELF64 little-endian reader (fixed trusted test input)
// ---------------------------------------------------------------------------

fn u16le(b: &[u8], off: usize) -> u16 {
    u16::from_le_bytes([b[off], b[off + 1]])
}
fn u32le(b: &[u8], off: usize) -> u32 {
    u32::from_le_bytes(b[off..off + 4].try_into().unwrap())
}
fn u64le(b: &[u8], off: usize) -> u64 {
    u64::from_le_bytes(b[off..off + 8].try_into().unwrap())
}

#[derive(Debug, Clone)]
struct Section {
    name: String,
    sh_type: u32,
    offset: usize,
    size: usize,
    link: u32,
    info: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Symbol {
    name: String,
    info: u8,
    other: u8,
    shndx: u16,
    value: u64,
    size: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Rela {
    offset: u64,
    kind: u32,
    symbol: u32,
    addend: i64,
}

struct Object {
    bytes: Vec<u8>,
    sections: Vec<Section>,
    symbols: Vec<Symbol>,
    text_index: usize,
    text_relocs: Vec<Rela>,
}

fn cstr(bytes: &[u8], offset: usize) -> String {
    let end = bytes[offset..].iter().position(|&c| c == 0).unwrap() + offset;
    String::from_utf8_lossy(&bytes[offset..end]).into_owned()
}

fn parse(bytes: &[u8]) -> Object {
    assert_eq!(&bytes[..6], b"\x7fELF\x02\x01", "ELF64 little-endian");
    assert_eq!(u16le(bytes, 16), 1, "ET_REL");
    assert_eq!(u16le(bytes, 18), 183, "EM_AARCH64");
    let shoff = u64le(bytes, 0x28) as usize;
    let shentsize = u16le(bytes, 0x3a) as usize;
    let shnum = u16le(bytes, 0x3c) as usize;
    let shstrndx = u16le(bytes, 0x3e) as usize;
    let shstr = u64le(bytes, shoff + shstrndx * shentsize + 0x18) as usize;
    let sections: Vec<Section> = (0..shnum)
        .map(|index| {
            let header = shoff + index * shentsize;
            Section {
                name: cstr(bytes, shstr + u32le(bytes, header) as usize),
                sh_type: u32le(bytes, header + 4),
                offset: u64le(bytes, header + 0x18) as usize,
                size: u64le(bytes, header + 0x20) as usize,
                link: u32le(bytes, header + 0x28),
                info: u32le(bytes, header + 0x2c),
            }
        })
        .collect();
    let symtab = sections
        .iter()
        .find(|section| section.sh_type == 2)
        .expect("SHT_SYMTAB");
    let strtab = &sections[symtab.link as usize];
    let symbols = (0..symtab.size / 24)
        .map(|index| {
            let entry = symtab.offset + index * 24;
            Symbol {
                name: cstr(bytes, strtab.offset + u32le(bytes, entry) as usize),
                info: bytes[entry + 4],
                other: bytes[entry + 5],
                shndx: u16le(bytes, entry + 6),
                value: u64le(bytes, entry + 8),
                size: u64le(bytes, entry + 16),
            }
        })
        .collect();
    let text_index = sections
        .iter()
        .position(|section| section.name == ".text")
        .expect(".text");
    let mut text_relocs = Vec::new();
    for section in sections.iter().filter(|section| section.sh_type == 4) {
        if section.info as usize != text_index {
            continue;
        }
        for index in 0..section.size / 24 {
            let entry = section.offset + index * 24;
            let info = u64le(bytes, entry + 8);
            text_relocs.push(Rela {
                offset: u64le(bytes, entry),
                kind: (info & 0xffff_ffff) as u32,
                symbol: (info >> 32) as u32,
                addend: u64le(bytes, entry + 16) as i64,
            });
        }
    }
    text_relocs.sort();
    Object {
        bytes: bytes.to_vec(),
        sections,
        symbols,
        text_index,
        text_relocs,
    }
}

impl Object {
    fn text(&self) -> &[u8] {
        let text = &self.sections[self.text_index];
        &self.bytes[text.offset..text.offset + text.size]
    }

    fn word(&self, offset: u64) -> u32 {
        u32le(self.text(), offset as usize)
    }

    fn symbol(&self, name: &str) -> &Symbol {
        let matches: Vec<_> = self
            .symbols
            .iter()
            .filter(|symbol| symbol.name == name)
            .collect();
        assert_eq!(matches.len(), 1, "exactly one `{name}` symbol");
        matches[0]
    }

    /// `(kind, target symbol name)` of every text relocation inside function
    /// `name`'s `[value, value + size)` range, in offset order.
    fn function_relocs(&self, name: &str) -> Vec<(u32, String)> {
        let function = self.symbol(name);
        assert_eq!(
            function.shndx as usize, self.text_index,
            "`{name}` is defined in .text"
        );
        self.text_relocs
            .iter()
            .filter(|rela| {
                rela.offset >= function.value && rela.offset < function.value + function.size
            })
            .map(|rela| {
                assert_eq!(rela.addend, 0, "`{name}` relocation addends are zero");
                (rela.kind, self.symbols[rela.symbol as usize].name.clone())
            })
            .collect()
    }
}

fn pairs(kinds: &[u32], symbol: &str) -> Vec<(u32, String)> {
    kinds
        .iter()
        .map(|&kind| (kind, symbol.to_owned()))
        .collect()
}

// ---------------------------------------------------------------------------
// Independent TLSDESC sequence validator
// ---------------------------------------------------------------------------

/// Validate one TLSDESC access in `object` starting at the ADRP relocated by
/// `R_AARCH64_TLSDESC_ADR_PAGE21` at `start`: the four canonical words, the
/// four relocations on consecutive slots against one STT_TLS symbol with zero
/// addends, and a thread-pointer add that consumes the resolver's x0 result.
fn validate_tlsdesc_access(object: &Object, start: u64, symbol: &str) -> Result<(), String> {
    if !start.is_multiple_of(4) {
        return Err(format!(
            "TLSDESC site {start:#x} is not instruction-aligned"
        ));
    }
    let text_len = object.text().len() as u64;
    if start + 16 > text_len {
        return Err("TLSDESC site runs past .text".into());
    }
    for (slot, (&want_word, &want_kind)) in TLSDESC_WORDS.iter().zip(&TLSDESC_KINDS).enumerate() {
        let offset = start + 4 * slot as u64;
        let word = object.word(offset);
        if word != want_word {
            return Err(format!(
                "slot {slot} word {word:#010x} != canonical {want_word:#010x}"
            ));
        }
        let relocs: Vec<_> = object
            .text_relocs
            .iter()
            .filter(|rela| rela.offset == offset)
            .collect();
        if relocs.len() != 1 {
            return Err(format!("slot {slot} carries {} relocations", relocs.len()));
        }
        let rela = relocs[0];
        if rela.kind != want_kind || rela.addend != 0 {
            return Err(format!(
                "slot {slot} relocation kind {:#x} addend {} (want {want_kind:#x}, 0)",
                rela.kind, rela.addend
            ));
        }
        let target = &object.symbols[rela.symbol as usize];
        if target.name != symbol || target.info & 0xf != STT_TLS {
            return Err(format!(
                "slot {slot} targets `{}` (type {}), want STT_TLS `{symbol}`",
                target.name,
                target.info & 0xf
            ));
        }
    }
    // After the call x0 holds TPREL(sym). Follow it through register moves
    // (`ORR Xd, XZR, Xm`) to an `ADD Xd, Xt, Xo` whose other input is a
    // `MRS Xt, TPIDR_EL0` result.
    let mut offset_regs = vec![0u32];
    let mut thread_reg = None;
    for index in 0..8 {
        let at = start + 16 + 4 * index;
        if at + 4 > text_len {
            break;
        }
        let word = object.word(at);
        let rd = word & 31;
        let rn = (word >> 5) & 31;
        let rm = (word >> 16) & 31;
        if word & 0xffff_ffe0 == 0xd53b_d040 {
            if rd == 31 {
                return Err("TPIDR_EL0 read discards its result".into());
            }
            offset_regs.retain(|&reg| reg != rd);
            thread_reg = Some(rd);
        } else if word & 0xffe0_ffe0 == 0xaa00_03e0 && offset_regs.contains(&rm) {
            offset_regs.push(rd);
        } else if word & 0xffe0_fc00 == 0x8b00_0000 {
            let Some(tp) = thread_reg else {
                continue;
            };
            let consumes =
                (rn == tp && offset_regs.contains(&rm)) || (rm == tp && offset_regs.contains(&rn));
            if consumes && rd != 31 {
                return Ok(());
            }
        } else if word & 0x1f == 0 && offset_regs.contains(&0) && word >> 24 != 0xd6 {
            // Any other instruction that writes x0 kills the offset held there.
            offset_regs.retain(|&reg| reg != 0);
        }
    }
    Err("no TP + TLSDESC-offset add follows the resolver call".into())
}

/// Every TLSDESC access in function `function`: validated and counted.
fn tlsdesc_accesses(object: &Object, function: &str, symbol: &str) -> usize {
    let relocs = object.function_relocs(function);
    let starts: Vec<u64> = {
        let function = object.symbol(function);
        object
            .text_relocs
            .iter()
            .filter(|rela| {
                rela.kind == R_TLSDESC_ADR_PAGE21
                    && rela.offset >= function.value
                    && rela.offset < function.value + function.size
            })
            .map(|rela| rela.offset)
            .collect()
    };
    assert_eq!(
        relocs.len(),
        4 * starts.len(),
        "{function}: only TLSDESC relocations"
    );
    for &start in &starts {
        validate_tlsdesc_access(object, start, symbol)
            .unwrap_or_else(|error| panic!("{function}: {error}"));
    }
    starts.len()
}

// ---------------------------------------------------------------------------
// Object-level tests (every host)
// ---------------------------------------------------------------------------

#[test]
fn executable_models_address_definitions_directly_and_select_le_ie_tls() {
    for model in [RelocationModel::Static, RelocationModel::Pie] {
        for opt in LEVELS {
            let object = parse(&compile(opt, model));
            let context = format!("{model} {opt:?}");
            for name in ["rm_pub_data", "rm_hid_data", "rm_prot_data", "rm_loc_data"] {
                assert_eq!(
                    object.function_relocs(&format!("rm_addr_{}", &name[3..])),
                    pairs(&[R_ADR_PREL_PG_HI21, R_ADD_ABS_LO12_NC], name),
                    "{context}: `{name}` binds within the executable image"
                );
            }
            assert_eq!(
                object.function_relocs("rm_addr_ext_data"),
                pairs(&[R_ADR_GOT_PAGE, R_LD64_GOT_LO12_NC], "rm_ext_data"),
                "{context}: an import is always GOT-indirect"
            );
            assert_eq!(
                object.function_relocs("rm_addr_pub_fn"),
                pairs(&[R_ADR_PREL_PG_HI21, R_ADD_ABS_LO12_NC], "rm_pub_fn"),
                "{context}"
            );
            assert_eq!(
                object.function_relocs("rm_addr_tls_def"),
                pairs(
                    &[R_TLSLE_ADD_TPREL_HI12, R_TLSLE_ADD_TPREL_LO12_NC],
                    "rm_tls_def"
                ),
                "{context}: a thread-local this module defines uses local-exec"
            );
            assert_eq!(
                object.function_relocs("rm_addr_tls_imp"),
                pairs(
                    &[R_TLSIE_ADR_GOTTPREL_PAGE21, R_TLSIE_LD64_GOTTPREL_LO12_NC],
                    "rm_tls_imp"
                ),
                "{context}: a thread-local import uses initial-exec"
            );
            assert!(
                object
                    .text_relocs
                    .iter()
                    .all(|rela| !TLSDESC_KINDS.contains(&rela.kind)),
                "{context}: executable models never emit TLSDESC"
            );
        }
    }
}

#[test]
fn pic_model_routes_preemptible_definitions_through_got_and_tls_through_tlsdesc() {
    for opt in LEVELS {
        let object = parse(&compile(opt, RelocationModel::Pic));
        let context = format!("pic {opt:?}");
        for name in ["rm_pub_data", "rm_ext_data"] {
            assert_eq!(
                object.function_relocs(&format!("rm_addr_{}", &name[3..])),
                pairs(&[R_ADR_GOT_PAGE, R_LD64_GOT_LO12_NC], name),
                "{context}: `{name}` is preemptible and must come from the GOT"
            );
        }
        for name in ["rm_hid_data", "rm_prot_data", "rm_loc_data"] {
            assert_eq!(
                object.function_relocs(&format!("rm_addr_{}", &name[3..])),
                pairs(&[R_ADR_PREL_PG_HI21, R_ADD_ABS_LO12_NC], name),
                "{context}: `{name}` cannot be preempted and stays PC-relative"
            );
        }
        assert_eq!(
            object.function_relocs("rm_addr_pub_fn"),
            pairs(&[R_ADR_GOT_PAGE, R_LD64_GOT_LO12_NC], "rm_pub_fn"),
            "{context}: the address of a preemptible function comes from the GOT"
        );
        // A preemptible callee is never inlined: the call stays relocated
        // against its symbol so the linker can route it through the PLT.
        let call = object.function_relocs("rm_call_pub_fn");
        assert_eq!(call.len(), 1, "{context}: {call:?}");
        assert!(
            [R_CALL26, R_JUMP26].contains(&call[0].0) && call[0].1 == "rm_pub_fn",
            "{context}: {call:?}"
        );
        assert_eq!(
            tlsdesc_accesses(&object, "rm_addr_tls_def", "rm_tls_def"),
            1,
            "{context}"
        );
        assert_eq!(
            tlsdesc_accesses(&object, "rm_addr_tls_imp", "rm_tls_imp"),
            1,
            "{context}"
        );
        assert!(
            object.text_relocs.iter().all(|rela| ![
                R_TLSLE_ADD_TPREL_HI12,
                R_TLSLE_ADD_TPREL_LO12_NC,
                R_TLSIE_ADR_GOTTPREL_PAGE21,
                R_TLSIE_LD64_GOTTPREL_LO12_NC
            ]
            .contains(&rela.kind)),
            "{context}: a shared object never uses executable-only TLS models"
        );
        // Symbol table: bindings/visibility the preemption decision relied on.
        for &(name, linkage, visibility, defined, tls) in &GLOBALS {
            let symbol = object.symbol(name);
            let want_visibility = match visibility {
                Visibility::Default => STV_DEFAULT,
                Visibility::Hidden => STV_HIDDEN,
                Visibility::Protected => STV_PROTECTED,
            };
            assert_eq!(
                symbol.other & 3,
                want_visibility,
                "{context}: `{name}` visibility"
            );
            assert_eq!(
                symbol.shndx != 0,
                defined,
                "{context}: `{name}` definedness"
            );
            assert_eq!(
                symbol.info & 0xf == STT_TLS,
                tls,
                "{context}: `{name}` type"
            );
            let local = linkage == Linkage::Internal;
            assert_eq!(symbol.info >> 4 == 0, local, "{context}: `{name}` binding");
        }
        let pub_fn = object.symbol("rm_pub_fn");
        assert_eq!(pub_fn.info >> 4, 1, "{context}: rm_pub_fn is STB_GLOBAL");
        assert_eq!(
            pub_fn.other & 3,
            STV_DEFAULT,
            "{context}: rm_pub_fn is STV_DEFAULT"
        );
    }
}

#[test]
fn static_model_inlining_control_shows_pic_keeps_the_preemptible_call() {
    // Control for the pic assertion above: with the same module, the static
    // model (every definition binds locally) is free to splice the tiny
    // callee, so a surviving relocated call under pic is the model's doing.
    let object = parse(&compile(OptLevel::O2, RelocationModel::Static));
    let static_relocs = object.function_relocs("rm_call_pub_fn");
    let pic = parse(&compile(OptLevel::O2, RelocationModel::Pic));
    assert_eq!(pic.function_relocs("rm_call_pub_fn").len(), 1);
    assert!(
        static_relocs.is_empty(),
        "static O2 is expected to inline the leaf callee (control); got {static_relocs:?}"
    );
}

#[test]
fn tlsdesc_validator_rejects_word_relocation_and_symbol_mutations() {
    let bytes = compile(OptLevel::O2, RelocationModel::Pic);
    let object = parse(&bytes);
    let function = object.symbol("rm_addr_tls_def").clone();
    let start = object
        .text_relocs
        .iter()
        .find(|rela| rela.kind == R_TLSDESC_ADR_PAGE21 && rela.offset >= function.value)
        .expect("TLSDESC site")
        .offset;
    validate_tlsdesc_access(&object, start, "rm_tls_def").expect("canonical sequence");
    let text_offset = object.sections[object.text_index].offset;
    let rela_section = object
        .sections
        .iter()
        .find(|section| section.sh_type == 4 && section.info as usize == object.text_index)
        .expect(".rela.text")
        .clone();
    let rela_entry = |slot: u64| {
        let wanted = start + 4 * slot;
        (0..rela_section.size / 24)
            .map(|index| rela_section.offset + index * 24)
            .find(|&entry| u64le(&bytes, entry) == wanted)
            .expect("slot relocation")
    };
    let word_at = |slot: u64| text_offset + (start + 4 * slot) as usize;
    let mut mutations: Vec<(String, usize, u8)> = Vec::new();
    for slot in 0..4u64 {
        // Register fields (the linker relaxes with FIXED x0/x1), opcode bits,
        // placeholders.
        for bit in [0u32, 5, 10, 16, 22, 24, 29, 31] {
            mutations.push((
                format!("slot {slot} word bit {bit}"),
                word_at(slot) + (bit / 8) as usize,
                1 << (bit % 8),
            ));
        }
        mutations.push((format!("slot {slot} reloc offset"), rela_entry(slot), 4));
        mutations.push((format!("slot {slot} reloc kind"), rela_entry(slot) + 8, 1));
        mutations.push((
            format!("slot {slot} reloc addend"),
            rela_entry(slot) + 16,
            1,
        ));
        mutations.push((
            format!("slot {slot} reloc symbol"),
            rela_entry(slot) + 12,
            1,
        ));
    }
    for (label, offset, mask) in mutations {
        let mut corrupt = bytes.clone();
        corrupt[offset] ^= mask;
        let corrupt = parse(&corrupt);
        assert!(
            validate_tlsdesc_access(&corrupt, start, "rm_tls_def").is_err(),
            "mutation `{label}` must be rejected"
        );
    }
    // Wrong symbol expectation and a shifted start are also rejected.
    assert!(validate_tlsdesc_access(&object, start, "rm_tls_imp").is_err());
    assert!(validate_tlsdesc_access(&object, start + 4, "rm_tls_def").is_err());
}

#[test]
fn tlsdesc_validator_accepts_clang_ground_truth_words() {
    // The retained clang words form an object-independent positive control
    // for the TP-add dataflow part of the validator.
    let words = [
        0x9000_0000u32,
        0xf940_0001,
        0x9100_0000,
        0xd63f_0020,
        0xd53b_d048,
        0x8b00_0100,
    ];
    assert_eq!(&words[..4], &TLSDESC_WORDS);
    // mrs x8, tpidr_el0 ; add x0, x8, x0
    assert_eq!(words[4] & 0xffff_ffe0, 0xd53b_d040);
    assert_eq!(words[5] & 0xffe0_fc00, 0x8b00_0000);
    assert_eq!((words[5] >> 5) & 31, words[4] & 31);
    assert_eq!((words[5] >> 16) & 31, 0);
}

#[test]
fn pipeline_general_and_local_dynamic_models_emit_the_same_tlsdesc_sequence() {
    for model in [TlsModel::GeneralDynamic, TlsModel::LocalDynamic] {
        for opt in LEVELS {
            let bytes = tls_pipeline_object(opt, model, RelocationModel::Pic, LINUX)
                .unwrap_or_else(|error| panic!("{model:?} {opt:?}: {error}"));
            let object = parse(&bytes);
            assert_eq!(
                tlsdesc_accesses(&object, "cg_tls_addr", "tls_probe_var"),
                1,
                "{model:?} {opt:?}"
            );
            let symbol = object.symbol("tls_probe_var");
            assert_eq!(symbol.shndx, 0, "the probe symbol is an undefined import");
            assert_eq!(symbol.info & 0xf, STT_TLS);
        }
    }
}

// ---------------------------------------------------------------------------
// Fail-closed controls
// ---------------------------------------------------------------------------

fn tls_addr_function(
    name: &str,
    symbol: &str,
    model: TlsModel,
) -> trust_cg_lower::function::Function {
    use trust_cg_lower::function::{BasicBlock, Function as LowerFunction, Signature};
    use trust_cg_lower::instructions::{Block as LowerBlock, Instruction, Opcode, Value};
    use trust_cg_lower::types::Type as LowerType;
    let mut func = LowerFunction::new(
        name.to_owned(),
        Signature {
            params: vec![],
            returns: vec![LowerType::I64],
        },
    );
    func.entry_block = LowerBlock(0);
    func.block_order = vec![LowerBlock(0)];
    func.blocks.insert(
        LowerBlock(0),
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::TlsRef {
                        name: symbol.to_owned(),
                        model: map_tls_model(model),
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
            source_locs: vec![],
        },
    );
    func
}

fn map_tls_model(model: TlsModel) -> trust_cg_ir::TlsModel {
    match model {
        TlsModel::LocalExec => trust_cg_ir::TlsModel::LocalExec,
        TlsModel::InitialExec => trust_cg_ir::TlsModel::InitialExec,
        TlsModel::GeneralDynamic => trust_cg_ir::TlsModel::GeneralDynamic,
        TlsModel::LocalDynamic => trust_cg_ir::TlsModel::LocalDynamic,
    }
}

fn tls_pipeline_object(
    opt_level: OptLevel,
    model: TlsModel,
    relocation_model: RelocationModel,
    triple: &str,
) -> Result<Vec<u8>, String> {
    let pipeline = Pipeline::new(PipelineConfig {
        target_triple: triple.to_owned(),
        opt_level,
        relocation_model,
        ..PipelineConfig::default()
    });
    let prepared = pipeline
        .prepare_function(&tls_addr_function("cg_tls_addr", "tls_probe_var", model))
        .map_err(|error| error.to_string())?;
    let globals = vec![ObjectGlobal {
        name: "tls_probe_var".to_owned(),
        data: vec![],
        mutable: true,
        is_external: true,
        symbol_refs: vec![],
        is_thread_local: true,
        is_import: true,
        is_weak: false,
        align: 8,
        visibility: Visibility::Default,
        retained: false,
        section: None,
        comdat: false,
    }];
    pipeline
        .compile_module_with_globals(&[prepared], &globals)
        .map_err(|error| error.to_string())
}

/// The object-relocation inventory names every TLSDESC relocation the object
/// actually carries (the artifact's own relocation records agree with the
/// mirrored inventory) and refuses to certify them: they are the only
/// uncovered rows, so proof-required promotion of a `pic` TLS access fails
/// closed on exactly the unproven TLSDESC relocations.
#[test]
fn tlsdesc_relocations_are_inventoried_by_name_and_block_proof_promotion() {
    use trust_cg_verify::ObjectRelocationKind as K;
    let pipeline = Pipeline::new(PipelineConfig {
        target_triple: LINUX.to_owned(),
        opt_level: OptLevel::O1,
        relocation_model: RelocationModel::Pic,
        ..PipelineConfig::default()
    });
    let (prepared, metrics) = pipeline
        .prepare_function_with_metrics(
            &tls_addr_function("cg_tls_addr", "tls_probe_var", TlsModel::GeneralDynamic),
            None,
        )
        .expect("prepare");
    let globals = vec![ObjectGlobal {
        name: "tls_probe_var".to_owned(),
        data: vec![],
        mutable: true,
        is_external: true,
        symbol_refs: vec![],
        is_thread_local: true,
        is_import: true,
        is_weak: false,
        align: 8,
        visibility: Visibility::Default,
        retained: false,
        section: None,
        comdat: false,
    }];
    let functions = vec![prepared];
    let layouts = vec![metrics.frame_layout];
    let report = pipeline
        .module_relocation_inventory_report_with_object_state(
            &functions,
            &globals,
            &layouts,
            "tlsdesc.o",
        )
        .expect("inventory")
        .expect("AArch64 ELF carries a relocation inventory");
    let inventoried: Vec<K> = report.entries.iter().map(|entry| entry.kind).collect();
    for row in K::aarch64_elf_named_tlsdesc_rows() {
        assert_eq!(
            inventoried.iter().filter(|kind| *kind == row).count(),
            1,
            "{row}: {inventoried:?}"
        );
    }
    assert!(!report.is_promotable(), "TLSDESC rows must block promotion");
    let uncovered: std::collections::BTreeSet<K> = report
        .uncovered_relocations()
        .iter()
        .map(|entry| entry.kind)
        .collect();
    assert_eq!(
        uncovered,
        K::aarch64_elf_named_tlsdesc_rows()
            .iter()
            .copied()
            .collect(),
        "only the unproven TLSDESC rows may be uncovered"
    );

    // The emitted object's own relocation records (every SHT_RELA section,
    // read independently) name exactly the inventoried kinds.
    let bytes = pipeline
        .compile_module_with_globals_and_layouts(&functions, &globals, &layouts)
        .expect("object");
    let object = parse(&bytes);
    let mut emitted: Vec<u32> = Vec::new();
    for section in object
        .sections
        .iter()
        .filter(|section| section.sh_type == 4)
    {
        for index in 0..section.size / 24 {
            let info = u64le(&bytes, section.offset + index * 24 + 8);
            emitted.push((info & 0xffff_ffff) as u32);
        }
    }
    let r_type = |kind: &K| -> u32 {
        match kind {
            K::AArch64ElfTlsdescAdrPage21 => R_TLSDESC_ADR_PAGE21,
            K::AArch64ElfTlsdescLd64Lo12 => R_TLSDESC_LD64_LO12,
            K::AArch64ElfTlsdescAddLo12 => R_TLSDESC_ADD_LO12,
            K::AArch64ElfTlsdescCall => R_TLSDESC_CALL,
            K::AArch64ElfPrel32 => 261,
            other => panic!("unexpected inventory row {other}"),
        }
    };
    let mut expected: Vec<u32> = inventoried.iter().map(r_type).collect();
    emitted.sort_unstable();
    expected.sort_unstable();
    assert_eq!(
        emitted, expected,
        "artifact relocations must match the inventory"
    );
}

#[test]
fn pic_objects_refuse_executable_only_tls_models() {
    for model in [TlsModel::LocalExec, TlsModel::InitialExec] {
        let error = tls_pipeline_object(OptLevel::O1, model, RelocationModel::Pic, LINUX)
            .expect_err("pic must refuse an executable-only TLS model");
        assert!(
            error.contains("executable-only TLS model"),
            "{model:?}: unexpected error {error}"
        );
        // The same machine code is legal for an executable image.
        tls_pipeline_object(OptLevel::O1, model, RelocationModel::Pie, LINUX)
            .unwrap_or_else(|error| panic!("{model:?} pie: {error}"));
    }
}

#[test]
fn tlsdesc_is_refused_on_mach_o() {
    let error = tls_pipeline_object(
        OptLevel::O1,
        TlsModel::GeneralDynamic,
        RelocationModel::Static,
        "aarch64-apple-darwin",
    )
    .expect_err("Mach-O has no TLSDESC relocations");
    assert!(
        error.contains("ELF") || error.contains("Elf"),
        "unexpected error {error}"
    );
}

/// A layout-less machine function whose `ADRP`/`ADD` pair addresses `symbol`
/// PC-relatively.
fn direct_address_function(name: &str, symbol: &str) -> trust_cg_ir::function::MachFunction {
    use trust_cg_ir::function::{MachFunction, Signature, Type};
    use trust_cg_ir::inst::{AArch64Opcode, MachInst};
    use trust_cg_ir::operand::MachOperand;
    use trust_cg_ir::regs::X0;
    let mut function = MachFunction::new(name.into(), Signature::new(vec![], vec![Type::Ptr]));
    for inst in [
        MachInst::new(
            AArch64Opcode::Adrp,
            vec![MachOperand::PReg(X0), MachOperand::Symbol(symbol.into())],
        ),
        MachInst::new(
            AArch64Opcode::AddPCRel,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
                MachOperand::Symbol(symbol.into()),
            ],
        ),
        MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_uses(&[X0]),
    ] {
        let id = function.push_inst(inst);
        function.append_inst(function.entry, id);
    }
    function
}

fn data_global(name: &str, is_external: bool, visibility: Visibility) -> ObjectGlobal {
    ObjectGlobal {
        name: name.into(),
        data: 42u64.to_le_bytes().to_vec(),
        mutable: true,
        is_external,
        symbol_refs: vec![],
        is_thread_local: false,
        is_import: false,
        is_weak: false,
        align: 8,
        visibility,
        retained: false,
        section: None,
        comdat: false,
    }
}

fn emit_direct(
    relocation_model: RelocationModel,
    triple: &str,
    symbol: &str,
) -> Result<Vec<u8>, String> {
    let pipeline = Pipeline::new(PipelineConfig {
        target_triple: triple.to_owned(),
        relocation_model,
        ..PipelineConfig::default()
    });
    let functions = vec![
        direct_address_function("getter", symbol),
        direct_address_function("other_fn", "local_words"),
    ];
    let globals = vec![
        data_global("local_words", false, Visibility::Default),
        data_global("hidden_words", true, Visibility::Hidden),
        data_global("public_words", true, Visibility::Default),
        ObjectGlobal {
            // An absolute pointer slot in writable data stays legal under pic:
            // the linker turns it into a dynamic relocation.
            symbol_refs: vec![GlobalSymbolRef {
                offset: 0,
                symbol: "public_words".into(),
                addend: 0,
            }],
            ..data_global("slot", true, Visibility::Default)
        },
    ];
    pipeline
        .compile_module_with_globals(&functions, &globals)
        .map_err(|error| error.to_string())
}

#[test]
fn pic_emitter_backstop_refuses_direct_references_to_preemptible_symbols() {
    for symbol in ["public_words", "other_fn", "undefined_words"] {
        let error = emit_direct(RelocationModel::Pic, LINUX, symbol)
            .expect_err("pic must refuse a PC-relative reference to a preemptible symbol");
        assert!(
            error.contains("PC-relatively") && error.contains(symbol),
            "`{symbol}`: unexpected error {error}"
        );
    }
    for symbol in ["local_words", "hidden_words"] {
        let bytes = emit_direct(RelocationModel::Pic, LINUX, symbol)
            .unwrap_or_else(|error| panic!("`{symbol}` binds locally: {error}"));
        let object = parse(&bytes);
        assert_eq!(
            object.function_relocs("getter"),
            pairs(&[R_ADR_PREL_PG_HI21, R_ADD_ABS_LO12_NC], symbol)
        );
    }
    // Executable models accept every direct reference (the image binds them).
    for model in [RelocationModel::Static, RelocationModel::Pie] {
        for symbol in ["public_words", "other_fn"] {
            emit_direct(model, LINUX, symbol)
                .unwrap_or_else(|error| panic!("{model} `{symbol}`: {error}"));
        }
    }
    // pie/pic are ELF concepts; Mach-O refuses them rather than ignore them.
    for model in [RelocationModel::Pie, RelocationModel::Pic] {
        let error = emit_direct(model, "aarch64-apple-darwin", "local_words")
            .expect_err("Mach-O refuses pie/pic");
        assert!(
            error.contains("implemented only for AArch64 ELF"),
            "{model}: unexpected error {error}"
        );
    }
}

// ---------------------------------------------------------------------------
// Function linkage under the relocation models
// ---------------------------------------------------------------------------

const STB_LOCAL: u8 = 0;
const STB_GLOBAL: u8 = 1;
const STB_WEAK: u8 = 2;

/// `x * mul + add` over `u64`, the body of the linkage fixture's definitions.
fn affine_blocks(mul: i128, add: i128) -> Vec<Block> {
    vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::U64)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(mul),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::U64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(add),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U64,
                lhs: ValueId::new(2),
                rhs: ValueId::new(3),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(4)],
            }),
        ],
    }]
}

/// ```c
/// __attribute__((weak)) uint64_t rm_weak_fn(uint64_t x) { return x * 5 + 1; }
/// uint64_t rm_odr_fn(uint64_t x) { return x * 9 + 2; }        // weak_odr
/// extern __attribute__((weak)) uint64_t rm_weak_ref_fn(uint64_t);
/// extern __attribute__((weak)) uint64_t rm_weak_ref_data;
/// uint64_t rm_call_weak_fn(uint64_t x) { return rm_weak_fn(x); }
/// /* rm_addr_<f>() returns &<f> for the four symbols above */
/// ```
fn linkage_fixture() -> Module {
    let mut module = Module::new("relocation_model_linkage");
    module.target_info = fixture().target_info;
    module.globals = vec![Global {
        section: None,
        visibility: Visibility::Default,
        retained: false,
        name: "rm_weak_ref_data".into(),
        ty: Ty::U64,
        mutable: true,
        initializer: None,
        linkage: Linkage::ExternalWeak,
        tls: None,
        align: Some(8),
    }];
    let unary = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let nullary_fn = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Func(unary)],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let nullary_ptr = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut define = |name: &str, ty, linkage, blocks: Vec<Block>| {
        let id = FuncId::new(module.functions.len() as u32);
        let mut function = Function::new(id, name, ty, BlockId::new(0));
        function.linkage = linkage;
        function.blocks = blocks;
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
        id
    };
    let weak_fn = define("rm_weak_fn", unary, Linkage::Weak, affine_blocks(5, 1));
    let odr_fn = define("rm_odr_fn", unary, Linkage::WeakOdr, affine_blocks(9, 2));
    define("rm_weak_ref_fn", unary, Linkage::ExternalWeak, vec![]);
    define(
        "rm_call_weak_fn",
        unary,
        Linkage::External,
        vec![Block {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::U64)],
            body: vec![
                InstrNode::new(Inst::Call {
                    callee: weak_fn,
                    args: vec![ValueId::new(0)],
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(1)],
                }),
            ],
        }],
    );
    let returns = |node: InstrNode| {
        vec![Block {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                node.with_result(ValueId::new(0)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(0)],
                }),
            ],
        }]
    };
    for (name, target) in [("rm_addr_weak_fn", weak_fn), ("rm_addr_odr_fn", odr_fn)] {
        define(
            name,
            nullary_fn,
            Linkage::External,
            returns(InstrNode::new(Inst::Const {
                ty: Ty::Func(unary),
                value: Constant::FnDef(target),
            })),
        );
    }
    // A weak REFERENCE's address is nullable: trust-ir spells it as a
    // `SymbolAddr` at `Ty::Ptr` (a `FnDef` of a bodyless `external_weak`
    // declaration is `WeakDeclarationAsFnDef`, refused at ingestion since
    // WS7.3).
    define(
        "rm_addr_weak_ref_fn",
        nullary_ptr,
        Linkage::External,
        returns(InstrNode::new(Inst::Const {
            ty: Ty::Ptr,
            value: Constant::SymbolAddr {
                symbol: "rm_weak_ref_fn".into(),
                addend: 0,
            },
        })),
    );
    define(
        "rm_addr_weak_ref_data",
        nullary_ptr,
        Linkage::External,
        returns(InstrNode::new(Inst::GlobalAddr {
            global: GlobalId::new(0),
        })),
    );
    module
}

fn compile_linkage(
    opt_level: OptLevel,
    relocation_model: RelocationModel,
    parallel: bool,
) -> Vec<u8> {
    let target_spec = TargetSpec::parse(LINUX).expect("supported target triple");
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            target: target_spec.architecture,
            parallel,
            relocation_model,
            ..CompilerConfig::default()
        },
        target_spec,
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&linkage_fixture())
    .unwrap_or_else(|error| panic!("{relocation_model} {opt_level:?} parallel={parallel}: {error}"))
    .object_code
}

#[test]
fn weak_definitions_and_weak_references_follow_the_relocation_model() {
    let got = [R_ADR_GOT_PAGE, R_LD64_GOT_LO12_NC];
    let direct = [R_ADR_PREL_PG_HI21, R_ADD_ABS_LO12_NC];
    for model in RelocationModel::ALL {
        for opt in LEVELS {
            for parallel in [false, true] {
                let object = parse(&compile_linkage(opt, model, parallel));
                let context = format!("{model} {opt:?} parallel={parallel}");
                // A weak or ODR DEFINITION binds within an executable image
                // (a strong definition elsewhere replaces it at static link,
                // which the symbol reference follows); in a shared object it
                // is preemptible like any default-visibility definition.
                let definition_access = if model == RelocationModel::Pic {
                    got
                } else {
                    direct
                };
                for name in ["rm_weak_fn", "rm_odr_fn"] {
                    assert_eq!(
                        object.function_relocs(&format!("rm_addr_{}", &name[3..])),
                        pairs(&definition_access, name),
                        "{context}: address of `{name}`"
                    );
                }
                // A weak REFERENCE is GOT-indirect under every model: its
                // slot reads null when nothing defines the symbol.
                for name in ["rm_weak_ref_fn", "rm_weak_ref_data"] {
                    assert_eq!(
                        object.function_relocs(&format!("rm_addr_{}", &name[3..])),
                        pairs(&got, name),
                        "{context}: address of `{name}`"
                    );
                }
                // A non-ODR weak definition is interposable at static link
                // under every model and preemptible under pic: the call is
                // never replaced by a spliced copy of this module's body.
                let call = object.function_relocs("rm_call_weak_fn");
                assert_eq!(call.len(), 1, "{context}: {call:?}");
                assert!(
                    [R_CALL26, R_JUMP26].contains(&call[0].0) && call[0].1 == "rm_weak_fn",
                    "{context}: {call:?}"
                );
                for (name, bind, defined) in [
                    ("rm_weak_fn", STB_WEAK, true),
                    ("rm_odr_fn", STB_WEAK, true),
                    ("rm_weak_ref_fn", STB_WEAK, false),
                    ("rm_weak_ref_data", STB_WEAK, false),
                    ("rm_call_weak_fn", STB_GLOBAL, true),
                ] {
                    let symbol = object.symbol(name);
                    assert_eq!(symbol.info >> 4, bind, "{context}: `{name}` binding");
                    assert_eq!(
                        symbol.shndx != 0,
                        defined,
                        "{context}: `{name}` definedness"
                    );
                    assert_eq!(
                        symbol.other & 3,
                        STV_DEFAULT,
                        "{context}: `{name}` visibility"
                    );
                }
            }
        }
    }
}

/// `getter` addresses `other_fn` PC-relatively; `other_fn`'s symbol binding
/// is `binding`.
fn emit_direct_to_bound_function(
    relocation_model: RelocationModel,
    binding: FunctionSymbolBinding,
) -> Result<Vec<u8>, String> {
    let pipeline = Pipeline::new(PipelineConfig {
        target_triple: LINUX.to_owned(),
        relocation_model,
        ..PipelineConfig::default()
    });
    let functions = vec![
        direct_address_function("getter", "other_fn"),
        direct_address_function("other_fn", "local_words"),
    ];
    let globals = vec![data_global("local_words", false, Visibility::Default)];
    pipeline
        .compile_module_emission(
            &functions,
            &globals,
            &[],
            &[FunctionSymbolBinding::GLOBAL, binding],
        )
        .map(|emission| emission.object)
        .map_err(|error| error.to_string())
}

#[test]
fn pic_backstop_reads_function_symbol_bindings() {
    let protected =
        FunctionSymbolBinding::new(FunctionSymbolLinkage::Global, Visibility::Protected);
    for (label, binding, bind, visibility) in [
        (
            "local",
            FunctionSymbolBinding::LOCAL,
            STB_LOCAL,
            STV_DEFAULT,
        ),
        (
            "hidden",
            FunctionSymbolBinding::HIDDEN,
            STB_GLOBAL,
            STV_HIDDEN,
        ),
        ("protected", protected, STB_GLOBAL, STV_PROTECTED),
    ] {
        let bytes = emit_direct_to_bound_function(RelocationModel::Pic, binding)
            .unwrap_or_else(|error| panic!("{label} function binds locally: {error}"));
        let object = parse(&bytes);
        assert_eq!(
            object.function_relocs("getter"),
            pairs(&[R_ADR_PREL_PG_HI21, R_ADD_ABS_LO12_NC], "other_fn"),
            "{label}"
        );
        let symbol = object.symbol("other_fn");
        assert_eq!(symbol.info >> 4, bind, "{label}: binding");
        assert_eq!(symbol.other & 3, visibility, "{label}: visibility");
    }
    for (label, binding) in [
        ("global", FunctionSymbolBinding::GLOBAL),
        ("weak", FunctionSymbolBinding::WEAK),
    ] {
        let error = emit_direct_to_bound_function(RelocationModel::Pic, binding)
            .expect_err("a default-visibility global or weak function is preemptible");
        assert!(
            error.contains("PC-relatively") && error.contains("a preemptible function definition"),
            "{label}: unexpected error {error}"
        );
        // The executable models bind every definition within the image.
        for model in [RelocationModel::Static, RelocationModel::Pie] {
            emit_direct_to_bound_function(model, binding)
                .unwrap_or_else(|error| panic!("{model} {label}: {error}"));
        }
    }
    // A binding vector that is not 1:1 with the functions is refused before
    // the relocation-model check could read the wrong function's binding.
    let pipeline = Pipeline::new(PipelineConfig {
        target_triple: LINUX.to_owned(),
        relocation_model: RelocationModel::Pic,
        ..PipelineConfig::default()
    });
    let error = pipeline
        .compile_module_emission(
            &[direct_address_function("getter", "local_words")],
            &[data_global("local_words", false, Visibility::Default)],
            &[],
            &[FunctionSymbolBinding::LOCAL, FunctionSymbolBinding::LOCAL],
        )
        .expect_err("mismatched binding vector");
    assert!(error.to_string().contains("1:1"), "{error}");
}

// ---------------------------------------------------------------------------
// One preemption predicate: adapter, emitter backstop and inliner agree
// ---------------------------------------------------------------------------

/// ```c
/// uint64_t pb_word = 7;           // with `linkage` and `visibility`
/// uint64_t pb_fn(uint64_t x) { return x * 3 + 5; }   // likewise
/// uint64_t *addr_pb_word(void) { return &pb_word; }
/// uint64_t (*addr_pb_fn(void))(uint64_t) { return pb_fn; }
/// uint64_t call_pb_fn(uint64_t x) { return pb_fn(x); }
/// ```
///
/// A local `pb_fn` and its two users are left out: AOT refuses a local
/// function's identity and direct calls to it.
fn predicate_module(linkage: Linkage, visibility: Visibility) -> Module {
    let mut module = Module::new("preemption_predicate");
    module.target_info = fixture().target_info;
    module.globals = vec![Global {
        section: None,
        visibility,
        retained: false,
        name: "pb_word".into(),
        ty: Ty::U64,
        mutable: true,
        initializer: Some(u64_value(7)),
        linkage,
        tls: None,
        align: Some(8),
    }];
    let unary = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let nullary_fn = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Func(unary)],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let nullary_ptr = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut define = |name: &str, ty, blocks: Vec<Block>| {
        let id = FuncId::new(module.functions.len() as u32);
        let mut function = Function::new(id, name, ty, BlockId::new(0));
        function.linkage = Linkage::External;
        function.blocks = blocks;
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
        id
    };
    let returns = |node: InstrNode| {
        vec![Block {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                node.with_result(ValueId::new(0)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(0)],
                }),
            ],
        }]
    };
    define(
        "addr_pb_word",
        nullary_ptr,
        returns(InstrNode::new(Inst::GlobalAddr {
            global: GlobalId::new(0),
        })),
    );
    if !matches!(linkage, Linkage::Internal | Linkage::Private) {
        let target = define("pb_fn", unary, affine_blocks(3, 5));
        define(
            "addr_pb_fn",
            nullary_fn,
            returns(InstrNode::new(Inst::Const {
                ty: Ty::Func(unary),
                value: Constant::FnDef(target),
            })),
        );
        define(
            "call_pb_fn",
            unary,
            vec![Block {
                id: BlockId::new(0),
                params: vec![(ValueId::new(0), Ty::U64)],
                body: vec![
                    InstrNode::new(Inst::Call {
                        callee: target,
                        args: vec![ValueId::new(0)],
                    })
                    .with_result(ValueId::new(1)),
                    InstrNode::new(Inst::Return {
                        values: vec![ValueId::new(1)],
                    }),
                ],
            }],
        );
        let function = &mut module.functions[target.index() as usize];
        function.linkage = linkage;
        function.visibility = visibility;
    }
    module
}

/// `getter` addresses `global` PC-relatively.
fn emit_direct_to_global(
    relocation_model: RelocationModel,
    global: &ObjectGlobal,
) -> Result<Vec<u8>, String> {
    Pipeline::new(PipelineConfig {
        target_triple: LINUX.to_owned(),
        relocation_model,
        ..PipelineConfig::default()
    })
    .compile_module_with_globals(
        &[direct_address_function("getter", &global.name)],
        std::slice::from_ref(global),
    )
    .map_err(|error| error.to_string())
}

/// Every decision that reads preemption agrees with
/// [`RelocationModel::definition_is_preemptible`] for each admissible trust-ir
/// definition `(linkage, visibility)` under every relocation model:
///
/// * the emitter backstop, fed the object symbols the compiler derives
///   (`module_object_globals`, `FunctionSymbolBinding::for_trust_ir_definition`),
///   accepts a PC-relative page reference to the symbol exactly when it is not
///   preemptible;
/// * the adapter, read from the compiled object at O0 and O2, addresses the
///   function and the word through the GOT exactly when they are
///   preemptible;
/// * the module inliner keeps the call at O2 exactly when the body may be
///   replaced: preemptible and not ODR, or named by the static-link
///   predicate `definition_is_link_replaceable` (`Weak`/`LinkOnce`, whatever
///   the visibility), whose table is pinned here independently.
///
/// A copy of the decision that drifted, as the function-address path did
/// when it read every function as default-visible, fails here.
#[test]
fn adapter_backstop_and_inliner_read_one_preemption_predicate() {
    let linkages = [
        Linkage::External,
        Linkage::Internal,
        Linkage::Private,
        Linkage::Weak,
        Linkage::LinkOnce,
        Linkage::WeakOdr,
        Linkage::LinkOnceOdr,
    ];
    let got = [R_ADR_GOT_PAGE, R_LD64_GOT_LO12_NC];
    let direct = [R_ADR_PREL_PG_HI21, R_ADD_ABS_LO12_NC];
    let (mut rows, mut preemptible_rows) = (0, 0);
    for model in RelocationModel::ALL {
        for linkage in linkages {
            for visibility in [
                Visibility::Default,
                Visibility::Hidden,
                Visibility::Protected,
            ] {
                let local = matches!(linkage, Linkage::Internal | Linkage::Private);
                if local && visibility != Visibility::Default {
                    continue; // contradictory; refused by name elsewhere
                }
                let label = format!("{model} {linkage:?} {visibility:?}");
                let preemptible = model.definition_is_preemptible(
                    trust_cg_codegen::DefinitionBinding::for_trust_ir_linkage(linkage),
                    visibility,
                );
                preemptible_rows += usize::from(preemptible);
                rows += 1;
                assert_eq!(
                    trust_cg_codegen::definition_is_link_replaceable(linkage),
                    matches!(linkage, Linkage::Weak | Linkage::LinkOnce),
                    "{label}: the static-link predicate"
                );
                let module = predicate_module(linkage, visibility);

                let globals = trust_cg_codegen::compiler::module_object_globals(&module)
                    .unwrap_or_else(|error| panic!("{label}: {error}"));
                let word = globals
                    .iter()
                    .find(|global| global.name == "pb_word")
                    .expect("pb_word");
                assert_eq!(
                    word.binds_outside_object_under(model),
                    preemptible,
                    "{label}"
                );
                assert_eq!(
                    emit_direct_to_global(model, word).is_ok(),
                    !preemptible,
                    "{label}: the backstop's data verdict"
                );
                if !local {
                    let binding =
                        FunctionSymbolBinding::for_trust_ir_definition(linkage, visibility)
                            .unwrap_or_else(|error| panic!("{label}: {error}"));
                    assert_eq!(binding.is_preemptible_under(model), preemptible, "{label}");
                    assert_eq!(
                        emit_direct_to_bound_function(model, binding).is_ok(),
                        !preemptible,
                        "{label}: the backstop's function verdict"
                    );
                }

                for opt in [OptLevel::O0, OptLevel::O2] {
                    let object = parse(
                        &compiler(opt, model, LINUX)
                            .compile(&module)
                            .unwrap_or_else(|error| panic!("{label} {opt:?}: {error}"))
                            .object_code,
                    );
                    let access = if preemptible { &got } else { &direct };
                    assert_eq!(
                        object.function_relocs("addr_pb_word"),
                        pairs(access, "pb_word"),
                        "{label} {opt:?}: the adapter's data verdict"
                    );
                    if local {
                        continue;
                    }
                    assert_eq!(
                        object.function_relocs("addr_pb_fn"),
                        pairs(access, "pb_fn"),
                        "{label} {opt:?}: the adapter's function verdict"
                    );
                    let replaceable = trust_cg_codegen::definition_is_link_replaceable(linkage)
                        || (preemptible
                            && !matches!(linkage, Linkage::WeakOdr | Linkage::LinkOnceOdr));
                    let call = object.function_relocs("call_pb_fn");
                    if opt == OptLevel::O0 || replaceable {
                        assert!(
                            call.len() == 1
                                && [R_CALL26, R_JUMP26].contains(&call[0].0)
                                && call[0].1 == "pb_fn",
                            "{label} {opt:?}: the call must stay: {call:?}"
                        );
                    } else {
                        assert!(
                            call.is_empty(),
                            "{label} {opt:?}: the inliner may splice a body no module can \
                             replace: {call:?}"
                        );
                    }
                }
            }
        }
    }
    // 3 models x (5 global linkages x 3 visibilities + 2 local linkages), of
    // which only pic's five default-visibility global rows are preemptible.
    assert_eq!((rows, preemptible_rows), (51, 5));
}

#[test]
fn single_function_objects_refuse_pie_and_pic_on_mach_o() {
    for model in [RelocationModel::Pie, RelocationModel::Pic] {
        let pipeline = Pipeline::new(PipelineConfig {
            target_triple: "aarch64-apple-darwin".to_owned(),
            relocation_model: model,
            ..PipelineConfig::default()
        });
        let mut function = direct_address_function("getter", "words");
        let error = pipeline
            .compile_ir_function(&mut function)
            .expect_err("Mach-O refuses pie/pic");
        assert!(
            error
                .to_string()
                .contains("implemented only for AArch64 ELF"),
            "{model}: unexpected error {error}"
        );
    }
    // Controls: the same function compiles for Mach-O under the static
    // model, and the ELF single-function path under pic refuses it because
    // its undefined target is preemptible.
    let pipeline = Pipeline::new(PipelineConfig {
        target_triple: "aarch64-apple-darwin".to_owned(),
        ..PipelineConfig::default()
    });
    pipeline
        .compile_ir_function(&mut direct_address_function("getter", "words"))
        .expect("static Mach-O single-function object");
    let pipeline = Pipeline::new(PipelineConfig {
        target_triple: LINUX.to_owned(),
        relocation_model: RelocationModel::Pic,
        ..PipelineConfig::default()
    });
    let error = pipeline
        .compile_ir_function(&mut direct_address_function("getter", "words"))
        .expect_err("pic refuses a PC-relative reference to an undefined symbol");
    assert!(error.to_string().contains("an undefined symbol"), "{error}");
}

#[test]
fn unsupported_routes_refuse_non_static_relocation_models() {
    let module = fixture();
    for (triple, model) in [
        ("aarch64-apple-darwin", RelocationModel::Pic),
        ("aarch64-apple-darwin", RelocationModel::Pie),
        ("x86_64-unknown-linux-gnu", RelocationModel::Pic),
        ("x86_64-unknown-linux-gnu", RelocationModel::Pie),
    ] {
        let error = compiler(OptLevel::O1, model, triple)
            .compile(&module)
            .err()
            .unwrap_or_else(|| panic!("{triple} {model} must be refused"));
        assert!(
            matches!(
                &error,
                CompileError::RelocationModelUnsupported { model: refused, .. } if *refused == model
            ),
            "{triple} {model}: unexpected error {error}"
        );
    }
    // The in-process JIT is never linked: only `static` is accepted.
    let jit = Compiler::new(CompilerConfig {
        relocation_model: RelocationModel::Pic,
        ..CompilerConfig::for_host_jit()
    })
    .with_codegen_license(permit_unlicensed());
    let error = jit
        .compile_module_to_jit(&module, &Default::default())
        .expect_err("JIT must refuse pic");
    assert!(
        matches!(error, CompileError::RelocationModelUnsupported { .. }),
        "unexpected JIT error {error}"
    );
    // The model names round-trip through the CLI spelling.
    for model in RelocationModel::ALL {
        assert_eq!(model.name().parse::<RelocationModel>(), Ok(model));
    }
    assert!("fpic".parse::<RelocationModel>().is_err());
}

// ---------------------------------------------------------------------------
// Link-level controls with LLD
// ---------------------------------------------------------------------------
//
// With an LLD these checks link real AArch64 ELF shared objects and
// executables on any host. The Trust package's sysroot is asked first for
// `rust-lld`; the installed Darwin package ships none today (measured: no
// lib/rustlib/<host>/bin/rust-lld or gcc-ld), so the `ld.lld` fallback below is
// what runs there until it does. They establish that a
// production static linker accepts the relocation-model output (`-shared -z
// text`), refuses the static model for a shared object, and relaxes the
// TLSDESC slots in executables to the value the TLS layout requires. They
// read the linked images with the independent reader above; nothing executes.
// Without `rust-lld` in the rustc sysroot they use the first `ld.lld` in
// `TCG_LLD_DIR`, `~/.local/bin` and `PATH` (the same GNU-flavour LLD); with
// neither they print `SKIP`, and with `TCG_REQUIRE_LLD` set they fail.

#[allow(dead_code)]
#[path = "common/skip.rs"]
mod skip;

const R_AARCH64_GLOB_DAT: u32 = 0x401;
const R_AARCH64_JUMP_SLOT: u32 = 0x402;
const R_AARCH64_TLS_TPREL64: u32 = 0x406;
const R_AARCH64_TLSDESC: u32 = 0x407;
const PT_TLS: u32 = 7;
const NOP: u32 = 0xd503_201f;

/// The LLD the link-level controls run: `program`, invoked with
/// `-flavor gnu` when it is `rust-lld`.
struct Lld {
    program: std::path::PathBuf,
    rust_lld: bool,
}

/// The LLD for `test`: the `rust-lld` of the toolchain that `rustc` resolves
/// for this checkout, else the first `ld.lld` in `TCG_LLD_DIR`,
/// `~/.local/bin` and `PATH` ([`host_ld_lld`]). With neither, `test` prints
/// `SKIP` and gets `None`, unless `TCG_REQUIRE_LLD` is set, which makes a
/// missing LLD a failure.
fn lld_for(test: &str) -> Option<Lld> {
    let rust_lld = rust_lld();
    let ld_lld = rust_lld.is_none().then(host_ld_lld).flatten();
    match resolve_lld(
        rust_lld,
        ld_lld,
        std::env::var_os("TCG_REQUIRE_LLD").is_some(),
    ) {
        Ok(Some(lld)) => Some(lld),
        Ok(None) => {
            skip::skip_test(test, LLD_NOT_FOUND);
            None
        }
        Err(message) => panic!("{test}: {message}"),
    }
}

const LLD_NOT_FOUND: &str =
    "neither rust-lld (rustc sysroot) nor ld.lld (TCG_LLD_DIR, ~/.local/bin, PATH) found";

/// The LLD [`lld_for`] runs, from what the host offers: `rust-lld` first,
/// then an `ld.lld`. `Ok(None)` is a skip; with `require` (`TCG_REQUIRE_LLD`)
/// a missing LLD is an error instead.
fn resolve_lld(
    rust_lld: Option<std::path::PathBuf>,
    ld_lld: Option<std::path::PathBuf>,
    require: bool,
) -> Result<Option<Lld>, String> {
    if let Some(program) = rust_lld {
        return Ok(Some(Lld {
            program,
            rust_lld: true,
        }));
    }
    if let Some(program) = ld_lld {
        return Ok(Some(Lld {
            program,
            rust_lld: false,
        }));
    }
    if require {
        return Err(format!("TCG_REQUIRE_LLD is set but {LLD_NOT_FOUND}"));
    }
    Ok(None)
}

/// The first `ld.lld` in [`ld_lld_directories`] of this process's
/// environment.
fn host_ld_lld() -> Option<std::path::PathBuf> {
    ld_lld_directories(
        std::env::var_os("TCG_LLD_DIR"),
        std::env::var_os("HOME"),
        std::env::var_os("PATH"),
    )
    .into_iter()
    .map(|dir| dir.join("ld.lld"))
    .find(|path| path.is_file())
}

/// The directories searched for an `ld.lld`, in order: `TCG_LLD_DIR`, the
/// home directory's `.local/bin`, then each `PATH` entry. A directory that
/// holds none (a `TCG_LLD_DIR` included) passes the search to the next.
fn ld_lld_directories(
    tcg_lld_dir: Option<std::ffi::OsString>,
    home: Option<std::ffi::OsString>,
    path: Option<std::ffi::OsString>,
) -> Vec<std::path::PathBuf> {
    tcg_lld_dir
        .map(std::path::PathBuf::from)
        .into_iter()
        .chain(home.map(|home| std::path::Path::new(&home).join(".local/bin")))
        .chain(
            path.map(|paths| std::env::split_paths(&paths).collect::<Vec<_>>())
                .unwrap_or_default(),
        )
        .collect()
}

/// The LLD legs' lookup (L02-P6): `rust-lld` wins over an `ld.lld`, an
/// `ld.lld` stands in when `rust-lld` is missing (run without `-flavor`),
/// and with neither the legs skip, unless `TCG_REQUIRE_LLD` is set, which
/// makes a missing LLD a failure.
#[test]
fn lld_legs_require_an_lld_under_tcg_require_lld() {
    let rust = || Some(std::path::PathBuf::from("/sysroot/bin/rust-lld"));
    let ld = || Some(std::path::PathBuf::from("/home/u/.local/bin/ld.lld"));
    for require in [false, true] {
        let found = resolve_lld(rust(), ld(), require)
            .unwrap()
            .expect("rust-lld");
        assert_eq!((found.program, found.rust_lld), (rust().unwrap(), true));
        let found = resolve_lld(None, ld(), require).unwrap().expect("ld.lld");
        assert_eq!((found.program, found.rust_lld), (ld().unwrap(), false));
    }
    assert!(matches!(resolve_lld(None, None, false), Ok(None)));
    let error = resolve_lld(None, None, true)
        .map(|_| ())
        .expect_err("TCG_REQUIRE_LLD with no LLD");
    assert!(error.contains("TCG_REQUIRE_LLD is set"), "{error}");
    // The `ld.lld` search visits `TCG_LLD_DIR`, then `~/.local/bin`, then
    // `PATH`, whichever are set.
    let os = |text: &str| Some(std::ffi::OsString::from(text));
    let dirs = |paths: &[&str]| {
        paths
            .iter()
            .map(std::path::PathBuf::from)
            .collect::<Vec<_>>()
    };
    assert_eq!(
        ld_lld_directories(os("/lld"), os("/home/u"), os("/a:/b")),
        dirs(&["/lld", "/home/u/.local/bin", "/a", "/b"])
    );
    assert_eq!(
        ld_lld_directories(None, os("/home/u"), os("/a")),
        dirs(&["/home/u/.local/bin", "/a"])
    );
    assert_eq!(ld_lld_directories(os("/lld"), None, None), dirs(&["/lld"]));
}

/// `rust-lld` of the installed Trust package (`trustc`, the compiler this
/// checkout builds with). trustc refuses to run under any TRUST_CG_*/TCG_*
/// control a gate may export to this test, so they are removed.
fn rust_lld() -> Option<std::path::PathBuf> {
    use std::process::Command;
    let trustc = || {
        let mut command = Command::new("trustc");
        for (key, _) in std::env::vars_os() {
            let key_text = key.to_string_lossy();
            if key_text.starts_with("TRUST_CG_") || key_text.starts_with("TCG_") {
                command.env_remove(&key);
            }
        }
        command
    };
    let sysroot = trustc().args(["--print", "sysroot"]).output().ok()?;
    let verbose = trustc().arg("-vV").output().ok()?;
    let host = String::from_utf8(verbose.stdout)
        .ok()?
        .lines()
        .find_map(|line| line.strip_prefix("host: ").map(str::to_owned))?;
    let path = std::path::PathBuf::from(String::from_utf8(sysroot.stdout).ok()?.trim())
        .join("lib/rustlib")
        .join(host)
        .join("bin/rust-lld");
    path.is_file().then_some(path)
}

struct Scratch(fresh_dir::ScratchDir);

impl Scratch {
    fn new(label: &str) -> Self {
        let dir = fresh_dir::create(&format!("trust-cg-relocation-model-{label}-"));
        Self(dir)
    }

    fn write(&self, name: &str, bytes: &[u8]) -> std::path::PathBuf {
        let path = self.0.join(name);
        std::fs::write(&path, bytes).unwrap();
        path
    }
}

fn lld(lld: &Lld, args: &[&std::ffi::OsStr]) -> std::process::Output {
    let mut command = std::process::Command::new(&lld.program);
    if lld.rust_lld {
        command.args(["-flavor", "gnu"]);
    }
    command
        .args(["-m", "aarch64linux"])
        .args(args)
        .output()
        .expect("LLD launches")
}

fn lld_ok(linker: &Lld, args: &[&std::ffi::OsStr]) {
    let output = lld(linker, args);
    assert!(
        output.status.success(),
        "{} {args:?} failed:\n{}",
        linker.program.display(),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// A linked ELF image (ET_EXEC or ET_DYN) read without the production writer.
struct Image {
    bytes: Vec<u8>,
    sections: Vec<(Section, u64)>,
}

impl Image {
    fn read(path: &std::path::Path) -> Self {
        let bytes = std::fs::read(path).unwrap();
        assert_eq!(&bytes[..6], b"\x7fELF\x02\x01");
        assert!(matches!(u16le(&bytes, 16), 2 | 3), "ET_EXEC or ET_DYN");
        assert_eq!(u16le(&bytes, 18), 183);
        let shoff = u64le(&bytes, 0x28) as usize;
        let shnum = u16le(&bytes, 0x3c) as usize;
        let shstr = u64le(&bytes, shoff + u16le(&bytes, 0x3e) as usize * 64 + 0x18) as usize;
        let sections = (0..shnum)
            .map(|index| {
                let header = shoff + index * 64;
                (
                    Section {
                        name: cstr(&bytes, shstr + u32le(&bytes, header) as usize),
                        sh_type: u32le(&bytes, header + 4),
                        offset: u64le(&bytes, header + 0x18) as usize,
                        size: u64le(&bytes, header + 0x20) as usize,
                        link: u32le(&bytes, header + 0x28),
                        info: u32le(&bytes, header + 0x2c),
                    },
                    u64le(&bytes, header + 0x10),
                )
            })
            .collect();
        Self { bytes, sections }
    }

    fn symbols(&self, table_type: u32) -> Vec<Symbol> {
        let Some((table, _)) = self.sections.iter().find(|(s, _)| s.sh_type == table_type) else {
            return Vec::new();
        };
        let strings = &self.sections[table.link as usize].0;
        (0..table.size / 24)
            .map(|index| {
                let entry = table.offset + index * 24;
                Symbol {
                    name: cstr(
                        &self.bytes,
                        strings.offset + u32le(&self.bytes, entry) as usize,
                    ),
                    info: self.bytes[entry + 4],
                    other: self.bytes[entry + 5],
                    shndx: u16le(&self.bytes, entry + 6),
                    value: u64le(&self.bytes, entry + 8),
                    size: u64le(&self.bytes, entry + 16),
                }
            })
            .collect()
    }

    /// `(r_type, symbol name)` of every dynamic relocation (`.rela.dyn`,
    /// `.rela.plt`), resolved through the dynamic symbol table.
    fn dynamic_relocs(&self) -> Vec<(u32, String)> {
        let dynsym = self.symbols(11);
        let mut out = Vec::new();
        for (section, _) in &self.sections {
            if section.sh_type != 4 || !section.name.starts_with(".rela.") {
                continue;
            }
            for index in 0..section.size / 24 {
                let entry = section.offset + index * 24;
                let info = u64le(&self.bytes, entry + 8);
                let symbol = (info >> 32) as usize;
                out.push((
                    (info & 0xffff_ffff) as u32,
                    dynsym
                        .get(symbol)
                        .map(|s| s.name.clone())
                        .unwrap_or_default(),
                ));
            }
        }
        out
    }

    /// The instruction word at virtual address `address`.
    fn word_at(&self, address: u64) -> u32 {
        let (section, base) = self
            .sections
            .iter()
            .find(|(section, base)| {
                section.sh_type == 1
                    && address >= *base
                    && address + 4 <= *base + section.size as u64
            })
            .expect("address inside a PROGBITS section");
        u32le(&self.bytes, section.offset + (address - base) as usize)
    }

    /// Words of function `name` (from `.symtab`).
    fn function_words(&self, name: &str) -> Vec<u32> {
        let symbol = self
            .symbols(2)
            .into_iter()
            .find(|symbol| symbol.name == name)
            .unwrap_or_else(|| panic!("`{name}` in .symtab"));
        (0..symbol.size / 4)
            .map(|index| self.word_at(symbol.value + 4 * index))
            .collect()
    }

    fn tls_alignment(&self) -> u64 {
        let phoff = u64le(&self.bytes, 0x20) as usize;
        let phnum = u16le(&self.bytes, 0x38) as usize;
        (0..phnum)
            .map(|index| phoff + index * 56)
            .find(|&header| u32le(&self.bytes, header) == PT_TLS)
            .map(|header| u64le(&self.bytes, header + 48))
            .expect("PT_TLS program header")
    }
}

/// The four linker-owned TLSDESC slots of `function`: the four words before
/// its `MRS Xt, TPIDR_EL0`.
fn tls_slots(image: &Image, function: &str) -> [u32; 4] {
    let words = image.function_words(function);
    let mrs = words
        .iter()
        .position(|word| word & 0xffff_ffe0 == 0xd53b_d040)
        .unwrap_or_else(|| panic!("`{function}` reads TPIDR_EL0"));
    assert!(
        mrs >= 4,
        "`{function}` has four slots before its TPIDR_EL0 read"
    );
    words[mrs - 4..mrs].try_into().unwrap()
}

/// Decode a linker local-exec relaxation of the slots: one `MOVZ x0, #hi, LSL
/// #16`, one `MOVK x0, #lo` and two NOPs, returning the TP-relative offset.
fn local_exec_value(slots: [u32; 4]) -> Option<u64> {
    let mut high = None;
    let mut low = None;
    let mut nops = 0;
    for word in slots {
        if word == NOP {
            nops += 1;
        } else if word & 0xffe0_001f == 0xd2a0_0000 {
            high = Some(u64::from((word >> 5) & 0xffff));
        } else if word & 0xffe0_001f == 0xf280_0000 {
            low = Some(u64::from((word >> 5) & 0xffff));
        } else {
            return None;
        }
    }
    (nops == 2).then_some((high? << 16) | low?)
}

/// A trust-cg provider object: `rm_ext_data`, the thread-local `rm_tls_imp`
/// and one function named `entry` (never executed; `_start` for executables).
fn provider_object(entry: &str) -> Vec<u8> {
    use trust_cg_ir::function::{MachFunction, Signature};
    use trust_cg_ir::inst::{AArch64Opcode, MachInst};
    let pipeline = Pipeline::new(PipelineConfig {
        target_triple: LINUX.to_owned(),
        relocation_model: RelocationModel::Pic,
        ..PipelineConfig::default()
    });
    let mut function = MachFunction::new(entry.into(), Signature::new(vec![], vec![]));
    let ret = function.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    function.append_inst(function.entry, ret);
    let globals = vec![
        data_global("rm_ext_data", true, Visibility::Default),
        ObjectGlobal {
            is_thread_local: true,
            data: 0x7777_u64.to_le_bytes().to_vec(),
            ..data_global("rm_tls_imp", true, Visibility::Default)
        },
    ];
    pipeline
        .compile_module_with_globals(&[function], &globals)
        .expect("provider object")
}

#[test]
fn lld_links_pic_objects_into_text_clean_shared_objects() {
    let Some(linker) = lld_for("lld_links_pic_objects_into_text_clean_shared_objects") else {
        return;
    };
    let scratch = Scratch::new("shared");
    for opt in LEVELS {
        let object = scratch.write(
            &format!("pic-{opt:?}.o"),
            &compile(opt, RelocationModel::Pic),
        );
        let library = scratch.0.join(format!("libpic-{opt:?}.so"));
        lld_ok(
            &linker,
            &[
                "-shared".as_ref(),
                "-z".as_ref(),
                "text".as_ref(),
                "-o".as_ref(),
                library.as_os_str(),
                object.as_os_str(),
            ],
        );
        let image = Image::read(&library);
        let relocs = image.dynamic_relocs();
        for want in [
            (R_AARCH64_TLSDESC, "rm_tls_def"),
            (R_AARCH64_TLSDESC, "rm_tls_imp"),
            (R_AARCH64_GLOB_DAT, "rm_pub_data"),
            (R_AARCH64_GLOB_DAT, "rm_ext_data"),
            (R_AARCH64_GLOB_DAT, "rm_pub_fn"),
            (R_AARCH64_JUMP_SLOT, "rm_pub_fn"),
        ] {
            assert!(
                relocs.contains(&(want.0, want.1.to_owned())),
                "{opt:?}: missing dynamic relocation {want:?} in {relocs:?}"
            );
        }
        for local in ["rm_hid_data", "rm_prot_data", "rm_loc_data"] {
            assert!(
                relocs.iter().all(|(_, name)| name != local),
                "{opt:?}: `{local}` binds locally and needs no dynamic relocation: {relocs:?}"
            );
        }
        let dynsym = image.symbols(11);
        assert!(
            dynsym
                .iter()
                .all(|symbol| symbol.name != "rm_hid_data" && symbol.name != "rm_loc_data")
        );
        let protected = dynsym
            .iter()
            .find(|symbol| symbol.name == "rm_prot_data")
            .expect("protected data is exported");
        assert_eq!(protected.other & 3, STV_PROTECTED);
        // The TLSDESC slots stay a descriptor call in a shared object.
        let slots = tls_slots(&image, "rm_addr_tls_def");
        assert_eq!(slots[0] & 0x9f00_001f, 0x9000_0000, "{opt:?}: ADRP x0");
        assert_eq!(
            slots[1] & 0xffc0_03ff,
            0xf940_0001,
            "{opt:?}: LDR x1, [x0, #lo12]"
        );
        assert_eq!(
            slots[2] & 0xffc0_03ff,
            0x9100_0000,
            "{opt:?}: ADD x0, x0, #lo12"
        );
        assert_eq!(slots[3], 0xd63f_0020, "{opt:?}: BLR x1");
    }
    // Negative control: the static model's PC-relative references to
    // preemptible definitions cannot be linked into a shared object.
    let object = scratch.write("static.o", &compile(OptLevel::O2, RelocationModel::Static));
    let library = scratch.0.join("libstatic.so");
    let output = lld(
        &linker,
        &[
            "-shared".as_ref(),
            "-o".as_ref(),
            library.as_os_str(),
            object.as_os_str(),
        ],
    );
    assert!(
        !output.status.success(),
        "the static model must not link into -shared"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("recompile with -fPIC"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    std::fs::remove_dir_all(&scratch.0).unwrap();
}

#[test]
fn lld_links_pic_weak_linkage_into_text_clean_shared_objects() {
    let Some(linker) = lld_for("lld_links_pic_weak_linkage_into_text_clean_shared_objects") else {
        return;
    };
    let scratch = Scratch::new("weak-shared");
    for opt in LEVELS {
        let object = scratch.write(
            &format!("weak-pic-{opt:?}.o"),
            &compile_linkage(opt, RelocationModel::Pic, false),
        );
        let library = scratch.0.join(format!("libweak-{opt:?}.so"));
        lld_ok(
            &linker,
            &[
                "-shared".as_ref(),
                "-z".as_ref(),
                "text".as_ref(),
                "-o".as_ref(),
                library.as_os_str(),
                object.as_os_str(),
            ],
        );
        let image = Image::read(&library);
        let relocs = image.dynamic_relocs();
        for want in [
            (R_AARCH64_GLOB_DAT, "rm_weak_fn"),
            (R_AARCH64_GLOB_DAT, "rm_odr_fn"),
            (R_AARCH64_GLOB_DAT, "rm_weak_ref_fn"),
            (R_AARCH64_GLOB_DAT, "rm_weak_ref_data"),
            (R_AARCH64_JUMP_SLOT, "rm_weak_fn"),
        ] {
            assert!(
                relocs.contains(&(want.0, want.1.to_owned())),
                "{opt:?}: missing dynamic relocation {want:?} in {relocs:?}"
            );
        }
        let dynsym = image.symbols(11);
        for (name, defined) in [
            ("rm_weak_fn", true),
            ("rm_odr_fn", true),
            ("rm_weak_ref_fn", false),
            ("rm_weak_ref_data", false),
        ] {
            let symbol = dynsym
                .iter()
                .find(|symbol| symbol.name == name)
                .unwrap_or_else(|| panic!("{opt:?}: `{name}` in .dynsym"));
            assert_eq!(symbol.info >> 4, STB_WEAK, "{opt:?}: `{name}` stays weak");
            assert_eq!(symbol.shndx != 0, defined, "{opt:?}: `{name}` definedness");
        }
    }
    // Negative control: the static model addresses the weak definitions
    // PC-relatively, which a shared object cannot preempt.
    let object = scratch.write(
        "weak-static.o",
        &compile_linkage(OptLevel::O2, RelocationModel::Static, false),
    );
    let library = scratch.0.join("libweak-static.so");
    let output = lld(
        &linker,
        &[
            "-shared".as_ref(),
            "-o".as_ref(),
            library.as_os_str(),
            object.as_os_str(),
        ],
    );
    assert!(
        !output.status.success(),
        "the static model must not link into -shared"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("recompile with -fPIC"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    std::fs::remove_dir_all(&scratch.0).unwrap();
}

#[test]
fn lld_relaxes_tlsdesc_slots_in_executables() {
    let Some(linker) = lld_for("lld_relaxes_tlsdesc_slots_in_executables") else {
        return;
    };
    let scratch = Scratch::new("relax");
    let provider = scratch.write("provider.o", &provider_object("_start"));
    let tls_provider = scratch.write("tlsprov.o", &provider_object("rm_tlsprov_anchor"));
    let shared_provider = scratch.0.join("libtlsprov.so");
    lld_ok(
        &linker,
        &[
            "-shared".as_ref(),
            "-o".as_ref(),
            shared_provider.as_os_str(),
            tls_provider.as_os_str(),
        ],
    );
    let start = scratch.write("start.o", &{
        use trust_cg_ir::function::{MachFunction, Signature};
        use trust_cg_ir::inst::{AArch64Opcode, MachInst};
        let mut start = MachFunction::new("_start".into(), Signature::new(vec![], vec![]));
        let ret = start.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        start.append_inst(start.entry, ret);
        Pipeline::new(PipelineConfig {
            target_triple: LINUX.to_owned(),
            ..PipelineConfig::default()
        })
        .compile_module_with_globals(&[start], &[])
        .expect("start object")
    });
    for opt in LEVELS {
        let object = scratch.write(
            &format!("pic-{opt:?}.o"),
            &compile(opt, RelocationModel::Pic),
        );

        // Static executable: both thread-locals live in the executable, so the
        // linker relaxes general-dynamic to local-exec. The relaxed constant
        // must equal the variable's TP offset under the AArch64 variant-1
        // layout: align_up(16, PT_TLS alignment) + st_value.
        let executable = scratch.0.join(format!("static-{opt:?}"));
        lld_ok(
            &linker,
            &[
                "-static".as_ref(),
                "-e".as_ref(),
                "_start".as_ref(),
                "-o".as_ref(),
                executable.as_os_str(),
                object.as_os_str(),
                provider.as_os_str(),
            ],
        );
        let image = Image::read(&executable);
        assert!(image.dynamic_relocs().is_empty(), "{opt:?}: static image");
        let tcb = 16u64.next_multiple_of(image.tls_alignment());
        for (function, symbol) in [
            ("rm_addr_tls_def", "rm_tls_def"),
            ("rm_addr_tls_imp", "rm_tls_imp"),
        ] {
            let variable = image
                .symbols(2)
                .into_iter()
                .find(|s| s.name == symbol)
                .unwrap_or_else(|| panic!("`{symbol}` in .symtab"));
            assert_eq!(variable.info & 0xf, STT_TLS);
            assert_eq!(
                local_exec_value(tls_slots(&image, function)),
                Some(tcb + variable.value),
                "{opt:?} {function}: relaxed local-exec slots must address `{symbol}`"
            );
        }

        // PIE importing `rm_tls_imp` from a shared object: the executable's
        // own definition relaxes to local-exec, the import to initial-exec
        // (a GOT-held TP offset with a dynamic TLS_TPREL64).
        let pie = scratch.0.join(format!("pie-{opt:?}"));
        lld_ok(
            &linker,
            &[
                "-pie".as_ref(),
                "-e".as_ref(),
                "_start".as_ref(),
                "-o".as_ref(),
                pie.as_os_str(),
                object.as_os_str(),
                start.as_os_str(),
                shared_provider.as_os_str(),
            ],
        );
        let image = Image::read(&pie);
        assert!(
            image
                .dynamic_relocs()
                .contains(&(R_AARCH64_TLS_TPREL64, "rm_tls_imp".to_owned())),
            "{opt:?}: initial-exec GOT slot for the imported thread-local"
        );
        assert!(
            image
                .dynamic_relocs()
                .iter()
                .all(|(kind, _)| *kind != R_AARCH64_TLSDESC),
            "{opt:?}: an executable needs no TLS descriptor"
        );
        let slots = tls_slots(&image, "rm_addr_tls_imp");
        assert_eq!(
            slots[0] & 0x9f00_001f,
            0x9000_0000,
            "{opt:?}: ADRP x0 (GOT page)"
        );
        assert_eq!(
            slots[1] & 0xffc0_03ff,
            0xf940_0000,
            "{opt:?}: LDR x0, [x0, #slot]"
        );
        assert_eq!(&slots[2..], &[NOP, NOP], "{opt:?}");
        assert!(
            local_exec_value(tls_slots(&image, "rm_addr_tls_def")).is_some(),
            "{opt:?}"
        );
    }
    std::fs::remove_dir_all(&scratch.0).unwrap();
}

// ---------------------------------------------------------------------------
// Linux-native controls (aarch64-unknown-linux-gnu hosts only)
// ---------------------------------------------------------------------------

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[path = "common/rosetta.rs"]
mod native_process;

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
mod native {
    use super::{LEVELS, RelocationModel, Scratch, compile, initial_value, native_process};
    use std::path::Path;
    use std::process::Command;

    fn checked(command: &mut Command, timeout: std::time::Duration) -> std::process::Output {
        let result = native_process::command_output_with_timeout(command, timeout)
            .unwrap_or_else(|error| panic!("required native command {command:?}: {error}"));
        assert!(
            !result.timed_out && result.output.status.success(),
            "{command:?}: {}\nstdout={}\nstderr={}",
            result.output.status,
            String::from_utf8_lossy(&result.output.stdout),
            String::from_utf8_lossy(&result.output.stderr),
        );
        result.output
    }

    /// Initial values as C literals, indexed like `GLOBALS`.
    fn defines() -> String {
        [
            ("PUB_INIT", 0),
            ("HID_INIT", 1),
            ("PROT_INIT", 2),
            ("LOC_INIT", 3),
            ("TLS_DEF_INIT", 5),
        ]
        .iter()
        .map(|(name, index)| format!("#define {name} UINT64_C({:#x})\n", initial_value(*index)))
        .collect()
    }

    /// C compiled INTO the library/executable next to the CG object: it
    /// defines the CG imports and gives C-compiled views of both thread-locals.
    const HELPER: &str = r#"
#include <stdint.h>
uint64_t rm_ext_data = UINT64_C(0x0e0e0e0e0e0e0e0e);
__thread uint64_t rm_tls_imp = UINT64_C(0x7777);
extern __thread uint64_t rm_tls_def;
uint64_t *c_addr_tls_def(void) { return &rm_tls_def; }
uint64_t *c_addr_tls_imp(void) { return &rm_tls_imp; }
"#;

    /// Shared TLS exercise: three threads compare CG and C views of both
    /// thread-locals, check the initial template values, mutate their own
    /// copies and require distinct per-thread addresses.
    const TLS_THREADS: &str = r#"
static addr_fn cg_tls_def, cg_tls_imp, c_tls_def, c_tls_imp;
static pthread_barrier_t barrier;
static uintptr_t def_addrs[3], imp_addrs[3];
static int check_thread(int id) {
    uint64_t *d = cg_tls_def(), *i = cg_tls_imp();
    if (d != c_tls_def() || i != c_tls_imp() || d == i) return 10;
    if (*d != TLS_DEF_INIT || *i != UINT64_C(0x7777)) return 11;
    def_addrs[id] = (uintptr_t)d;
    imp_addrs[id] = (uintptr_t)i;
    return 0;
}
static void *worker(void *arg) {
    int id = (int)(intptr_t)arg;
    int failed = check_thread(id);
    pthread_barrier_wait(&barrier);
    for (int round = 0; round < 64; ++round) {
        uint64_t v = ((uint64_t)id << 40) ^ (uint64_t)round;
        *cg_tls_def() = v;
        *c_tls_imp() = ~v;
        if (*c_tls_def() != v || *cg_tls_imp() != ~v) failed = 12;
    }
    pthread_barrier_wait(&barrier);
    for (int other = 0; other < 3; ++other)
        if (other != id && (def_addrs[other] == def_addrs[id] ||
                            imp_addrs[other] == imp_addrs[id])) failed = 13;
    return (void *)(intptr_t)failed;
}
static int run_tls_threads(void) {
    if (check_thread(0)) return 30;
    *cg_tls_def() = 333;
    *cg_tls_imp() = 444;
    if (pthread_barrier_init(&barrier, 0, 2)) return 31;
    pthread_t threads[2];
    for (intptr_t i = 0; i < 2; ++i)
        if (pthread_create(&threads[i], 0, worker, (void *)(i + 1))) return 32;
    for (int i = 0; i < 2; ++i) {
        void *result;
        if (pthread_join(threads[i], &result) || result) return 33;
    }
    if (*c_tls_def() != 333 || *c_tls_imp() != 444) return 34;
    if (def_addrs[0] == def_addrs[1] || def_addrs[0] == def_addrs[2]) return 35;
    return pthread_barrier_destroy(&barrier) ? 36 : 0;
}
"#;

    /// `dlopen`s the CG shared object and checks preemption, visibility and
    /// dynamic TLS. With `-DINTERPOSE` the executable exports its own
    /// `rm_pub_data`, `rm_pub_fn` and `rm_prot_data`: the library's GOT and
    /// PLT must bind the first two to the executable, never the protected one.
    const DLOPEN_DRIVER: &str = r#"
#include <dlfcn.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <unistd.h>
typedef uint64_t *(*addr_fn)(void);
typedef uint64_t (*unary_fn)(uint64_t);
typedef unary_fn (*fn_addr_fn)(void);
#ifdef INTERPOSE
uint64_t rm_pub_data = UINT64_C(0xfeedf00dfeedf00d);
uint64_t rm_prot_data = UINT64_C(0xdeadbeefdeadbeef);
uint64_t rm_pub_fn(uint64_t x) { return x ^ UINT64_C(0xabcdef); }
#endif
static void *lib;
static void *need(const char *name) {
    void *p = dlsym(lib, name);
    if (!p) { fprintf(stderr, "missing %s: %s\n", name, dlerror()); _exit(90); }
    return p;
}
TLS_THREADS
int main(int argc, char **argv) {
    if (argc != 2) return 2;
    lib = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
    if (!lib) { fprintf(stderr, "dlopen: %s\n", dlerror()); return 3; }
    addr_fn cg_pub = (addr_fn)need("rm_addr_pub_data");
    addr_fn cg_hid = (addr_fn)need("rm_addr_hid_data");
    addr_fn cg_prot = (addr_fn)need("rm_addr_prot_data");
    addr_fn cg_loc = (addr_fn)need("rm_addr_loc_data");
    addr_fn cg_ext = (addr_fn)need("rm_addr_ext_data");
    unary_fn cg_call = (unary_fn)need("rm_call_pub_fn");
    fn_addr_fn cg_fn_addr = (fn_addr_fn)need("rm_addr_pub_fn");
    cg_tls_def = (addr_fn)need("rm_addr_tls_def");
    cg_tls_imp = (addr_fn)need("rm_addr_tls_imp");
    c_tls_def = (addr_fn)need("c_addr_tls_def");
    c_tls_imp = (addr_fn)need("c_addr_tls_imp");
    uint64_t *lib_pub = (uint64_t *)need("rm_pub_data");
#ifdef INTERPOSE
    if (cg_pub() != &rm_pub_data || cg_pub() == lib_pub) return 20;
    if (cg_call(5) != (UINT64_C(5) ^ UINT64_C(0xabcdef))) return 21;
    if (cg_fn_addr() != rm_pub_fn) return 22;
    if (cg_prot() == &rm_prot_data) return 23;
#else
    if (cg_pub() != lib_pub || *lib_pub != PUB_INIT) return 20;
    if (cg_call(5) != UINT64_C(22)) return 21;
    if (cg_fn_addr() != (unary_fn)need("rm_pub_fn")) return 22;
#endif
    if (*cg_hid() != HID_INIT || *cg_prot() != PROT_INIT || *cg_loc() != LOC_INIT) return 24;
    if (cg_ext() != (uint64_t *)need("rm_ext_data") ||
        *cg_ext() != UINT64_C(0x0e0e0e0e0e0e0e0e)) return 25;
    if (dlsym(lib, "rm_hid_data") || dlsym(lib, "rm_loc_data")) return 26;
    int tls = run_tls_threads();
    if (tls) return tls;
    puts("CG pic shared object: preemption, visibility and dlopen TLS matched in three threads");
    return dlclose(lib) ? 91 : 0;
}
"#;

    /// Executable-model driver: the CG object is linked into the executable
    /// with the C helper (local-exec for the CG definition, initial-exec for
    /// the helper's thread-local, both relaxed or resolved by the linker).
    const EXEC_DRIVER: &str = r#"
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
typedef uint64_t *(*addr_fn)(void);
extern uint64_t *rm_addr_pub_data(void), *rm_addr_hid_data(void), *rm_addr_loc_data(void);
extern uint64_t *rm_addr_ext_data(void), *rm_addr_tls_def(void), *rm_addr_tls_imp(void);
extern uint64_t *c_addr_tls_def(void), *c_addr_tls_imp(void);
extern uint64_t rm_pub_data, rm_ext_data;
extern uint64_t rm_call_pub_fn(uint64_t);
TLS_THREADS
int main(void) {
    cg_tls_def = rm_addr_tls_def;
    cg_tls_imp = rm_addr_tls_imp;
    c_tls_def = c_addr_tls_def;
    c_tls_imp = c_addr_tls_imp;
    if (rm_addr_pub_data() != &rm_pub_data || rm_pub_data != PUB_INIT) return 20;
    if (rm_addr_ext_data() != &rm_ext_data) return 21;
    if (*rm_addr_hid_data() != HID_INIT || *rm_addr_loc_data() != LOC_INIT) return 22;
    if (rm_call_pub_fn(5) != UINT64_C(22)) return 23;
    int tls = run_tls_threads();
    if (tls) return tls;
    puts("CG executable-model object: direct access and LE/IE TLS matched in three threads");
    return 0;
}
"#;

    fn source(dir: &Path, name: &str, body: &str) -> std::path::PathBuf {
        let path = dir.join(name);
        let text = format!(
            "#define _GNU_SOURCE\n#include <stdint.h>\n{}{}",
            defines(),
            body.replace("TLS_THREADS", TLS_THREADS)
        );
        std::fs::write(&path, text).unwrap();
        path
    }

    #[test]
    fn pic_shared_object_dlopen_threads_and_interposition_native() {
        let scratch = Scratch::new("native-dlopen");
        let dir = &scratch.0;
        let helper = source(dir, "helper.c", HELPER);
        let driver = source(dir, "driver.c", DLOPEN_DRIVER);
        let helper_object = dir.join("helper.o");
        checked(
            Command::new("cc")
                .args(["-O2", "-fPIC", "-c"])
                .arg(&helper)
                .arg("-o")
                .arg(&helper_object),
            native_process::codegen_link_timeout(),
        );
        let plain = dir.join("driver");
        let interposing = dir.join("driver-interpose");
        checked(
            Command::new("cc")
                .args(["-O2", "-pthread"])
                .arg(&driver)
                .arg("-o")
                .arg(&plain)
                .arg("-ldl"),
            native_process::codegen_link_timeout(),
        );
        checked(
            Command::new("cc")
                .args(["-O2", "-pthread", "-rdynamic", "-DINTERPOSE"])
                .arg(&driver)
                .arg("-o")
                .arg(&interposing)
                .arg("-ldl"),
            native_process::codegen_link_timeout(),
        );
        let mut executions = 0;
        for opt in LEVELS {
            let object = scratch.write(
                &format!("cg-{opt:?}.o"),
                &compile(opt, RelocationModel::Pic),
            );
            let library = dir.join(format!("libcg-{opt:?}.so"));
            checked(
                Command::new("cc")
                    .args(["-shared", "-pthread", "-Wl,-z,defs,-z,text,-z,now"])
                    .arg(&object)
                    .arg(&helper_object)
                    .arg("-o")
                    .arg(&library),
                native_process::codegen_link_timeout(),
            );
            let dynamic = String::from_utf8(
                checked(
                    Command::new("readelf")
                        .env("LC_ALL", "C")
                        .args(["--wide", "--relocs", "--dynamic"])
                        .arg(&library),
                    native_process::codegen_link_timeout(),
                )
                .stdout,
            )
            .unwrap();
            assert!(!dynamic.contains("TEXTREL"), "{opt:?}: no text relocations");
            assert!(
                dynamic.contains("R_AARCH64_TLSDESC"),
                "{opt:?}: the shared object resolves CG thread-locals through TLS descriptors"
            );
            for (binary, label) in [(&plain, "plain"), (&interposing, "interposed")] {
                let output = checked(
                    Command::new(binary).arg(&library),
                    native_process::codegen_run_timeout(),
                );
                assert_eq!(
                    String::from_utf8_lossy(&output.stdout).trim(),
                    "CG pic shared object: preemption, visibility and dlopen TLS matched in three threads",
                    "{opt:?} {label}"
                );
                executions += 1;
            }
        }
        assert_eq!(executions, 8);

        // Negative control: GNU ld refuses the static model's PC-relative
        // references to preemptible definitions in a shared object.
        let object = scratch.write(
            "static.o",
            &compile(super::OptLevel::O2, RelocationModel::Static),
        );
        let result = native_process::command_output_with_timeout(
            Command::new("cc")
                .args(["-shared"])
                .arg(&object)
                .arg(&helper_object)
                .arg("-o")
                .arg(dir.join("libstatic.so")),
            native_process::codegen_link_timeout(),
        )
        .expect("cc launches");
        assert!(
            !result.output.status.success(),
            "static model must not link -shared"
        );
        assert!(
            String::from_utf8_lossy(&result.output.stderr).contains("recompile with -fPIC"),
            "{}",
            String::from_utf8_lossy(&result.output.stderr)
        );
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn executable_models_link_and_run_with_le_ie_tls_native() {
        let scratch = Scratch::new("native-exec");
        let dir = &scratch.0;
        let helper = source(dir, "helper.c", HELPER);
        let driver = source(dir, "driver.c", EXEC_DRIVER);
        let mut executions = 0;
        for (model, pie_flag) in [
            (RelocationModel::Static, "-no-pie"),
            (RelocationModel::Pie, "-pie"),
        ] {
            for opt in LEVELS {
                let object = scratch.write(&format!("cg-{model}-{opt:?}.o"), &compile(opt, model));
                let binary = dir.join(format!("exec-{model}-{opt:?}"));
                checked(
                    Command::new("cc")
                        .args(["-O2", "-pthread", pie_flag])
                        .arg(&driver)
                        .arg(&helper)
                        .arg(&object)
                        .arg("-o")
                        .arg(&binary),
                    native_process::codegen_link_timeout(),
                );
                let output = checked(
                    &mut Command::new(&binary),
                    native_process::codegen_run_timeout(),
                );
                assert_eq!(
                    String::from_utf8_lossy(&output.stdout).trim(),
                    "CG executable-model object: direct access and LE/IE TLS matched in three threads",
                    "{model} {opt:?}"
                );
                executions += 1;
            }
        }
        assert_eq!(executions, 8);
        std::fs::remove_dir_all(dir).unwrap();
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
