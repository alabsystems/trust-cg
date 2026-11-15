// trust-cg-codegen/tests/v41_abi_residue_objects.rs
//
// trust-ir v41 ABI / linkage residue, PROVED at the object level: for each
// field the emitters consume, the emitted Mach-O / ELF object is reparsed and
// the exact symbol or section bits are asserted; for each field they refuse,
// the compiler's typed refusal is asserted. Both object formats are produced
// on any host by pinning the target triple, so nothing here depends on the
// machine running the test.
//
//   Linkage::{WeakOdr, LinkOnceOdr}  global definition -> N_WEAK_DEF / STB_WEAK
//   Linkage::AvailableExternally     global -> undefined external (never defined)
//                                    function -> no body emitted; call resolves
//                                    to the external symbol
//   Linkage::ExternalWeak            AArch64 ELF: weak undefined (STB_WEAK
//                                    UND) declaration; every other object
//                                    path REFUSED; a body or initializer is
//                                    refused everywhere
//   Function linkage                 AArch64 and x86-64 ELF: Internal/Private
//                                    STB_LOCAL, Weak/LinkOnce(+ODR) STB_WEAK,
//                                    External STB_GLOBAL; AArch64 and x86-64
//                                    Mach-O: Internal/Private without N_EXT,
//                                    Weak/LinkOnce(+ODR) N_EXT|N_WEAK_DEF
//   Global.visibility                definition -> N_PEXT (hidden) /
//                                    STV_HIDDEN, STV_PROTECTED; import ->
//                                    STV_HIDDEN, STV_PROTECTED on the
//                                    undefined symbol on AArch64 ELF only,
//                                    REFUSED elsewhere
//   Global.retained                  definition -> N_NO_DEAD_STRIP /
//                                    SHF_GNU_RETAIN + ELFOSABI_GNU
//   Global.section                   AArch64: placed by name or refused with a
//                                    named [TCG-SECTION-*] code; x86-64: REFUSED
//   FuncAttrs.naked, global_asm      REFUSED
//   FuncAttrs.target_features        known names compile; unknown REFUSED;
//                                    the vocabulary is parity-checked against
//                                    the backend's own feature enums
//   Function.body_gate               enforced by the compiler and the JIT
//                                    compile service, before any cache
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{AArch64IsaProfile, TargetSpec};
use trust_cg_codegen::x86_64::X86TargetFeature;
use trust_cg_codegen::{
    CompileGeneration, CompileRequest, CompileService, CompileServiceConfig, CompileStatus, Target,
};
use trust_cg_lower::{
    CLEAN_KERNEL_TV_AUTHORITY, CodegenLicensePolicy, GuardCarrierArch, UnlicensedBodyPolicy,
    known_target_features,
};
use trust_ir::value::GlobalId;
use trust_ir::{
    Block, BlockId, BodyGate, Constant, FuncId, FuncTy, Function, Global, Inst, InstrNode, Linkage,
    Module, Ty, ValueId, Visibility,
};

// =============================================================================
// Object reparse (minimal, self-contained)
// =============================================================================

fn rd_u16(b: &[u8], off: usize) -> u16 {
    u16::from_le_bytes([b[off], b[off + 1]])
}
fn rd_u32(b: &[u8], off: usize) -> u32 {
    u32::from_le_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]])
}
fn rd_u64(b: &[u8], off: usize) -> u64 {
    u64::from_le_bytes(b[off..off + 8].try_into().unwrap())
}
fn cstr(b: &[u8], start: usize) -> String {
    let mut end = start;
    while end < b.len() && b[end] != 0 {
        end += 1;
    }
    String::from_utf8_lossy(&b[start..end]).to_string()
}

/// `<mach-o/nlist.h>` bits.
const N_TYPE_MASK: u8 = 0x0e;
const N_UNDF: u8 = 0x00;
const N_SECT: u8 = 0x0e;
const N_EXT: u8 = 0x01;
const N_PEXT: u8 = 0x10;
const N_WEAK_DEF: u16 = 0x0080;
const N_NO_DEAD_STRIP: u16 = 0x0020;

#[derive(Debug, Clone, Copy)]
struct MachoSym {
    n_type: u8,
    n_sect: u8,
    n_desc: u16,
}

fn macho_symbols(bytes: &[u8]) -> HashMap<String, MachoSym> {
    assert_eq!(
        &bytes[0..4],
        &0xFEED_FACFu32.to_le_bytes(),
        "not a 64-bit Mach-O"
    );
    let ncmds = rd_u32(bytes, 16);
    let mut off = 32;
    let (mut symoff, mut nsyms, mut stroff) = (0usize, 0u32, 0usize);
    for _ in 0..ncmds {
        let cmd = rd_u32(bytes, off);
        let size = rd_u32(bytes, off + 4) as usize;
        if cmd == 0x2 {
            symoff = rd_u32(bytes, off + 8) as usize;
            nsyms = rd_u32(bytes, off + 12);
            stroff = rd_u32(bytes, off + 16) as usize;
        }
        off += size;
    }
    let mut out = HashMap::new();
    for i in 0..nsyms as usize {
        let e = symoff + i * 16;
        let name = cstr(bytes, stroff + rd_u32(bytes, e) as usize);
        out.insert(
            name,
            MachoSym {
                n_type: bytes[e + 4],
                n_sect: bytes[e + 5],
                n_desc: rd_u16(bytes, e + 6),
            },
        );
    }
    out
}

/// `<elf.h>` values.
const STB_LOCAL: u8 = 0;
const STB_GLOBAL: u8 = 1;
const STB_WEAK: u8 = 2;
const STV_DEFAULT: u8 = 0;
const STV_HIDDEN: u8 = 2;
const STV_PROTECTED: u8 = 3;
const SHF_GNU_RETAIN: u64 = 0x200000;
const ELFOSABI_NONE: u8 = 0;
const ELFOSABI_GNU: u8 = 3;

#[derive(Debug, Clone, Copy)]
struct ElfSym {
    st_bind: u8,
    st_visibility: u8,
    st_shndx: u16,
}

struct ElfObject {
    osabi: u8,
    /// section header index -> (name, sh_flags)
    sections: Vec<(String, u64)>,
    symbols: HashMap<String, ElfSym>,
}

fn elf_object(bytes: &[u8]) -> ElfObject {
    assert_eq!(&bytes[0..4], b"\x7FELF");
    assert_eq!(bytes[4], 2, "not ELF64");
    let osabi = bytes[7];
    let shoff = rd_u64(bytes, 0x28) as usize;
    let shentsize = rd_u16(bytes, 0x3A) as usize;
    let shnum = rd_u16(bytes, 0x3C) as usize;
    let shstrndx = rd_u16(bytes, 0x3E) as usize;
    let sh = |i: usize| shoff + i * shentsize;
    let shstr_off = rd_u64(bytes, sh(shstrndx) + 0x18) as usize;
    let mut sections = Vec::new();
    for i in 0..shnum {
        let name = cstr(bytes, shstr_off + rd_u32(bytes, sh(i)) as usize);
        sections.push((name, rd_u64(bytes, sh(i) + 0x08)));
    }
    let mut symbols = HashMap::new();
    for i in 0..shnum {
        if rd_u32(bytes, sh(i) + 0x04) != 2 {
            continue; // SHT_SYMTAB
        }
        let sym_off = rd_u64(bytes, sh(i) + 0x18) as usize;
        let sym_size = rd_u64(bytes, sh(i) + 0x20) as usize;
        let link = rd_u32(bytes, sh(i) + 0x28) as usize;
        let str_off = rd_u64(bytes, sh(link) + 0x18) as usize;
        for e in (sym_off..sym_off + sym_size).step_by(24) {
            let st_name = rd_u32(bytes, e) as usize;
            if st_name == 0 {
                continue;
            }
            symbols.insert(
                cstr(bytes, str_off + st_name),
                ElfSym {
                    st_bind: bytes[e + 4] >> 4,
                    st_visibility: bytes[e + 5] & 0x3,
                    st_shndx: rd_u16(bytes, e + 6),
                },
            );
        }
    }
    ElfObject {
        osabi,
        sections,
        symbols,
    }
}

impl ElfObject {
    fn section_flags_of(&self, symbol: &str) -> u64 {
        let sym = self.symbols[symbol];
        assert_ne!(sym.st_shndx, 0, "{symbol} is undefined");
        self.sections[sym.st_shndx as usize].1
    }
}

// =============================================================================
// Module builders and compilation
// =============================================================================

fn global(name: &str, linkage: Linkage) -> Global {
    Global {
        name: name.to_string(),
        ty: Ty::I64,
        mutable: false,
        initializer: Some(Constant::Int(5)),
        linkage,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

/// `entry: () -> i64` that loads `G` (so an import is REFERENCED and shows up
/// as an undefined symbol) plus the given global.
fn module_with_global(g: Global) -> Module {
    let mut m = Module::new("v41_residue");
    let sig = m
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut entry = Function::new(FuncId::new(0), "entry", sig, BlockId::new(0));
    entry.blocks.push(Block {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::GlobalAddr {
                global: GlobalId::new(0),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(0),
                volatile: false,
                align: Some(8),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    });
    m.functions.push(entry);
    m.globals.push(g);
    m
}

/// `entry: () -> i64` returning a constant; no globals.
fn const_module() -> Module {
    let mut m = Module::new("v41_residue_const");
    let sig = m
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut entry = Function::new(FuncId::new(0), "entry", sig, BlockId::new(0));
    entry.blocks.push(Block {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(7),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }),
        ],
    });
    m.functions.push(entry);
    m
}

/// The pinned target a module with an FFI boundary must carry.
fn target_info_for(triple: &str) -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}

const TRIPLES: [(&str, Target, bool); 4] = [
    ("x86_64-apple-darwin", Target::X86_64, false),
    ("aarch64-apple-darwin", Target::Aarch64, false),
    ("x86_64-unknown-linux-gnu", Target::X86_64, true),
    ("aarch64-unknown-linux-gnu", Target::Aarch64, true),
];

/// The fixtures of this file are hand-built and carry no codegen license
/// (`body_gate: None`), which the compiler's DEFAULT policy refuses (roadmap
/// WS7.5, DG-73). Every compile here therefore states `Permit` explicitly;
/// the license tests below use [`default_compiler_for`] to pin the default.
fn compiler_for(triple: &str, target: Target) -> Compiler {
    default_compiler_for(triple, target).with_codegen_license(
        CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit),
    )
}

/// [`compiler_for`] under the compiler's OWN default license policy.
fn default_compiler_for(triple: &str, target: Target) -> Compiler {
    let config = CompilerConfig {
        opt_level: OptLevel::O0,
        target,
        emit_proofs: false,
        trace_level: CompilerTraceLevel::None,
        emit_debug: false,
        parallel: false,
        cegis_superopt_budget_sec: None,
        enable_fsym_trust_ir_preflight: false,
        enable_jit_fast_regalloc: false,
        jit_validation_mode_override: None,
        jit_external_symbol_resolution:
            trust_cg_codegen::JitExternalSymbolResolutionPolicy::ExplicitThenProcess,
        panic_unwind: false,
        relocation_model: trust_cg_codegen::RelocationModel::Static,
        function_sections: false,
        aarch64_isa_profile: None,
        aarch64_force_frame_pointers: false,
        never_inline: Default::default(),
        eh_frames_cannot_unwind: false,
        eh_nounwind_callees: Default::default(),
        link_unit_definitions: Default::default(),
    };
    Compiler::new_for_target_spec(config, TargetSpec::parse(triple).expect("target triple"))
}

fn compile(module: &Module, triple: &str, target: Target) -> Vec<u8> {
    let result = compiler_for(triple, target)
        .compile(module)
        .unwrap_or_else(|error| panic!("{triple}: compilation must succeed: {error}"));
    assert!(!result.object_code.is_empty());
    result.object_code
}

fn compile_error(module: &Module, triple: &str, target: Target) -> String {
    match compiler_for(triple, target).compile(module) {
        Ok(_) => panic!("{triple}: compilation must be refused"),
        Err(error) => error.to_string(),
    }
}

// =============================================================================
// Linkage
// =============================================================================

#[test]
fn odr_global_definitions_are_emitted_weak_on_every_format() {
    for (triple, target, is_elf) in TRIPLES {
        for linkage in [Linkage::WeakOdr, Linkage::LinkOnceOdr] {
            let obj = compile(&module_with_global(global("G", linkage)), triple, target);
            if is_elf {
                let elf = elf_object(&obj);
                let sym = elf.symbols["G"];
                assert_eq!(sym.st_bind, STB_WEAK, "{triple} {linkage}: STB_WEAK");
                assert_ne!(sym.st_shndx, 0, "{triple} {linkage}: defined");
            } else {
                let sym = macho_symbols(&obj)["_G"];
                assert_ne!(sym.n_desc & N_WEAK_DEF, 0, "{triple} {linkage}: N_WEAK_DEF");
                assert_eq!(
                    sym.n_type & N_TYPE_MASK,
                    N_SECT,
                    "{triple} {linkage}: defined"
                );
            }
        }
        // Control: an `External` definition is strong.
        let obj = compile(
            &module_with_global(global("G", Linkage::External)),
            triple,
            target,
        );
        if is_elf {
            assert_eq!(
                elf_object(&obj).symbols["G"].st_bind,
                STB_GLOBAL,
                "{triple}"
            );
        } else {
            assert_eq!(macho_symbols(&obj)["_G"].n_desc & N_WEAK_DEF, 0, "{triple}");
        }
    }
}

#[test]
fn available_externally_global_is_an_undefined_reference_never_a_definition() {
    for (triple, target, is_elf) in TRIPLES {
        // The initializer is PRESENT and must be ignored: the definition lives
        // elsewhere.
        let obj = compile(
            &module_with_global(global("G", Linkage::AvailableExternally)),
            triple,
            target,
        );
        if is_elf {
            let sym = elf_object(&obj).symbols["G"];
            assert_eq!(sym.st_shndx, 0, "{triple}: undefined");
            assert_eq!(sym.st_bind, STB_GLOBAL, "{triple}: external reference");
        } else {
            let sym = macho_symbols(&obj)["_G"];
            assert_eq!(sym.n_type & N_TYPE_MASK, N_UNDF, "{triple}: undefined");
            assert_ne!(sym.n_type & N_EXT, 0, "{triple}: external reference");
            assert_eq!(sym.n_sect, 0, "{triple}: no section");
        }
    }
}

#[test]
fn available_externally_function_body_is_never_emitted() {
    // `entry` calls `helper`; `helper` has a body but is available_externally.
    let mut m = const_module();
    let sig = m.functions[0].ty;
    let mut helper = Function::new(FuncId::new(1), "helper", sig, BlockId::new(0));
    helper.blocks = m.functions[0].blocks.clone();
    helper.linkage = Linkage::AvailableExternally;
    m.functions.push(helper);
    m.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::Call {
            callee: FuncId::new(1),
            args: vec![],
        })
        .with_result(ValueId::new(0)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }),
    ];
    for (triple, target, is_elf) in TRIPLES {
        let obj = compile(&m, triple, target);
        if is_elf {
            let elf = elf_object(&obj);
            assert_ne!(elf.symbols["entry"].st_shndx, 0, "{triple}: entry defined");
            assert_eq!(
                elf.symbols["helper"].st_shndx, 0,
                "{triple}: helper undefined"
            );
        } else {
            let syms = macho_symbols(&obj);
            assert_eq!(syms["_entry"].n_type & N_TYPE_MASK, N_SECT, "{triple}");
            assert_eq!(syms["_helper"].n_type & N_TYPE_MASK, N_UNDF, "{triple}");
        }
    }
}

/// Function linkage on the object: the AArch64 ELF path places the ODR forms
/// (`LinkOnceOdr`, `WeakOdr`) in their own grouped `.text.<symbol>` section
/// with an `STB_WEAK` symbol, while the interposable base kinds (`Weak`,
/// `LinkOnce`) are plain `STB_WEAK` definitions in the shared `.text` with no
/// group. Another object may replace an interposable definition at link time,
/// so the compiler keeps its body out of the module inliner and the structural
/// purity inference. The Mach-O and x86-64 paths do not consume function
/// linkage: each ODR twin emits exactly what its base kind emits.
#[test]
fn odr_function_linkage_classifies_per_object_format() {
    for (base, odr) in [
        (Linkage::Weak, Linkage::WeakOdr),
        (Linkage::LinkOnce, Linkage::LinkOnceOdr),
    ] {
        for (triple, target, is_elf) in TRIPLES {
            let mut a = const_module();
            a.functions[0].linkage = base;
            let mut b = const_module();
            b.functions[0].linkage = odr;
            let (base_obj, odr_obj) = (compile(&a, triple, target), compile(&b, triple, target));
            if !(is_elf && target == Target::Aarch64) {
                assert_eq!(
                    base_obj, odr_obj,
                    "{triple}: {odr} must emit exactly what {base} emits"
                );
                continue;
            }
            let odr_elf = elf_object(&odr_obj);
            let entry = odr_elf.symbols["entry"];
            assert_eq!(entry.st_bind, STB_WEAK, "{triple} {odr}");
            assert_eq!(
                odr_elf.sections[entry.st_shndx as usize].0, ".text.entry",
                "{triple} {odr}"
            );
            assert!(
                odr_elf.sections.iter().any(|(name, _)| name == ".group"),
                "{triple} {odr}"
            );
            let base_elf = elf_object(&base_obj);
            let entry = base_elf.symbols["entry"];
            assert_eq!(entry.st_bind, STB_WEAK, "{triple} {base}");
            assert_eq!(
                base_elf.sections[entry.st_shndx as usize].0, ".text",
                "{triple} {base}: an interposable definition stays in .text"
            );
            assert!(
                !base_elf.sections.iter().any(|(name, _)| name == ".group"),
                "{triple} {base}: no COMDAT group for an interposable definition"
            );
        }
    }
}

#[test]
fn function_linkage_binds_aarch64_object_definitions() {
    // AArch64 and x86-64 ELF and Mach-O carry function linkage into the
    // symbol table: local definitions local, the weak forms weak, every other
    // definition global. x86-64 ELF binds a module-local definition
    // `STB_LOCAL` under ruling OD-X86-ELF-LOCAL-BINDING-20261027 (read back
    // by `tests/x86_64_elf_symbol_binding.rs`, which also admits references
    // to it there); x86-64 Mach-O binds an unreferenced one non-external
    // since the 2026-10-24 L02-P1 closure audit, through the same facts
    // (OD-MODULE-LOCAL-BINDING-OFF-AARCH64-20261024,
    // OD-X86-BINDING-ONE-CARRIER-20261105). Until that audit the x86-64
    // paths bound the local forms global, and another object's reference or
    // weak definition bound to the module-local body
    // (`module_local_binding_other_targets`).
    for (triple, target, is_elf) in TRIPLES {
        for (linkage, aarch64_elf_bind) in [
            (Linkage::External, STB_GLOBAL),
            (Linkage::Weak, STB_WEAK),
            (Linkage::LinkOnce, STB_WEAK),
            (Linkage::WeakOdr, STB_WEAK),
            (Linkage::LinkOnceOdr, STB_WEAK),
            (Linkage::Internal, STB_LOCAL),
            (Linkage::Private, STB_LOCAL),
        ] {
            let mut m = const_module();
            m.functions[0].linkage = linkage;
            let obj = compile(&m, triple, target);
            if is_elf {
                let want = aarch64_elf_bind;
                let sym = elf_object(&obj).symbols["entry"];
                assert_eq!(sym.st_bind, want, "{triple} {linkage}");
                assert_eq!(sym.st_visibility, STV_DEFAULT, "{triple} {linkage}");
                assert_ne!(sym.st_shndx, 0, "{triple} {linkage}: defined");
            } else {
                let sym = macho_symbols(&obj)["_entry"];
                let (n_type, weak) = match aarch64_elf_bind {
                    STB_LOCAL => (N_SECT, 0),
                    STB_WEAK => (N_SECT | N_EXT, N_WEAK_DEF),
                    _ => (N_SECT | N_EXT, 0),
                };
                assert_eq!(sym.n_type, n_type, "{triple} {linkage}");
                assert_eq!(sym.n_desc & N_WEAK_DEF, weak, "{triple} {linkage}");
            }
        }
    }
}

#[test]
fn external_weak_is_admitted_only_as_an_aarch64_elf_declaration() {
    for (triple, target, is_elf) in TRIPLES {
        let aarch64_elf = is_elf && target == Target::Aarch64;
        // An initializer-less global and a referenced bodyless function.
        let mut g = global("G", Linkage::ExternalWeak);
        g.initializer = None;
        let mut m = module_with_global(g);
        let sig = m.functions[0].ty;
        let mut maybe = Function::new(FuncId::new(1), "maybe", sig, BlockId::new(0));
        maybe.linkage = Linkage::ExternalWeak;
        m.functions.push(maybe);
        // A weak declaration's address is NULLABLE: trust-ir admits it only as
        // `SymbolAddr { addend: 0 }` at `Ty::Ptr` (a direct call is
        // `DirectCallToWeakDeclaration`), and a bodyless declaration is an FFI
        // boundary, so the module pins its target (`TargetInfoRequired`).
        // WS7.3 holds this fixture to that: every ingestion entry refuses
        // what the validator refuses.
        let address_sig = m
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::Ptr],
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        let mut caller = Function::new(
            FuncId::new(2),
            "address_of_maybe",
            address_sig,
            BlockId::new(0),
        );
        caller.blocks.push(Block {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::Ptr,
                    value: Constant::symbol_addr("maybe"),
                })
                .with_result(ValueId::new(0)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(0)],
                }),
            ],
        });
        m.functions.push(caller);
        m.target_info = Some(target_info_for(triple));
        if aarch64_elf {
            let elf = elf_object(&compile(&m, triple, target));
            for name in ["G", "maybe"] {
                let sym = elf.symbols[name];
                assert_eq!(sym.st_bind, STB_WEAK, "{triple} {name}: STB_WEAK");
                assert_eq!(sym.st_shndx, 0, "{triple} {name}: undefined");
            }
        } else {
            let error = compile_error(&m, triple, target);
            assert!(error.contains("external_weak"), "{triple}: {error}");
        }
        // A BODIED ExternalWeak function is not a weak declaration anywhere.
        let mut m = const_module();
        m.functions[0].linkage = Linkage::ExternalWeak;
        let error = compile_error(&m, triple, target);
        assert!(error.contains("external_weak"), "{triple}: {error}");
    }
}

// =============================================================================
// Visibility
// =============================================================================

#[test]
fn definition_visibility_is_honored_per_format() {
    for (triple, target, is_elf) in TRIPLES {
        for (visibility, want_elf, want_macho_type) in [
            (Visibility::Default, STV_DEFAULT, N_SECT | N_EXT),
            (Visibility::Hidden, STV_HIDDEN, N_SECT | N_EXT | N_PEXT),
            // Mach-O has no protected visibility: default there, as in LLVM.
            (Visibility::Protected, STV_PROTECTED, N_SECT | N_EXT),
        ] {
            let mut g = global("G", Linkage::External);
            g.visibility = visibility;
            let obj = compile(&module_with_global(g), triple, target);
            if is_elf {
                let sym = elf_object(&obj).symbols["G"];
                assert_eq!(sym.st_visibility, want_elf, "{triple} {visibility}");
                assert_eq!(sym.st_bind, STB_GLOBAL, "{triple} {visibility}");
            } else {
                let sym = macho_symbols(&obj)["_G"];
                assert_eq!(sym.n_type, want_macho_type, "{triple} {visibility}");
            }
        }
    }
}

/// A data import's hidden or protected visibility is spelled on its
/// undefined symbol by the AArch64 ELF module path (L02-P6) and refused by
/// every other object path.
#[test]
fn import_visibility_is_spelled_on_aarch64_elf_and_refused_elsewhere() {
    for (triple, target, _) in TRIPLES {
        for (visibility, st_visibility) in [
            (Visibility::Hidden, STV_HIDDEN),
            (Visibility::Protected, STV_PROTECTED),
        ] {
            let mut g = global("G", Linkage::External);
            g.initializer = None;
            g.visibility = visibility;
            let module = module_with_global(g);
            if triple == "aarch64-unknown-linux-gnu" {
                let sym = elf_object(&compile(&module, triple, target)).symbols["G"];
                assert_eq!(
                    (sym.st_shndx, sym.st_visibility),
                    (0, st_visibility),
                    "{triple} {visibility}: an undefined symbol with its visibility"
                );
                continue;
            }
            let error = compile_error(&module, triple, target);
            assert!(
                error.contains("visibility") && error.contains("import"),
                "{triple} {visibility}: {error}"
            );
        }
    }
}

// =============================================================================
// Retention
// =============================================================================

#[test]
fn retained_definition_is_no_dead_strip_on_macho_and_gnu_retain_on_elf() {
    for (triple, target, is_elf) in TRIPLES {
        for mutable in [false, true] {
            let mut g = global("G", Linkage::External);
            g.retained = true;
            g.mutable = mutable;
            let obj = compile(&module_with_global(g), triple, target);
            let mut control = global("G", Linkage::External);
            control.mutable = mutable;
            let control_obj = compile(&module_with_global(control), triple, target);
            if is_elf {
                let elf = elf_object(&obj);
                assert_ne!(
                    elf.section_flags_of("G") & SHF_GNU_RETAIN,
                    0,
                    "{triple} mutable={mutable}: SHF_GNU_RETAIN"
                );
                assert_eq!(elf.osabi, ELFOSABI_GNU, "{triple}: GNU OSABI");
                let control = elf_object(&control_obj);
                assert_eq!(
                    control.section_flags_of("G") & SHF_GNU_RETAIN,
                    0,
                    "{triple}"
                );
                assert_eq!(control.osabi, ELFOSABI_NONE, "{triple}");
            } else {
                assert_ne!(
                    macho_symbols(&obj)["_G"].n_desc & N_NO_DEAD_STRIP,
                    0,
                    "{triple} mutable={mutable}: N_NO_DEAD_STRIP"
                );
                assert_eq!(
                    macho_symbols(&control_obj)["_G"].n_desc & N_NO_DEAD_STRIP,
                    0,
                    "{triple}"
                );
            }
        }
    }
}

// =============================================================================
// Refusals through the compiler
// =============================================================================

/// `Global.section` is placed or refused BY NAME per object format: a data
/// global in an executable ELF section and a non-pair Mach-O name are named
/// refusals, a valid name is honored on AArch64 (the symbol lands in that
/// section), and the x86-64 emitters refuse every explicit section. The full
/// placement matrix is pinned in `e2e_aarch64_elf_sections.rs`.
#[test]
fn explicit_section_is_placed_or_refused_by_name_per_format() {
    for (triple, target, is_elf) in TRIPLES {
        let mut g = global("G", Linkage::External);
        g.section = Some(".text.custom".to_string());
        let error = compile_error(&module_with_global(g), triple, target);
        let want = match (target, is_elf) {
            (Target::X86_64, _) => "TCG-SECTION-TARGET",
            (_, true) => "TCG-SECTION-EXEC",
            (_, false) => "TCG-SECTION-MACHO-PAIR",
        };
        assert!(error.contains(want), "{triple}: {error}");

        let name = if is_elf {
            ".rodata.custom"
        } else {
            "__TEXT,__custom"
        };
        let mut g = global("G", Linkage::External);
        g.section = Some(name.to_string());
        let module = module_with_global(g);
        if target == Target::X86_64 {
            let error = compile_error(&module, triple, target);
            assert!(error.contains("TCG-SECTION-TARGET"), "{triple}: {error}");
            continue;
        }
        let obj = compile(&module, triple, target);
        if is_elf {
            let elf = elf_object(&obj);
            let sym = elf.symbols["G"];
            assert_eq!(elf.sections[sym.st_shndx as usize].0, name, "{triple}");
            assert_eq!(elf.section_flags_of("G"), 0x2, "{triple}: SHF_ALLOC only");
        } else {
            let sym = macho_symbols(&obj)["_G"];
            assert_eq!(sym.n_type & N_TYPE_MASK, N_SECT, "{triple}");
        }
    }
}

#[test]
fn naked_and_global_asm_are_refused() {
    for (triple, target, _) in TRIPLES {
        let mut m = const_module();
        m.functions[0].attrs.naked = true;
        let error = compile_error(&m, triple, target);
        assert!(error.contains("#[naked]"), "{triple}: {error}");

        let mut m = const_module();
        m.global_asm.push(".globl marker".to_string());
        let error = compile_error(&m, triple, target);
        assert!(error.contains("global_asm"), "{triple}: {error}");
    }
}

#[test]
fn completeness_claims_are_refused_before_native_emission() {
    use trust_cg_codegen::compiler::CompileError;
    use trust_cg_codegen::pipeline::{PipelineError, encode_tmbc};
    use trust_cg_lower::AdapterError;
    use trust_ir::{ModuleCompleteness, UnloweredRow};

    let control = const_module();
    assert_eq!(control.completeness, None);
    encode_tmbc(&control).expect("a claim-less module keeps its wire identity");
    for (triple, target, _) in TRIPLES {
        compile(&control, triple, target);
        for claim in [
            ModuleCompleteness::Complete,
            ModuleCompleteness::Partial(vec![UnloweredRow {
                symbol: "missing".into(),
                display_path: None,
                reason: "body was not lowered".into(),
            }]),
            ModuleCompleteness::Partial(vec![]),
        ] {
            let mut module = control.clone();
            module.completeness = Some(claim.clone());
            match compiler_for(triple, target).compile(&module) {
                Err(CompileError::Adapter(AdapterError::ModuleCompletenessUnsupported {
                    module: name,
                })) => assert_eq!(name, module.name),
                // An EMPTY `Partial` is not even well-formed trust-ir (one
                // spelling per construct: nothing unlowered is `Complete`), so
                // ingestion admission (WS7.3) refuses it first, by name.
                Err(CompileError::InvalidTrustIr(refusal)) if matches!(&claim, ModuleCompleteness::Partial(rows) if rows.is_empty()) =>
                {
                    assert!(
                        refusal.any(|error| matches!(
                            error,
                            trust_ir_build::ValidationError::EmptyPartialClaim
                        )),
                        "{triple}: {refusal}"
                    );
                }
                Err(error) => panic!("{triple}, {claim:?}: wrong refusal: {error}"),
                Ok(_) => panic!("{triple}, {claim:?}: completeness claim reached emission"),
            }
            // This transport entry can run before the adapter. It must use
            // its fallible identity guard, never the binary writer's panic.
            let error = encode_tmbc(&module).expect_err("no wire carrier for a claim");
            assert!(
                matches!(&error, PipelineError::NoTmbcWireImage(detail)
                    if detail.contains("Module.completeness")),
                "{error}"
            );
            assert_eq!(module.completeness, Some(claim), "claim must not be erased");
        }
    }
    assert_eq!(control.completeness, None, "no implicit completeness claim");
}

#[test]
fn target_features_are_validated_per_target() {
    for (triple, target, _) in TRIPLES {
        let (arch, known) = match target {
            Target::Aarch64 => (GuardCarrierArch::AArch64, vec!["neon", "lse"]),
            Target::X86_64 => (GuardCarrierArch::X86_64, vec!["sse4.2", "avx2"]),
            Target::Riscv64 => unreachable!(),
        };
        let mut m = const_module();
        m.functions[0].attrs.target_features = known.iter().map(|f| f.to_string()).collect();
        compile(&m, triple, target);

        let mut m = const_module();
        m.functions[0].attrs.target_features = vec!["mmx-nonsense".to_string()];
        let error = compile_error(&m, triple, target);
        assert!(
            error.contains("mmx-nonsense") && error.contains(arch.name()),
            "{triple}: {error}"
        );
    }
}

#[test]
fn known_target_feature_vocabulary_covers_the_backend_feature_enums() {
    // The adapter's vocabulary must name every feature the ISA profiles can
    // admit, or a legitimately feature-gated body would be refused.
    let aarch64 = known_target_features(GuardCarrierArch::AArch64);
    for feature in AArch64IsaProfile::APPLE_ARM64.enabled_feature_names() {
        assert!(
            aarch64.contains(&feature),
            "aarch64 vocabulary lacks {feature}"
        );
    }
    assert!(aarch64.contains(&"neon"), "aarch64 baseline");
    let x86 = known_target_features(GuardCarrierArch::X86_64);
    for feature in X86TargetFeature::ALL {
        assert!(
            x86.contains(&feature.name()),
            "x86_64 vocabulary lacks {}",
            feature.name()
        );
    }
    assert!(x86.contains(&"sse2"), "x86_64 baseline");
}

// =============================================================================
// Codegen license through the compiler and the JIT compile service
// =============================================================================

#[test]
fn compiler_enforces_the_codegen_license_before_any_cache() {
    for (triple, target, _) in TRIPLES {
        let default_error = |m: &Module| match default_compiler_for(triple, target).compile(m) {
            Ok(_) => panic!("{triple}: compilation must be refused"),
            Err(error) => error.to_string(),
        };
        let mut m = const_module();
        m.functions[0].body_gate = Some(BodyGate::Ungated);
        let error = default_error(&m);
        assert!(error.contains("affirmatively ungated"), "{triple}: {error}");
        let error = compile_error(&m, triple, target);
        assert!(
            error.contains("affirmatively ungated"),
            "{triple}: Permit: {error}"
        );

        let mut m = const_module();
        m.functions[0].body_gate = Some(BodyGate::gated("vendor-gate"));
        let error = default_error(&m);
        assert!(error.contains("does not recognize"), "{triple}: {error}");
        let compiled = default_compiler_for(triple, target)
            .with_codegen_license(
                CodegenLicensePolicy::default().with_recognized_authority("vendor-gate"),
            )
            .compile(&m)
            .unwrap_or_else(|error| panic!("{triple}: recognized authority compiles: {error}"));
        assert!(!compiled.object_code.is_empty());

        // `clean-kernel-tv` is recognized by default and EVIDENCE-BOUND
        // (roadmap WS7.5(b)): worn without its certificate it is refused by
        // name before any cache, under every policy.
        let mut m = const_module();
        m.functions[0].body_gate = Some(BodyGate::gated(CLEAN_KERNEL_TV_AUTHORITY));
        for error in [default_error(&m), compile_error(&m, triple, target)] {
            assert!(
                error.contains("without the evidence it names"),
                "{triple}: {error}"
            );
        }

        // `None` is REFUSED by default (DG-73) and compiles only under an
        // explicit `Permit`.
        let m = const_module();
        let error = default_error(&m);
        assert!(error.contains("no codegen license"), "{triple}: {error}");
        compile(&m, triple, target);
    }
}

fn service_response(config: CompileServiceConfig, module: &Module, id: &str) -> Vec<String> {
    let service = CompileService::new(config);
    let response = service.compile(CompileRequest::new(id, CompileGeneration::new(1)), module);
    assert_ne!(
        response.status,
        CompileStatus::Compiled,
        "{id}: the service must not compile this module"
    );
    response
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.message.clone())
        .collect()
}

#[test]
fn jit_compile_service_enforces_the_same_license_with_the_same_defaults() {
    // The host-JIT profile compiles for the machine running the test; the
    // module never reaches codegen, so the target does not matter.
    let mut m = const_module();
    m.functions[0].body_gate = Some(BodyGate::Ungated);
    let messages = service_response(CompileServiceConfig::default(), &m, "ungated");
    assert!(
        messages.iter().any(|m| m.contains("affirmatively ungated")),
        "{messages:?}"
    );

    // The service's DEFAULT refuses a claim-less body (DG-73), exactly as
    // the compiler's does.
    let m = const_module();
    let messages = service_response(CompileServiceConfig::default(), &m, "unlicensed");
    assert!(
        messages.iter().any(|m| m.contains("no codegen license")),
        "{messages:?}"
    );

    // And the evidence-bound authority without its certificate.
    let mut m = const_module();
    m.functions[0].body_gate = Some(BodyGate::gated(CLEAN_KERNEL_TV_AUTHORITY));
    let messages = service_response(
        CompileServiceConfig {
            codegen_license: CodegenLicensePolicy::default()
                .with_unlicensed(UnlicensedBodyPolicy::Permit),
            ..CompileServiceConfig::default()
        },
        &m,
        "kernel-tv-without-evidence",
    );
    assert!(
        messages
            .iter()
            .any(|m| m.contains("without the evidence it names")),
        "{messages:?}"
    );
}

// =============================================================================
// Writer-level: the new symbol attributes round-trip through the reparse gate
// =============================================================================

#[test]
fn macho_writer_encodes_no_dead_strip_and_private_extern_and_refuses_undefined() {
    use trust_cg_codegen::macho::MachOWriter;
    let mut writer = MachOWriter::new();
    writer.add_data_section(&[1, 2, 3, 4, 5, 6, 7, 8]);
    writer
        .add_defined_symbol_with_attrs("_retained", 1, 0, true, false, Visibility::Hidden, true)
        .expect("defined symbol");
    writer
        .add_defined_symbol_with_attrs("_plain", 1, 0, true, true, Visibility::Protected, false)
        .expect("defined weak symbol");
    // A LOCAL definition: hidden is vacuous and adds nothing.
    writer
        .add_defined_symbol_with_attrs("_local", 1, 0, false, false, Visibility::Hidden, true)
        .expect("defined local symbol");
    assert!(
        writer
            .add_defined_symbol_with_attrs("_undef", 0, 0, true, false, Visibility::Hidden, false)
            .is_err(),
        "an undefined symbol has no visibility or retention channel"
    );
    let bytes = writer.write().expect("write");
    let syms = macho_symbols(&bytes);
    assert_eq!(syms["_retained"].n_type, N_SECT | N_EXT | N_PEXT);
    assert_eq!(syms["_retained"].n_desc, N_NO_DEAD_STRIP);
    assert_eq!(syms["_plain"].n_type, N_SECT | N_EXT);
    assert_eq!(syms["_plain"].n_desc, N_WEAK_DEF);
    assert_eq!(syms["_local"].n_type, N_SECT);
    assert_eq!(syms["_local"].n_desc, N_NO_DEAD_STRIP);
}

#[test]
fn elf_writer_encodes_visibility_and_gnu_retain_with_gnu_osabi() {
    use trust_cg_codegen::elf::constants::{SHF_ALLOC, SHF_WRITE, SHT_PROGBITS, STT_OBJECT};
    use trust_cg_codegen::elf::{ElfMachine, ElfWriter};
    let mut writer = ElfWriter::new(ElfMachine::X86_64);
    let plain = writer
        .add_section(
            ".data",
            &[1, 2, 3, 4],
            SHT_PROGBITS,
            SHF_ALLOC | SHF_WRITE,
            4,
        )
        .unwrap();
    writer.add_symbol_with_attrs("hidden", plain, 0, 4, true, false, STT_OBJECT, STV_HIDDEN);
    writer.add_symbol_with_attrs(
        "protected_weak",
        plain,
        0,
        4,
        true,
        true,
        STT_OBJECT,
        STV_PROTECTED,
    );
    let bytes = writer
        .write_checked()
        .expect("reparse gate agrees with intent");
    let elf = elf_object(&bytes);
    assert_eq!(elf.osabi, ELFOSABI_NONE);
    assert_eq!(elf.symbols["hidden"].st_visibility, STV_HIDDEN);
    assert_eq!(elf.symbols["hidden"].st_bind, STB_GLOBAL);
    assert_eq!(elf.symbols["protected_weak"].st_visibility, STV_PROTECTED);
    assert_eq!(elf.symbols["protected_weak"].st_bind, STB_WEAK);

    let mut writer = ElfWriter::new(ElfMachine::AArch64);
    let retained = writer
        .add_section(
            ".rodata",
            &[9, 9, 9, 9],
            SHT_PROGBITS,
            SHF_ALLOC | SHF_GNU_RETAIN,
            4,
        )
        .unwrap();
    writer.add_symbol("kept", retained, 0, 4, true, STT_OBJECT);
    let bytes = writer
        .write_checked()
        .expect("reparse gate agrees with intent");
    let elf = elf_object(&bytes);
    assert_eq!(elf.osabi, ELFOSABI_GNU, "SHF_GNU_RETAIN flips the OSABI");
    assert_ne!(elf.section_flags_of("kept") & SHF_GNU_RETAIN, 0);
}
