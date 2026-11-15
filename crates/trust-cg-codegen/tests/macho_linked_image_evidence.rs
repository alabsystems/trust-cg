// trust-cg-codegen/tests/macho_linked_image_evidence.rs - linked-image
// evidence records for CG Mach-O executables and dylibs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! L02-P5: `macho::linked_image::record_linked_image` binds a linked arm64
//! Mach-O image to the trust-cg objects it was linked from by replaying the
//! objects' relocations against the image, excluding linker-consumed
//! `__LD,__compact_unwind` and sections marked `S_ATTR_DEBUG`.
//!
//! Host-neutral rows link CG objects with the in-repo standalone linker
//! (executables and dylibs, a program importing from a CG dylib) and check
//! the positive records at O0-O3: every relocation outside linker-consumed
//! `__LD,__compact_unwind` and `S_ATTR_DEBUG` sections replayed, direct and stubbed branches, page
//! references, GOT and TLV slot loads, rebased and bound pointers in
//! `__DATA_CONST`, TLV descriptors, weak-definition lookups and two-level
//! import ordinals. Corruption controls patch a positive image and re-hash
//! its code-signature pages (so only the replay can object): a patched
//! branch target or `BL`->`B` opcode, a changed `ADRP`, `PAGEOFF12` or GOT
//! load register, a moved GOT slot, TLV template offset, data pointer,
//! export address or entry point, a wrong import ordinal, a flipped
//! weak-import bit, a read-only-after-fixup segment left writable, an
//! unwritable `__DATA`, a patched instruction outside any relocation, a
//! cleared `MH_PIE`, the flat namespace, a load-time initializer section,
//! an arm64e header and a wrong linker placement are each refused by name;
//! an unsigned patch is refused by the signature check. Object-side
//! controls give the replay inputs that disagree with the image: a missing
//! pointer relocation (an unexplained fixup), a missing object (unaccounted
//! content), a definition made hidden or local while the dylib exports it,
//! and an optimization-hint load command, an `__eh_frame` section, a
//! literal section and a section-relative relocation, each refused by name.
//!
//! Native rows (macOS AArch64) link the same objects with ld64 (`cc`) into
//! executables and dylibs, with chained fixups and with `LC_DYLD_INFO`
//! opcodes (`-no_fixup_chains`), record them against the SDK's libSystem
//! stub and the provider dylib's own exports, and run them: every
//! executable exits 42 only when every value it reads through those
//! relocations is right. ld64-specific forms are required in the records
//! (GOT and TLV loads ld64 relaxed to `ADD`, a thread-local import through
//! ld64's `__got`, weak-lookup stubs, lazy binds). Two ld64 links ld64
//! itself accepts are refused: `-no_data_const`, which leaves relocated
//! constants writable, and a direct page reference to a weak definition a
//! dylib exports for coalescing. `-dead_strip` images record the dropped
//! atoms, and the corruption controls run on ld64 images too (with classic
//! relocation entries and threaded binds). Content from a link input the
//! request does not name (a clang object), a `-needed-l` dylib no bind
//! uses and a clang object with linker optimization hints are refused; a
//! clang-assembled `SUBTRACTOR` difference is replayed and a patched one
//! refused.
//!
//! This is execution and replay evidence for these images on this host, not
//! a linker or loader proof.

use std::collections::BTreeSet;

use sha2::{Digest, Sha256};
use trust_cg_codegen::macho::linked_image::{
    AtomPlacement, CODE_BRANCH26, CODE_CONST_WRITABLE, CODE_CONTENT, CODE_ENTRY, CODE_EXPORT,
    CODE_GOT, CODE_HEADER, CODE_IMPORT_BINDING, CODE_IMPORT_PROVIDER, CODE_PAGE, CODE_PARSE,
    CODE_PLACEMENT, CODE_POINTER, CODE_PROTECTION, CODE_SIGNATURE, CODE_TLV,
    CODE_UNACCOUNTED_CONTENT, CODE_UNEXPLAINED_FIXUP, CODE_UNSUPPORTED, LinkedImageRecord,
    LinkedImageRefusal, LinkedImageRequest, LinkedObject, ProviderExports, RelocationRecord,
    linked_image_record_path, record_linked_image,
};
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
use trust_cg_codegen::macho::linked_image::{CODE_DIFFERENCE, CODE_UNUSED_DYLIB};
use trust_cg_codegen::macho::linker::{
    DylibConfig, MachOParser, PlacedImage, link_dylib, link_dylib_placed, link_with_dylibs,
    link_with_dylibs_placed,
};
use trust_cg_codegen::pipeline::{FunctionSymbolBinding, OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_cg_lower::function::{BasicBlock, Function as LirFunction, Signature};
use trust_cg_lower::instructions::{Block as LirBlock, Instruction, Opcode, Value};
use trust_cg_lower::types::Type as LirType;
use trust_ir::value::GlobalId;
use trust_ir::{CastOp, Constant, Global, ICmpOp, Linkage, Module, Ty, Visibility};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

const DARWIN: &str = "aarch64-apple-darwin";

/// The pinned target of every fixture module: they call bodyless
/// declarations (`labs`, the other objects' symbols), an FFI boundary trust-ir
/// refuses without one (`TargetInfoRequired`; WS7.3 ingestion admission).
fn darwin_target() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: DARWIN.into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}
const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
const LIBSYSTEM: &str = "/usr/lib/libSystem.B.dylib";
const PROVIDER_INSTALL_NAME: &str = "@loader_path/libprov.dylib";
const CG_DYLIB_INSTALL_NAME: &str = "@loader_path/libcg.dylib";
const STANDALONE: &str = "trust-cg standalone Mach-O linker (macho::linker)";

// =============================================================================
// CG objects
// =============================================================================

fn global(name: &str, ty: Ty, mutable: bool, init: Option<Constant>, linkage: Linkage) -> Global {
    Global {
        name: name.into(),
        ty,
        mutable,
        initializer: init,
        linkage,
        tls: None,
        align: Some(8),
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

fn symbol_addr(symbol: &str) -> Constant {
    Constant::SymbolAddr {
        symbol: symbol.into(),
        addend: 0,
    }
}

fn constant_function(
    mb: &mut ModuleBuilder,
    name: &str,
    value: i128,
    linkage: Linkage,
) -> trust_ir::FuncId {
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function(name, ty);
    fb.set_linkage(linkage);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let v = fb.iconst(Ty::I64, value);
    fb.ret(vec![v]);
    fb.build()
}

/// `return sum == want ? 42 : 1` for `main`.
fn finish_main(fb: &mut FunctionBuilder<'_>, values: &[trust_ir::ValueId], want: i128) {
    let mut sum = values[0];
    for &value in &values[1..] {
        sum = fb.add(Ty::I64, sum, value);
    }
    let want = fb.iconst(Ty::I64, want);
    let ok = fb.icmp(ICmpOp::Eq, Ty::I64, sum, want);
    let pass = fb.iconst(Ty::I32, 42);
    let fail = fb.iconst(Ty::I32, 1);
    let status = fb.select(Ty::I32, ok, pass, fail);
    fb.ret(vec![status]);
}

/// The executable's main object: direct and cross-object calls, a weak
/// function and weak data, page references, a relocated constant table
/// (`__DATA,__const`), a thread-local, a libSystem call through a stub, a
/// constant slot bound to that import, a libSystem data import through
/// the GOT, a floating-point constant in another object and that object's
/// data through the GOT (ld64 relaxes the load to an `ADD`; the standalone
/// linker keeps a rebased slot). `main` returns 42 when all twelve values
/// sum to 10215.
fn exe_module() -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("cg_image_main", darwin_target());
    let nullary = mb.add_func_type(vec![], vec![Ty::I64]);
    let unary = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let main_ty = mb.add_func_type(vec![], vec![Ty::I32]);
    let ptr = mb.add_type(Ty::Ptr);
    mb.add_global(global(
        "cg_data",
        Ty::I64,
        true,
        Some(Constant::Int(11)),
        Linkage::External,
    ));
    mb.add_global(global(
        "cg_weak_data",
        Ty::I64,
        true,
        Some(Constant::Int(13)),
        Linkage::Weak,
    ));
    mb.add_global(global(
        "cg_table",
        Ty::Array(ptr, 2),
        false,
        Some(Constant::Aggregate(vec![
            symbol_addr("cg_leaf"),
            symbol_addr("cg_data"),
        ])),
        Linkage::External,
    ));
    let mut tls = global(
        "cg_tls",
        Ty::I64,
        true,
        Some(Constant::Int(7)),
        Linkage::External,
    );
    tls.tls = Some(trust_ir::TlsModel::GeneralDynamic);
    mb.add_global(tls);
    mb.add_global(global(
        "cg_import_slot",
        Ty::Ptr,
        false,
        Some(symbol_addr("labs")),
        Linkage::External,
    ));
    let mut optind = global("optind", Ty::I32, true, None, Linkage::External);
    optind.align = Some(4);
    mb.add_global(optind);
    mb.add_global(global(
        "cg_other_data",
        Ty::I64,
        true,
        None,
        Linkage::External,
    ));

    let leaf = constant_function(&mut mb, "cg_leaf", 1001, Linkage::External);
    let weak = constant_function(&mut mb, "cg_weak_fn", 3001, Linkage::Weak);
    let labs = mb.declare_function("labs", unary);
    let other = mb.declare_function("cg_other", nullary);
    let scale = mb.declare_function("cg_scale", unary);
    let mut fb = mb.function("main", main_ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let a = fb.call(leaf, vec![]);
    let b = fb.call(weak, vec![]);
    let p = fb.global_addr(GlobalId::new(0));
    let c = fb.load(Ty::I64, p);
    let q = fb.global_addr(GlobalId::new(1));
    let d = fb.load(Ty::I64, q);
    let t = fb.global_addr(GlobalId::new(2));
    let f = fb.load(Ty::Ptr, t);
    let e = fb.call_indirect(f, nullary, vec![]);
    let tl = fb.global_addr(GlobalId::new(3));
    let g = fb.load(Ty::I64, tl);
    let minus5 = fb.iconst(Ty::I64, -5);
    let h = fb.call(labs, vec![minus5]);
    let o = fb.call(other, vec![]);
    let s = fb.global_addr(GlobalId::new(4));
    let slot = fb.load(Ty::Ptr, s);
    let minus9 = fb.iconst(Ty::I64, -9);
    let i = fb.call_indirect(slot, unary, vec![minus9]);
    let oi = fb.global_addr(GlobalId::new(5));
    let j32 = fb.load(Ty::I32, oi);
    let j = fb.cast(CastOp::SExt, Ty::I32, Ty::I64, j32);
    let thousand = fb.iconst(Ty::I64, 1000);
    let k = fb.call(scale, vec![thousand]);
    let od = fb.global_addr(GlobalId::new(6));
    let l = fb.load(Ty::I64, od);
    // 1001 + 3001 + 11 + 13 + 1001 + 7 + 5 + 2002 + 9 + optind (1) + 3141 + 23
    finish_main(&mut fb, &[a, b, c, d, e, g, h, o, i, j, k, l], 10215);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `cg_other` reads a local constant (2002); `cg_scale(x)` is `x * pi`
/// truncated (a floating-point constant); `cg_other_data` (23) is read by
/// `main` through the GOT; `cg_unused` is referenced by nothing, and
/// `cg_retained` is `#[used]` data nothing references.
fn other_module() -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("cg_image_other", darwin_target());
    let nullary = mb.add_func_type(vec![], vec![Ty::I64]);
    let unary = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    mb.add_global(global(
        "cg_local_word",
        Ty::I64,
        false,
        Some(Constant::Int(2002)),
        Linkage::Internal,
    ));
    let mut retained = global(
        "cg_retained",
        Ty::I64,
        true,
        Some(Constant::Int(77)),
        Linkage::External,
    );
    retained.retained = true;
    mb.add_global(retained);
    mb.add_global(global(
        "cg_other_data",
        Ty::I64,
        true,
        Some(Constant::Int(23)),
        Linkage::External,
    ));
    let mut fb = mb.function("cg_other", nullary);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let p = fb.global_addr(GlobalId::new(0));
    let v = fb.load(Ty::I64, p);
    fb.ret(vec![v]);
    fb.build();
    let mut fb = mb.function("cg_scale", unary);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let x = fb.add_block_param(entry, Ty::I64);
    let wide = fb.cast(CastOp::SIToFP, Ty::I64, Ty::F64, x);
    let pi = fb.fconst(Ty::F64, std::f64::consts::PI);
    let product = fb.fmul(Ty::F64, wide, pi);
    let truncated = fb.cast(CastOp::FPToSI, Ty::F64, Ty::I64, product);
    fb.ret(vec![truncated]);
    fb.build();
    constant_function(&mut mb, "cg_unused", 5, Linkage::External);
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The CG dylib body: exported, hidden and weak data, a relocated constant
/// vtable and weak slot (`__DATA,__const`), exported and weak functions,
/// callers of each and of an import served by `libprov`, the address of the
/// weak data (GOT), and an exported thread-local.
fn dylib_module() -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("cg_image_dylib", darwin_target());
    let nullary = mb.add_func_type(vec![], vec![Ty::I64]);
    let pointer_fn = mb.add_func_type(vec![], vec![Ty::Ptr]);
    let ptr = mb.add_type(Ty::Ptr);
    mb.add_global(global(
        "cg_export_data",
        Ty::I64,
        true,
        Some(Constant::Int(11)),
        Linkage::External,
    ));
    let mut hidden = global(
        "cg_hidden_data",
        Ty::I64,
        true,
        Some(Constant::Int(12)),
        Linkage::External,
    );
    hidden.visibility = Visibility::Hidden;
    mb.add_global(hidden);
    mb.add_global(global(
        "cg_weak_data",
        Ty::I64,
        true,
        Some(Constant::Int(13)),
        Linkage::Weak,
    ));
    mb.add_global(global(
        "cg_vtable",
        Ty::Array(ptr, 2),
        false,
        Some(Constant::Aggregate(vec![
            symbol_addr("cg_export_fn"),
            symbol_addr("cg_export_data"),
        ])),
        Linkage::External,
    ));
    mb.add_global(global(
        "cg_weak_slot",
        Ty::Ptr,
        false,
        Some(symbol_addr("cg_weak_data")),
        Linkage::External,
    ));
    let mut tls = global(
        "cg_dylib_tls",
        Ty::I64,
        true,
        Some(Constant::Int(7)),
        Linkage::External,
    );
    tls.tls = Some(trust_ir::TlsModel::GeneralDynamic);
    mb.add_global(tls);

    let export_fn = constant_function(&mut mb, "cg_export_fn", 1001, Linkage::External);
    let weak_fn = constant_function(&mut mb, "cg_weak_fn", 3001, Linkage::Weak);
    let provider = mb.declare_function("cg_provider_fn", nullary);
    for (name, callee) in [
        ("cg_call_export_fn", export_fn),
        ("cg_call_weak_fn", weak_fn),
        ("cg_call_provider", provider),
    ] {
        let mut fb = mb.function(name, nullary);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let v = fb.call(callee, vec![]);
        fb.ret(vec![v]);
        fb.build();
    }
    for (name, index) in [("cg_weak_data_addr", 2), ("cg_vtable_addr", 3)] {
        let mut fb = mb.function(name, pointer_fn);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let v = fb.global_addr(GlobalId::new(index));
        fb.ret(vec![v]);
        fb.build();
    }
    for (name, index) in [("cg_hidden_value", 1), ("cg_tls_value", 5)] {
        let mut fb = mb.function(name, nullary);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let p = fb.global_addr(GlobalId::new(index));
        let v = fb.load(Ty::I64, p);
        fb.ret(vec![v]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A program that imports from the CG dylib: calls, a GOT data import and
/// a thread-local import through a TLV pointer slot. Returns 42 when
/// 1001 + 1001 + 3001 + 5 + 11 + 12 + 7 + 7 = 5045.
fn consumer_module() -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("cg_image_consumer", darwin_target());
    let nullary = mb.add_func_type(vec![], vec![Ty::I64]);
    let main_ty = mb.add_func_type(vec![], vec![Ty::I32]);
    mb.add_global(global(
        "cg_export_data",
        Ty::I64,
        true,
        None,
        Linkage::External,
    ));
    let mut tls = global("cg_dylib_tls", Ty::I64, true, None, Linkage::External);
    tls.tls = Some(trust_ir::TlsModel::GeneralDynamic);
    mb.add_global(tls);
    let callees: Vec<_> = [
        "cg_export_fn",
        "cg_call_export_fn",
        "cg_call_weak_fn",
        "cg_call_provider",
        "cg_hidden_value",
        "cg_tls_value",
    ]
    .into_iter()
    .map(|name| mb.declare_function(name, nullary))
    .collect();
    let mut fb = mb.function("main", main_ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let mut values: Vec<_> = callees
        .iter()
        .map(|&callee| fb.call(callee, vec![]))
        .collect();
    let data = fb.global_addr(GlobalId::new(0));
    values.push(fb.load(Ty::I64, data));
    let tls = fb.global_addr(GlobalId::new(1));
    values.push(fb.load(Ty::I64, tls));
    finish_main(&mut fb, &values, 5045);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn compile(module: &Module, opt_level: OptLevel) -> Vec<u8> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(DARWIN).expect("Darwin triple"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .unwrap_or_else(|error| panic!("{opt_level:?}: {}: {error}", module.name))
    .object_code
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

fn lir_returning(name: &str, opcode: Opcode) -> LirFunction {
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
            instructions: vec![
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
            source_locs: vec![],
        },
    );
    function
}

/// A hidden (`N_PEXT`) function `cg_hidden_fn` (2002) and its exported
/// caller: the construct trust-ir functions cannot spell.
fn hidden_object(opt_level: OptLevel) -> Vec<u8> {
    let pipeline = Pipeline::new(PipelineConfig {
        target_triple: DARWIN.into(),
        opt_level,
        ..PipelineConfig::default()
    });
    let functions = [
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
    ];
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
        .compile_module_emission(
            &prepared,
            &[],
            &layouts,
            &[FunctionSymbolBinding::HIDDEN, FunctionSymbolBinding::GLOBAL],
        )
        .unwrap_or_else(|error| panic!("{opt_level:?}: hidden object: {error}"))
        .object
}

/// Weak data `cg_direct_weak` addressed by a DIRECT page reference. The
/// trust-ir lowering reaches a coalescable weak definition through the GOT;
/// the direct form comes from the Pipeline, as in the dylib e2e's mutation
/// control.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn direct_weak_object() -> Vec<u8> {
    let pipeline = Pipeline::new(PipelineConfig {
        target_triple: DARWIN.into(),
        opt_level: OptLevel::O0,
        ..PipelineConfig::default()
    });
    let function = lir_returning(
        "cg_direct_weak_addr",
        Opcode::GlobalRef {
            name: "cg_direct_weak".into(),
        },
    );
    let (prepared, metrics) = pipeline
        .prepare_function_with_metrics(&function, None)
        .expect("prepare the direct weak reference");
    pipeline
        .compile_module_emission(
            &[prepared],
            &[trust_cg_codegen::pipeline::ObjectGlobal {
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
            }],
            &[metrics.frame_layout],
            &[],
        )
        .expect("direct weak object")
        .object
}

// =============================================================================
// Links and records
// =============================================================================

fn libsystem_config(extra: &[&str]) -> DylibConfig {
    let mut config = DylibConfig::with_libsystem();
    config.dylibs[0]
        .symbols
        .extend(extra.iter().map(|symbol| symbol.to_string()));
    config
}

fn exe_config() -> DylibConfig {
    libsystem_config(&["_labs", "_optind"])
}

fn dylib_config() -> DylibConfig {
    let mut config = DylibConfig::with_libsystem();
    config.add_dylib(
        PROVIDER_INSTALL_NAME,
        ["_cg_provider_fn".to_string()].into_iter().collect(),
    );
    config
}

fn parsed(objects: &[Vec<u8>]) -> Vec<trust_cg_codegen::macho::linker::ParsedObject> {
    objects
        .iter()
        .map(|bytes| MachOParser::parse(bytes).expect("CG object parses"))
        .collect()
}

fn exe_objects(opt_level: OptLevel) -> Vec<Vec<u8>> {
    vec![
        compile(&exe_module(), opt_level),
        compile(&other_module(), opt_level),
    ]
}

fn dylib_objects(opt_level: OptLevel) -> Vec<Vec<u8>> {
    vec![
        compile(&dylib_module(), opt_level),
        hidden_object(opt_level),
    ]
}

/// The placed entry points and the plain ones agree (both wrap the same
/// `link_image`; this is API agreement, not evidence that the standalone
/// linker's emission is unchanged, which rests on its own e2e targets).
fn standalone_exe(objects: &[Vec<u8>], config: &DylibConfig) -> PlacedImage {
    let placed = link_with_dylibs_placed(&parsed(objects), config).expect("standalone executable");
    assert_eq!(
        placed.image,
        link_with_dylibs(&parsed(objects), config).unwrap(),
        "link_with_dylibs_placed returns link_with_dylibs's image"
    );
    placed
}

fn standalone_dylib(objects: &[Vec<u8>]) -> PlacedImage {
    let placed = link_dylib_placed(&parsed(objects), &dylib_config(), CG_DYLIB_INSTALL_NAME)
        .expect("standalone dylib");
    assert_eq!(
        placed.image,
        link_dylib(&parsed(objects), &dylib_config(), CG_DYLIB_INSTALL_NAME).unwrap(),
        "link_dylib_placed returns link_dylib's image"
    );
    placed
}

fn request<'a>(
    image: &'a [u8],
    objects: &'a [Vec<u8>],
    placement: AtomPlacement<'a>,
    providers: Vec<ProviderExports>,
    linker: &str,
) -> LinkedImageRequest<'a> {
    LinkedImageRequest {
        image_name: "image",
        image,
        objects: objects
            .iter()
            .enumerate()
            .map(|(index, bytes)| LinkedObject {
                name: ["cg0.o", "cg1.o", "cg2.o", "cg3.o"][index],
                bytes,
            })
            .collect(),
        placement,
        providers,
        linker: linker.to_string(),
    }
}

fn record(request: &LinkedImageRequest<'_>, label: &str) -> LinkedImageRecord {
    record_linked_image(request).unwrap_or_else(|refusal| panic!("{label}: {refusal}"))
}

fn refusal(request: &LinkedImageRequest<'_>, label: &str) -> LinkedImageRefusal {
    match record_linked_image(request) {
        Ok(_) => panic!("{label}: the corrupted image was recorded"),
        Err(refusal) => refusal,
    }
}

/// Relocation rows of `record` with `kind` naming `symbol`.
fn rows<'r>(record: &'r LinkedImageRecord, kind: &str, symbol: &str) -> Vec<&'r RelocationRecord> {
    record
        .relocations
        .iter()
        .filter(|row| row.kind == kind && row.symbol == symbol)
        .collect()
}

/// Every relocation of every placed atom was replayed.
fn assert_complete(record: &LinkedImageRecord, label: &str) {
    let total: usize = record.objects.iter().map(|object| object.relocations).sum();
    let summary = &record.summary;
    assert_eq!(
        summary.relocations_replayed
            + summary.relocations_paired
            + summary.relocations_consumed
            + summary.relocations_not_in_image,
        total,
        "{label}: every relocation is replayed, consumed by the linker or outside the image"
    );
    assert!(summary.relocations_replayed > 0, "{label}");
    assert_eq!(record.schema, "trust-cg.macho-linked-image/v1");
    assert!(record.evidence.contains("not a proof"), "{label}");
    assert_eq!(record.image.sha256.len(), 64);
    assert_eq!(record.image.code_signature.cdhash.len(), 40, "{label}");
}

fn libsystem_declared() -> ProviderExports {
    ProviderExports::from_dylib_config(&exe_config())
        .into_iter()
        .next()
        .unwrap()
}

// =============================================================================
// Corruption helpers (their own Mach-O parsing, independent of the record)
// =============================================================================

fn u32_at(bytes: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap())
}

fn u64_at(bytes: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap())
}

fn be32(bytes: &[u8], at: usize) -> u32 {
    u32::from_be_bytes(bytes[at..at + 4].try_into().unwrap())
}

fn load_commands(image: &[u8]) -> Vec<(u32, usize)> {
    let mut commands = Vec::new();
    let mut at = 32;
    for _ in 0..u32_at(image, 16) {
        commands.push((u32_at(image, at), at));
        at += u32_at(image, at + 4) as usize;
    }
    commands
}

/// `(name, vmaddr, fileoff, filesize, command offset)` of each segment.
fn segments(image: &[u8]) -> Vec<(String, u64, u64, u64, usize)> {
    load_commands(image)
        .into_iter()
        .filter(|(cmd, _)| *cmd == 0x19)
        .map(|(_, at)| {
            let raw = &image[at + 8..at + 24];
            let end = raw.iter().position(|&b| b == 0).unwrap_or(16);
            (
                String::from_utf8_lossy(&raw[..end]).into_owned(),
                u64_at(image, at + 24),
                u64_at(image, at + 40),
                u64_at(image, at + 48),
                at,
            )
        })
        .collect()
}

fn file_offset(image: &[u8], address: u64) -> usize {
    segments(image)
        .into_iter()
        .find_map(|(_, vmaddr, fileoff, filesize, _)| {
            (address >= vmaddr && address < vmaddr + filesize)
                .then(|| (fileoff + address - vmaddr) as usize)
        })
        .unwrap_or_else(|| panic!("{address:#x} has no file bytes"))
}

fn parse_hex(text: &str) -> u64 {
    u64::from_str_radix(text.trim_start_matches("0x"), 16).unwrap()
}

/// Recompute every code-page hash of every CodeDirectory, so a patched
/// image keeps a valid ad-hoc signature and only the replay can object.
fn resign(image: &mut [u8]) {
    let (_, at) = load_commands(image)
        .into_iter()
        .find(|(cmd, _)| *cmd == 0x1D)
        .expect("LC_CODE_SIGNATURE");
    let blob = u32_at(image, at + 8) as usize;
    let count = be32(image, blob + 8) as usize;
    for index in 0..count {
        let slot = be32(image, blob + 12 + index * 8);
        if slot != 0 && slot != 0x1000 {
            continue;
        }
        let directory = blob + be32(image, blob + 16 + index * 8) as usize;
        let hash_offset = be32(image, directory + 16) as usize;
        let code_slots = be32(image, directory + 28) as usize;
        let code_limit = be32(image, directory + 32) as usize;
        let hash_size = image[directory + 36] as usize;
        let page_size = 1usize << image[directory + 39];
        assert_eq!(hash_size, 32, "SHA-256 code directory");
        for page in 0..code_slots {
            let start = page * page_size;
            let end = (start + page_size).min(code_limit);
            let digest = Sha256::digest(&image[start..end]);
            let at = directory + hash_offset + page * hash_size;
            image[at..at + 32].copy_from_slice(&digest);
        }
    }
}

/// Offset of the chained import entry naming `symbol`.
fn chained_import(image: &[u8], symbol: &str) -> usize {
    let (_, at) = load_commands(image)
        .into_iter()
        .find(|(cmd, _)| *cmd == 0x8000_0034)
        .expect("LC_DYLD_CHAINED_FIXUPS");
    let start = u32_at(image, at + 8) as usize;
    let imports = start + u32_at(image, start + 8) as usize;
    let names = start + u32_at(image, start + 12) as usize;
    let count = u32_at(image, start + 16) as usize;
    assert_eq!(u32_at(image, start + 20), 1, "DYLD_CHAINED_IMPORT");
    (0..count)
        .map(|index| imports + index * 4)
        .find(|&entry| {
            let name = names + (u32_at(image, entry) >> 9) as usize;
            let end = name + image[name..].iter().position(|&b| b == 0).unwrap();
            &image[name..end] == symbol.as_bytes()
        })
        .unwrap_or_else(|| panic!("no chained import {symbol}"))
}

#[derive(Debug, Clone, Copy)]
enum Corruption {
    /// Retarget a direct BL by one instruction.
    BranchTarget,
    /// Move a rebased `__DATA_CONST` pointer by 8 bytes.
    DataPointer,
    /// Bind the libprov import to libSystem's ordinal.
    ImportOrdinal,
    /// Clear `SG_READ_ONLY` from `__DATA_CONST`.
    ConstWritable,
    /// Mark a strong import weak.
    WeakImport,
    /// Flip an instruction bit outside any relocation field.
    Instruction,
    /// Move `LC_MAIN` by one instruction.
    Entry,
    /// Turn a direct `BL` into a `B` with the same offset.
    BranchOpcode,
    /// Change the destination register of a page reference's `ADRP`.
    AdrpRegister,
    /// Change the register of a page reference's `PAGEOFF12` instruction.
    PageoffRegister,
    /// Change the destination register of a GOT slot load.
    GotRegister,
    /// Move a rebased GOT slot's target by 8 bytes.
    GotSlot,
    /// Move a TLV descriptor's template offset by 8 bytes.
    TlvOffset,
    /// Move `_cg_export_fn`'s exports-trie address by one instruction.
    ExportAddress,
    /// Clear `MH_PIE` from an executable.
    NotPie,
    /// Leave the `__DATA` segment unwritable.
    DataUnwritable,
    /// Clear `MH_TWOLEVEL`: a flat-namespace image.
    FlatNamespace,
    /// Mark the image arm64e.
    Arm64e,
    /// Claim one classic external relocation entry in `LC_DYSYMTAB`.
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    ClassicRelocation,
    /// Turn the first `LC_DYLD_INFO` bind opcode into a threaded-bind one.
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    ThreadedBind,
    /// Retype `__DATA,__data` as `S_MOD_INIT_FUNC_POINTERS`.
    InitializerSection,
    /// Add 8 to a `SUBTRACTOR` difference.
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    Difference,
}

/// The first relocation row of `record` matching `keep`.
fn row_where<'r>(
    record: &'r LinkedImageRecord,
    what: &str,
    keep: impl Fn(&RelocationRecord) -> bool,
) -> &'r RelocationRecord {
    record
        .relocations
        .iter()
        .find(|row| keep(row))
        .unwrap_or_else(|| panic!("no {what} row"))
}

fn patch_u32(bytes: &mut [u8], at: usize, patch: impl FnOnce(u32) -> u32) {
    let word = patch(u32_at(bytes, at));
    bytes[at..at + 4].copy_from_slice(&word.to_le_bytes());
}

/// Add `delta` to the pointer at `address`: a chained rebase holds its
/// target in the low 36 bits, an `LC_DYLD_INFO` image the pointer itself.
fn move_pointer(bytes: &mut [u8], record: &LinkedImageRecord, address: u64, delta: u64) {
    let at = file_offset(bytes, address);
    let raw = u64_at(bytes, at);
    let patched = if record.fixups.format.contains("CHAINED") {
        (raw & !0xF_FFFF_FFFF) | ((raw + delta) & 0xF_FFFF_FFFF)
    } else {
        raw + delta
    };
    bytes[at..at + 8].copy_from_slice(&patched.to_le_bytes());
}

/// `(header offset, segment, section)` of every `section_64` of a Mach-O
/// image or object.
fn section_headers(bytes: &[u8]) -> Vec<(usize, String, String)> {
    let name = |raw: &[u8]| {
        let end = raw.iter().position(|&b| b == 0).unwrap_or(16);
        String::from_utf8_lossy(&raw[..end]).into_owned()
    };
    load_commands(bytes)
        .into_iter()
        .filter(|(cmd, _)| *cmd == 0x19)
        .flat_map(|(_, at)| {
            (0..u32_at(bytes, at + 64) as usize).map(move |index| at + 72 + index * 80)
        })
        .map(|header| {
            (
                header,
                name(&bytes[header + 16..header + 32]),
                name(&bytes[header..header + 16]),
            )
        })
        .collect()
}

fn section_header(bytes: &[u8], segment: &str, section: &str) -> usize {
    section_headers(bytes)
        .into_iter()
        .find(|(_, seg, sect)| seg == segment && sect == section)
        .unwrap_or_else(|| panic!("no section {segment},{section}"))
        .0
}

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

/// Offset and length of the address ULEB in `symbol`'s exports-trie
/// terminal (`LC_DYLD_EXPORTS_TRIE`, or `LC_DYLD_INFO`'s export range).
fn export_address_field(image: &[u8], symbol: &str) -> (usize, usize) {
    let trie = load_commands(image)
        .into_iter()
        .find_map(|(cmd, at)| match cmd {
            0x8000_0033 => Some(u32_at(image, at + 8) as usize),
            0x8000_0022 => Some(u32_at(image, at + 40) as usize),
            _ => None,
        })
        .expect("an exports trie");
    let mut pending = vec![(0usize, String::new())];
    while let Some((node, prefix)) = pending.pop() {
        let mut at = trie + node;
        let terminal = uleb(image, &mut at) as usize;
        let children = at + terminal;
        if terminal > 0 && prefix == symbol {
            let flags = uleb(image, &mut at);
            assert_eq!(flags & 0x8, 0, "{symbol} is a re-export");
            let field = at;
            uleb(image, &mut at);
            return (field, at - field);
        }
        let mut at = children;
        let count = image[at];
        at += 1;
        for _ in 0..count {
            let end = at + image[at..].iter().position(|&b| b == 0).unwrap();
            let edge = String::from_utf8_lossy(&image[at..end]).into_owned();
            at = end + 1;
            let child = uleb(image, &mut at) as usize;
            let name = format!("{prefix}{edge}");
            if symbol.starts_with(&name) {
                pending.push((child, name));
            }
        }
    }
    panic!("{symbol} is not in the exports trie")
}

/// Apply `corruption` to a copy of a recorded image and re-sign it.
fn corrupt(image: &[u8], record: &LinkedImageRecord, corruption: Corruption) -> Vec<u8> {
    let mut bytes = image.to_vec();
    match corruption {
        Corruption::BranchTarget => {
            let row = record
                .relocations
                .iter()
                .find(|row| row.kind == "ARM64_RELOC_BRANCH26" && row.resolution == "direct")
                .expect("a direct branch");
            let at = file_offset(&bytes, parse_hex(&row.site));
            let word = u32_at(&bytes, at);
            let patched = (word & 0xFC00_0000) | (word.wrapping_add(1) & 0x03FF_FFFF);
            bytes[at..at + 4].copy_from_slice(&patched.to_le_bytes());
        }
        Corruption::DataPointer => {
            let row = row_where(record, "rebased constant pointer", |row| {
                row.kind == "ARM64_RELOC_UNSIGNED"
                    && row.section == "__DATA,__const"
                    && row.resolution.starts_with("rebase")
            });
            move_pointer(&mut bytes, record, parse_hex(&row.site), 8);
        }
        Corruption::ImportOrdinal => {
            // The image loads libSystem and libprov: name the other one.
            let entry = chained_import(&bytes, "_cg_provider_fn");
            let raw = u32_at(&bytes, entry);
            let ordinal = raw & 0xFF;
            assert!(ordinal == 1 || ordinal == 2, "{ordinal}");
            bytes[entry..entry + 4].copy_from_slice(&((raw & !0xFF) | (3 - ordinal)).to_le_bytes());
        }
        Corruption::WeakImport => {
            let entry = chained_import(&bytes, "_cg_provider_fn");
            let raw = u32_at(&bytes, entry);
            bytes[entry..entry + 4].copy_from_slice(&(raw | 0x100).to_le_bytes());
        }
        Corruption::ConstWritable => {
            let (_, _, _, _, at) = segments(&bytes)
                .into_iter()
                .find(|segment| segment.0 == "__DATA_CONST")
                .expect("__DATA_CONST");
            let flags = u32_at(&bytes, at + 68) & !0x10;
            bytes[at + 68..at + 72].copy_from_slice(&flags.to_le_bytes());
        }
        Corruption::Instruction => {
            let row = record
                .relocations
                .iter()
                .find(|row| row.kind == "ARM64_RELOC_BRANCH26" && row.resolution == "direct")
                .expect("a direct branch");
            // The instruction after the branch belongs to no relocation.
            let at = file_offset(&bytes, parse_hex(&row.site) + 4);
            bytes[at] ^= 0x01;
        }
        Corruption::Entry => {
            let (_, at) = load_commands(&bytes)
                .into_iter()
                .find(|(cmd, _)| *cmd == 0x8000_0028)
                .expect("LC_MAIN");
            let entry = u64_at(&bytes, at + 8) + 4;
            bytes[at + 8..at + 16].copy_from_slice(&entry.to_le_bytes());
        }
        Corruption::BranchOpcode => {
            let row = row_where(record, "direct BL", |row| {
                row.kind == "ARM64_RELOC_BRANCH26"
                    && row.resolution == "direct"
                    && u32_at(image, file_offset(image, parse_hex(&row.site))) >> 26 == 0x25
            });
            let at = file_offset(&bytes, parse_hex(&row.site));
            patch_u32(&mut bytes, at, |word| word & !0x8000_0000);
        }
        Corruption::AdrpRegister | Corruption::PageoffRegister | Corruption::GotRegister => {
            let kind = match corruption {
                Corruption::AdrpRegister => "ARM64_RELOC_PAGE21",
                Corruption::PageoffRegister => "ARM64_RELOC_PAGEOFF12",
                _ => "ARM64_RELOC_GOT_LOAD_PAGEOFF12",
            };
            let row = row_where(record, kind, |row| {
                row.kind == kind
                    && (kind != "ARM64_RELOC_GOT_LOAD_PAGEOFF12"
                        || row.resolution.starts_with("LDR slot"))
            });
            let at = file_offset(&bytes, parse_hex(&row.site));
            patch_u32(&mut bytes, at, |word| word ^ 1);
        }
        Corruption::GotSlot => {
            let row = row_where(record, "GOT load of a rebased slot", |row| {
                row.kind == "ARM64_RELOC_GOT_LOAD_PAGEOFF12"
                    && row.resolution.starts_with("LDR slot")
                    && record.linker_fixups.iter().any(|fixup| {
                        fixup.address == row.target && fixup.resolution.starts_with("rebase")
                    })
            });
            move_pointer(&mut bytes, record, parse_hex(&row.target), 8);
        }
        Corruption::TlvOffset => {
            let row = row_where(record, "TLV template offset", |row| {
                row.kind == "ARM64_RELOC_UNSIGNED" && row.symbol.ends_with("$tlv$init")
            });
            let at = file_offset(&bytes, parse_hex(&row.site));
            let offset = u64_at(&bytes, at) + 8;
            bytes[at..at + 8].copy_from_slice(&offset.to_le_bytes());
        }
        Corruption::ExportAddress => {
            let (at, len) = export_address_field(&bytes, "_cg_export_fn");
            let mut cursor = at;
            let value = uleb(&bytes, &mut cursor) + 4;
            // Re-encode in the same number of bytes (padded ULEB).
            for index in 0..len {
                let low = ((value >> (7 * index)) & 0x7F) as u8;
                bytes[at + index] = if index + 1 < len { low | 0x80 } else { low };
            }
            assert_eq!(value >> (7 * len), 0, "the moved address fits the field");
        }
        Corruption::NotPie => patch_u32(&mut bytes, 24, |flags| flags & !0x20_0000),
        Corruption::FlatNamespace => patch_u32(&mut bytes, 24, |flags| flags & !0x80),
        Corruption::Arm64e => patch_u32(&mut bytes, 8, |_| 2),
        Corruption::DataUnwritable => {
            let (_, _, _, _, at) = segments(&bytes)
                .into_iter()
                .find(|segment| segment.0 == "__DATA")
                .expect("__DATA");
            patch_u32(&mut bytes, at + 60, |prot| prot & !0x2);
        }
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        Corruption::ClassicRelocation => {
            let (_, at) = load_commands(&bytes)
                .into_iter()
                .find(|(cmd, _)| *cmd == 0xB)
                .expect("LC_DYSYMTAB");
            patch_u32(&mut bytes, at + 68, |_| 1);
        }
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        Corruption::ThreadedBind => {
            let (_, at) = load_commands(&bytes)
                .into_iter()
                .find(|(cmd, _)| *cmd == 0x8000_0022)
                .expect("LC_DYLD_INFO_ONLY");
            let bind = u32_at(&bytes, at + 16) as usize;
            assert!(u32_at(&bytes, at + 20) > 0, "the image has binds");
            bytes[bind] = 0xD0;
        }
        Corruption::InitializerSection => {
            let header = section_header(&bytes, "__DATA", "__data");
            patch_u32(&mut bytes, header + 64, |flags| (flags & !0xFF) | 0x9);
        }
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        Corruption::Difference => {
            let row = row_where(record, "SUBTRACTOR difference", |row| {
                row.resolution.starts_with("difference")
            });
            let at = file_offset(&bytes, parse_hex(&row.site));
            let value = u64_at(&bytes, at) + 8;
            bytes[at..at + 8].copy_from_slice(&value.to_le_bytes());
        }
    }
    resign(&mut bytes);
    bytes
}

// =============================================================================
// Object edits (the replay's inputs, not the image)
// =============================================================================

/// `(nlist offset, name)` of every symbol of an object.
fn object_symbols(object: &[u8]) -> Vec<(usize, String)> {
    let (_, at) = load_commands(object)
        .into_iter()
        .find(|(cmd, _)| *cmd == 0x2)
        .expect("LC_SYMTAB");
    let (symoff, nsyms, stroff) = (
        u32_at(object, at + 8) as usize,
        u32_at(object, at + 12) as usize,
        u32_at(object, at + 16) as usize,
    );
    (0..nsyms)
        .map(|index| {
            let entry = symoff + index * 16;
            let name = stroff + u32_at(object, entry) as usize;
            let end = name + object[name..].iter().position(|&b| b == 0).unwrap();
            (
                entry,
                String::from_utf8_lossy(&object[name..end]).into_owned(),
            )
        })
        .collect()
}

/// Rewrite the `n_type` of `symbol` in a copy of `object`.
fn with_symbol_type(object: &[u8], symbol: &str, patch: impl FnOnce(u8) -> u8) -> Vec<u8> {
    let mut bytes = object.to_vec();
    let (entry, _) = object_symbols(object)
        .into_iter()
        .find(|(_, name)| name == symbol)
        .unwrap_or_else(|| panic!("no symbol {symbol}"));
    bytes[entry + 4] = patch(bytes[entry + 4]);
    bytes
}

/// A copy of `object` without the `ARM64_RELOC_UNSIGNED` relocation of
/// `segment,section` that names `symbol` (the last entry takes its place).
fn without_pointer_relocation(
    object: &[u8],
    segment: &str,
    section: &str,
    symbol: &str,
) -> Vec<u8> {
    let mut bytes = object.to_vec();
    let symbols = object_symbols(object);
    let header = section_header(object, segment, section);
    let (reloff, nreloc) = (
        u32_at(object, header + 56) as usize,
        u32_at(object, header + 60) as usize,
    );
    let index = (0..nreloc)
        .find(|&index| {
            let info = u32_at(object, reloff + index * 8 + 4);
            info >> 28 == 0
                && (info >> 27) & 1 == 1
                && symbols[(info & 0x00FF_FFFF) as usize].1 == symbol
        })
        .unwrap_or_else(|| panic!("no pointer relocation to {symbol}"));
    let (at, last) = (reloff + index * 8, reloff + (nreloc - 1) * 8);
    let moved: Vec<u8> = object[last..last + 8].to_vec();
    bytes[at..at + 8].copy_from_slice(&moved);
    patch_u32(&mut bytes, header + 60, |count| count - 1);
    bytes
}

/// A recorded positive image the corruption controls start from.
struct Recorded<'a> {
    image: &'a [u8],
    objects: &'a [Vec<u8>],
    placement: AtomPlacement<'a>,
    providers: &'a [ProviderExports],
    record: &'a LinkedImageRecord,
    label: &'a str,
}

/// `corruption` of `positive`, re-signed, must be refused with `code` and a
/// finding that mentions `needle`.
fn expect_refused(positive: &Recorded<'_>, corruption: Corruption, code: &str, needle: &str) {
    let label = positive.label;
    let corrupted = corrupt(positive.image, positive.record, corruption);
    let refused = refusal(
        &request(
            &corrupted,
            positive.objects,
            positive.placement,
            positive.providers.to_vec(),
            "corrupted",
        ),
        &format!("{label} {corruption:?}"),
    );
    assert!(
        refused
            .findings
            .iter()
            .any(|finding| finding.code == code && finding.detail.contains(needle)),
        "{label} {corruption:?}: expected [{code}] naming {needle:?}, got {refused}"
    );
    assert!(
        !refused.has(CODE_SIGNATURE),
        "{label} {corruption:?}: the re-signed image keeps a valid signature: {refused}"
    );
}

/// The replay of `image` against `objects` must be refused with `code` and a
/// finding that mentions `needle`.
fn expect_objects_refused(
    image: &[u8],
    objects: &[Vec<u8>],
    placement: AtomPlacement<'_>,
    providers: &[ProviderExports],
    code: &str,
    needle: &str,
) -> LinkedImageRefusal {
    let refused = refusal(
        &request(
            image,
            objects,
            placement,
            providers.to_vec(),
            "edited objects",
        ),
        &format!("[{code}] {needle}"),
    );
    assert!(
        refused
            .findings
            .iter()
            .any(|finding| finding.code == code && finding.detail.contains(needle)),
        "expected [{code}] naming {needle:?}, got {refused}"
    );
    refused
}

// =============================================================================
// Host-neutral rows: the standalone linker
// =============================================================================

#[test]
fn standalone_executable_records_bind_every_relocation_at_o0_through_o3() {
    let mut branch_forms = BTreeSet::new();
    for opt_level in OPT_LEVELS {
        let label = format!("standalone executable {opt_level:?}");
        let objects = exe_objects(opt_level);
        let placed = standalone_exe(&objects, &exe_config());
        let providers = ProviderExports::from_dylib_config(&exe_config());
        let request = request(
            &placed.image,
            &objects,
            AtomPlacement::SectionAddresses(&placed.section_addresses),
            providers.clone(),
            STANDALONE,
        );
        let record = record(&request, &label);
        assert_complete(&record, &label);
        assert_eq!(record.image.filetype, "MH_EXECUTE");
        assert!(record.image.flags.contains("MH_PIE"), "{label}");
        assert!(
            record.fixups.format.contains("DYLD_CHAINED_PTR_64"),
            "{label}: {}",
            record.fixups.format
        );
        // The cross-object call is direct; the libSystem call goes through
        // a stub whose slot binds libSystem (ordinal 1).
        assert!(
            rows(&record, "ARM64_RELOC_BRANCH26", "_cg_other")
                .iter()
                .all(|row| row.resolution == "direct"),
            "{label}"
        );
        let labs = rows(&record, "ARM64_RELOC_BRANCH26", "_labs");
        assert!(
            !labs.is_empty()
                && labs.iter().all(|row| row.resolution.contains("stub")
                    && row.resolution.contains("bind _labs from ordinal 1")),
            "{label}: {labs:?}"
        );
        for row in &record.relocations {
            if row.kind == "ARM64_RELOC_BRANCH26" {
                branch_forms.insert(row.resolution.split(' ').next().unwrap().to_string());
            }
        }
        // GOT loads of the data import and of another object's data (a
        // rebased slot), and TLV loads of the thread-local.
        assert!(
            !rows(&record, "ARM64_RELOC_GOT_LOAD_PAGEOFF12", "_optind").is_empty(),
            "{label}"
        );
        let other_data = rows(&record, "ARM64_RELOC_GOT_LOAD_PAGEOFF12", "_cg_other_data");
        assert!(
            !other_data.is_empty()
                && other_data
                    .iter()
                    .all(|row| row.resolution.starts_with("LDR slot")
                        && record.linker_fixups.iter().any(|fixup| {
                            fixup.address == row.target && fixup.resolution.starts_with("rebase")
                        })),
            "{label}: {other_data:?}"
        );
        let tlv = rows(&record, "ARM64_RELOC_TLVP_LOAD_PAGEOFF12", "_cg_tls");
        assert!(
            !tlv.is_empty() && tlv.iter().all(|row| row.resolution.starts_with("LDR slot")),
            "{label}: the standalone linker keeps TLV slots: {tlv:?}"
        );
        // Relocated constants are rebased (and bound) in __DATA_CONST.
        let table = rows(&record, "ARM64_RELOC_UNSIGNED", "_cg_leaf");
        assert!(
            table
                .iter()
                .any(|row| row.section == "__DATA,__const" && row.resolution.starts_with("rebase")),
            "{label}: {table:?}"
        );
        assert!(
            rows(&record, "ARM64_RELOC_UNSIGNED", "_labs")
                .iter()
                .all(|row| row.resolution == "bind _labs from ordinal 1"),
            "{label}"
        );
        let data_const = record
            .segments
            .iter()
            .find(|segment| segment.name == "__DATA_CONST")
            .expect("__DATA_CONST");
        assert!(data_const.read_only_after_fixups, "{label}");
        assert!(record.summary.read_only_after_fixup_atoms >= 2, "{label}");
        let const_atoms: Vec<_> = record
            .atoms
            .iter()
            .filter(|atom| atom.section == "__DATA,__const")
            .collect();
        assert!(
            const_atoms
                .iter()
                .all(|atom| atom.image_section.as_deref() == Some("__DATA_CONST,__const")),
            "{label}: {const_atoms:?}"
        );
        // The TLV descriptor binds dyld's bootstrap and holds its template
        // offset without a fixup.
        assert!(rows(&record, "ARM64_RELOC_UNSIGNED", "__tlv_bootstrap").len() == 1);
        assert!(
            rows(&record, "ARM64_RELOC_UNSIGNED", "_cg_tls$tlv$init")
                .iter()
                .all(|row| row.resolution.starts_with("no fixup")),
            "{label}"
        );
        let imports: BTreeSet<(&str, i32)> = record
            .imports
            .iter()
            .map(|import| (import.symbol.as_str(), import.ordinal))
            .collect();
        for symbol in ["_labs", "_optind", "__tlv_bootstrap"] {
            assert!(imports.contains(&(symbol, 1)), "{label}: {imports:?}");
        }
        // The executable exports nothing, so its weak definitions resolve
        // statically.
        assert!(record.exports.is_empty(), "{label}");
        assert!(
            rows(&record, "ARM64_RELOC_BRANCH26", "_cg_weak_fn")
                .iter()
                .all(|row| row.resolution == "direct"),
            "{label}"
        );
        // Deterministic: the same inputs give the same record.
        let again = record_linked_image(&request).expect("second replay");
        assert_eq!(again.to_json(), record.to_json(), "{label}");
    }
    assert!(branch_forms.contains("direct") && branch_forms.contains("stub"));
}

#[test]
fn standalone_dylib_records_bind_weak_coalescing_imports_and_exports_at_o0_through_o3() {
    for opt_level in OPT_LEVELS {
        let label = format!("standalone dylib {opt_level:?}");
        let objects = dylib_objects(opt_level);
        let placed = standalone_dylib(&objects);
        let providers = ProviderExports::from_dylib_config(&dylib_config());
        let record = record(
            &request(
                &placed.image,
                &objects,
                AtomPlacement::SectionAddresses(&placed.section_addresses),
                providers,
                STANDALONE,
            ),
            &label,
        );
        assert_complete(&record, &label);
        assert_eq!(record.image.filetype, "MH_DYLIB");
        assert_eq!(
            record.image.install_name.as_deref(),
            Some(CG_DYLIB_INSTALL_NAME)
        );
        let exported: BTreeSet<(&str, bool)> = record
            .exports
            .iter()
            .map(|export| (export.symbol.as_str(), export.weak))
            .collect();
        for (name, weak) in [
            ("_cg_export_fn", false),
            ("_cg_weak_fn", true),
            ("_cg_weak_data", true),
            ("_cg_vtable", false),
            ("_cg_call_hidden_fn", false),
        ] {
            assert!(exported.contains(&(name, weak)), "{label}: {exported:?}");
        }
        for hidden in ["_cg_hidden_fn", "_cg_hidden_data"] {
            assert!(!exported.contains(&(hidden, false)), "{label}: {hidden}");
        }
        assert!(
            record
                .exports
                .iter()
                .any(|export| export.symbol == "_cg_dylib_tls" && export.kind == "thread-local"),
            "{label}"
        );
        // References to the coalescable weak definitions go through dyld's
        // weak lookup: the weak slot pointer and the GOT load.
        assert!(
            rows(&record, "ARM64_RELOC_UNSIGNED", "_cg_weak_data")
                .iter()
                .all(|row| row.resolution.starts_with("dyld weak lookup")),
            "{label}"
        );
        assert!(
            record.fixups.weak_lookups >= 2,
            "{label}: {:?}",
            record.fixups
        );
        let provider = record
            .imports
            .iter()
            .find(|import| import.symbol == "_cg_provider_fn")
            .expect("the provider import");
        assert_eq!(
            (provider.ordinal, provider.library.as_str()),
            (2, PROVIDER_INSTALL_NAME),
            "{label}"
        );
        // The hidden function's caller binds it directly.
        assert!(
            rows(&record, "ARM64_RELOC_BRANCH26", "_cg_hidden_fn")
                .iter()
                .all(|row| row.resolution == "direct"),
            "{label}"
        );
    }
}

#[test]
fn standalone_program_importing_from_a_cg_dylib_binds_the_dylibs_own_exports() {
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let label = format!("standalone consumer {opt_level:?}");
        let dylib = standalone_dylib(&dylib_objects(opt_level));
        let libcg = ProviderExports::from_dylib_image(&dylib.image, "libcg.dylib").unwrap();
        assert_eq!(libcg.install_name, CG_DYLIB_INSTALL_NAME);
        let mut config = DylibConfig::with_libsystem();
        config.add_dylib(
            CG_DYLIB_INSTALL_NAME,
            libcg.symbols.iter().cloned().collect(),
        );
        let objects = vec![compile(&consumer_module(), opt_level)];
        let placed = standalone_exe(&objects, &config);
        let providers = vec![libsystem_declared(), libcg.clone()];
        let record = record(
            &request(
                &placed.image,
                &objects,
                AtomPlacement::SectionAddresses(&placed.section_addresses),
                providers.clone(),
                STANDALONE,
            ),
            &label,
        );
        assert_complete(&record, &label);
        for symbol in ["_cg_export_fn", "_cg_export_data", "_cg_dylib_tls"] {
            let import = record
                .imports
                .iter()
                .find(|import| import.symbol == symbol)
                .unwrap_or_else(|| panic!("{label}: {symbol} is not imported"));
            assert_eq!(import.library, CG_DYLIB_INSTALL_NAME, "{label}");
            assert!(import.provider.contains("exports trie"), "{label}");
        }
        let tlv = rows(&record, "ARM64_RELOC_TLVP_LOAD_PAGEOFF12", "_cg_dylib_tls");
        assert!(
            !tlv.is_empty() && tlv.iter().all(|row| row.resolution.starts_with("LDR slot")),
            "{label}: {tlv:?}"
        );
        // Without the dylib's export list the binds are not bound to intent.
        let refused = refusal(
            &request(
                &placed.image,
                &objects,
                AtomPlacement::SectionAddresses(&placed.section_addresses),
                vec![libsystem_declared()],
                STANDALONE,
            ),
            &label,
        );
        assert!(refused.has(CODE_IMPORT_PROVIDER), "{label}: {refused}");
    }
}

#[test]
fn corrupted_standalone_images_are_refused_by_name() {
    let objects = exe_objects(OptLevel::O0);
    let exe = standalone_exe(&objects, &exe_config());
    let exe_providers = ProviderExports::from_dylib_config(&exe_config());
    let placement = AtomPlacement::SectionAddresses(&exe.section_addresses);
    let exe_record = record(
        &request(
            &exe.image,
            &objects,
            placement,
            exe_providers.clone(),
            STANDALONE,
        ),
        "standalone executable",
    );
    for (corruption, code, needle) in [
        (Corruption::BranchTarget, CODE_BRANCH26, ""),
        (Corruption::BranchOpcode, CODE_BRANCH26, ""),
        (Corruption::AdrpRegister, CODE_PAGE, ""),
        (Corruption::PageoffRegister, CODE_PAGE, ""),
        (Corruption::GotRegister, CODE_GOT, ""),
        (Corruption::GotSlot, CODE_GOT, ""),
        (Corruption::TlvOffset, CODE_TLV, ""),
        (Corruption::DataPointer, CODE_POINTER, ""),
        (Corruption::ConstWritable, CODE_CONST_WRITABLE, ""),
        (Corruption::DataUnwritable, CODE_PROTECTION, "not writable"),
        (Corruption::Instruction, CODE_CONTENT, ""),
        (Corruption::Entry, CODE_ENTRY, ""),
        (Corruption::NotPie, CODE_HEADER, "MH_PIE"),
        (
            Corruption::FlatNamespace,
            CODE_UNSUPPORTED,
            "flat namespace",
        ),
        (
            Corruption::InitializerSection,
            CODE_UNSUPPORTED,
            "load time",
        ),
        (Corruption::Arm64e, CODE_PARSE, "arm64e"),
    ] {
        expect_refused(
            &Recorded {
                image: &exe.image,
                objects: &objects,
                placement,
                providers: &exe_providers,
                record: &exe_record,
                label: "standalone executable",
            },
            corruption,
            code,
            needle,
        );
    }

    // Object-side controls: the replay's inputs disagree with the image.
    let edited = |index: usize, bytes: Vec<u8>| {
        let mut edited = objects.clone();
        edited[index] = bytes;
        edited
    };
    // The image binds `_labs` into `cg_import_slot`; an object without that
    // relocation leaves the fixup unexplained.
    expect_objects_refused(
        &exe.image,
        &edited(
            0,
            without_pointer_relocation(&objects[0], "__DATA", "__const", "_labs"),
        ),
        placement,
        &exe_providers,
        CODE_UNEXPLAINED_FIXUP,
        "no pointer relocation",
    );
    // Linker optimization hints (an object load command retyped), a
    // section named `__eh_frame`, a literal section and a section-relative
    // relocation are refused by name.
    let mut hinted = objects[0].clone();
    let (_, dysymtab) = load_commands(&hinted)
        .into_iter()
        .find(|(cmd, _)| *cmd == 0xB)
        .expect("LC_DYSYMTAB");
    patch_u32(&mut hinted, dysymtab, |_| 0x2E);
    expect_objects_refused(
        &exe.image,
        &edited(0, hinted),
        placement,
        &exe_providers,
        CODE_PARSE,
        "LC_LINKER_OPTIMIZATION_HINT",
    );
    let mut eh_frame = objects[1].clone();
    let header = section_header(&eh_frame, "__DATA", "__data");
    eh_frame[header..header + 16].copy_from_slice(b"__eh_frame\0\0\0\0\0\0");
    expect_objects_refused(
        &exe.image,
        &edited(1, eh_frame),
        placement,
        &exe_providers,
        CODE_UNSUPPORTED,
        "__eh_frame",
    );
    let mut literal = objects[1].clone();
    let header = section_header(&literal, "__DATA", "__data");
    patch_u32(&mut literal, header + 64, |flags| (flags & !0xFF) | 0x4);
    expect_objects_refused(
        &exe.image,
        &edited(1, literal),
        placement,
        &exe_providers,
        CODE_UNSUPPORTED,
        "literal section",
    );
    let mut section_relative = objects[0].clone();
    let header = section_header(&section_relative, "__TEXT", "__text");
    let reloff = u32_at(&section_relative, header + 56) as usize;
    let branch = (0..u32_at(&section_relative, header + 60) as usize)
        .map(|index| reloff + index * 8 + 4)
        .find(|&info| u32_at(&section_relative, info) >> 28 == 2)
        .expect("a BRANCH26 relocation");
    // r_extern = 0, r_symbolnum = section 1.
    patch_u32(&mut section_relative, branch, |info| {
        (info & 0xF700_0000) | 1
    });
    expect_objects_refused(
        &exe.image,
        &edited(0, section_relative),
        placement,
        &exe_providers,
        CODE_UNSUPPORTED,
        "section-relative",
    );

    let dylib_objects = dylib_objects(OptLevel::O0);
    let dylib = standalone_dylib(&dylib_objects);
    let dylib_providers = ProviderExports::from_dylib_config(&dylib_config());
    let placement = AtomPlacement::SectionAddresses(&dylib.section_addresses);
    let dylib_record = record(
        &request(
            &dylib.image,
            &dylib_objects,
            placement,
            dylib_providers.clone(),
            STANDALONE,
        ),
        "standalone dylib",
    );
    for (corruption, code, needle) in [
        (Corruption::ImportOrdinal, CODE_IMPORT_BINDING, ""),
        (Corruption::WeakImport, CODE_IMPORT_BINDING, ""),
        (Corruption::DataPointer, CODE_POINTER, ""),
        (Corruption::ConstWritable, CODE_CONST_WRITABLE, ""),
        (Corruption::ExportAddress, CODE_EXPORT, "_cg_export_fn at"),
    ] {
        expect_refused(
            &Recorded {
                image: &dylib.image,
                objects: &dylib_objects,
                placement,
                providers: &dylib_providers,
                record: &dylib_record,
                label: "standalone dylib",
            },
            corruption,
            code,
            needle,
        );
    }
    // The dylib exports `_cg_export_fn`: an object that defines it hidden
    // (`N_PEXT`, which keeps `N_EXT`) or local must not be exported.
    for (patch, needle) in [
        (0x10u8, "_cg_export_fn, which cg0.o defines hidden"),
        (0x01, "_cg_export_fn, which cg0.o defines local"),
    ] {
        let mut edited = dylib_objects.clone();
        edited[0] = with_symbol_type(&dylib_objects[0], "_cg_export_fn", |n_type| {
            if patch == 0x10 {
                n_type | 0x10
            } else {
                n_type & !0x01
            }
        });
        expect_objects_refused(
            &dylib.image,
            &edited,
            placement,
            &dylib_providers,
            CODE_EXPORT,
            needle,
        );
    }

    // A patch without re-signing is refused by the signature check too.
    let mut unsigned = exe.image.clone();
    let row = exe_record
        .relocations
        .iter()
        .find(|row| row.kind == "ARM64_RELOC_BRANCH26" && row.resolution == "direct")
        .unwrap();
    let at = file_offset(&unsigned, parse_hex(&row.site));
    unsigned[at] ^= 0x01;
    let refused = refusal(
        &request(
            &unsigned,
            &objects,
            AtomPlacement::SectionAddresses(&exe.section_addresses),
            exe_providers.clone(),
            STANDALONE,
        ),
        "unsigned patch",
    );
    assert!(
        refused.has(CODE_SIGNATURE) && refused.has(CODE_BRANCH26),
        "{refused}"
    );

    // A placement claim that disagrees with the image is refused.
    let mut shifted = exe.section_addresses.clone();
    let text = shifted[1]
        .iter_mut()
        .find_map(Option::as_mut)
        .expect("a placed section");
    *text += 4;
    let refused = refusal(
        &request(
            &exe.image,
            &objects,
            AtomPlacement::SectionAddresses(&shifted),
            exe_providers.clone(),
            STANDALONE,
        ),
        "shifted placement",
    );
    assert!(
        refused.has(CODE_CONTENT) || refused.has(CODE_PLACEMENT),
        "{refused}"
    );
    // The standalone image has no symbol table to place atoms by.
    let refused = refusal(
        &request(
            &exe.image,
            &objects,
            AtomPlacement::ImageSymbolTable,
            exe_providers,
            STANDALONE,
        ),
        "symbol-table placement of a standalone image",
    );
    assert!(refused.has(CODE_PLACEMENT), "{refused}");
    // A link missing an input object is not bound to the objects it names:
    // the missing object's code and data are content no input accounts for.
    let refused = refusal(
        &request(
            &exe.image,
            &objects[..1],
            AtomPlacement::SectionAddresses(&exe.section_addresses[..1]),
            ProviderExports::from_dylib_config(&exe_config()),
            STANDALONE,
        ),
        "missing input object",
    );
    assert!(refused.has(CODE_UNACCOUNTED_CONTENT), "{refused}");
}

#[test]
fn records_are_written_next_to_the_linked_artifact() {
    let objects = exe_objects(OptLevel::O1);
    let placed = standalone_exe(&objects, &exe_config());
    let record = record(
        &request(
            &placed.image,
            &objects,
            AtomPlacement::SectionAddresses(&placed.section_addresses),
            ProviderExports::from_dylib_config(&exe_config()),
            STANDALONE,
        ),
        "write",
    );
    let directory = tempfile::tempdir().unwrap();
    let output = directory.path().join("prog");
    std::fs::write(&output, &placed.image).unwrap();
    let path = record.write_next_to(&output).unwrap();
    assert_eq!(path, linked_image_record_path(&output));
    assert_eq!(path.file_name().unwrap(), "prog.linked-image.json");
    let json: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
    assert_eq!(json["schema"], "trust-cg.macho-linked-image/v1");
    assert_eq!(
        json["image"]["sha256"],
        format!("{:x}", Sha256::digest(&placed.image))
    );
    assert_eq!(json["linker"]["declared"], STANDALONE);
    assert!(json["boundary"].as_array().unwrap().len() >= 4);
}

/// Truncated and bit-flipped images and objects are refused (or, for a flip
/// the replay cannot see, recorded) without a panic: the readers bound
/// every offset they follow.
#[test]
fn malformed_images_and_objects_are_refused_without_panicking() {
    let objects = exe_objects(OptLevel::O0);
    let placed = standalone_exe(&objects, &exe_config());
    let providers = ProviderExports::from_dylib_config(&exe_config());
    let placement = AtomPlacement::SectionAddresses(&placed.section_addresses);
    let replay = |image: &[u8], objects: &[Vec<u8>]| {
        record_linked_image(&request(
            image,
            objects,
            placement,
            providers.clone(),
            STANDALONE,
        ))
    };
    let length = placed.image.len();
    for step in 0..64 {
        let cut = length * step / 64;
        let refused = replay(&placed.image[..cut], &objects).expect_err("a truncated image");
        assert!(!refused.findings.is_empty(), "cut {cut}");
    }
    // A deterministic walk over the header, load commands and linkedit.
    let mut state = 0x2545_F491_4F6C_DD1Du64;
    let mut next = |bound: usize| {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        (state % bound as u64) as usize
    };
    let mut refused = 0;
    for _ in 0..400 {
        let mut image = placed.image.clone();
        let at = if next(2) == 0 {
            next(0x1000.min(length))
        } else {
            next(length)
        };
        image[at] ^= 1 << next(8);
        resign(&mut image);
        if replay(&image, &objects).is_err() {
            refused += 1;
        }
        let mut object = objects[0].clone();
        let at = next(object.len());
        object[at] ^= 1 << next(8);
        let _ = replay(&placed.image, &[object, objects[1].clone()]);
    }
    assert!(refused > 0);
    let refused = replay(b"not a Mach-O image", &objects).unwrap_err();
    assert!(refused.has(CODE_PARSE), "{refused}");
    let mut fat = placed.image.clone();
    fat[..4].copy_from_slice(&0xCAFE_BABEu32.to_be_bytes());
    let refused = replay(&fat, &objects).unwrap_err();
    assert!(refused.to_string().contains("universal"), "{refused}");
}

#[test]
fn tapi_stubs_give_install_names_reexports_and_arm64_symbols() {
    let text = r#"--- !tapi-tbd
tbd-version:     4
targets:         [ x86_64-macos, arm64e-macos ]
install-name:    '/usr/lib/libTop.dylib'
reexported-libraries:
  - targets:         [ x86_64-macos, arm64e-macos ]
    libraries:       [ '/usr/lib/libInner.dylib' ]
exports:
  - targets:         [ arm64e-macos ]
    symbols:         [ _top_a, _top_b ]
  - targets:         [ x86_64-macos ]
    symbols:         [ _x86_only ]
...
--- !tapi-tbd
tbd-version:     4
targets:         [ x86_64-macos, arm64e-macos ]
install-name:    '/usr/lib/libInner.dylib'
exports:
  - targets:         [ x86_64-macos, arm64e-macos ]
    symbols:         [ _inner_a,
                       _inner_b ]
    thread-local-symbols: [ _inner_tlv ]
...
"#;
    let provider = ProviderExports::from_tbd(text, "inline").unwrap();
    assert_eq!(provider.install_name, "/usr/lib/libTop.dylib");
    let names: Vec<&str> = provider.symbols.iter().map(String::as_str).collect();
    assert_eq!(
        names,
        ["_inner_a", "_inner_b", "_inner_tlv", "_top_a", "_top_b"]
    );
    assert_eq!(
        provider.thread_local_symbols,
        Some(["_inner_tlv".to_string()].into_iter().collect())
    );
    let v5 = "{\"tapi_tbd_version\": 5}";
    assert!(ProviderExports::from_tbd(v5, "v5").is_err());
    let error = ProviderExports::from_tbd(
        &text.replace("tbd-version:     4", "tbd-version:     3"),
        "v3",
    )
    .unwrap_err();
    assert!(error.contains("tbd-version 3"), "{error}");
}

// =============================================================================
// Native rows (macOS AArch64): ld64 images, execution
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

    fn checked(command: &mut Command, what: &str) -> std::process::Output {
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

    fn write(path: &Path, bytes: impl AsRef<[u8]>) -> PathBuf {
        std::fs::write(path, bytes).unwrap();
        path.to_path_buf()
    }

    fn sdk_libsystem() -> ProviderExports {
        let sdk = checked(
            Command::new("/usr/bin/xcrun").arg("--show-sdk-path"),
            "xcrun --show-sdk-path",
        );
        let sdk = String::from_utf8(sdk.stdout).unwrap();
        let path = Path::new(sdk.trim()).join("usr/lib/libSystem.B.tbd");
        let text = std::fs::read_to_string(&path).unwrap();
        let provider = ProviderExports::from_tbd(&text, path.display().to_string()).unwrap();
        assert_eq!(provider.install_name, LIBSYSTEM);
        provider
    }

    fn ld_identity() -> String {
        let output = checked(Command::new("/usr/bin/ld").arg("-v"), "ld -v");
        String::from_utf8_lossy(&output.stderr)
            .lines()
            .next()
            .unwrap_or("ld")
            .to_string()
    }

    /// Link `objects` with `cc` (ld64) into `output`.
    fn ld64(directory: &Path, objects: &[Vec<u8>], output: &Path, extra: &[&str]) {
        let mut command = Command::new("/usr/bin/cc");
        command.args(["-arch", "arm64"]);
        for (index, bytes) in objects.iter().enumerate() {
            command.arg(write(&directory.join(format!("cg{index}.o")), bytes));
        }
        checked(
            command.args(extra).arg("-o").arg(output),
            &format!("ld64 {}", output.display()),
        );
    }

    fn provider(directory: &Path) -> ProviderExports {
        let source = write(&directory.join("prov.c"), PROVIDER_SOURCE);
        let dylib = directory.join("libprov.dylib");
        checked(
            Command::new("/usr/bin/clang")
                .args(["-dynamiclib", "-O1", "-install_name", PROVIDER_INSTALL_NAME])
                .arg(&source)
                .arg("-o")
                .arg(&dylib),
            "libprov.dylib",
        );
        ProviderExports::from_dylib_image(&std::fs::read(&dylib).unwrap(), "libprov.dylib").unwrap()
    }

    fn run_status(path: &Path) -> i32 {
        let output = command_output_with_timeout(&mut Command::new(path), Duration::from_secs(60))
            .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        assert!(!output.timed_out, "{} timed out", path.display());
        output.output.status.code().unwrap_or(-1)
    }

    fn native_record(
        image: &[u8],
        objects: &[Vec<u8>],
        providers: Vec<ProviderExports>,
        label: &str,
    ) -> LinkedImageRecord {
        record(
            &request(
                image,
                objects,
                AtomPlacement::ImageSymbolTable,
                providers,
                &ld_identity(),
            ),
            label,
        )
    }

    #[test]
    fn ld64_executables_are_recorded_and_exit_42_with_chained_fixups_and_dyld_info() {
        let libsystem = sdk_libsystem();
        for opt_level in OPT_LEVELS {
            for (variant, extra) in [
                ("chained", &[][..]),
                ("dyld-info", &["-Wl,-no_fixup_chains"][..]),
            ] {
                let label = format!("ld64 executable {variant} {opt_level:?}");
                let directory = tempfile::tempdir().unwrap();
                let objects = exe_objects(opt_level);
                let output = directory.path().join("prog");
                ld64(directory.path(), &objects, &output, extra);
                let image = std::fs::read(&output).unwrap();
                let record = native_record(&image, &objects, vec![libsystem.clone()], &label);
                assert_complete(&record, &label);
                assert!(
                    record
                        .linker
                        .image_tools
                        .iter()
                        .any(|tool| tool.starts_with("ld ")),
                    "{label}: {:?}",
                    record.linker.image_tools
                );
                if variant == "chained" {
                    assert!(record.fixups.format.contains("CHAINED"), "{label}");
                    // ld64 exports the executable's weak definitions and
                    // reaches them through dyld's weak lookup.
                    assert!(
                        rows(&record, "ARM64_RELOC_BRANCH26", "_cg_weak_fn")
                            .iter()
                            .all(|row| row.resolution.contains("dyld weak lookup")),
                        "{label}"
                    );
                } else {
                    assert!(record.fixups.format.contains("LC_DYLD_INFO"), "{label}");
                    assert!(
                        rows(&record, "ARM64_RELOC_BRANCH26", "_labs")
                            .iter()
                            .all(|row| row.resolution.contains("lazy bind _labs")),
                        "{label}"
                    );
                }
                // ld64 relaxes the TLV load of a local thread-local and the
                // GOT load of another object's data to an ADD.
                for (kind, symbol) in [
                    ("ARM64_RELOC_TLVP_LOAD_PAGEOFF12", "_cg_tls"),
                    ("ARM64_RELOC_GOT_LOAD_PAGEOFF12", "_cg_other_data"),
                ] {
                    let relaxed = rows(&record, kind, symbol);
                    assert!(
                        !relaxed.is_empty()
                            && relaxed
                                .iter()
                                .all(|row| row.resolution.starts_with("relaxed LDR -> ADD")),
                        "{label}: {relaxed:?}"
                    );
                }
                assert!(
                    record
                        .imports
                        .iter()
                        .all(|import| import.library == LIBSYSTEM),
                    "{label}"
                );
                assert_eq!(run_status(&output), 42, "{label}");
                // The standalone twin runs the same.
                let placed = standalone_exe(&objects, &exe_config());
                let twin = directory.path().join("prog_standalone");
                write(&twin, &placed.image);
                std::fs::set_permissions(
                    &twin,
                    std::os::unix::fs::PermissionsExt::from_mode(0o755),
                )
                .unwrap();
                assert_eq!(run_status(&twin), 42, "{label} standalone twin");
            }
        }
    }

    #[test]
    fn ld64_and_standalone_dylibs_are_recorded_and_serve_a_cg_program() {
        let libsystem = sdk_libsystem();
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            for linker in ["ld64", "ld64-dyld-info", "standalone"] {
                let label = format!("{linker} dylib {opt_level:?}");
                let directory = tempfile::tempdir().unwrap();
                let dir = directory.path();
                let libprov = provider(dir);
                let objects = dylib_objects(opt_level);
                let dylib = dir.join("libcg.dylib");
                let providers = vec![libsystem.clone(), libprov.clone()];
                let record = match linker {
                    "standalone" => {
                        let placed = standalone_dylib(&objects);
                        write(&dylib, &placed.image);
                        super::record(
                            &request(
                                &placed.image,
                                &objects,
                                AtomPlacement::SectionAddresses(&placed.section_addresses),
                                providers,
                                STANDALONE,
                            ),
                            &label,
                        )
                    }
                    _ => {
                        let mut extra = vec![
                            "-dynamiclib",
                            "-install_name",
                            CG_DYLIB_INSTALL_NAME,
                            "-L",
                            dir.to_str().unwrap(),
                            "-lprov",
                        ];
                        if linker == "ld64-dyld-info" {
                            extra.push("-Wl,-no_fixup_chains");
                        }
                        ld64(dir, &objects, &dylib, &extra);
                        native_record(&std::fs::read(&dylib).unwrap(), &objects, providers, &label)
                    }
                };
                assert_complete(&record, &label);
                let provider_import = record
                    .imports
                    .iter()
                    .find(|import| import.symbol == "_cg_provider_fn")
                    .expect("provider import");
                assert_eq!(provider_import.library, PROVIDER_INSTALL_NAME, "{label}");
                assert!(
                    provider_import.provider.contains("libprov.dylib"),
                    "{label}"
                );
                assert!(
                    record.fixups.weak_lookups >= 2,
                    "{label}: {:?}",
                    record.fixups
                );

                // A CG program imports from the dylib (calls, GOT data and a
                // TLV pointer slot) and exits 42.
                let libcg = ProviderExports::from_dylib_image(
                    &std::fs::read(&dylib).unwrap(),
                    "libcg.dylib",
                )
                .unwrap();
                let consumer_objects = vec![compile(&consumer_module(), opt_level)];
                let consumer = dir.join("consumer");
                ld64(
                    dir,
                    &consumer_objects,
                    &consumer,
                    &["-L", dir.to_str().unwrap(), "-lcg"],
                );
                let consumer_record = native_record(
                    &std::fs::read(&consumer).unwrap(),
                    &consumer_objects,
                    vec![libsystem.clone(), libcg],
                    &format!("{label} consumer"),
                );
                assert!(
                    consumer_record
                        .imports
                        .iter()
                        .any(|import| import.symbol == "_cg_dylib_tls"
                            && import.library == CG_DYLIB_INSTALL_NAME),
                    "{label}"
                );
                // ld64 puts the thread-local import's pointer in __got,
                // bound to the dylib; the TLV loads reach that slot.
                let tlv = rows(
                    &consumer_record,
                    "ARM64_RELOC_TLVP_LOAD_PAGEOFF12",
                    "_cg_dylib_tls",
                );
                assert!(
                    !tlv.is_empty()
                        && tlv.iter().all(|row| {
                            row.resolution.starts_with("LDR slot")
                                && consumer_record.linker_fixups.iter().any(|fixup| {
                                    fixup.address == row.target
                                        && fixup.section == "__DATA_CONST,__got"
                                        && fixup.resolution.starts_with("bind _cg_dylib_tls")
                                })
                        }),
                    "{label}: {tlv:?}"
                );
                assert_eq!(run_status(&consumer), 42, "{label} consumer");
            }
        }
    }

    /// `-no_data_const` leaves the relocated constants in writable `__DATA`:
    /// ld64 links it, the record refuses it.
    #[test]
    fn ld64_no_data_const_leaves_relocated_constants_writable_and_is_refused() {
        let libsystem = sdk_libsystem();
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            let directory = tempfile::tempdir().unwrap();
            let objects = exe_objects(opt_level);
            let output = directory.path().join("prog");
            ld64(directory.path(), &objects, &output, &["-Wl,-no_data_const"]);
            let refused = refusal(
                &request(
                    &std::fs::read(&output).unwrap(),
                    &objects,
                    AtomPlacement::ImageSymbolTable,
                    vec![libsystem.clone()],
                    &ld_identity(),
                ),
                "-no_data_const",
            );
            assert_eq!(
                refused.codes(),
                [CODE_CONST_WRITABLE].into_iter().collect(),
                "{opt_level:?}: {refused}"
            );
            assert_eq!(
                run_status(&output),
                42,
                "{opt_level:?}: the image still runs"
            );
        }
    }

    /// A direct page reference to a weak definition the dylib exports: ld64
    /// links it without a diagnostic and dyld cannot coalesce it.
    #[test]
    fn ld64_direct_weak_reference_in_a_dylib_is_refused() {
        let libsystem = sdk_libsystem();
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        let libprov = provider(dir);
        let mut objects = dylib_objects(OptLevel::O0);
        objects.push(direct_weak_object());
        let dylib = dir.join("libcg.dylib");
        ld64(
            dir,
            &objects,
            &dylib,
            &[
                "-dynamiclib",
                "-install_name",
                CG_DYLIB_INSTALL_NAME,
                "-L",
                dir.to_str().unwrap(),
                "-lprov",
            ],
        );
        let refused = refusal(
            &request(
                &std::fs::read(&dylib).unwrap(),
                &objects,
                AtomPlacement::ImageSymbolTable,
                vec![libsystem, libprov],
                &ld_identity(),
            ),
            "direct weak reference",
        );
        assert_eq!(
            refused.codes(),
            [trust_cg_codegen::macho::linked_image::CODE_WEAK_DIRECT]
                .into_iter()
                .collect(),
            "{refused}"
        );
        assert!(refused.to_string().contains("_cg_direct_weak"), "{refused}");
    }

    /// An exported-symbols list makes ld64 demote the other globals to local
    /// symbols: an executable is still placed and recorded through them, a
    /// dylib that no longer exports a default-visibility definition is
    /// refused.
    #[test]
    fn ld64_exported_symbols_lists_demote_globals_and_dylibs_are_refused() {
        let libsystem = sdk_libsystem();
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        let objects = exe_objects(OptLevel::O1);
        let output = dir.join("prog");
        ld64(dir, &objects, &output, &["-Wl,-exported_symbol,_main"]);
        let record = native_record(
            &std::fs::read(&output).unwrap(),
            &objects,
            vec![libsystem.clone()],
            "exported symbols list",
        );
        assert_complete(&record, "exported symbols list");
        let exported: BTreeSet<&str> = record
            .exports
            .iter()
            .map(|export| export.symbol.as_str())
            .collect();
        assert_eq!(exported, ["_main"].into_iter().collect());
        assert!(
            record
                .atoms
                .iter()
                .all(|atom| atom.address.is_some() && atom.placement == "image symbol table"),
            "every atom placed through the demoted local symbols"
        );
        assert_eq!(run_status(&output), 42);

        let libprov = provider(dir);
        let dylib_objects = dylib_objects(OptLevel::O1);
        let dylib = dir.join("libcg.dylib");
        ld64(
            dir,
            &dylib_objects,
            &dylib,
            &[
                "-dynamiclib",
                "-install_name",
                CG_DYLIB_INSTALL_NAME,
                "-L",
                dir.to_str().unwrap(),
                "-lprov",
                "-Wl,-exported_symbol,_cg_export_fn",
            ],
        );
        let refused = refusal(
            &request(
                &std::fs::read(&dylib).unwrap(),
                &dylib_objects,
                AtomPlacement::ImageSymbolTable,
                vec![libsystem, libprov],
                &ld_identity(),
            ),
            "dylib exported symbols list",
        );
        assert!(
            refused.has(CODE_EXPORT) && refused.to_string().contains("_cg_call_export_fn"),
            "{refused}"
        );
    }

    /// `-dead_strip` drops `cg_unused`; the record names it outside the
    /// image, keeps the retained data and still binds every live relocation.
    #[test]
    fn ld64_dead_strip_records_dropped_atoms_and_keeps_retained_ones() {
        let libsystem = sdk_libsystem();
        let directory = tempfile::tempdir().unwrap();
        let objects = exe_objects(OptLevel::O1);
        let output = directory.path().join("prog");
        ld64(directory.path(), &objects, &output, &["-Wl,-dead_strip"]);
        let record = native_record(
            &std::fs::read(&output).unwrap(),
            &objects,
            vec![libsystem],
            "dead strip",
        );
        assert_complete(&record, "dead strip");
        let atom = |symbol: &str| {
            record
                .atoms
                .iter()
                .find(|atom| atom.symbol == symbol)
                .unwrap_or_else(|| panic!("{symbol}"))
        };
        assert_eq!(atom("_cg_unused").placement, "not in the image");
        assert!(atom("_cg_retained").address.is_some());
        assert!(record.summary.atoms_not_in_image >= 1);
        assert_eq!(run_status(&output), 42);
    }

    #[test]
    fn corrupted_ld64_images_are_refused_by_name() {
        let libsystem = sdk_libsystem();
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        let objects = exe_objects(OptLevel::O0);
        let output = dir.join("prog");
        ld64(dir, &objects, &output, &[]);
        let image = std::fs::read(&output).unwrap();
        let providers = vec![libsystem.clone()];
        let exe_record = native_record(&image, &objects, providers.clone(), "ld64 executable");
        for (corruption, code, needle) in [
            (Corruption::BranchTarget, CODE_BRANCH26, ""),
            (Corruption::BranchOpcode, CODE_BRANCH26, ""),
            (Corruption::AdrpRegister, CODE_PAGE, ""),
            (Corruption::PageoffRegister, CODE_PAGE, ""),
            (Corruption::GotRegister, CODE_GOT, ""),
            (Corruption::TlvOffset, CODE_TLV, ""),
            (Corruption::DataPointer, CODE_POINTER, ""),
            (Corruption::ConstWritable, CODE_CONST_WRITABLE, ""),
            (Corruption::DataUnwritable, CODE_PROTECTION, "not writable"),
            (Corruption::Instruction, CODE_CONTENT, ""),
            (Corruption::Entry, CODE_ENTRY, ""),
            (Corruption::NotPie, CODE_HEADER, "MH_PIE"),
            (
                Corruption::FlatNamespace,
                CODE_UNSUPPORTED,
                "flat namespace",
            ),
            (
                Corruption::InitializerSection,
                CODE_UNSUPPORTED,
                "load time",
            ),
            (Corruption::Arm64e, CODE_PARSE, "arm64e"),
            (Corruption::ClassicRelocation, CODE_PARSE, "classic"),
        ] {
            expect_refused(
                &Recorded {
                    image: &image,
                    objects: &objects,
                    placement: AtomPlacement::ImageSymbolTable,
                    providers: &providers,
                    record: &exe_record,
                    label: "ld64 executable",
                },
                corruption,
                code,
                needle,
            );
        }
        // Threaded binds exist only in LC_DYLD_INFO opcode streams.
        let opcodes = dir.join("prog_dyld_info");
        ld64(dir, &objects, &opcodes, &["-Wl,-no_fixup_chains"]);
        let opcodes_image = std::fs::read(&opcodes).unwrap();
        let opcodes_record = native_record(
            &opcodes_image,
            &objects,
            providers.clone(),
            "ld64 LC_DYLD_INFO executable",
        );
        expect_refused(
            &Recorded {
                image: &opcodes_image,
                objects: &objects,
                placement: AtomPlacement::ImageSymbolTable,
                providers: &providers,
                record: &opcodes_record,
                label: "ld64 LC_DYLD_INFO executable",
            },
            Corruption::ThreadedBind,
            CODE_PARSE,
            "threaded bind",
        );

        let libprov = provider(dir);
        let dylib_objects = dylib_objects(OptLevel::O0);
        let dylib = dir.join("libcg.dylib");
        ld64(
            dir,
            &dylib_objects,
            &dylib,
            &[
                "-dynamiclib",
                "-install_name",
                CG_DYLIB_INSTALL_NAME,
                "-L",
                dir.to_str().unwrap(),
                "-lprov",
            ],
        );
        let image = std::fs::read(&dylib).unwrap();
        let providers = vec![libsystem, libprov];
        let dylib_record = native_record(&image, &dylib_objects, providers.clone(), "ld64 dylib");
        for (corruption, code, needle) in [
            (Corruption::ImportOrdinal, CODE_IMPORT_BINDING, ""),
            (Corruption::WeakImport, CODE_IMPORT_BINDING, ""),
            (Corruption::DataPointer, CODE_POINTER, ""),
            (Corruption::ConstWritable, CODE_CONST_WRITABLE, ""),
            (Corruption::ExportAddress, CODE_EXPORT, "_cg_export_fn at"),
        ] {
            expect_refused(
                &Recorded {
                    image: &image,
                    objects: &dylib_objects,
                    placement: AtomPlacement::ImageSymbolTable,
                    providers: &providers,
                    record: &dylib_record,
                    label: "ld64 dylib",
                },
                corruption,
                code,
                needle,
            );
        }
    }

    /// Clang-compiled `foreign.c`: hidden code, data and a pointer the CG
    /// objects never reference.
    const FOREIGN_SOURCE: &str = "__attribute__((visibility(\"hidden\"))) long foreign_counter = 3;\n\
        __attribute__((visibility(\"hidden\"))) long *foreign_ptr = &foreign_counter;\n\
        __attribute__((visibility(\"hidden\"))) long foreign_fn(long x) { return x * 7 + *foreign_ptr; }\n";

    fn clang_object(directory: &Path, name: &str, source: &str, flags: &[&str]) -> Vec<u8> {
        let path = write(&directory.join(name), source);
        let object = directory.join(format!("{name}.o"));
        checked(
            Command::new("/usr/bin/clang")
                .args(["-arch", "arm64", "-c"])
                .args(flags)
                .arg(&path)
                .arg("-o")
                .arg(&object),
            name,
        );
        std::fs::read(object).unwrap()
    }

    /// Content from a link input the request does not name (a `-Wl` object)
    /// and a dependent dylib no bind uses are refused; the same image with
    /// that object named is recorded.
    #[test]
    fn ld64_unnamed_link_inputs_and_unused_dylibs_are_refused() {
        let libsystem = sdk_libsystem();
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        let objects = exe_objects(OptLevel::O1);
        let foreign = clang_object(dir, "foreign.c", FOREIGN_SOURCE, &["-O0"]);
        let mut linked = objects.clone();
        linked.push(foreign);
        let output = dir.join("prog");
        ld64(dir, &linked, &output, &[]);
        let image = std::fs::read(&output).unwrap();
        let providers = vec![libsystem.clone()];
        let refused = expect_objects_refused(
            &image,
            &objects,
            AtomPlacement::ImageSymbolTable,
            &providers,
            CODE_UNACCOUNTED_CONTENT,
            "__TEXT,__text",
        );
        assert!(
            refused.to_string().contains("_foreign_fn"),
            "the finding names the image symbol: {refused}"
        );
        assert!(
            refused.has(CODE_UNEXPLAINED_FIXUP),
            "the foreign pointer's rebase is no linker slot: {refused}"
        );
        let record = native_record(&image, &linked, providers.clone(), "foreign object named");
        assert_complete(&record, "foreign object named");
        assert_eq!(run_status(&output), 42);

        let output = dir.join("prog_needed");
        ld64(dir, &objects, &output, &["-Wl,-needed-lz"]);
        let refused = refusal(
            &request(
                &std::fs::read(&output).unwrap(),
                &objects,
                AtomPlacement::ImageSymbolTable,
                providers,
                &ld_identity(),
            ),
            "-needed-lz",
        );
        assert_eq!(
            refused.codes(),
            [CODE_UNUSED_DYLIB].into_iter().collect(),
            "{refused}"
        );
        assert!(refused.to_string().contains("libz"), "{refused}");
    }

    /// A `SUBTRACTOR` difference (clang-assembled data naming a CG function)
    /// is replayed with no fixup; a patched difference is refused. A clang
    /// object with linker optimization hints is refused by name.
    #[test]
    fn ld64_differences_are_replayed_and_optimization_hints_are_refused() {
        let libsystem = sdk_libsystem();
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        let difference = clang_object(
            dir,
            "difference.s",
            "\t.section __DATA,__data\n\t.globl _cg_difference\n\t.p2align 3\n\
             _cg_difference:\n\t.quad _cg_leaf - _cg_difference\n\
             \t.subsections_via_symbols\n",
            &[],
        );
        let mut objects = exe_objects(OptLevel::O0);
        objects.push(difference);
        let output = dir.join("prog");
        ld64(dir, &objects, &output, &[]);
        let image = std::fs::read(&output).unwrap();
        let providers = vec![libsystem];
        let record = native_record(&image, &objects, providers.clone(), "difference");
        assert_complete(&record, "difference");
        let row = row_where(&record, "SUBTRACTOR difference", |row| {
            row.symbol == "_cg_leaf" && row.resolution.starts_with("difference")
        });
        assert_eq!(row.target, "_cg_leaf - _cg_difference");
        assert!(record.summary.relocations_paired >= 1);
        expect_refused(
            &Recorded {
                image: &image,
                objects: &objects,
                placement: AtomPlacement::ImageSymbolTable,
                providers: &providers,
                record: &record,
                label: "difference",
            },
            Corruption::Difference,
            CODE_DIFFERENCE,
            "_cg_leaf - _cg_difference",
        );
        assert_eq!(run_status(&output), 42);

        let hinted = clang_object(
            dir,
            "hinted.c",
            "extern long cg_data;\nlong hinted_read(void) { return cg_data + 1; }\n",
            &["-O2"],
        );
        let mut with_hints = exe_objects(OptLevel::O0);
        with_hints.push(hinted);
        expect_objects_refused(
            &image,
            &with_hints,
            AtomPlacement::ImageSymbolTable,
            &providers,
            CODE_PARSE,
            "LC_LINKER_OPTIMIZATION_HINT",
        );
    }
}
