// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Runtime dependencies, the ELF stack canary, the system link driver and
//! relocation-range controls for real trust-cg objects.
//!
//! Object-level tests run on every host: they compile trust-ir fixtures for
//! AArch64 Linux ELF and Darwin Mach-O and read the objects back with the
//! independent in-crate readers. Native controls link and run with the host
//! toolchain: the macOS arm64 legs run on Darwin, the Linux AArch64 GNU legs
//! only on Linux. This is execution evidence for the named link shapes, not a
//! claim about every linker or C runtime.

#[path = "common/rosetta.rs"]
mod process;

use std::collections::BTreeSet;

use trust_cg_codegen::elf::reparse::read_object_records;
use trust_cg_codegen::pipeline::{
    ObjectGlobal, OptLevel, Pipeline, PipelineConfig, stack_protector_target_abi,
};
use trust_cg_codegen::runtime_deps::{
    ObjectFormat, RUNTIME_DEPENDENCY_SCHEMA, RuntimeDependencyManifest, RuntimeProvider,
};
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig, frame};
use trust_ir::value::GlobalId;
use trust_ir::{
    BinOp, Constant, Endianness, Global, Linkage, Module, ProofAnnotation, ProofTag,
    StructPassingPolicy, TargetInfo, Ty,
};
use trust_ir_build::ModuleBuilder;

const LINUX: &str = "aarch64-unknown-linux-gnu";
const DARWIN: &str = "aarch64-apple-darwin";

fn target_info(triple: &str) -> TargetInfo {
    TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn compile(module: &Module, triple: &str) -> Vec<u8> {
    compile_at(module, triple, OptLevel::O0)
}

fn compile_at(module: &Module, triple: &str, opt_level: OptLevel) -> Vec<u8> {
    trust_cg_codegen::env_lock::with_env_edits(|env| {
        // Normalize only optional allocation-quality search; mandatory
        // verification, allocation and encoding checks stay enabled.
        env.remove("TCG_AY_REGALLOC");
        Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level,
                parallel: false,
                ..CompilerConfig::default()
            },
            TargetSpec::parse(triple).unwrap(),
        )
        .with_codegen_license(permit_unlicensed())
        .compile(module)
        .unwrap_or_else(|error| panic!("{triple} fixture must compile: {error:?}"))
        .object_code
    })
}

fn ssp_required() -> ProofAnnotation {
    ProofAnnotation::Custom(ProofTag::new(
        trust_cg_lower::LLVM_STACK_PROTECTOR_REQUIRED_FUNCTION_ATTR_TAG,
    ))
}

/// Functions whose lowering needs every non-unwinder runtime family:
/// 128-bit division helpers, `fmod`, `memcpy` with a run-time length, the
/// stack-protector runtime (the guarded function requests SSP) and one
/// program-supplied external.
fn runtime_probe(triple: &str) -> Module {
    probe_module(triple, true)
}

/// The probe without the guarded function: every reference resolves inside
/// the C and compiler runtimes, so it can be linked as a shared object on
/// both Darwin (which refuses undefined dylib symbols) and Linux.
#[cfg_attr(
    not(any(
        all(target_os = "macos", target_arch = "aarch64"),
        all(target_os = "linux", target_arch = "aarch64", target_env = "gnu")
    )),
    allow(dead_code)
)]
fn library_probe(triple: &str) -> Module {
    probe_module(triple, false)
}

fn probe_module(triple: &str, with_guarded: bool) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("tcg_runtime_probe", target_info(triple));

    let wide_ty = mb.add_func_type(vec![Ty::I128, Ty::I128], vec![Ty::I128]);
    for (name, op) in [("tcg_i128_div", BinOp::SDiv), ("tcg_u128_rem", BinOp::URem)] {
        let mut fb = mb.function(name, wide_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let a = fb.add_block_param(entry, Ty::I128);
        let b = fb.add_block_param(entry, Ty::I128);
        let result = fb.binop(op, Ty::I128, a, b);
        fb.ret(vec![result]);
        fb.build();
    }

    let fmod_ty = mb.add_func_type(vec![Ty::F64, Ty::F64], vec![Ty::F64]);
    {
        let mut fb = mb.function("tcg_fmod", fmod_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let a = fb.add_block_param(entry, Ty::F64);
        let b = fb.add_block_param(entry, Ty::F64);
        let result = fb.binop(BinOp::FRem, Ty::F64, a, b);
        fb.ret(vec![result]);
        fb.build();
    }

    if with_guarded {
        let hook_ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let hook = mb.declare_function("tcg_external_hook", hook_ty);
        let memcpy_ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::I64], vec![Ty::Ptr]);
        let memcpy = mb.declare_function("memcpy", memcpy_ty);
        let guarded_ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("tcg_guarded", guarded_ty);
        fb.add_function_proof(ssp_required());
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let x = fb.add_block_param(entry, Ty::I64);
        let len = fb.add_block_param(entry, Ty::I64);
        let source = fb.alloca(Ty::I64);
        fb.store(Ty::I64, source, x);
        let dest = fb.alloca(Ty::I64);
        fb.call(memcpy, vec![dest, source, len]);
        let copied = fb.load(Ty::I64, dest);
        let hooked = fb.call(hook, vec![copied]);
        fb.ret(vec![hooked]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The C harness for [`runtime_probe`]: supplies the external hook and checks
/// every probe result (exit 0 on success, a distinct code per failure).
#[cfg_attr(
    not(any(
        all(target_os = "macos", target_arch = "aarch64"),
        all(target_os = "linux", target_arch = "aarch64", target_env = "gnu")
    )),
    allow(dead_code)
)]
const RUNTIME_PROBE_HARNESS: &str = r#"
extern __int128 tcg_i128_div(__int128, __int128);
extern unsigned __int128 tcg_u128_rem(unsigned __int128, unsigned __int128);
extern double tcg_fmod(double, double);
extern long tcg_guarded(long, long);
long tcg_external_hook(long x) { return x * 3 + 1; }
int main(void) {
    __int128 numerator = -((__int128)100 << 64) - 3;
    if (tcg_i128_div(numerator, 7) != numerator / 7) return 11;
    unsigned __int128 big = ((unsigned __int128)1 << 100) + 5;
    if (tcg_u128_rem(big, 1000003) != big % 1000003) return 12;
    if (tcg_fmod(7.5, 2.0) != 1.5) return 13;
    if (tcg_guarded(5, 8) != 16) return 14;
    return 0;
}
"#;

/// The C harness for [`library_probe`].
#[cfg_attr(
    not(any(
        all(target_os = "macos", target_arch = "aarch64"),
        all(target_os = "linux", target_arch = "aarch64", target_env = "gnu")
    )),
    allow(dead_code)
)]
const LIBRARY_PROBE_HARNESS: &str = r#"
extern __int128 tcg_i128_div(__int128, __int128);
extern unsigned __int128 tcg_u128_rem(unsigned __int128, unsigned __int128);
extern double tcg_fmod(double, double);
int main(void) {
    __int128 numerator = -((__int128)100 << 64) - 3;
    if (tcg_i128_div(numerator, 7) != numerator / 7) return 11;
    unsigned __int128 big = ((unsigned __int128)1 << 100) + 5;
    if (tcg_u128_rem(big, 1000003) != big % 1000003) return 12;
    if (tcg_fmod(7.5, 2.0) != 1.5) return 13;
    return 0;
}
"#;

fn expected_runtime_groups() -> Vec<(RuntimeProvider, Vec<&'static str>)> {
    vec![
        (RuntimeProvider::MemoryIntrinsics, vec!["memcpy"]),
        (
            RuntimeProvider::Libc,
            vec!["__stack_chk_fail", "__stack_chk_guard"],
        ),
        (RuntimeProvider::Libm, vec!["fmod"]),
        (
            RuntimeProvider::CompilerRuntime,
            vec!["__divti3", "__umodti3"],
        ),
        (RuntimeProvider::External, vec!["tcg_external_hook"]),
    ]
}

fn c_names(manifest: &RuntimeDependencyManifest, provider: RuntimeProvider) -> Vec<String> {
    manifest
        .dependencies
        .iter()
        .filter(|dependency| dependency.provider == provider)
        .map(|dependency| dependency.c_name.clone())
        .collect()
}

#[test]
fn elf_runtime_manifest_groups_every_undefined_symbol_of_a_real_object() {
    let object = compile(&runtime_probe(LINUX), LINUX);
    let manifest = RuntimeDependencyManifest::from_object(&object).unwrap();
    assert_eq!(manifest.format, ObjectFormat::Elf);
    for (provider, expected) in expected_runtime_groups() {
        assert_eq!(
            manifest.symbols_for(provider),
            expected,
            "{provider} group of {manifest:#?}"
        );
    }
    assert!(
        manifest.providers().iter().all(|provider| !matches!(
            provider,
            RuntimeProvider::Unwinder
                | RuntimeProvider::EhPersonality
                | RuntimeProvider::TlsRuntime
        )),
        "the probe has no EH or TLS: {manifest:#?}"
    );
    assert!(
        manifest
            .dependencies
            .iter()
            .all(|dependency| !dependency.weak)
    );

    // Independent cross-check: the manifest is exactly the set of undefined
    // symbols that the object's relocation records reference.
    let records = read_object_records(&object).unwrap();
    let relocated_undefined: BTreeSet<&str> = records
        .relocations
        .iter()
        .map(|relocation| &records.symbols[relocation.record.symbol_index as usize])
        .filter(|symbol| symbol.is_undefined_reference())
        .map(|symbol| symbol.name.as_str())
        .collect();
    assert_eq!(relocated_undefined, manifest.required_symbols());
}

#[test]
fn macho_runtime_manifest_uses_the_same_c_level_names() {
    let elf =
        RuntimeDependencyManifest::from_object(&compile(&runtime_probe(LINUX), LINUX)).unwrap();
    let macho =
        RuntimeDependencyManifest::from_object(&compile(&runtime_probe(DARWIN), DARWIN)).unwrap();
    assert_eq!(macho.format, ObjectFormat::MachO);
    for (provider, expected) in expected_runtime_groups() {
        let underscored: Vec<String> = expected.iter().map(|name| format!("_{name}")).collect();
        assert_eq!(macho.symbols_for(provider), underscored, "{provider}");
        assert_eq!(c_names(&macho, provider), c_names(&elf, provider));
    }
}

/// `tcg_eh_cleanup` invokes the external `tcg_eh_throw` with a cleanup-only
/// landing pad that calls `tcg_eh_record` and resumes the exception.
fn eh_cleanup_module(triple: &str) -> Module {
    use trust_ir::{Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, ValueId};

    let mut module = Module::new("tcg_eh_runtime_probe");
    module.target_info = Some(target_info(triple));
    let void_ty = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    for (id, name) in [(0, "tcg_eh_throw"), (1, "tcg_eh_record")] {
        let mut external = Function::new(FuncId::new(id), name, void_ty, BlockId::new(0));
        external.linkage = Linkage::External;
        module
            .try_add_function(external)
            .expect("Module::try_add_function: test fixture");
    }
    let int_ty = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut cleanup = Function::new(FuncId::new(2), "tcg_eh_cleanup", int_ty, BlockId::new(0));
    cleanup.blocks = vec![
        Block {
            id: BlockId::new(0),
            params: vec![],
            body: vec![InstrNode::new(Inst::Invoke {
                callee: FuncId::new(0),
                args: vec![],
                normal_dest: BlockId::new(1),
                normal_args: vec![],
                unwind_dest: BlockId::new(2),
            })],
        },
        Block {
            id: BlockId::new(1),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(10)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(10)],
                }),
            ],
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
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![],
                }),
                InstrNode::new(Inst::Resume {
                    exn: ValueId::new(20),
                }),
            ],
        },
    ];
    module
        .try_add_function(cleanup)
        .expect("Module::try_add_function: test fixture");
    module
}

/// The unwinder and personality groups come from a real exception-handling
/// object: the cleanup pad's `Resume` needs `_Unwind_Resume` and the unwind
/// tables name a personality routine. The manifest is again exactly the
/// object's relocated undefined symbols, and the two formats agree on C names.
#[test]
fn eh_object_manifest_names_the_unwinder_and_personality() {
    let elf_object = compile(&eh_cleanup_module(LINUX), LINUX);
    let elf = RuntimeDependencyManifest::from_object(&elf_object).unwrap();
    assert_eq!(
        elf.symbols_for(RuntimeProvider::Unwinder),
        ["_Unwind_Resume"],
        "{elf:#?}"
    );
    let personalities = elf.symbols_for(RuntimeProvider::EhPersonality);
    assert_eq!(personalities.len(), 1, "{elf:#?}");
    assert!(personalities[0].ends_with("_personality_v0"), "{elf:#?}");
    assert_eq!(
        elf.symbols_for(RuntimeProvider::External),
        ["tcg_eh_record", "tcg_eh_throw"]
    );
    let records = read_object_records(&elf_object).unwrap();
    let relocated_undefined: BTreeSet<&str> = records
        .relocations
        .iter()
        .map(|relocation| &records.symbols[relocation.record.symbol_index as usize])
        .filter(|symbol| symbol.is_undefined_reference())
        .map(|symbol| symbol.name.as_str())
        .collect();
    assert_eq!(relocated_undefined, elf.required_symbols());

    let macho =
        RuntimeDependencyManifest::from_object(&compile(&eh_cleanup_module(DARWIN), DARWIN))
            .unwrap();
    for provider in [
        RuntimeProvider::Unwinder,
        RuntimeProvider::EhPersonality,
        RuntimeProvider::External,
    ] {
        assert_eq!(
            c_names(&macho, provider),
            c_names(&elf, provider),
            "{provider}"
        );
    }
}

#[test]
fn runtime_manifest_json_names_schema_providers_and_library_hints() {
    let manifest =
        RuntimeDependencyManifest::from_object(&compile(&runtime_probe(LINUX), LINUX)).unwrap();
    let json = manifest.to_json();
    assert_eq!(json["schema"], RUNTIME_DEPENDENCY_SCHEMA);
    assert_eq!(json["format"], "elf");
    assert_eq!(json["undefined_symbol_count"], 7);
    let providers: Vec<&str> = json["providers"]
        .as_array()
        .unwrap()
        .iter()
        .map(|group| group["provider"].as_str().unwrap())
        .collect();
    assert_eq!(
        providers,
        [
            "memory_intrinsics",
            "libc",
            "libm",
            "compiler_runtime",
            "external"
        ]
    );
    let compiler_runtime = &json["providers"][3];
    assert!(
        compiler_runtime["library_hint"]
            .as_str()
            .unwrap()
            .contains("libgcc")
    );
    assert_eq!(compiler_runtime["symbols"][0]["name"], "__divti3");
    assert_eq!(compiler_runtime["symbols"][0]["weak"], false);
}

#[test]
fn elf_stack_guard_is_read_through_the_got_and_fails_through_call26() {
    use trust_cg_codegen::elf::constants::{
        R_AARCH64_ADR_GOT_PAGE, R_AARCH64_CALL26, R_AARCH64_LD64_GOT_LO12_NC,
    };
    stack_protector_target_abi(LINUX).unwrap();
    let object = compile(&runtime_probe(LINUX), LINUX);
    let records = read_object_records(&object).unwrap();
    let kinds_against = |name: &str| -> Vec<u32> {
        records
            .relocations
            .iter()
            .filter(|relocation| {
                records.symbols[relocation.record.symbol_index as usize].name == name
            })
            .map(|relocation| relocation.record.reloc_type)
            .collect()
    };
    let guard = kinds_against("__stack_chk_guard");
    assert!(
        !guard.is_empty(),
        "the guarded function must read the guard"
    );
    assert_eq!(guard.len() % 2, 0, "{guard:?}");
    for pair in guard.chunks(2) {
        assert_eq!(pair, [R_AARCH64_ADR_GOT_PAGE, R_AARCH64_LD64_GOT_LO12_NC]);
    }
    assert!(
        !kinds_against("__stack_chk_fail").is_empty()
            && kinds_against("__stack_chk_fail")
                .iter()
                .all(|kind| *kind == R_AARCH64_CALL26)
    );
}

// ---------------------------------------------------------------------------
// Link-control fixtures
// ---------------------------------------------------------------------------

/// `tcg_calls_missing` calls an undefined `tcg_missing_symbol`.
fn undefined_reference_module(triple: &str) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("tcg_undefined_ref", target_info(triple));
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let missing = mb.declare_function("tcg_missing_symbol", ty);
    let mut fb = mb.function("tcg_calls_missing", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let value = fb.call(missing, vec![]);
    fb.ret(vec![value]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A strong definition of `tcg_duplicate` returning `value`.
#[cfg(any(
    all(target_os = "macos", target_arch = "aarch64"),
    all(target_os = "linux", target_arch = "aarch64", target_env = "gnu")
))]
fn duplicate_definition_module(triple: &str, value: i128) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("tcg_duplicate_def", target_info(triple));
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("tcg_duplicate", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let result = fb.iconst(Ty::I64, value);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `tcg_read_far` reads the module's own exported word `tcg_far_word` (42)
/// through a direct ADRP page reference.
fn far_word_module(triple: &str) -> Module {
    far_word_module_in(triple, None)
}

/// [`far_word_module`] with `tcg_far_word` in `section` when one is given,
/// where it is read-only (a writable section of its own made gold 2.42 stop
/// with an internal error when placed), and in `.data` otherwise.
fn far_word_module_in(triple: &str, section: Option<&str>) -> Module {
    let mut module = {
        let mut mb = ModuleBuilder::new_with_target_info("tcg_far_word", target_info(triple));
        let ty = mb.add_func_type(vec![], vec![Ty::I64]);
        let mut fb = mb.function("tcg_read_far", ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let address = fb.global_addr(GlobalId::new(0));
        let value = fb.load(Ty::I64, address);
        fb.ret(vec![value]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    module.globals = vec![Global {
        section: section.map(str::to_string),
        visibility: trust_ir::Visibility::Default,
        retained: false,
        name: "tcg_far_word".into(),
        ty: Ty::U64,
        mutable: section.is_none(),
        initializer: Some(Constant::Int(42)),
        linkage: Linkage::External,
        tls: None,
        align: Some(8),
    }];
    module
}

/// `tcg_call_far` calls the externally supplied `tcg_far_fn`.
fn far_call_module(triple: &str) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("tcg_far_call", target_info(triple));
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let far = mb.declare_function("tcg_far_fn", ty);
    let mut fb = mb.function("tcg_call_far", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let value = fb.call(far, vec![]);
    let one = fb.iconst(Ty::I64, 0);
    let sum = fb.add(Ty::I64, value, one);
    fb.ret(vec![sum]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `tcg_tail_far` returns `tcg_far_fn()` from tail position.
fn tail_call_module(triple: &str) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("tcg_tail_far", target_info(triple));
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let far = mb.declare_function("tcg_far_fn", ty);
    let mut fb = mb.function("tcg_tail_far", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let value = fb.call(far, vec![]);
    fb.ret(vec![value]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// [`tail_call_module`] compiled at the first optimization level whose
/// object branches to `tcg_far_fn` with a tail `B` (`R_AARCH64_JUMP26`),
/// and that level.
fn tail_call_object(triple: &str) -> (OptLevel, Vec<u8>) {
    [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3]
        .into_iter()
        .map(|level| (level, compile_at(&tail_call_module(triple), triple, level)))
        .find(|(_, object)| {
            relocations_by_symbol(object).contains(&(
                trust_cg_codegen::elf::constants::R_AARCH64_JUMP26,
                "tcg_far_fn".to_string(),
            ))
        })
        .expect("some optimization level tail-calls tcg_far_fn with JUMP26")
}

/// `tcg_tls_far_addr()` returns the address of `tcg_tls_far`, an 8-byte
/// thread-local another object defines: initial exec
/// (`R_AARCH64_TLSIE_*`) with the default relocation model, a TLS
/// descriptor (`R_AARCH64_TLSDESC_*`) with `pic`.
fn tls_import_module(triple: &str) -> Module {
    let mut module = {
        let mut mb = ModuleBuilder::new_with_target_info("tcg_tls_far", target_info(triple));
        let ty = mb.add_func_type(vec![], vec![Ty::I64]);
        let mut fb = mb.function("tcg_tls_far_addr", ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let address = fb.global_addr(GlobalId::new(0));
        let value = fb.cast(trust_ir::CastOp::PtrToInt, Ty::Ptr, Ty::I64, address);
        fb.ret(vec![value]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    module.globals = vec![Global {
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        name: "tcg_tls_far".into(),
        ty: Ty::I64,
        mutable: true,
        initializer: None,
        linkage: Linkage::External,
        tls: Some(trust_ir::TlsModel::InitialExec),
        align: Some(8),
    }];
    module
}

/// The `TLSLE_ADD_TPREL_HI12` window is `0 <= TPREL(S + A) < 2^24`.
const TLSLE_WINDOW: usize = 1 << 24;

/// Compile `module` for `triple` with `configure` applied to the default
/// configuration, returning the refusal text instead of panicking.
fn try_compile_with(
    module: &Module,
    triple: &str,
    configure: impl FnOnce(&mut CompilerConfig),
) -> Result<Vec<u8>, String> {
    trust_cg_codegen::env_lock::with_env_edits(|env| {
        env.remove("TCG_AY_REGALLOC");
        let mut config = CompilerConfig {
            opt_level: OptLevel::O0,
            parallel: false,
            ..CompilerConfig::default()
        };
        configure(&mut config);
        Compiler::new_for_target_spec(config, TargetSpec::parse(triple).unwrap())
            .with_codegen_license(permit_unlicensed())
            .compile(module)
            .map(|compiled| compiled.object_code)
            .map_err(|error| error.to_string())
    })
}

/// Local-exec TLS probe: a zero-filled thread-local `tcg_le_pad` of `pad`
/// bytes (absent when `pad` is 0) followed in `.tbss` by the 8-byte
/// `tcg_le_edge`, which `tcg_le_edge_bump` increments by 42 and returns.
/// `.tbss` members are 16-byte aligned, so `tcg_le_edge` sits at offset
/// `pad` rounded up to 16 and its `TPREL` is at least 16 more than that.
fn local_exec_tls_module(triple: &str, pad: usize) -> Module {
    let edge_index = usize::from(pad > 0);
    let mut module = {
        let mut mb = ModuleBuilder::new_with_target_info("tcg_le_edge", target_info(triple));
        let ty = mb.add_func_type(vec![], vec![Ty::I64]);
        let mut fb = mb.function("tcg_le_edge_bump", ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let address = fb.global_addr(GlobalId::new(edge_index as u32));
        let value = fb.load(Ty::I64, address);
        let step = fb.iconst(Ty::I64, 42);
        let bumped = fb.add(Ty::I64, value, step);
        fb.store(Ty::I64, address, bumped);
        fb.ret(vec![bumped]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let byte = module
        .add_type(Ty::U8)
        .expect("Module::add_type: test fixture");
    let thread_local = |name: &str, ty: Ty, initializer: Constant| Global {
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        name: name.into(),
        ty,
        mutable: true,
        initializer: Some(initializer),
        linkage: Linkage::External,
        tls: Some(trust_ir::TlsModel::LocalExec),
        align: Some(8),
    };
    let mut globals = Vec::new();
    if pad > 0 {
        globals.push(thread_local(
            "tcg_le_pad",
            Ty::Array(byte, pad as u64),
            Constant::splat(Constant::Int(0), pad as u64),
        ));
    }
    globals.push(thread_local("tcg_le_edge", Ty::I64, Constant::Int(0)));
    assert_eq!(globals[edge_index].name, "tcg_le_edge");
    module.globals = globals;
    module
}

/// `tcg_desc_bump()` adds 2 to the thread-local `tcg_desc_tls` (40) and
/// returns it plus `tcg_desc_word` (100) minus 100: 42, then 44. Compiled
/// with the `pic` relocation model, the thread-local is reached through a
/// TLS descriptor (`R_AARCH64_TLSDESC_*`) and the preemptible
/// `tcg_desc_word` through its GOT slot (`R_AARCH64_ADR_GOT_PAGE`).
fn got_page_module(triple: &str) -> Module {
    let mut module = {
        let mut mb = ModuleBuilder::new_with_target_info("tcg_desc", target_info(triple));
        let ty = mb.add_func_type(vec![], vec![Ty::I32]);
        let mut fb = mb.function("tcg_desc_bump", ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let tls = fb.global_addr(GlobalId::new(0));
        let value = fb.load(Ty::I32, tls);
        let two = fb.iconst(Ty::I32, 2);
        let bumped = fb.add(Ty::I32, value, two);
        fb.store(Ty::I32, tls, bumped);
        let word = fb.global_addr(GlobalId::new(1));
        let word = fb.load(Ty::I32, word);
        let sum = fb.add(Ty::I32, bumped, word);
        let hundred = fb.iconst(Ty::I32, 100);
        let result = fb.binop(BinOp::Sub, Ty::I32, sum, hundred);
        fb.ret(vec![result]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let global = |name: &str, value: i128, tls| Global {
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        name: name.into(),
        ty: Ty::I32,
        mutable: true,
        initializer: Some(Constant::Int(value)),
        linkage: Linkage::External,
        tls,
        align: None,
    };
    module.globals = vec![
        global("tcg_desc_tls", 40, Some(trust_ir::TlsModel::LocalExec)),
        global("tcg_desc_word", 100, None),
    ];
    module
}

/// `tcg_debug_probe()` returns 42; compiled with `-g` it carries DWARF whose
/// section offsets are `R_AARCH64_ABS32` relocations.
fn debug_probe_module(triple: &str) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("tcg_debug_probe", target_info(triple));
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("tcg_debug_probe", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let value = fb.iconst(Ty::I64, 42);
    fb.ret(vec![value]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `(relocation type, symbol name)` of every record in an ELF object.
fn relocations_by_symbol(object: &[u8]) -> Vec<(u32, String)> {
    let records = read_object_records(object).unwrap();
    records
        .relocations
        .iter()
        .map(|relocation| {
            let symbol = &records.symbols[relocation.record.symbol_index as usize];
            let name = if symbol.name.is_empty() {
                records.sections[usize::from(symbol.section_index)]
                    .name
                    .clone()
            } else {
                symbol.name.clone()
            };
            (relocation.record.reloc_type, name)
        })
        .collect()
}

/// A local-exec thread-local whose `TPREL` this object already puts at
/// `2^24` or above is refused by name; one 16-byte slot earlier (`TPREL`
/// at least `2^24 - 16`) it compiles, with its `.tbss` pad as zero-fill.
#[test]
fn local_exec_tls_past_the_hi12_window_is_refused_by_name_at_the_edge() {
    use trust_cg_codegen::elf::constants as c;
    let error = try_compile_with(
        &local_exec_tls_module(LINUX, TLSLE_WINDOW - 16),
        LINUX,
        |_| {},
    )
    .expect_err("TPREL >= 2^24 in every link");
    assert!(
        error.contains("[TCG-RELOC-WINDOW-TLSLE] R_AARCH64_TLSLE_ADD_TPREL_HI12")
            && error.contains("`tcg_le_edge`")
            && error.contains("at least 16777216"),
        "{error}"
    );

    let object = try_compile_with(
        &local_exec_tls_module(LINUX, TLSLE_WINDOW - 32),
        LINUX,
        |_| {},
    )
    .expect("TPREL >= 2^24 - 16 is left to the linker");
    let records = read_object_records(&object).unwrap();
    let edge = records
        .symbols
        .iter()
        .find(|symbol| symbol.name == "tcg_le_edge")
        .unwrap();
    assert_eq!(edge.value, (TLSLE_WINDOW - 32) as u64);
    let relocations = relocations_by_symbol(&object);
    for kind in [
        c::R_AARCH64_TLSLE_ADD_TPREL_HI12,
        c::R_AARCH64_TLSLE_ADD_TPREL_LO12_NC,
    ] {
        assert!(
            relocations.contains(&(kind, "tcg_le_edge".to_string())),
            "{kind:#x}: {relocations:?}"
        );
    }
    assert!(object.len() < 1 << 20, "the 16 MiB pad is zero-fill");
}

/// The fixtures of the relocation-limit controls carry the relocation kinds
/// those controls rely on.
#[test]
fn relocation_limit_fixtures_carry_the_kinds_their_controls_rely_on() {
    use trust_cg_codegen::elf::constants as c;
    let pic = try_compile_with(&got_page_module(LINUX), LINUX, |config| {
        config.relocation_model = trust_cg_codegen::RelocationModel::Pic;
    })
    .unwrap();
    let relocations = relocations_by_symbol(&pic);
    for expected in [
        (c::R_AARCH64_TLSDESC_ADR_PAGE21, "tcg_desc_tls"),
        (c::R_AARCH64_ADR_GOT_PAGE, "tcg_desc_word"),
    ] {
        assert!(
            relocations.contains(&(expected.0, expected.1.to_string())),
            "{expected:?}: {relocations:?}"
        );
    }

    let small = try_compile_with(&local_exec_tls_module(LINUX, 0), LINUX, |_| {}).unwrap();
    assert!(
        relocations_by_symbol(&small)
            .contains(&(c::R_AARCH64_TLSLE_ADD_TPREL_HI12, "tcg_le_edge".to_string()))
    );

    let debug = try_compile_with(&debug_probe_module(LINUX), LINUX, |config| {
        config.emit_debug = true;
    })
    .unwrap();
    assert!(
        relocations_by_symbol(&debug).contains(&(c::R_AARCH64_ABS32, ".debug_str".to_string())),
        "{:?}",
        relocations_by_symbol(&debug)
    );

    // The word in its own read-only section is still read through a direct
    // page reference.
    let placed = compile(&far_word_module_in(LINUX, Some(".tcg_far_data")), LINUX);
    assert!(
        relocations_by_symbol(&placed)
            .contains(&(c::R_AARCH64_ADR_PREL_PG_HI21, "tcg_far_word".to_string())),
        "{:?}",
        relocations_by_symbol(&placed)
    );
    let records = read_object_records(&placed).unwrap();
    let section = records
        .sections
        .iter()
        .find(|section| section.name == ".tcg_far_data")
        .expect("the word's own section");
    assert_eq!(section.sh_flags & 0x3, 0x2, "allocated, not writable");

    // Some level tail-calls through JUMP26 (`tail_call_object` finds it).
    let (_, tail) = tail_call_object(LINUX);
    assert!(
        !relocations_by_symbol(&tail).contains(&(c::R_AARCH64_CALL26, "tcg_far_fn".to_string()))
    );

    // The imported thread-local: initial exec, and a descriptor with `pic`.
    let ie = try_compile_with(&tls_import_module(LINUX), LINUX, |_| {}).unwrap();
    assert!(
        relocations_by_symbol(&ie).contains(&(
            c::R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21,
            "tcg_tls_far".to_string()
        )),
        "{:?}",
        relocations_by_symbol(&ie)
    );
    let desc = try_compile_with(&tls_import_module(LINUX), LINUX, |config| {
        config.relocation_model = trust_cg_codegen::RelocationModel::Pic;
    })
    .unwrap();
    assert!(
        relocations_by_symbol(&desc)
            .contains(&(c::R_AARCH64_TLSDESC_ADR_PAGE21, "tcg_tls_far".to_string())),
        "{:?}",
        relocations_by_symbol(&desc)
    );
}

#[test]
fn link_control_fixtures_carry_the_references_the_controls_rely_on() {
    let undefined =
        RuntimeDependencyManifest::from_object(&compile(&undefined_reference_module(LINUX), LINUX))
            .unwrap();
    assert_eq!(
        undefined.symbols_for(RuntimeProvider::External),
        ["tcg_missing_symbol"]
    );

    let far_word = compile(&far_word_module(LINUX), LINUX);
    let records = read_object_records(&far_word).unwrap();
    let direct_page = records.relocations.iter().any(|relocation| {
        relocation.record.reloc_type == trust_cg_codegen::elf::constants::R_AARCH64_ADR_PREL_PG_HI21
            && records.symbols[relocation.record.symbol_index as usize].name == "tcg_far_word"
    });
    assert!(
        direct_page,
        "the ADRP range control needs a direct page reference: {:?}",
        records.relocations
    );

    let far_call = compile(&far_call_module(LINUX), LINUX);
    let records = read_object_records(&far_call).unwrap();
    assert!(records.relocations.iter().any(|relocation| {
        matches!(
            relocation.record.reloc_type,
            trust_cg_codegen::elf::constants::R_AARCH64_CALL26
                | trust_cg_codegen::elf::constants::R_AARCH64_JUMP26
        ) && records.symbols[relocation.record.symbol_index as usize].name == "tcg_far_fn"
    }));
}

/// A stack-protected leaf returning 42; `corrupt` overwrites the saved guard
/// so the epilogue must take the failure path. ELF triple, Pipeline level.
fn elf_guard_object(corrupt: bool) -> Vec<u8> {
    use trust_cg_ir::regs::{X0, XZR};
    use trust_cg_ir::{
        AArch64Opcode as Op, MachFunction, MachInst, MachOperand as Operand, Signature,
        StackProtectorMode, Type,
    };
    trust_cg_codegen::env_lock::with_env_edits(|env| {
        env.remove("TCG_AY_REGALLOC");
        let mut func = MachFunction::new(
            "tcg_guard_target".into(),
            Signature::new(vec![], vec![Type::I64]),
        );
        func.stack_protector = StackProtectorMode::StackGuard;
        frame::ensure_stack_protector_slot(&mut func).unwrap();
        if corrupt {
            let store = func.push_inst(MachInst::new(
                Op::StrRI,
                vec![
                    Operand::PReg(XZR),
                    Operand::StackSlot(func.stack_protector_slot.unwrap()),
                ],
            ));
            func.append_inst(func.entry, store);
        }
        let mov = func.push_inst(MachInst::new(
            Op::Movz,
            vec![Operand::PReg(X0), Operand::Imm(42)],
        ));
        func.append_inst(func.entry, mov);
        let ret = func.push_inst(MachInst::new(Op::Ret, vec![]).with_implicit_uses(&[X0]));
        func.append_inst(func.entry, ret);
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level: OptLevel::O0,
            verify: true,
            target_triple: LINUX.into(),
            ..PipelineConfig::default()
        });
        pipeline.prepare_ir_function(&mut func).unwrap();
        let no_globals: [ObjectGlobal; 0] = [];
        pipeline
            .compile_module_with_globals(&[func], &no_globals)
            .unwrap()
    })
}

#[test]
fn elf_guard_objects_differ_only_by_the_corrupting_store() {
    let intact_object = elf_guard_object(false);
    let corrupt_object = elf_guard_object(true);
    let intact = RuntimeDependencyManifest::from_object(&intact_object).unwrap();
    let corrupt = RuntimeDependencyManifest::from_object(&corrupt_object).unwrap();
    assert_eq!(
        intact.symbols_for(RuntimeProvider::Libc),
        ["__stack_chk_fail", "__stack_chk_guard"]
    );
    assert_eq!(intact, corrupt);

    // The Linux execution control relies on the corrupting `str xzr` being
    // present: the corrupt text is exactly one 64-bit XZR store longer.
    let text_words = |object: &[u8]| -> Vec<u32> {
        let records = read_object_records(object).unwrap();
        let index = records
            .sections
            .iter()
            .position(|section| section.name == ".text")
            .unwrap();
        object_section_bytes(object, index)
            .as_chunks::<4>()
            .0
            .iter()
            .map(|word| u32::from_le_bytes(*word))
            .collect()
    };
    // STR Xt (unsigned offset) or STUR Xt with Rt = XZR.
    let stores_xzr = |word: &u32| {
        word & 0x1f == 31
            && (word & 0xffc0_0000 == 0xf900_0000 || word & 0xffe0_0c00 == 0xf800_0000)
    };
    let intact_text = text_words(&intact_object);
    let corrupt_text = text_words(&corrupt_object);
    assert_eq!(corrupt_text.len(), intact_text.len() + 1);
    assert_eq!(
        corrupt_text.iter().filter(|word| stores_xzr(word)).count(),
        intact_text.iter().filter(|word| stores_xzr(word)).count() + 1,
        "the corrupt object must carry exactly one extra XZR store"
    );
}

// ---------------------------------------------------------------------------
// Fused ADRP + LDR/STR #:lo12: (R_AARCH64_LDST*_ABS_LO12_NC)
// ---------------------------------------------------------------------------

fn typed_global(name: &str, ty: Ty, value: Constant, align: u32, linkage: Linkage) -> Global {
    Global {
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        name: name.into(),
        ty,
        mutable: true,
        initializer: Some(value),
        linkage,
        tls: None,
        align: Some(align),
    }
}

/// Byte, halfword, word, doubleword and double globals at their natural
/// alignment, read by `tcg_lo12_sum`/`tcg_lo12_scale` and written by
/// `tcg_lo12_store`; plus an under-aligned (`align 1`) doubleword and a weak
/// doubleword read by `tcg_lo12_unfusible`.
fn lo12_probe(triple: &str) -> Module {
    let mut module = {
        let mut mb = ModuleBuilder::new_with_target_info("tcg_lo12_probe", target_info(triple));
        let sum_ty = mb.add_func_type(vec![], vec![Ty::I64]);
        {
            let mut fb = mb.function("tcg_lo12_sum", sum_ty);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let mut total = None;
            for (index, ty) in [(0, Ty::I8), (1, Ty::I16), (2, Ty::I32)] {
                let address = fb.global_addr(GlobalId::new(index));
                let narrow = fb.load(ty.clone(), address);
                let wide = fb.zext(ty, Ty::I64, narrow);
                total = Some(match total {
                    None => wide,
                    Some(sum) => fb.add(Ty::I64, sum, wide),
                });
            }
            let address = fb.global_addr(GlobalId::new(3));
            let doubleword = fb.load(Ty::I64, address);
            let sum = fb.add(Ty::I64, total.unwrap(), doubleword);
            fb.ret(vec![sum]);
            fb.build();
        }
        let scale_ty = mb.add_func_type(vec![], vec![Ty::F64]);
        {
            let mut fb = mb.function("tcg_lo12_scale", scale_ty);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let address = fb.global_addr(GlobalId::new(4));
            let value = fb.load(Ty::F64, address);
            let doubled = fb.fadd(Ty::F64, value, value);
            fb.ret(vec![doubled]);
            fb.build();
        }
        let store_ty = mb.add_func_type(vec![Ty::I64], vec![]);
        {
            let mut fb = mb.function("tcg_lo12_store", store_ty);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let value = fb.add_block_param(entry, Ty::I64);
            let address = fb.global_addr(GlobalId::new(3));
            fb.store(Ty::I64, address, value);
            for (index, ty) in [(2, Ty::I32), (1, Ty::I16), (0, Ty::I8)] {
                let narrow = fb.trunc(Ty::I64, ty.clone(), value);
                let address = fb.global_addr(GlobalId::new(index));
                fb.store(ty, address, narrow);
            }
            fb.ret(vec![]);
            fb.build();
        }
        {
            let mut fb = mb.function("tcg_lo12_unfusible", sum_ty);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let packed = fb.global_addr(GlobalId::new(5));
            let packed = fb.load(Ty::I64, packed);
            let weak = fb.global_addr(GlobalId::new(6));
            let weak = fb.load(Ty::I64, weak);
            let sum = fb.add(Ty::I64, packed, weak);
            fb.ret(vec![sum]);
            fb.build();
        }
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    module.globals = vec![
        typed_global(
            "tcg_lo12_b",
            Ty::I8,
            Constant::Int(0x5a),
            1,
            Linkage::External,
        ),
        typed_global(
            "tcg_lo12_h",
            Ty::I16,
            Constant::Int(0x1234),
            2,
            Linkage::External,
        ),
        typed_global(
            "tcg_lo12_w",
            Ty::I32,
            // The bit pattern 0x89abcdef, as the signed lane value it is.
            Constant::Int((0x89ab_cdef_u32 as i32).into()),
            4,
            Linkage::External,
        ),
        typed_global(
            "tcg_lo12_d",
            Ty::I64,
            Constant::Int(0x0123_4567_89ab_cdef),
            8,
            Linkage::External,
        ),
        typed_global(
            "tcg_lo12_f",
            Ty::F64,
            Constant::Float(1.5),
            8,
            Linkage::External,
        ),
        typed_global(
            "tcg_lo12_packed",
            Ty::I64,
            Constant::Int(7),
            1,
            Linkage::External,
        ),
        typed_global(
            "tcg_lo12_weak",
            Ty::I64,
            Constant::Int(11),
            8,
            Linkage::Weak,
        ),
    ];
    module
}

/// Q-register (`v4i32`) globals: `tcg_lo12_q_double` loads the 16-byte
/// aligned `tcg_lo12_q` ([1, 2, 3, 4]), adds it to itself lane-wise and
/// stores the sum into the 16-byte aligned `tcg_lo12_q_out`.
fn lo12_q_probe(triple: &str) -> Module {
    let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
    let mut module = {
        let mut mb = ModuleBuilder::new_with_target_info("tcg_lo12_q_probe", target_info(triple));
        let ty = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("tcg_lo12_q_double", ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let source = fb.global_addr(GlobalId::new(0));
        let value = fb.load(v4i32.clone(), source);
        let doubled = fb.add(v4i32.clone(), value, value);
        let target = fb.global_addr(GlobalId::new(1));
        fb.store(v4i32.clone(), target, doubled);
        fb.ret(vec![]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let vector = |name: &str, lanes: [i128; 4]| Global {
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        name: name.into(),
        ty: v4i32.clone(),
        mutable: true,
        initializer: Some(Constant::Vector(
            lanes.into_iter().map(Constant::Int).collect(),
        )),
        linkage: Linkage::External,
        tls: None,
        align: Some(16),
    };
    module.globals = vec![
        vector("tcg_lo12_q", [1, 2, 3, 4]),
        vector("tcg_lo12_q_out", [0; 4]),
    ];
    module
}

/// Relocation types applied to the page-offset half of each reference to
/// `symbol` (everything except the ADRP page relocation).
fn lo12_kinds_against(object: &[u8], symbol: &str) -> Vec<u32> {
    let records = read_object_records(object).unwrap();
    records
        .relocations
        .iter()
        .filter(|relocation| {
            records.symbols[relocation.record.symbol_index as usize].name == symbol
        })
        .map(|relocation| relocation.record.reloc_type)
        .filter(|kind| *kind != trust_cg_codegen::elf::constants::R_AARCH64_ADR_PREL_PG_HI21)
        .collect()
}

/// Raw bytes of section `index` of an ELF64 little-endian object.
fn object_section_bytes(object: &[u8], index: usize) -> Vec<u8> {
    let shoff = u64::from_le_bytes(object[40..48].try_into().unwrap()) as usize;
    let header = shoff + index * 64;
    let offset = u64::from_le_bytes(object[header + 24..header + 32].try_into().unwrap()) as usize;
    let size = u64::from_le_bytes(object[header + 32..header + 40].try_into().unwrap()) as usize;
    object[offset..offset + size].to_vec()
}

#[test]
fn elf_global_accesses_fuse_into_ldst_lo12_at_guaranteed_alignment() {
    use trust_cg_codegen::elf::constants as c;
    let object = compile_at(&lo12_probe(LINUX), LINUX, OptLevel::O2);
    for (symbol, expected) in [
        ("tcg_lo12_b", c::R_AARCH64_LDST8_ABS_LO12_NC),
        ("tcg_lo12_h", c::R_AARCH64_LDST16_ABS_LO12_NC),
        ("tcg_lo12_w", c::R_AARCH64_LDST32_ABS_LO12_NC),
        ("tcg_lo12_d", c::R_AARCH64_LDST64_ABS_LO12_NC),
        ("tcg_lo12_f", c::R_AARCH64_LDST64_ABS_LO12_NC),
    ] {
        // Fusion is an optimization over the allocated schedule: a site whose
        // page register is still needed keeps ADRP+ADD (correct, unfused).
        let kinds = lo12_kinds_against(&object, symbol);
        assert!(
            kinds.contains(&expected),
            "{symbol}: at least one access uses the fused LDST form, got {kinds:?}"
        );
        assert!(
            kinds
                .iter()
                .all(|kind| *kind == expected || *kind == c::R_AARCH64_ADD_ABS_LO12_NC),
            "{symbol}: only its own LDST size or the unfused ADD, got {kinds:?}"
        );
    }

    // Every fused site is an unsigned-offset load/store whose imm12 is the
    // zero placeholder and whose base is the page register of the nearest
    // preceding ADRP against the same symbol.
    let records = read_object_records(&object).unwrap();
    let text_index = records
        .sections
        .iter()
        .position(|section| section.name == ".text")
        .unwrap();
    let text = object_section_bytes(&object, text_index);
    let word_at = |offset: u64| {
        let offset = offset as usize;
        u32::from_le_bytes(text[offset..offset + 4].try_into().unwrap())
    };
    let ldst = [
        c::R_AARCH64_LDST8_ABS_LO12_NC,
        c::R_AARCH64_LDST16_ABS_LO12_NC,
        c::R_AARCH64_LDST32_ABS_LO12_NC,
        c::R_AARCH64_LDST64_ABS_LO12_NC,
        c::R_AARCH64_LDST128_ABS_LO12_NC,
    ];
    let mut checked = 0;
    for relocation in &records.relocations {
        if !ldst.contains(&relocation.record.reloc_type) {
            continue;
        }
        let word = word_at(relocation.record.r_offset);
        assert_eq!((word >> 27) & 0b111, 0b111, "{word:#010x}");
        assert_eq!((word >> 24) & 0b11, 0b01, "unsigned offset: {word:#010x}");
        assert_eq!((word >> 10) & 0xFFF, 0, "zero placeholder: {word:#010x}");
        let base = (word >> 5) & 31;
        let page = records
            .relocations
            .iter()
            .filter(|other| {
                other.record.reloc_type == c::R_AARCH64_ADR_PREL_PG_HI21
                    && other.record.symbol_index == relocation.record.symbol_index
                    && other.record.r_offset < relocation.record.r_offset
            })
            .max_by_key(|other| other.record.r_offset)
            .map(|other| word_at(other.record.r_offset) & 31);
        assert_eq!(
            page,
            Some(base),
            "fused access must use the ADRP page register"
        );
        checked += 1;
    }
    assert!(
        checked >= 8,
        "reads and writes of five globals, got {checked}"
    );
}

/// A 16-byte aligned Q-register load and store of a global this object
/// defines fuse into `LDR/STR Qt, [Xpage, #:lo12:sym]` with
/// `R_AARCH64_LDST128_ABS_LO12_NC`.
#[test]
fn q_register_global_accesses_fuse_into_ldst128_lo12() {
    use trust_cg_codegen::elf::constants as c;
    let object = compile_at(&lo12_q_probe(LINUX), LINUX, OptLevel::O2);
    for symbol in ["tcg_lo12_q", "tcg_lo12_q_out"] {
        assert_eq!(
            lo12_kinds_against(&object, symbol),
            [c::R_AARCH64_LDST128_ABS_LO12_NC],
            "{symbol}"
        );
    }
}

#[test]
fn lo12_fusion_keeps_the_add_for_under_aligned_weak_and_macho_references() {
    use trust_cg_codegen::elf::constants as c;
    let object = compile_at(&lo12_probe(LINUX), LINUX, OptLevel::O2);
    for symbol in ["tcg_lo12_packed", "tcg_lo12_weak"] {
        assert_eq!(
            lo12_kinds_against(&object, symbol),
            [c::R_AARCH64_ADD_ABS_LO12_NC],
            "{symbol} keeps ADRP+ADD+LDR"
        );
    }
    // Mach-O never receives the ELF-only carriers: every record is one of
    // the Mach-O ARM64 r_types 0..=11.
    let macho = compile_at(&lo12_probe(DARWIN), DARWIN, OptLevel::O2);
    let parsed = trust_cg_codegen::macho::linker::MachOParser::parse(&macho).unwrap();
    for section in &parsed.sections {
        for relocation in &section.relocations {
            assert!(
                !relocation.kind.is_elf_only(),
                "{:?} in {}",
                relocation.kind,
                section.name
            );
        }
    }
}

/// The C harness for [`lo12_probe`]: reads, doubles and rewrites every
/// fused global through the trust-cg functions and checks the C view.
#[cfg_attr(
    not(any(
        all(target_os = "macos", target_arch = "aarch64"),
        all(target_os = "linux", target_arch = "aarch64", target_env = "gnu")
    )),
    allow(dead_code)
)]
const LO12_PROBE_HARNESS: &str = r#"
extern unsigned char tcg_lo12_b;
extern unsigned short tcg_lo12_h;
extern unsigned int tcg_lo12_w;
extern unsigned long tcg_lo12_d;
long tcg_lo12_sum(void);
double tcg_lo12_scale(void);
void tcg_lo12_store(long);
long tcg_lo12_unfusible(void);
int main(void) {
    if ((unsigned long)tcg_lo12_sum() != 0x5aUL + 0x1234UL + 0x89abcdefUL + 0x0123456789abcdefUL) return 21;
    if (tcg_lo12_scale() != 3.0) return 22;
    tcg_lo12_store(0x1122334455667788L);
    if (tcg_lo12_d != 0x1122334455667788UL || tcg_lo12_w != 0x55667788U) return 23;
    if (tcg_lo12_h != 0x7788 || tcg_lo12_b != 0x88) return 24;
    if ((unsigned long)tcg_lo12_sum() != 0x88UL + 0x7788UL + 0x55667788UL + 0x1122334455667788UL) return 25;
    if (tcg_lo12_unfusible() != 18) return 26;
    return 0;
}
"#;

// ---------------------------------------------------------------------------
// Native link/run helpers (hosts with a native AArch64 toolchain)
// ---------------------------------------------------------------------------

#[cfg(any(
    all(target_os = "macos", target_arch = "aarch64"),
    all(target_os = "linux", target_arch = "aarch64", target_env = "gnu")
))]
mod native {
    use super::*;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::time::Duration;
    use trust_cg_codegen::link_driver::{
        LinkDiagnostic, LinkDiagnosticKind, LinkOutputKind, LinkRequest, PositionIndependence,
        classify_linker_stderr, parse_wl_group,
    };

    pub const HOST: &str = if cfg!(target_os = "macos") {
        DARWIN
    } else {
        LINUX
    };

    /// Mach-O spells C symbol `name` with a leading underscore.
    pub fn object_symbol(name: &str) -> String {
        if cfg!(target_os = "macos") {
            format!("_{name}")
        } else {
            name.to_string()
        }
    }

    pub fn scratch(prefix: &str) -> tempfile::TempDir {
        tempfile::Builder::new().prefix(prefix).tempdir().unwrap()
    }

    pub fn write_object(dir: &Path, name: &str, module: &Module) -> PathBuf {
        let path = dir.join(name);
        fs::write(&path, compile(module, HOST)).unwrap();
        path
    }

    /// Compile a C or assembly source with the host C driver.
    pub fn cc_object(dir: &Path, name: &str, extension: &str, source: &str) -> PathBuf {
        cc_object_with(dir, name, extension, source, &[])
    }

    /// [`cc_object`] with extra driver `flags`.
    pub fn cc_object_with(
        dir: &Path,
        name: &str,
        extension: &str,
        source: &str,
        flags: &[&str],
    ) -> PathBuf {
        let source_path = dir.join(format!("{name}.{extension}"));
        let object_path = dir.join(format!("{name}.o"));
        fs::write(&source_path, source).unwrap();
        let mut command = Command::new("cc");
        command
            .arg("-c")
            .arg("-fno-stack-protector")
            .args(flags)
            .arg(&source_path)
            .arg("-o")
            .arg(&object_path);
        let compiled =
            process::command_output_with_timeout(&mut command, Duration::from_secs(60)).unwrap();
        assert!(!compiled.timed_out, "cc timed out");
        assert!(compiled.output.status.success(), "{:?}", compiled.output);
        object_path
    }

    pub struct Linked {
        pub success: bool,
        pub diagnostics: Vec<LinkDiagnostic>,
        pub stderr: String,
    }

    /// Run `request` through the host `cc` with a timeout and classify it.
    pub fn link(request: &LinkRequest) -> Linked {
        link_with(request, "cc")
    }

    /// [`link`] through the C driver `driver`.
    pub fn link_with(request: &LinkRequest, driver: &str) -> Linked {
        let mut command = request.command(driver).expect("request must be admissible");
        let linked =
            process::command_output_with_timeout(&mut command, Duration::from_secs(120)).unwrap();
        assert!(!linked.timed_out, "link timed out");
        let stderr = String::from_utf8_lossy(&linked.output.stderr).into_owned();
        Linked {
            success: linked.output.status.success(),
            diagnostics: if linked.output.status.success() {
                Vec::new()
            } else {
                classify_linker_stderr(&stderr)
            },
            stderr,
        }
    }

    pub fn executable(objects: Vec<PathBuf>, output: PathBuf) -> LinkRequest {
        LinkRequest::executable(TargetSpec::parse(HOST).unwrap(), objects, output)
    }

    /// Libraries the manifest's `libm` group needs beyond the driver default:
    /// the GNU C driver does not link libm by default (Darwin's libSystem
    /// already provides it).
    pub fn math_libs() -> Vec<String> {
        if cfg!(target_os = "linux") {
            vec!["m".to_string()]
        } else {
            Vec::new()
        }
    }

    pub fn with_wl(mut request: LinkRequest, group: &str) -> LinkRequest {
        request
            .linker_arg_groups
            .push(parse_wl_group(group, request.target).unwrap());
        request
    }

    pub fn run(path: &Path) -> Option<i32> {
        let result = process::run_executable_with_timeout(
            path,
            process::exec_timeout(Duration::from_secs(30)),
        )
        .unwrap();
        assert!(!result.timed_out, "{} timed out", path.display());
        result.output.status.code()
    }

    pub fn assert_link_fails_with(
        linked: &Linked,
        kind: LinkDiagnosticKind,
        subject: Option<&str>,
    ) {
        assert!(
            !linked.success,
            "link unexpectedly succeeded:\n{}",
            linked.stderr
        );
        assert!(
            linked
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.kind == kind
                    && subject
                        .is_none_or(|subject| diagnostic.subject.as_deref() == Some(subject))),
            "expected {kind:?} {subject:?}, got {:#?}\nstderr:\n{}",
            linked.diagnostics,
            linked.stderr
        );
    }

    /// `-nostdlib` removes every runtime library, so the link must report
    /// exactly the manifest's required symbols as undefined.
    #[test]
    fn nostdlib_link_reports_exactly_the_manifest_requirements() {
        let dir = scratch("tcg-runtime-nostdlib-");
        let object = write_object(dir.path(), "probe.o", &runtime_probe(HOST));
        let manifest = RuntimeDependencyManifest::from_object(&fs::read(&object).unwrap()).unwrap();
        // Name a defined entry point so the only undefined symbols are the
        // object's own references (ld64 otherwise also demands `_main`).
        let entry = format!("-e,{}", object_symbol("tcg_fmod"));
        let mut request = with_wl(executable(vec![object], dir.path().join("probe")), &entry);
        request.nostdlib = true;
        let linked = link(&request);
        assert!(!linked.success, "{}", linked.stderr);
        let undefined: BTreeSet<String> = linked
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.kind == LinkDiagnosticKind::UndefinedSymbol)
            .filter_map(|diagnostic| diagnostic.subject.clone())
            .collect();
        let required: BTreeSet<String> = manifest
            .required_symbols()
            .into_iter()
            .map(str::to_string)
            .collect();
        assert_eq!(undefined, required, "stderr:\n{}", linked.stderr);
    }

    /// The default link supplies every runtime provider the manifest names;
    /// the harness supplies the one external symbol and checks each result.
    #[test]
    fn default_link_resolves_every_runtime_dependency_and_runs() {
        let dir = scratch("tcg-runtime-default-");
        let object = write_object(dir.path(), "probe.o", &runtime_probe(HOST));
        let harness = cc_object(dir.path(), "harness", "c", RUNTIME_PROBE_HARNESS);
        let output = dir.path().join("probe");
        let mut request = executable(vec![object, harness], output.clone());
        request.libs = math_libs();
        let linked = link(&request);
        assert!(linked.success, "{}", linked.stderr);
        assert_eq!(run(&output), Some(0));
    }

    pub const CALLS_MISSING_MAIN: &str = "extern long tcg_calls_missing(void);\nint main(void) { return (int)tcg_calls_missing(); }\n";
    pub const DUPLICATE_MAIN: &str =
        "extern long tcg_duplicate(void);\nint main(void) { return (int)tcg_duplicate(); }\n";
    pub const READ_FAR_MAIN: &str = "extern long tcg_read_far(void);\nint main(void) { return tcg_read_far() == 42 ? 0 : 1; }\n";
    pub const CALL_FAR_MAIN: &str =
        "extern long tcg_call_far(void);\nint main(void) { return (int)tcg_call_far(); }\n";
    pub const PLAIN_MAIN: &str = "int main(void) { return 0; }\n";

    /// Undefined reference, duplicate strong definition across two trust-cg
    /// objects and a missing library each fail with their named diagnostic.
    #[test]
    fn link_failures_are_classified_by_name() {
        let dir = scratch("tcg-link-controls-");
        let dir = dir.path();

        let calls_missing = write_object(dir, "missing.o", &undefined_reference_module(HOST));
        let main = cc_object(dir, "missing_main", "c", CALLS_MISSING_MAIN);
        assert_link_fails_with(
            &link(&executable(vec![main, calls_missing], dir.join("missing"))),
            LinkDiagnosticKind::UndefinedSymbol,
            Some(&object_symbol("tcg_missing_symbol")),
        );

        let first = write_object(dir, "dup_a.o", &duplicate_definition_module(HOST, 1));
        let second = write_object(dir, "dup_b.o", &duplicate_definition_module(HOST, 2));
        let main = cc_object(dir, "dup_main", "c", DUPLICATE_MAIN);
        assert_link_fails_with(
            &link(&executable(
                vec![main.clone(), first.clone(), second],
                dir.join("dup"),
            )),
            LinkDiagnosticKind::DuplicateSymbol,
            Some(&object_symbol("tcg_duplicate")),
        );
        // Positive twin: one definition links and runs.
        let single = link(&executable(vec![main, first], dir.join("single")));
        assert!(single.success, "{}", single.stderr);
        assert_eq!(run(&dir.join("single")), Some(1));

        let plain = cc_object(dir, "plain_main", "c", PLAIN_MAIN);
        let mut missing_library = executable(vec![plain], dir.join("nolib"));
        missing_library.libs = vec!["tcg_no_such_library".into()];
        assert_link_fails_with(
            &link(&missing_library),
            LinkDiagnosticKind::LibraryNotFound,
            Some("tcg_no_such_library"),
        );
    }

    /// Shared-object output with a soname/install name and a run-time search
    /// path: the program runs only when the loader finds the library under
    /// that name through that path (the build copy is removed first).
    #[test]
    fn shared_library_links_under_its_soname_and_loads_through_rpath() {
        let dir = scratch("tcg-shared-");
        let build = dir.path().join("build");
        let runtime = dir.path().join("run");
        fs::create_dir_all(&build).unwrap();
        fs::create_dir_all(&runtime).unwrap();
        let object = write_object(&build, "probe.o", &library_probe(HOST));
        let harness = cc_object(&build, "harness", "c", LIBRARY_PROBE_HARNESS);
        let (built_name, soname, loaded_name) = if cfg!(target_os = "macos") {
            (
                "libtcgprobe.dylib",
                "@rpath/libtcgprobe.dylib",
                "libtcgprobe.dylib",
            )
        } else {
            ("libtcgprobe.so", "libtcgprobe.so.1", "libtcgprobe.so.1")
        };
        let library = build.join(built_name);
        let mut shared = executable(vec![object], library.clone());
        shared.kind = LinkOutputKind::SharedLibrary;
        shared.soname = Some(soname.into());
        shared.libs = math_libs();
        let linked = link(&shared);
        assert!(linked.success, "{}", linked.stderr);

        let program = dir.path().join("probe");
        let mut consumer = executable(vec![harness, library.clone()], program.clone());
        consumer.rpaths = vec![runtime.display().to_string()];
        let linked = link(&consumer);
        assert!(linked.success, "{}", linked.stderr);

        fs::copy(&library, runtime.join(loaded_name)).unwrap();
        fs::remove_file(&library).unwrap();
        assert_eq!(run(&program), Some(0));
    }

    #[test]
    fn position_independence_modes_link_and_run() {
        let dir = scratch("tcg-pie-");
        let object = write_object(dir.path(), "probe.o", &runtime_probe(HOST));
        let harness = cc_object(dir.path(), "harness", "c", RUNTIME_PROBE_HARNESS);
        let mut modes = vec![
            PositionIndependence::DriverDefault,
            PositionIndependence::Pie,
        ];
        if cfg!(target_os = "linux") {
            modes.push(PositionIndependence::NoPie);
        }
        for (index, mode) in modes.into_iter().enumerate() {
            let output = dir.path().join(format!("probe{index}"));
            let mut request = executable(vec![object.clone(), harness.clone()], output.clone());
            request.position_independence = mode;
            request.libs = math_libs();
            let linked = link(&request);
            assert!(linked.success, "{mode:?}: {}", linked.stderr);
            assert_eq!(run(&output), Some(0), "{mode:?}");
        }
    }
}

#[cfg(any(
    all(target_os = "macos", target_arch = "aarch64"),
    all(target_os = "linux", target_arch = "aarch64", target_env = "gnu")
))]
mod lo12_native {
    use super::native::*;
    use super::*;

    /// The lo12 probe links and runs: on Linux through the fused LDST forms,
    /// on Darwin (no fusion) as the unfused baseline of the same program.
    #[test]
    fn lo12_probe_runs_with_the_expected_global_values() {
        let dir = scratch("tcg-lo12-");
        let object = dir.path().join("lo12.o");
        std::fs::write(&object, compile_at(&lo12_probe(HOST), HOST, OptLevel::O2)).unwrap();
        let harness = cc_object(dir.path(), "lo12_main", "c", LO12_PROBE_HARNESS);
        let output = dir.path().join("lo12");
        let linked = link(&executable(vec![harness, object], output.clone()));
        assert!(linked.success, "{}", linked.stderr);
        assert_eq!(run(&output), Some(0));
    }
}

// ---------------------------------------------------------------------------
// macOS arm64 native controls
// ---------------------------------------------------------------------------

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
mod darwin_native {
    use super::native::*;
    use super::*;
    use trust_cg_codegen::link_driver::LinkDiagnosticKind;

    /// ld64 refuses every text relocation on arm64.
    const TEXTREL_ASM: &str = "    .section __TEXT,__const\n    .globl _tcg_textrel_table\n    .p2align 3\n_tcg_textrel_table:\n    .quad _puts\n";

    #[test]
    fn text_relocation_is_classified_by_name() {
        let dir = scratch("tcg-darwin-textrel-");
        let dir = dir.path();
        let table = cc_object(dir, "textrel", "s", TEXTREL_ASM);
        let main = cc_object(dir, "plain_main", "c", PLAIN_MAIN);
        assert_link_fails_with(
            &link(&executable(vec![main, table], dir.join("textrel"))),
            LinkDiagnosticKind::TextRelocation,
            Some("_puts"),
        );
    }

    /// Synthetic distance: `__DATA` is placed 8 GiB above `__TEXT`, so the
    /// trust-cg ADRP to its own `_tcg_far_word` overflows the +-4 GiB window;
    /// ld64 names the fixup and the target. The unmoved twin runs.
    #[test]
    fn adrp_beyond_4_gib_is_a_classified_linker_overflow() {
        let dir = scratch("tcg-darwin-adrp-");
        let dir = dir.path();
        let object = write_object(dir, "far_word.o", &far_word_module(HOST));
        let main = cc_object(dir, "far_main", "c", READ_FAR_MAIN);
        let near = executable(vec![main.clone(), object.clone()], dir.join("near"));
        let linked = link(&near);
        assert!(linked.success, "{}", linked.stderr);
        assert_eq!(run(&dir.join("near")), Some(0));

        let far = with_wl(
            executable(vec![main, object], dir.join("far")),
            "-segaddr,__DATA,0x300000000",
        );
        let linked = link(&far);
        assert_link_fails_with(
            &linked,
            LinkDiagnosticKind::RelocationOutOfRange,
            Some("_tcg_far_word"),
        );
        assert!(
            linked
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.relocation.as_deref() == Some("arm64_adrp_lo12")),
            "{:#?}",
            linked.diagnostics
        );
    }

    /// Synthetic distance: the callee lives in its own segment 512 MiB above
    /// `__TEXT`; ld64 does not island across segments, so the trust-cg BL
    /// overflows the +-128 MiB CALL26 window. The unmoved twin runs.
    #[test]
    fn call26_beyond_128_mib_is_a_classified_linker_overflow() {
        const FAR_ASM: &str = "    .section __FARTEXT,__text,regular,pure_instructions\n    .globl _tcg_far_fn\n    .p2align 2\n_tcg_far_fn:\n    mov x0, #42\n    ret\n";
        const NEAR_ASM: &str = "    .text\n    .globl _tcg_far_fn\n    .p2align 2\n_tcg_far_fn:\n    mov x0, #42\n    ret\n";
        let dir = scratch("tcg-darwin-call26-");
        let dir = dir.path();
        let object = write_object(dir, "far_call.o", &far_call_module(HOST));
        let main = cc_object(dir, "call_main", "c", CALL_FAR_MAIN);
        let near_callee = cc_object(dir, "near_fn", "s", NEAR_ASM);
        let near = executable(
            vec![main.clone(), object.clone(), near_callee],
            dir.join("near"),
        );
        let linked = link(&near);
        assert!(linked.success, "{}", linked.stderr);
        assert_eq!(run(&dir.join("near")), Some(42));

        let far_callee = cc_object(dir, "far_fn", "s", FAR_ASM);
        let far = with_wl(
            executable(vec![main, object, far_callee], dir.join("far")),
            "-segaddr,__FARTEXT,0x120000000,-no_compact_unwind",
        );
        let linked = link(&far);
        assert_link_fails_with(
            &linked,
            LinkDiagnosticKind::RelocationOutOfRange,
            Some("_tcg_far_fn"),
        );
        assert!(
            linked
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.relocation.as_deref() == Some("arm64_b26")),
            "{:#?}",
            linked.diagnostics
        );
    }
}

// ---------------------------------------------------------------------------
// Linux AArch64 GNU native controls
// ---------------------------------------------------------------------------

#[cfg(all(target_os = "linux", target_arch = "aarch64", target_env = "gnu"))]
mod linux_native {
    use super::native::*;
    use super::*;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use trust_cg_codegen::link_driver::{
        LinkDiagnostic, LinkDiagnosticKind, LinkOutputKind, LinkRequest, PositionIndependence,
    };

    /// An absolute pointer to a libc function in `.rodata`: a PIE needs a
    /// dynamic relocation in a read-only segment, refused under `-z text`.
    const TEXTREL_ASM: &str = "    .section .rodata\n    .globl tcg_textrel_table\n    .p2align 3\ntcg_textrel_table:\n    .quad puts\n";

    const GUARD_CALLER: &str = r#"
#include <unistd.h>
extern long tcg_guard_target(void);
__attribute__((noreturn)) void __stack_chk_fail(void) { _exit(87); }
int main(void) { return tcg_guard_target() == 42 ? 0 : 1; }
"#;

    /// The ELF canary reads glibc's `__stack_chk_guard` through the GOT and
    /// calls `__stack_chk_fail` on mismatch: the intact frame returns, the
    /// corrupted one takes the failure path (overridden here to exit 87).
    #[test]
    fn stack_guard_returns_normally_and_detects_corruption() {
        let dir = scratch("tcg-linux-guard-");
        let dir = dir.path();
        let caller = cc_object(dir, "guard_caller", "c", GUARD_CALLER);
        for corrupt in [false, true] {
            let body = dir.join(if corrupt { "corrupt.o" } else { "intact.o" });
            fs::write(&body, elf_guard_object(corrupt)).unwrap();
            let output = dir.join(if corrupt { "corrupt" } else { "intact" });
            let linked = link(&executable(vec![caller.clone(), body], output.clone()));
            assert!(linked.success, "{}", linked.stderr);
            assert_eq!(run(&output), Some(if corrupt { 87 } else { 0 }));
        }
    }

    /// A static link resolves every manifest provider from the static C
    /// library and libgcc (including glibc's static `__stack_chk_guard`).
    #[test]
    fn static_link_resolves_every_runtime_dependency_and_runs() {
        let dir = scratch("tcg-linux-static-");
        let object = write_object(dir.path(), "probe.o", &runtime_probe(HOST));
        let harness = cc_object(dir.path(), "harness", "c", RUNTIME_PROBE_HARNESS);
        let output = dir.path().join("probe");
        let mut request = executable(vec![object, harness], output.clone());
        request.static_link = true;
        request.libs = vec!["m".into()];
        let linked = link(&request);
        assert!(linked.success, "{}", linked.stderr);
        assert_eq!(run(&output), Some(0));
    }

    /// The base symbol version GNU ld names for `puts` from glibc on AArch64
    /// (`GLIBC_2.17`, the first glibc release with an AArch64 port).
    const PUTS_SUBJECT: &str = "puts@@GLIBC_2.17";

    /// Under `-z text` GNU ld refuses the text relocation that the `.rodata`
    /// table's absolute `puts` address needs in a PIE, and names the symbol
    /// (`relocation against `puts@@GLIBC_2.17' in read-only section
    /// `.rodata'`) before it reports the read-only segment. The link
    /// driver's `run_link` reports the same two diagnostics and writes
    /// nothing. Twin: without `-z text` the same PIE links (directly and
    /// through `run_link`) with the relocation in its image, which
    /// `readelf -d` shows as a `TEXTREL` entry and `TEXTREL` in `FLAGS`,
    /// and it runs (0).
    #[test]
    fn text_relocation_under_z_text_is_classified_by_name() {
        use trust_cg_codegen::link_driver::{LinkError, run_link};
        let dir = scratch("tcg-linux-textrel-");
        let dir = dir.path();
        let table = cc_object(dir, "textrel", "s", TEXTREL_ASM);
        let main = cc_object(dir, "plain_main", "c", PLAIN_MAIN);
        let mut request = with_wl(
            executable(vec![main.clone(), table.clone()], dir.join("textrel")),
            "-z,text",
        );
        request.position_independence = PositionIndependence::Pie;
        assert_link_fails_with(&link(&request), LinkDiagnosticKind::TextRelocation, None);
        let linked = link(&request);
        assert_link_fails_with(
            &linked,
            LinkDiagnosticKind::TextRelocation,
            Some(PUTS_SUBJECT),
        );
        let named = |diagnostics: &[LinkDiagnostic]| {
            diagnostics
                .iter()
                .map(|diagnostic| (diagnostic.kind, diagnostic.subject.clone()))
                .collect::<Vec<_>>()
        };
        let expected = [
            (
                LinkDiagnosticKind::TextRelocation,
                Some(PUTS_SUBJECT.to_string()),
            ),
            (LinkDiagnosticKind::TextRelocation, None),
        ];
        assert_eq!(named(&linked.diagnostics), expected, "{}", linked.stderr);
        match run_link(&request, "cc") {
            Err(LinkError::Failed(failure)) => {
                assert_eq!(named(&failure.diagnostics), expected, "{}", failure.stderr);
            }
            other => panic!("expected the linker's TEXTREL refusal, got {other:?}"),
        }
        assert!(!request.output.exists());

        // Twin: without `-z text` the text relocation is linked in.
        for (name, driver) in [("textrel_direct", false), ("textrel_driver", true)] {
            let mut twin = executable(vec![main.clone(), table.clone()], dir.join(name));
            twin.position_independence = PositionIndependence::Pie;
            if driver {
                run_link(&twin, "cc").unwrap_or_else(|error| panic!("{name}: {error}"));
            } else {
                let linked = link(&twin);
                assert!(linked.success, "{name}: {}", linked.stderr);
            }
            let dynamic = std::process::Command::new("readelf")
                .args(["-d", "-W"])
                .arg(&twin.output)
                .output()
                .unwrap();
            assert!(dynamic.status.success(), "{dynamic:?}");
            let dynamic = String::from_utf8_lossy(&dynamic.stdout);
            assert!(
                dynamic.lines().any(|line| line.contains("(TEXTREL)")),
                "{name}: {dynamic}"
            );
            assert!(
                dynamic.lines().any(|line| line.contains("(FLAGS)")
                    && line.split_whitespace().any(|flag| flag == "TEXTREL")),
                "{name}: {dynamic}"
            );
            assert_eq!(run(&twin.output), Some(0), "{name}");
        }
    }

    /// trust-cg's default objects address their own default-visibility data
    /// with a direct ADRP; a shared object cannot preempt it, so the linker
    /// refuses the object with a named non-PIC diagnostic.
    #[test]
    fn preemptible_direct_data_reference_in_a_shared_object_is_classified() {
        let dir = scratch("tcg-linux-nonpic-");
        let dir = dir.path();
        let object = write_object(dir, "far_word.o", &far_word_module(HOST));
        let mut shared = executable(vec![object], dir.join("libtcgword.so"));
        shared.kind = LinkOutputKind::SharedLibrary;
        assert_link_fails_with(
            &link(&shared),
            LinkDiagnosticKind::NonPicRelocation,
            Some("tcg_far_word"),
        );
    }

    /// What [`window_refusal`] saw: the linker refused the link itself, or
    /// the link driver refused the image the linker wrote.
    enum Refusal {
        Linker(Vec<LinkDiagnostic>),
        Driver(Vec<LinkDiagnostic>),
    }

    /// Link `request` through the link driver (`run_link`) with the C driver
    /// `driver` of `linker` and require a refusal: the linker's own failure,
    /// classified `relocation-out-of-range`, for `relocation` at the
    /// trust-cg access `sites` names (its target symbol, its function, its
    /// object): a classified diagnostic of `relocation` whose subject (the
    /// target GNU ld and LLD name) or function (the one gold or LLD names
    /// the place in) is one of `sites`, or whose line names one. A diagnostic
    /// of the kind at another place (the C runtime's own page references,
    /// which LLD and gold also refuse) does not count. Or the driver's
    /// refusal of the staged image by a `[TCG-LINK-*]` name, which removes
    /// the image. Nothing is installed either way.
    fn window_refusal(
        request: &LinkRequest,
        driver: &str,
        linker: &str,
        relocation: &str,
        sites: &[&str],
    ) -> Refusal {
        use trust_cg_codegen::link_driver::{LinkError, run_link};
        let what = format!("{linker} {}", request.output.display());
        let refusal = match run_link(request, driver) {
            Err(LinkError::Failed(failure)) => {
                let classified = |diagnostic: &LinkDiagnostic| {
                    diagnostic.kind == LinkDiagnosticKind::RelocationOutOfRange
                };
                let named = failure.diagnostics.iter().any(|diagnostic| {
                    classified(diagnostic)
                        && diagnostic.relocation.as_deref() == Some(relocation)
                        && (diagnostic
                            .subject
                            .as_deref()
                            .is_some_and(|subject| sites.contains(&subject))
                            || diagnostic
                                .function
                                .as_deref()
                                .is_some_and(|function| sites.contains(&function))
                            || sites.iter().any(|site| diagnostic.line.contains(site)))
                });
                assert!(
                    failure.diagnostics.iter().any(classified) && named,
                    "{what}: {:#?}\n{}",
                    failure.diagnostics,
                    failure.stderr
                );
                eprintln!(
                    "{what}: the linker refused it: {}",
                    failure.diagnostics[0].line
                );
                Refusal::Linker(failure.diagnostics)
            }
            Err(LinkError::OutputRefused {
                removed,
                diagnostics,
                ..
            }) => {
                assert!(removed, "{what}: the refused image must be removed");
                assert!(
                    !diagnostics.is_empty()
                        && diagnostics
                            .iter()
                            .all(|diagnostic| diagnostic.line.starts_with("[TCG-LINK-")),
                    "{what}: {diagnostics:#?}"
                );
                eprintln!("{what}: the driver refused it: {}", diagnostics[0].line);
                Refusal::Driver(diagnostics)
            }
            other => panic!("{what}: must not link: {other:?}"),
        };
        assert!(!request.output.exists(), "{what}");
        refusal
    }

    /// `request` links through the link driver with `driver` and its
    /// program exits with `status`.
    fn runs_through(request: &LinkRequest, driver: &str, linker: &str, status: i32) {
        trust_cg_codegen::link_driver::run_link(request, driver)
            .unwrap_or_else(|error| panic!("{linker} {}: {error}", request.output.display()));
        assert_eq!(
            run(&request.output),
            Some(status),
            "{linker} {}",
            request.output.display()
        );
    }

    /// Synthetic distance: the trust-cg word `tcg_far_word`, in its own
    /// read-only section `.tcg_far_data`, is placed 8 GiB above `.text`
    /// (pinned at 8 MiB: LLD otherwise lays `.text` out after the placed
    /// section), so the trust-cg ADRP to it overflows the +-4 GiB window.
    /// Through GNU ld 2.42, LLD 22.1.6 and gold 2.42 the link driver's link
    /// fails with the linker's `relocation-out-of-range` refusal of
    /// `R_AARCH64_ADR_PREL_PG_HI21` at trust-cg's own access: a typed
    /// diagnostic whose line names `far_word.o`, with the subject
    /// `tcg_far_word` (GNU ld, LLD) and the function `tcg_read_far` (gold,
    /// which names no target, and LLD). LLD and gold also refuse the C runtime's own page
    /// references there, each kept as its own diagnostic. Nothing is
    /// installed. The twin at 1 GiB links and runs through each.
    /// Without LLD or gold their legs print `SKIP:`.
    #[test]
    fn adrp_beyond_4_gib_is_a_classified_linker_overflow() {
        let dir = scratch("tcg-linux-adrp-");
        let dir = dir.path();
        let object = write_object(
            dir,
            "far_word.o",
            &far_word_module_in(HOST, Some(".tcg_far_data")),
        );
        let main = cc_object(dir, "far_main", "c", READ_FAR_MAIN);
        let placed = |name: &str, address: u64| {
            let mut request = with_wl(
                executable(vec![main.clone(), object.clone()], dir.join(name)),
                &format!(
                    "--section-start=.text=0x800000,--section-start=.tcg_far_data={address:#x}"
                ),
            );
            request.position_independence = PositionIndependence::NoPie;
            request
        };
        for (linker, driver) in linker_drivers(dir) {
            runs_through(
                &placed(&format!("near_{linker}"), 0x4000_0000),
                &driver,
                linker,
                0,
            );
            let refusal = window_refusal(
                &placed(&format!("far_{linker}"), 0x2_0000_0000),
                &driver,
                linker,
                "R_AARCH64_ADR_PREL_PG_HI21",
                &["tcg_far_word", "tcg_read_far", "far_word.o"],
            );
            let Refusal::Linker(diagnostics) = refusal else {
                panic!("{linker}: every linker refuses a direct ADRP page delta out of range");
            };
            // GNU ld and LLD name the target, gold and LLD the trust-cg
            // function; the diagnostic is typed and its line names trust-cg's
            // object.
            let (subject, function, located) = match linker {
                "gold" => (
                    None,
                    Some("tcg_read_far"),
                    "far_word.o:function tcg_read_far:(.text+0x0)",
                ),
                "lld" => (
                    Some("tcg_far_word"),
                    Some("tcg_read_far"),
                    "far_word.o:(function tcg_read_far: .text+0x0)",
                ),
                _ => (Some("tcg_far_word"), None, "far_word.o"),
            };
            assert!(
                diagnostics.iter().any(|diagnostic| {
                    diagnostic.kind == LinkDiagnosticKind::RelocationOutOfRange
                        && diagnostic.relocation.as_deref() == Some("R_AARCH64_ADR_PREL_PG_HI21")
                        && diagnostic.subject.as_deref() == subject
                        && diagnostic.function.as_deref() == function
                        && diagnostic.line.contains(located)
                }),
                "{linker}: {diagnostics:#?}"
            );
        }
    }

    /// A tail call across sections more than 128 MiB apart: the trust-cg
    /// `tcg_tail_far` branches to `tcg_far_fn` with a `B`
    /// (`R_AARCH64_JUMP26`, [`tail_call_object`]), and the callee's section
    /// starts at 512 MiB with `.text` at 8 MiB. GNU ld 2.42, LLD 22.1.6 and
    /// gold 2.42 each reach it through a range-extension veneer (which may
    /// clobber IP0/IP1, as the psABI allows for `JUMP26`), so the program
    /// returns the callee's 42 and no `B` in the image branches to
    /// `tcg_far_fn` itself; a linker that refused instead would have to be
    /// classified (`relocation-out-of-range`). Without LLD or gold their
    /// legs print `SKIP:`.
    #[test]
    fn jump26_beyond_128_mib_is_reached_through_a_linker_veneer() {
        const FAR_ASM: &str = "    .section .tcg_far_text,\"ax\",%progbits\n    .globl tcg_far_fn\n    .type tcg_far_fn,%function\n    .p2align 2\ntcg_far_fn:\n    mov x0, #42\n    ret\n";
        const TAIL_MAIN: &str =
            "extern long tcg_tail_far(void);\nint main(void) { return (int)tcg_tail_far(); }\n";
        let dir = scratch("tcg-linux-jump26-");
        let dir = dir.path();
        let (level, bytes) = tail_call_object(HOST);
        eprintln!("tcg_tail_far tail-calls through JUMP26 at {level:?}");
        let object = dir.join("tail.o");
        fs::write(&object, bytes).unwrap();
        let main = cc_object(dir, "tail_main", "c", TAIL_MAIN);
        let callee = cc_object(dir, "far_fn", "s", FAR_ASM);
        for (linker, driver) in linker_drivers(dir) {
            let output = dir.join(format!("far_{linker}"));
            let mut far = with_wl(
                executable(
                    vec![main.clone(), object.clone(), callee.clone()],
                    output.clone(),
                ),
                "--section-start=.text=0x800000,--section-start=.tcg_far_text=0x20000000",
            );
            far.position_independence = PositionIndependence::NoPie;
            match trust_cg_codegen::link_driver::run_link(&far, &driver) {
                Ok(_) => {}
                Err(trust_cg_codegen::link_driver::LinkError::Failed(failure)) => {
                    assert!(
                        failure.diagnostics.iter().any(|diagnostic| diagnostic.kind
                            == LinkDiagnosticKind::RelocationOutOfRange
                            && diagnostic.relocation.as_deref() == Some("R_AARCH64_JUMP26")),
                        "{linker}: {:#?}",
                        failure.diagnostics
                    );
                    assert!(!output.exists());
                    continue;
                }
                Err(other) => panic!("{linker}: {other}"),
            }
            assert_eq!(run(&output), Some(42), "{linker}");
            let disassembly = Command::new("objdump")
                .args(["-d", "--no-show-raw-insn"])
                .arg(&output)
                .output()
                .unwrap();
            let disassembly = String::from_utf8_lossy(&disassembly.stdout).into_owned();
            let address = |label: &str| {
                disassembly
                    .lines()
                    .find(|line| line.ends_with(&format!("<{label}>:")))
                    .and_then(|line| u64::from_str_radix(line.split(' ').next()?, 16).ok())
                    .unwrap_or_else(|| panic!("{linker}: no {label} in {disassembly}"))
            };
            let distance = address("tcg_far_fn").abs_diff(address("tcg_tail_far"));
            assert!(distance > 128 << 20, "{linker}: {distance:#x}");
            // The tail branch reaches a veneer, not the callee.
            let tail = &disassembly[disassembly.find("<tcg_tail_far>:").unwrap()..];
            let tail = &tail[..tail.find("\n\n").unwrap_or(tail.len())];
            assert!(
                tail.lines().any(|line| line.contains("\tb\t")),
                "{linker}: {tail}"
            );
            assert!(
                !disassembly
                    .lines()
                    .any(|line| line.contains("\tb\t") && line.ends_with("<tcg_far_fn>")),
                "{linker}: {disassembly}"
            );
        }
    }

    /// `cc` drivers that link through GNU ld (`cc`), LLD and gold, with
    /// `SKIP:` for a missing LLD or gold unless `TCG_REQUIRE_LLD` or
    /// `TCG_REQUIRE_GOLD` is set. LLD is found in `TCG_LLD_DIR`, the home
    /// directory's `.local/bin` or on `PATH`, gold as `ld.gold` on `PATH` or
    /// in `/usr/bin`. Each shim is written from a child shell, so no
    /// writable descriptor to it stays in this process.
    fn linker_drivers(dir: &Path) -> Vec<(&'static str, String)> {
        let shim = |name: &str, flags: String| -> String {
            let path = dir.join(name);
            let status = Command::new("/bin/sh")
                .arg("-c")
                .arg("printf '%s\\n' \"$2\" > \"$1\" && chmod 755 \"$1\"")
                .arg("sh")
                .arg(&path)
                .arg(format!("#!/bin/sh\nexec cc {flags} \"$@\""))
                .status()
                .unwrap();
            assert!(status.success());
            path.display().to_string()
        };
        let on_path = |tool: &str| -> Option<PathBuf> {
            std::env::var_os("PATH").and_then(|paths| {
                std::env::split_paths(&paths).find(|dir| dir.join(tool).is_file())
            })
        };
        let mut drivers = vec![("gnu", "cc".to_string())];
        match std::env::var_os("TCG_LLD_DIR")
            .map(PathBuf::from)
            .or_else(|| std::env::var_os("HOME").map(|home| Path::new(&home).join(".local/bin")))
            .filter(|dir| dir.join("ld.lld").is_file())
            .or_else(|| on_path("ld.lld"))
        {
            Some(lld) => drivers.push((
                "lld",
                shim("lld-cc.sh", format!("-fuse-ld=lld -B'{}/'", lld.display())),
            )),
            None => {
                assert!(std::env::var_os("TCG_REQUIRE_LLD").is_none(), "no ld.lld");
                eprintln!(
                    "SKIP: no ld.lld (TCG_LLD_DIR, ~/.local/bin, PATH); the LLD leg did not run"
                );
            }
        }
        match on_path("ld.gold")
            .or_else(|| Some(PathBuf::from("/usr/bin")).filter(|dir| dir.join("ld.gold").is_file()))
        {
            Some(_) => drivers.push(("gold", shim("gold-cc.sh", "-fuse-ld=gold".to_string()))),
            None => {
                assert!(std::env::var_os("TCG_REQUIRE_GOLD").is_none(), "no ld.gold");
                eprintln!("SKIP: no ld.gold (PATH, /usr/bin); the gold leg did not run");
            }
        }
        drivers
    }

    /// Synthetic distance: the callee's section starts at 512 MiB and
    /// `.text` at 8 MiB, more than 128 MiB from the trust-cg caller. GNU ld
    /// 2.42, LLD 22.1.6 and gold 2.42 each reach it through a
    /// range-extension veneer (which may clobber IP0/IP1, as the psABI
    /// allows for CALL26), so the trust-cg BL still returns the callee's 42:
    /// no BL in the image branches to `tcg_far_fn` itself. Without LLD or
    /// gold their legs print `SKIP:`.
    #[test]
    fn call26_beyond_128_mib_is_reached_through_a_linker_veneer() {
        const FAR_ASM: &str = "    .section .tcg_far_text,\"ax\",%progbits\n    .globl tcg_far_fn\n    .type tcg_far_fn,%function\n    .p2align 2\ntcg_far_fn:\n    mov x0, #42\n    ret\n";
        let dir = scratch("tcg-linux-call26-");
        let dir = dir.path();
        let object = write_object(dir, "far_call.o", &far_call_module(HOST));
        let main = cc_object(dir, "call_main", "c", CALL_FAR_MAIN);
        let callee = cc_object(dir, "far_fn", "s", FAR_ASM);
        for (name, driver) in linker_drivers(dir) {
            let output = dir.join(format!("far_{name}"));
            // `.text` pinned too: LLD otherwise places it after the callee.
            let mut far = with_wl(
                executable(
                    vec![main.clone(), object.clone(), callee.clone()],
                    output.clone(),
                ),
                "--section-start=.text=0x800000,--section-start=.tcg_far_text=0x20000000",
            );
            far.position_independence = PositionIndependence::NoPie;
            let linked = link_with(&far, &driver);
            assert!(linked.success, "{name}: {}", linked.stderr);
            assert_eq!(run(&output), Some(42), "{name}");
            // Every BL in the image: none reaches the callee directly.
            let disassembly = Command::new("objdump")
                .args(["-d", "--no-show-raw-insn"])
                .arg(&output)
                .output()
                .unwrap();
            let disassembly = String::from_utf8_lossy(&disassembly.stdout).into_owned();
            let address = |label: &str| {
                disassembly
                    .lines()
                    .find(|line| line.ends_with(&format!("<{label}>:")))
                    .and_then(|line| u64::from_str_radix(line.split(' ').next()?, 16).ok())
                    .unwrap_or_else(|| panic!("{name}: no {label} in {disassembly}"))
            };
            let distance = address("tcg_far_fn").abs_diff(address("tcg_call_far"));
            assert!(distance > 128 << 20, "{name}: {distance:#x}");
            assert!(
                !disassembly
                    .lines()
                    .any(|line| line.contains("\tbl\t") && line.ends_with("<tcg_far_fn>")),
                "{name}: {disassembly}"
            );
        }
    }

    const LO12_Q_HARNESS: &str = r#"
#include <stdint.h>
extern uint32_t tcg_lo12_q[4];
extern uint32_t tcg_lo12_q_out[4];
void tcg_lo12_q_double(void);
int main(void) {
    tcg_lo12_q_double();
    for (int lane = 0; lane < 4; lane++)
        if (tcg_lo12_q_out[lane] != 2u * (uint32_t)(lane + 1)) return 31 + lane;
    tcg_lo12_q[0] = 0x40000000u;
    tcg_lo12_q[3] = 7;
    tcg_lo12_q_double();
    if (tcg_lo12_q_out[0] != 0x80000000u || tcg_lo12_q_out[1] != 4 ||
        tcg_lo12_q_out[2] != 6 || tcg_lo12_q_out[3] != 14) return 35;
    return 0;
}
"#;

    /// The fused Q-register `LDR/STR` (`R_AARCH64_LDST128_ABS_LO12_NC`)
    /// reads and writes all four lanes of its globals in a linked program.
    #[test]
    fn q_register_fused_lo12_accesses_run_with_the_expected_lanes() {
        let dir = scratch("tcg-linux-lo12-q-");
        let object = dir.path().join("lo12_q.o");
        let bytes = compile_at(&lo12_q_probe(HOST), HOST, OptLevel::O2);
        for symbol in ["tcg_lo12_q", "tcg_lo12_q_out"] {
            assert_eq!(
                lo12_kinds_against(&bytes, symbol),
                [trust_cg_codegen::elf::constants::R_AARCH64_LDST128_ABS_LO12_NC],
                "{symbol}: the linked object uses the fused Q-register form"
            );
        }
        fs::write(&object, bytes).unwrap();
        let harness = cc_object(dir.path(), "lo12_q_main", "c", LO12_Q_HARNESS);
        let output = dir.path().join("lo12_q");
        let linked = link(&executable(vec![harness, object], output.clone()));
        assert!(linked.success, "{}", linked.stderr);
        assert_eq!(run(&output), Some(0));
    }

    const LOCAL_EXEC_MAIN: &str = "extern long tcg_le_edge_bump(void);\nint main(void) { return tcg_le_edge_bump() == 42 && tcg_le_edge_bump() == 84 ? 0 : 1; }\n";
    /// A 16 MiB thread-local from another object.
    const TLS_PAD_ASM: &str = "    .section .tbss,\"awT\",@nobits\n    .globl tcg_c_tls_pad\n    .p2align 4\ntcg_c_tls_pad:\n    .zero 16777216\n";

    /// `TLSLE_ADD_TPREL_HI12` at its window. trust-cg admits a thread-local
    /// whose `TPREL` it bounds at `2^24 - 16`, and the linked program (whose
    /// only TLS is that object's) reads and writes it. A small trust-cg
    /// thread-local placed behind another object's 16 MiB thread-local
    /// overflows only at link time. Through GNU ld 2.42, LLD 22.1.6 and gold
    /// 2.42 the link driver's link of that order fails with the linker's
    /// `relocation-out-of-range` refusal of `R_AARCH64_TLSLE_ADD_TPREL_HI12`
    /// (GNU ld and LLD name `tcg_le_edge`) and installs nothing, while the
    /// edge program and the same two objects in the other order link and
    /// run through each. Without LLD or gold their legs print `SKIP:`.
    #[test]
    fn local_exec_tls_at_the_16_mib_edge_runs_and_past_it_is_classified() {
        let dir = scratch("tcg-linux-tlsle-");
        let dir = dir.path();
        let main = cc_object(dir, "le_main", "c", LOCAL_EXEC_MAIN);
        let edge = write_object(
            dir,
            "le_edge.o",
            &local_exec_tls_module(HOST, TLSLE_WINDOW - 32),
        );
        let small = write_object(dir, "le_small.o", &local_exec_tls_module(HOST, 0));
        let pad = cc_object(dir, "tls_pad", "s", TLS_PAD_ASM);
        for (linker, driver) in linker_drivers(dir) {
            let request = |name: &str, objects: &[&PathBuf]| {
                executable(
                    objects.iter().map(|object| (*object).clone()).collect(),
                    dir.join(format!("{name}_{linker}")),
                )
            };
            runs_through(&request("edge", &[&main, &edge]), &driver, linker, 0);
            let refusal = window_refusal(
                &request("behind", &[&main, &pad, &small]),
                &driver,
                linker,
                "R_AARCH64_TLSLE_ADD_TPREL_HI12",
                &["tcg_le_edge", "tcg_le_edge_bump"],
            );
            let Refusal::Linker(diagnostics) = refusal else {
                panic!("{linker}: every linker refuses a local-exec TPREL of 2^24");
            };
            if linker != "gold" {
                assert!(
                    diagnostics
                        .iter()
                        .any(|diagnostic| diagnostic.subject.as_deref() == Some("tcg_le_edge")),
                    "{linker}: {diagnostics:#?}"
                );
            }
            runs_through(
                &request("ahead", &[&main, &small, &pad]),
                &driver,
                linker,
                0,
            );
        }
    }

    const DEBUG_PROBE_MAIN: &str = "extern long tcg_debug_probe(void);\nint main(void) { return tcg_debug_probe() == 42 ? 0 : 1; }\n";

    /// The address the section header table of `image` gives `.debug_str`.
    fn debug_str_address(image: &Path) -> u64 {
        let sections = Command::new("readelf")
            .args(["-SW"])
            .arg(image)
            .output()
            .unwrap();
        let sections = String::from_utf8_lossy(&sections.stdout).into_owned();
        sections
            .lines()
            .find_map(|line| {
                let mut words = line
                    .split_whitespace()
                    .skip_while(|word| *word != ".debug_str");
                words.next()?;
                words.next()?;
                u64::from_str_radix(words.next()?, 16).ok()
            })
            .unwrap_or_else(|| panic!("no .debug_str in {sections}"))
    }

    /// Synthetic distance for `R_AARCH64_ABS32`: the trust-cg `-g` object's
    /// DWARF section offsets are `S + A` against `.debug_str`, so placing
    /// the output `.debug_str` at 4 GiB overflows them. Through the link
    /// driver GNU ld 2.42 refuses that link, classified
    /// `relocation-out-of-range` for `R_AARCH64_ABS32` against `.debug_str`,
    /// and installs nothing. LLD 22.1.6 and gold 2.42 keep a non-allocated
    /// `.debug_str` at address 0 whatever `--section-start` asks, so this
    /// placement cannot move it: their images are installed with
    /// `.debug_str` at 0 (every offset within the section's size) and run.
    /// A linker script that puts `.debug_str` into an allocated section
    /// past 4 GiB does move it, and all three refuse that
    /// ([`abs32_debug_offset_placed_past_4_gib_by_a_script_is_refused_by_each_linker`]).
    /// The twin placed below 2 GiB links and runs through each. Without LLD
    /// or gold their legs print `SKIP:`.
    #[test]
    fn abs32_debug_offset_beyond_4_gib_is_a_classified_linker_overflow() {
        let dir = scratch("tcg-linux-abs32-");
        let dir = dir.path();
        let object = dir.join("debug_probe.o");
        fs::write(
            &object,
            try_compile_with(&debug_probe_module(HOST), HOST, |config| {
                config.emit_debug = true;
            })
            .unwrap(),
        )
        .unwrap();
        let main = cc_object(dir, "debug_main", "c", DEBUG_PROBE_MAIN);
        for (linker, driver) in linker_drivers(dir) {
            let placed = |name: &str, address: u64| {
                with_wl(
                    executable(
                        vec![main.clone(), object.clone()],
                        dir.join(format!("{name}_{linker}")),
                    ),
                    &format!("--section-start=.debug_str={address:#x}"),
                )
            };
            let near = placed("near", 0x7fff_0000);
            runs_through(&near, &driver, linker, 0);
            let far = placed("far", 0x1_0000_0000);
            if linker == "gnu" {
                let Refusal::Linker(diagnostics) =
                    window_refusal(&far, &driver, linker, "R_AARCH64_ABS32", &[".debug_str"])
                else {
                    panic!("GNU ld refuses the ABS32 offsets itself");
                };
                assert!(
                    diagnostics.iter().all(|diagnostic| diagnostic.kind
                        == LinkDiagnosticKind::RelocationOutOfRange
                        && diagnostic.relocation.as_deref() == Some("R_AARCH64_ABS32")
                        && diagnostic.subject.as_deref() == Some(".debug_str")),
                    "{diagnostics:#?}"
                );
                continue;
            }
            runs_through(&far, &driver, linker, 0);
            for request in [&near, &far] {
                assert_eq!(
                    debug_str_address(&request.output),
                    0,
                    "{linker}: {}",
                    request.output.display()
                );
            }
        }
    }

    /// `_start` calls the trust-cg `tcg_debug_probe` and exits with what it
    /// returns (42); a word of `.rodata` makes the output `.rodata`
    /// allocated.
    const DEBUG_PROBE_START: &str = "    .text\n    .globl _start\n_start:\n    bl \
        tcg_debug_probe\n    mov x8, #93\n    svc #0\n    .section .rodata\n    .p2align 3\n    \
        .globl tcg_debug_start_word\ntcg_debug_start_word:\n    .xword 42\n";

    /// A complete linker script for a static `-nostdlib` program that puts
    /// the `.debug_str` input into the allocated `.rodata` at `rodata` (after
    /// `.eh_frame` when `None`), with the code's segment on its own pages:
    /// LLD would otherwise put the build-id note on the code's last page
    /// in a read-only segment mapped over it.
    fn debug_str_script(rodata: Option<u64>) -> String {
        let placed = rodata.map_or_else(String::new, |address| format!(" {address:#x}"));
        format!(
            "SECTIONS {{\n  . = 0x400000 + SIZEOF_HEADERS;\n  .text : {{ *(.text .text.*) }}\n  \
             . = ALIGN(0x10000);\n  .note.gnu.build-id : {{ *(.note.gnu.build-id) }}\n  \
             .eh_frame_hdr : {{ *(.eh_frame_hdr) }}\n  .eh_frame : {{ KEEP(*(.eh_frame)) }}\n  \
             .rodata{placed} : {{ *(.rodata .rodata.*) *(.debug_str) }}\n}}\n"
        )
    }

    /// The ninth closure audit found the `ABS32` control's LLD and gold legs
    /// trigger no overflow (their `.debug_str` stays at address 0), so the
    /// window refusal of those two rested on the 76ead5025 probe. Here a
    /// complete linker script puts the trust-cg `-g` object's `.debug_str`
    /// input into an allocated `.rodata` at 4 GiB, so each DWARF section
    /// offset (`R_AARCH64_ABS32`, `S + A` against `.debug_str`) is past the
    /// window: GNU ld 2.42, LLD 22.1.6 and gold 2.42 each refuse the link
    /// through the link driver, classified `relocation-out-of-range` for
    /// `R_AARCH64_ABS32` at the trust-cg object (GNU ld names `.debug_str`;
    /// LLD and gold name `debug_probe.o`), and nothing is installed. The
    /// twin with `.rodata` after `.eh_frame` links and runs (exit 42)
    /// through each. Without LLD or gold their legs print `SKIP:`.
    #[test]
    fn abs32_debug_offset_placed_past_4_gib_by_a_script_is_refused_by_each_linker() {
        let dir = scratch("tcg-linux-abs32-script-");
        let dir = dir.path();
        let object = dir.join("debug_probe.o");
        fs::write(
            &object,
            try_compile_with(&debug_probe_module(HOST), HOST, |config| {
                config.emit_debug = true;
            })
            .unwrap(),
        )
        .unwrap();
        let start = cc_object(dir, "debug_start", "s", DEBUG_PROBE_START);
        for (name, rodata) in [("near", None), ("far", Some(0x1_0000_0000u64))] {
            fs::write(dir.join(format!("{name}.ld")), debug_str_script(rodata)).unwrap();
        }
        for (linker, driver) in linker_drivers(dir) {
            let placed = |name: &str| {
                let mut request = with_wl(
                    executable(
                        vec![start.clone(), object.clone()],
                        dir.join(format!("{name}_{linker}")),
                    ),
                    &format!("-T,{}", dir.join(format!("{name}.ld")).display()),
                );
                request.nostdlib = true;
                request.static_link = true;
                request
            };
            runs_through(&placed("near"), &driver, linker, 42);
            let Refusal::Linker(diagnostics) = window_refusal(
                &placed("far"),
                &driver,
                linker,
                "R_AARCH64_ABS32",
                &[".debug_str", "debug_probe.o"],
            ) else {
                panic!("{linker}: every linker refuses the ABS32 offsets itself");
            };
            assert!(
                diagnostics
                    .iter()
                    .all(|diagnostic| diagnostic.relocation.as_deref() == Some("R_AARCH64_ABS32")),
                "{linker}: {diagnostics:#?}"
            );
        }
    }

    /// Writes 42 through the address `tcg_tls_far_addr` gives and exits 42
    /// when that address lies at least `tcg_tls_pad_size` bytes above
    /// `tcg_tls_pad`, as the thread-local after the pad does, else 1.
    const TLS_FAR_MAIN: &str = r#"
extern __thread char tcg_tls_pad[];
extern const unsigned long tcg_tls_pad_size;
extern long tcg_tls_far_addr(void);
int main(void) {
    char *far = (char *)tcg_tls_far_addr();
    *(long *)far = 42;
    return far - tcg_tls_pad >= (long)tcg_tls_pad_size && *(long *)far == 42 ? 42 : 1;
}
"#;

    /// The 8-byte thread-local `tcg_tls_far`, zero-filled in `.tbss`.
    const TLS_FAR_VAR: &str = "__thread long tcg_tls_far;\n";

    /// A zero-filled thread-local `tcg_tls_pad` of `size` bytes and its
    /// size, `tcg_tls_pad_size`.
    fn tls_pad_source(size: u64) -> String {
        format!(
            "    .section .tbss,\"awT\",@nobits\n    .globl tcg_tls_pad\n    .type \
             tcg_tls_pad,%tls_object\n    .p2align 4\ntcg_tls_pad:\n    .zero {size:#x}\n    \
             .size tcg_tls_pad, {size:#x}\n    .section .rodata\n    .globl tcg_tls_pad_size\n    \
             .p2align 3\ntcg_tls_pad_size:\n    .xword {size:#x}\n"
        )
    }

    /// GNU ld 2.42 relaxes an executable's initial-exec and TLS-descriptor
    /// accesses to a thread-local it defines into the local-exec pair
    /// `movz xd, #:tprel_g1:` / `movk xd, #:tprel_g0_nc:`, which holds only
    /// the low 32 bits of `TPREL`, and writes a larger `TPREL` truncated
    /// without a diagnostic. Here the trust-cg `tcg_tls_far_addr` reaches
    /// `tcg_tls_far`, placed after a 4 GiB + 4 KiB thread-local pad, by
    /// initial exec (`R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21`) and, compiled
    /// `pic`, by a descriptor (`R_AARCH64_TLSDESC_ADR_PAGE21`). GNU ld links
    /// both, and outside the driver the program writes into the pad and
    /// exits 1; through the link driver the image is refused as
    /// `[TCG-LINK-TLS-TPREL-UNPROVEN]` (its thread-local block reaches 2^32
    /// bytes above the thread pointer) and nothing is installed. gold 2.42
    /// (`TLS variable referred by reloc N is too far from TP`) and LLD
    /// 22.1.6 refuse the link, classified `relocation-out-of-range` for the
    /// access's page relocation. With a 4 KiB pad each linker links both
    /// objects into programs that exit 42. Without LLD or gold their legs
    /// print `SKIP:`.
    #[test]
    fn tls_relaxed_to_local_exec_past_4_gib_is_refused_and_its_near_twin_runs() {
        let dir = scratch("tcg-linux-tprel-");
        let dir = dir.path();
        let main = cc_object(dir, "tls_far_main", "c", TLS_FAR_MAIN);
        let var = cc_object(dir, "tls_far_var", "c", TLS_FAR_VAR);
        let pads = [
            (
                "near",
                cc_object(dir, "pad_near", "s", &tls_pad_source(0x1000)),
            ),
            (
                "far",
                cc_object(dir, "pad_far", "s", &tls_pad_source(0x1_0000_1000)),
            ),
        ];
        let objects = [
            (
                "ie",
                "R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21",
                try_compile_with(&tls_import_module(HOST), HOST, |_| {}).unwrap(),
            ),
            (
                "desc",
                "R_AARCH64_TLSDESC_ADR_PAGE21",
                try_compile_with(&tls_import_module(HOST), HOST, |config| {
                    config.relocation_model = trust_cg_codegen::RelocationModel::Pic;
                })
                .unwrap(),
            ),
        ];
        for (access, relocation, bytes) in &objects {
            let object = dir.join(format!("tls_far_{access}.o"));
            fs::write(&object, bytes).unwrap();
            let request = |pad: &Path, name: String| {
                executable(
                    vec![main.clone(), pad.to_path_buf(), var.clone(), object.clone()],
                    dir.join(name),
                )
            };
            for (linker, driver) in linker_drivers(dir) {
                runs_through(
                    &request(&pads[0].1, format!("near_{access}_{linker}")),
                    &driver,
                    linker,
                    42,
                );
                let far = request(&pads[1].1, format!("far_{access}_{linker}"));
                match window_refusal(
                    &far,
                    &driver,
                    linker,
                    relocation,
                    &["tcg_tls_far", "tcg_tls_far_addr"],
                ) {
                    Refusal::Driver(diagnostics) => {
                        assert_eq!(linker, "gnu", "{diagnostics:#?}");
                        assert!(
                            diagnostics.iter().any(|diagnostic| diagnostic
                                .line
                                .starts_with("[TCG-LINK-TLS-TPREL-UNPROVEN] ")
                                && diagnostic.kind == LinkDiagnosticKind::Unclassified),
                            "{diagnostics:#?}"
                        );
                    }
                    Refusal::Linker(_) => assert_ne!(linker, "gnu"),
                }
            }
            // GNU ld outside the driver installs a program whose relaxed
            // access addresses the pad.
            let raw = request(&pads[1].1, format!("raw_{access}"));
            let linked = link(&raw);
            assert!(linked.success, "{}", linked.stderr);
            let status = run(&raw.output);
            eprintln!("raw_{access}, linked by GNU ld without the driver: exit {status:?}");
            assert_eq!(status, Some(1), "{access}");
        }
    }

    const GOT_PAGE_MAIN: &str = "extern int tcg_desc_bump(void);\nint main(void) { return tcg_desc_bump() == 42 && tcg_desc_bump() == 44 ? 0 : 1; }\n";

    /// Synthetic distance for the GOT-page `ADRP` kinds: a `pic` trust-cg
    /// object reaches its thread-local through a TLS descriptor
    /// (`R_AARCH64_TLSDESC_ADR_PAGE21`) and its preemptible word through the
    /// GOT (`R_AARCH64_ADR_GOT_PAGE`), and the shared object's GOT is placed
    /// 8 GiB above its code, then just past the window's upper edge (64 KiB
    /// beyond 4 GiB). GNU ld 2.42 links both without a diagnostic (the page
    /// deltas are written truncated), so the link driver's image check must
    /// refuse the staged image by name as an overflow (each use's slot is
    /// named by its dynamic relocation and out of reach of every code byte),
    /// remove it and leave the requested output untouched; a linker that
    /// checks the window fails the link with the same classification. The
    /// twin with the GOT 2 GiB away links, loads and runs.
    #[test]
    fn got_page_adrp_beyond_4_gib_is_refused_by_the_link_driver() {
        use trust_cg_codegen::link_driver::{LinkError, run_link};
        let dir = scratch("tcg-linux-gotpage-");
        let dir = dir.path();
        let object = dir.join("got_page.o");
        fs::write(
            &object,
            try_compile_with(&got_page_module(HOST), HOST, |config| {
                config.relocation_model = trust_cg_codegen::RelocationModel::Pic;
            })
            .unwrap(),
        )
        .unwrap();
        // `-nostdlib`: the C start files' own direct `ADRP`s to `.data` and
        // `.bss` (which GNU ld lays out after the placed GOT) would overflow
        // first; the library needs nothing from them.
        let shared = |name: &str, got: u64| {
            let mut request = with_wl(
                executable(vec![object.clone()], dir.join(name)),
                &format!(
                    "--section-start=.got={got:#x},--section-start=.got.plt={:#x}",
                    got + 0x10000
                ),
            );
            request.kind = LinkOutputKind::SharedLibrary;
            request.nostdlib = true;
            request
        };

        for (name, got) in [("libfar.so", 0x2_0000_0000), ("libedge.so", 0x1_0001_0000)] {
            let diagnostics = match run_link(&shared(name, got), "cc") {
                Err(LinkError::OutputRefused {
                    removed,
                    diagnostics,
                    ..
                }) => {
                    assert!(removed, "the refused library must be removed");
                    eprintln!(
                        "GOT at {got:#x}: the linker accepted it; the link driver refused the image"
                    );
                    diagnostics
                }
                Err(LinkError::Failed(failure)) => {
                    eprintln!(
                        "GOT at {got:#x}: the linker refused it:\n{}",
                        failure.stderr
                    );
                    failure.diagnostics
                }
                other => panic!("a GOT at {got:#x} must not link silently: {other:?}"),
            };
            for (symbol, relocation) in [
                ("tcg_desc_tls", "R_AARCH64_TLSDESC_ADR_PAGE21"),
                ("tcg_desc_word", "R_AARCH64_ADR_GOT_PAGE"),
            ] {
                assert!(
                    diagnostics.iter().any(|diagnostic| diagnostic.kind
                        == LinkDiagnosticKind::RelocationOutOfRange
                        && diagnostic.subject.as_deref() == Some(symbol)
                        && diagnostic.relocation.as_deref() == Some(relocation)),
                    "{got:#x} {symbol} {relocation}: {diagnostics:#?}"
                );
            }
            for diagnostic in &diagnostics {
                eprintln!("GOT at {got:#x} diagnostic: {}", diagnostic.line);
            }
            assert!(!dir.join(name).exists());
        }
        let staging_left = || {
            fs::read_dir(dir)
                .unwrap()
                .filter_map(|entry| entry.unwrap().file_name().into_string().ok())
                .filter(|name| name.starts_with(".tcg-link-"))
                .collect::<Vec<_>>()
        };
        assert_eq!(staging_left(), Vec::<String>::new());

        // A file already at the output keeps its bytes through the refusal:
        // the linker wrote the refused image at a staging path.
        fs::write(dir.join("libfar.so"), b"precious\n").unwrap();
        match run_link(&shared("libfar.so", 0x2_0000_0000), "cc") {
            Err(LinkError::OutputRefused { output, staged, .. }) => {
                assert_eq!(output, dir.join("libfar.so"));
                assert_ne!(staged, output);
            }
            Err(LinkError::Failed(_)) => {}
            other => panic!("a GOT 8 GiB from the code must not link silently: {other:?}"),
        }
        assert_eq!(fs::read(dir.join("libfar.so")).unwrap(), b"precious\n");
        assert_eq!(staging_left(), Vec::<String>::new());

        run_link(&shared("libnear.so", 0x8000_0000), "cc")
            .expect("a GOT 2 GiB from the code is in reach");
        let main = cc_object(dir, "desc_main", "c", GOT_PAGE_MAIN);
        let mut consumer = executable(vec![main, dir.join("libnear.so")], dir.join("desc"));
        consumer.rpaths = vec![dir.display().to_string()];
        let linked = link(&consumer);
        assert!(linked.success, "{}", linked.stderr);
        assert_eq!(run(&dir.join("desc")), Some(0));
    }
    /// A `pic` compile of [`got_page_module`] at `dir/got_page.o`.
    fn got_page_object(dir: &Path) -> PathBuf {
        let object = dir.join("got_page.o");
        fs::write(
            &object,
            try_compile_with(&got_page_module(HOST), HOST, |config| {
                config.relocation_model = trust_cg_codegen::RelocationModel::Pic;
            })
            .unwrap(),
        )
        .unwrap();
        object
    }

    /// The `.tcg-link-*` staging directories left in `dir`.
    fn staging_left(dir: &Path) -> Vec<String> {
        fs::read_dir(dir)
            .unwrap()
            .filter_map(|entry| entry.unwrap().file_name().into_string().ok())
            .filter(|name| name.starts_with(".tcg-link-"))
            .collect()
    }

    /// Run `request` through the link driver against a file already at its
    /// output holding `precious`, and return the refusal's diagnostics. The
    /// refused image must be removed with its staging directory and the
    /// file must keep its bytes. A linker that refuses the link itself (one
    /// that checks the page window) is accepted with its own diagnostics.
    fn refused_got_page_link(request: &LinkRequest, what: &str) -> Vec<LinkDiagnostic> {
        use trust_cg_codegen::link_driver::{LinkError, run_link};
        fs::write(&request.output, b"precious\n").unwrap();
        let diagnostics = match run_link(request, "cc") {
            Err(LinkError::OutputRefused {
                output,
                staged,
                removed,
                diagnostics,
                ..
            }) => {
                assert_eq!(output, request.output);
                assert_ne!(staged, output);
                assert!(removed, "{what}: the refused image must be removed");
                eprintln!("{what}: the linker accepted it; the link driver refused the image");
                diagnostics
            }
            Err(LinkError::Failed(failure)) => {
                eprintln!("{what}: the linker refused it:\n{}", failure.stderr);
                failure.diagnostics
            }
            other => panic!("{what}: must not link silently: {other:?}"),
        };
        for diagnostic in &diagnostics {
            eprintln!("{what} diagnostic: {diagnostic}");
        }
        assert_eq!(fs::read(&request.output).unwrap(), b"precious\n", "{what}");
        let dir = request.output.parent().unwrap();
        assert_eq!(staging_left(dir), Vec::<String>::new(), "{what}");
        diagnostics
    }

    /// The diagnostic for `symbol` in `diagnostics`.
    fn diagnostic_for<'a>(diagnostics: &'a [LinkDiagnostic], symbol: &str) -> &'a LinkDiagnostic {
        diagnostics
            .iter()
            .find(|diagnostic| diagnostic.subject.as_deref() == Some(symbol))
            .unwrap_or_else(|| panic!("no diagnostic for {symbol}: {diagnostics:#?}"))
    }

    /// Link `GOT_PAGE_MAIN` against the shared object `library` in `dir` and
    /// run it: `Some(0)` when both descriptor bumps return 42 and 44.
    fn run_against(dir: &Path, library: &str, name: &str) -> Option<i32> {
        let main = cc_object(dir, "desc_main", "c", GOT_PAGE_MAIN);
        let mut consumer = executable(vec![main, dir.join(library)], dir.join(name));
        consumer.rpaths = vec![dir.display().to_string()];
        let linked = link(&consumer);
        assert!(linked.success, "{}", linked.stderr);
        run(&dir.join(name))
    }

    /// Moves the GOT's contents into `.slots` at `address`; `.got.plt`
    /// stays where the default script and `--section-start` put it.
    fn slots_script(dir: &Path, address: u64) -> PathBuf {
        let script = dir.join(format!("slots-{address:#x}.ld"));
        fs::write(
            &script,
            format!(
                "SECTIONS {{ .slots {address:#x} : {{ *(.got) *(.igot) }} }} INSERT BEFORE .got;\n"
            ),
        )
        .unwrap();
        script
    }

    /// The GOT is found by what the image holds, not by section name: a
    /// linker script moves the GOT's contents into `.slots` 8 GiB above the
    /// code while `.got.plt` stays at 2 GiB. GNU ld 2.42 links that and
    /// truncates the `ADR_GOT_PAGE` page delta, and an executable using the
    /// library does not pass. The link driver refuses the staged image: the
    /// `R_AARCH64_GLOB_DAT` slot of `tcg_desc_word` in `.slots` is out of
    /// reach of every code byte (an observed overflow), while the descriptor
    /// slot of `tcg_desc_tls` in `.got.plt` is in reach, so its refusal is
    /// the conservative one. The same holds when the linker writes no
    /// section header table. With `.slots` at 1 GiB the library links,
    /// loads and runs.
    #[test]
    fn a_got_moved_by_a_linker_script_is_refused_whatever_its_name() {
        let dir = scratch("tcg-linux-gotslots-");
        let dir = dir.path();
        let object = got_page_object(dir);
        let shared = |name: &str, slots: u64, extra: &str| {
            let mut request = with_wl(
                executable(vec![object.clone()], dir.join(name)),
                &format!(
                    "{extra}-T,{},--section-start=.got.plt=0x80000000",
                    slots_script(dir, slots).display()
                ),
            );
            request.kind = LinkOutputKind::SharedLibrary;
            request.nostdlib = true;
            request
        };

        for (name, extra) in [
            ("libslots.so", ""),
            ("libslots-nosh.so", "-z,nosectionheader,"),
        ] {
            let diagnostics = refused_got_page_link(&shared(name, 0x2_0000_0000, extra), name);
            let word = diagnostic_for(&diagnostics, "tcg_desc_word");
            assert_eq!(
                word.kind,
                LinkDiagnosticKind::RelocationOutOfRange,
                "{word:#?}"
            );
            assert_eq!(word.relocation.as_deref(), Some("R_AARCH64_ADR_GOT_PAGE"));
            if word.line.starts_with("[TCG-LINK-") {
                assert!(
                    word.line.starts_with("[TCG-LINK-GOT-PAGE-WINDOW] ")
                        && word.line.contains("R_AARCH64_GLOB_DAT slot at 0x200000008"),
                    "{}",
                    word.line
                );
                let tls = diagnostic_for(&diagnostics, "tcg_desc_tls");
                assert_eq!(tls.kind, LinkDiagnosticKind::Unclassified, "{tls:#?}");
                assert!(
                    tls.line.starts_with("[TCG-LINK-GOT-PAGE-UNPROVEN] "),
                    "{}",
                    tls.line
                );
            }
        }

        // Without the driver's check GNU ld writes the library, and its
        // truncated page delta does not reach the slot.
        let raw = shared("libslots-raw.so", 0x2_0000_0000, "");
        let linked = link(&raw);
        if linked.success {
            let status = run_against(dir, "libslots-raw.so", "desc-raw");
            eprintln!("libslots-raw.so, linked without the driver's check: exit {status:?}");
            assert_ne!(status, Some(0));
        }

        run_link_ok(&shared("libslots-near.so", 0x4000_0000, ""));
        assert_eq!(run_against(dir, "libslots-near.so", "desc-near"), Some(0));
    }

    /// `_start` for a position-dependent executable with no C start files:
    /// it checks `tcg_desc_bump` and leaves through libc's `_exit`.
    const GOT_PAGE_START: &str = "extern int tcg_desc_bump(void);\nextern void _exit(int) __attribute__((noreturn));\nvoid _start(void) { _exit(tcg_desc_bump() == 42 && tcg_desc_bump() == 44 ? 0 : 1); }\n";

    /// A slot the static linker fills needs no dynamic relocation: in a
    /// position-dependent executable GNU ld writes `tcg_desc_word`'s slot
    /// itself and relaxes the descriptor to local exec, so moving the GOT's
    /// contents 8 GiB away leaves no dynamic relocation there, while the
    /// dynamic section, `DT_PLTGOT` and `.got.plt` (`_exit`'s jump slot) stay
    /// near the code. A check that looked only at `.got*` names, dynamic
    /// relocations and `DT_PLTGOT` would admit it; GNU ld links it and the
    /// executable does not pass. The link driver refuses it as unproven,
    /// since no dynamic relocation names the slot. Without the script the
    /// executable links and runs.
    #[test]
    fn a_got_slot_without_a_dynamic_relocation_is_still_found() {
        let dir = scratch("tcg-linux-gotstatic-");
        let dir = dir.path();
        let object = got_page_object(dir);
        let start = cc_object(dir, "start", "c", GOT_PAGE_START);
        let exe = |name: &str, script: bool| {
            let mut request = executable(vec![start.clone(), object.clone()], dir.join(name));
            request.position_independence = PositionIndependence::NoPie;
            request.nostdlib = true;
            request.libs = vec!["c".to_string()];
            if script {
                request = with_wl(
                    request,
                    &format!(
                        "-T,{},--section-start=.got.plt=0x80000000",
                        slots_script(dir, 0x2_0000_0000).display()
                    ),
                );
            }
            request
        };

        let diagnostics = refused_got_page_link(&exe("static-far", true), "static-far");
        let word = diagnostic_for(&diagnostics, "tcg_desc_word");
        if word.line.starts_with("[TCG-LINK-") {
            assert_eq!(word.kind, LinkDiagnosticKind::Unclassified, "{word:#?}");
            assert!(
                word.line.starts_with("[TCG-LINK-GOT-PAGE-UNPROVEN] ")
                    && word.line.contains("not an observed overflow"),
                "{}",
                word.line
            );
        } else {
            assert_eq!(
                word.kind,
                LinkDiagnosticKind::RelocationOutOfRange,
                "{word:#?}"
            );
        }

        let raw = exe("static-far-raw", true);
        let linked = link(&raw);
        if linked.success {
            let status = run(&raw.output);
            eprintln!("static-far-raw, linked without the driver's check: exit {status:?}");
            assert_ne!(status, Some(0));
        }

        run_link_ok(&exe("static-near", false));
        assert_eq!(run(&dir.join("static-near")), Some(0));
    }

    /// A function in `.farcode` with no GOT reference.
    const FAR_CODE: &str = "    .section .farcode,\"ax\",%progbits\n    .globl tcg_far_helper\n    .type tcg_far_helper,%function\ntcg_far_helper:\n    mov w0, #7\n    ret\n";

    /// The check cannot tell which code holds a GOT-page `ADRP`: an
    /// executable section 8 GiB from a GOT that the library's own code
    /// reaches makes every GOT-page use unproven, and the refusal says it
    /// is conservative (`unclassified`, `[TCG-LINK-GOT-PAGE-UNPROVEN]`), not
    /// an overflow. GNU ld links the same library, and it loads and runs.
    #[test]
    fn far_code_without_got_references_is_refused_as_unproven() {
        let dir = scratch("tcg-linux-farcode-");
        let dir = dir.path();
        let object = got_page_object(dir);
        let far = cc_object(dir, "far", "s", FAR_CODE);
        let shared = |name: &str| {
            let mut request = with_wl(
                executable(vec![object.clone(), far.clone()], dir.join(name)),
                "--section-start=.farcode=0x200000000",
            );
            request.kind = LinkOutputKind::SharedLibrary;
            request.nostdlib = true;
            request
        };

        let diagnostics = refused_got_page_link(&shared("libfarcode.so"), "far code");
        for (symbol, relocation) in [
            ("tcg_desc_tls", "R_AARCH64_TLSDESC_ADR_PAGE21"),
            ("tcg_desc_word", "R_AARCH64_ADR_GOT_PAGE"),
        ] {
            let diagnostic = diagnostic_for(&diagnostics, symbol);
            assert_eq!(
                diagnostic.kind,
                LinkDiagnosticKind::Unclassified,
                "{diagnostic:#?}"
            );
            assert_eq!(diagnostic.relocation.as_deref(), Some(relocation));
            assert!(
                diagnostic.line.starts_with("[TCG-LINK-GOT-PAGE-UNPROVEN] ")
                    && diagnostic
                        .line
                        .contains("this is a conservative refusal, not an observed overflow"),
                "{}",
                diagnostic.line
            );
        }

        let raw = shared("libfarcode-raw.so");
        let linked = link(&raw);
        assert!(linked.success, "{}", linked.stderr);
        let status = run_against(dir, "libfarcode-raw.so", "desc-farcode");
        eprintln!("libfarcode-raw.so, linked without the driver's check: exit {status:?}");
        assert_eq!(status, Some(0));
    }

    /// A static `_start` (no C library) that exits 0 when the undefined weak
    /// `tcg_weak_missing`, reached through its GOT slot (`-fPIC`), is null.
    const WEAK_START: &str = r#"
extern int tcg_weak_missing __attribute__((weak));
__attribute__((noinline)) int probe(void) { return &tcg_weak_missing == 0 ? 0 : 1; }
void _start(void) {
  register long x0 __asm__("x0") = probe();
  register long x8 __asm__("x8") = 93;
  __asm__ volatile("svc 0" :: "r"(x0), "r"(x8));
  __builtin_unreachable();
}
"#;

    /// A linker script's `INFO`, `COPY`, `DSECT` or `OVERLAY` output section
    /// is not allocated but keeps its address, and GNU ld 2.42 links the GOT
    /// into one. Laid over `NOLOAD` zero fill, the undefined weak's slot
    /// reads zero, its right value, so the static executable runs with the
    /// section at 1 GiB. At 8 GiB GNU ld truncates the page delta and the
    /// executable dies. No relocation or tag names the slot, so the driver
    /// finds the section by its address and refuses the image as unproven;
    /// the output keeps its bytes. The 1 GiB twins link and run through the
    /// driver. Without a section header table (`-z nosectionheader`) no
    /// program header describes the section, so the driver refuses the
    /// image at either address, although GNU ld's 1 GiB image runs.
    #[test]
    fn a_got_in_a_non_allocated_section_is_found() {
        let dir = scratch("tcg-linux-gotinfo-");
        let dir = dir.path();
        let object = got_page_object(dir);
        let weak = cc_object_with(dir, "weakst", "c", WEAK_START, &["-fPIC", "-O1"]);
        let script = |kind: &str, address: u64| {
            let path = dir.join(format!("{kind}-{address:#x}.ld"));
            fs::write(
                &path,
                format!(
                    "SECTIONS {{\n  .farbss {address:#x} (NOLOAD) : {{ . = . + 0x1000; }}\n  \
                     .slots {address:#x} ({kind}) : {{ *(.got) *(.igot) }}\n}} INSERT AFTER .bss;\n"
                ),
            )
            .unwrap();
            path
        };
        let exe = |name: &str, kind: &str, address: u64, extra: &str| {
            let mut request = with_wl(
                executable(vec![weak.clone(), object.clone()], dir.join(name)),
                &format!("{extra}-T,{}", script(kind, address).display()),
            );
            request.static_link = true;
            request.nostdlib = true;
            request
        };
        let all_unproven = |diagnostics: &[LinkDiagnostic], what: &str, text: &str| {
            for symbol in ["tcg_weak_missing", "tcg_desc_word"] {
                let diagnostic = diagnostic_for(diagnostics, symbol);
                if !diagnostic.line.starts_with("[TCG-LINK-") {
                    continue;
                }
                assert_eq!(
                    diagnostic.kind,
                    LinkDiagnosticKind::Unclassified,
                    "{what}: {diagnostic:#?}"
                );
                assert!(
                    diagnostic.line.starts_with("[TCG-LINK-GOT-PAGE-UNPROVEN] ")
                        && diagnostic.line.contains(text),
                    "{what}: {}",
                    diagnostic.line
                );
            }
        };

        for kind in ["INFO", "COPY", "DSECT", "OVERLAY"] {
            let far = format!("{kind}-far");
            let diagnostics = refused_got_page_link(&exe(&far, kind, 0x2_0000_0000, ""), &far);
            all_unproven(&diagnostics, &far, "`.slots` ends at 0x200000017");

            let raw = exe(&format!("{kind}-far-raw"), kind, 0x2_0000_0000, "");
            let linked = link(&raw);
            if linked.success {
                let status = run(&raw.output);
                eprintln!("{far}-raw, linked without the driver's check: exit {status:?}");
                assert_ne!(status, Some(0));
            }

            let near = exe(&format!("{kind}-near"), kind, 0x4000_0000, "");
            run_link_ok(&near);
            assert_eq!(run(&near.output), Some(0), "{kind} at 1 GiB");
        }

        for (name, address) in [
            ("INFO-far-nosh", 0x2_0000_0000),
            ("INFO-near-nosh", 0x4000_0000),
        ] {
            let request = exe(name, "INFO", address, "-z,nosectionheader,");
            let diagnostics = refused_got_page_link(&request, name);
            all_unproven(&diagnostics, name, "it has no section header table");
            let raw = exe(
                &format!("{name}-raw"),
                "INFO",
                address,
                "-z,nosectionheader,",
            );
            let linked = link(&raw);
            if linked.success {
                let status = run(&raw.output);
                eprintln!("{name}-raw, linked without the driver's check: exit {status:?}");
                assert_eq!(status == Some(0), address == 0x4000_0000, "{name}-raw");
            }
        }
    }

    /// `request` links through the driver and its image is installed.
    fn run_link_ok(request: &LinkRequest) {
        trust_cg_codegen::link_driver::run_link(request, "cc")
            .unwrap_or_else(|error| panic!("{}: {error}", request.output.display()));
        assert!(request.output.is_file());
    }

    /// The L02-P2 audit's library (2026-10-24): default-visibility data
    /// `rp_data` (1111) with its reader `rp_read_data` and its address
    /// `rp_addr_data`, and the function `rp_fn` (7) with its address
    /// `rp_addr_fn`.
    const RPD: &str = r#"module "rpd"
target "aarch64-unknown-linux-gnu" 8 little
functy.0 = () -> (u64)
functy.1 = () -> (ptr)
functy.2 = () -> (functy.0)
global mut align(8) @rp_data u64 = 1111
fn @rp_read_data(functy.0) {
bb0:
    %0 = global_addr @global.0
    %1 = load u64, ptr %0
    ret %1
}
fn @rp_addr_data(functy.1) {
bb0:
    %0 = global_addr @global.0
    ret %0
}
fn @rp_fn(functy.0) {
bb0:
    %0 = const u64 7
    ret %0
}
fn @rp_addr_fn(functy.2) {
bb0:
    %0 = const functy.0 fndef<func.2>
    ret %0
}
"#;

    /// A non-PIE executable that writes `rp_data` through its copy
    /// relocation: exit 0 when the library reads that one copy and its
    /// `rp_addr_fn()` is the executable's `&rp_fn` (the audit's
    /// `copyuser.c`).
    const RPD_COPY_USER: &str = "#include <stdint.h>\nextern uint64_t rp_data;\nextern \
        uint64_t rp_read_data(void);\nextern uint64_t *rp_addr_data(void);\nextern uint64_t \
        rp_fn(void);\nextern void *rp_addr_fn(void);\nint main(void) {\n  int bad = 0;\n  \
        rp_data = 99;\n  if (rp_addr_data() != &rp_data) bad |= 1;\n  if (rp_read_data() != 99) \
        bad |= 2;\n  if ((void *)&rp_fn != rp_addr_fn()) bad |= 4;\n  return bad;\n}\n";

    /// [`RPD`] compiled under `model`, at `dir/rpd-<model>.o`.
    fn rpd_object(dir: &Path, model: trust_cg_codegen::RelocationModel) -> PathBuf {
        let module = trust_cg_codegen::pipeline::parse_trust_ir_text(RPD).unwrap();
        let object = dir.join(format!("rpd-{model}.o"));
        fs::write(
            &object,
            try_compile_with(&module, HOST, |config| config.relocation_model = model).unwrap(),
        )
        .unwrap();
        object
    }

    /// L02-P2 (2026-10-24 closure audit): a `static`- or `pie`-model object
    /// addressing its default-visibility `rp_data` and `rp_fn` directly
    /// (`ADRP`/`ADD`/`LDR` lo12) cannot be linked into a shared object: the
    /// link driver refuses it by name before the linker runs, on GNU ld, gold
    /// and LLD alike (`[TCG-LINK-PREEMPTIBLE-DIRECT]`), and nothing is
    /// written. Before the repair gold installed that library and bound both
    /// symbols locally, so a copy-relocating executable's write was never
    /// seen by the library (exit 7). The same object still links into an
    /// executable and runs, and the `pic` twin links `-shared` with every
    /// linker and keeps one `rp_data` and one `rp_fn` with that executable
    /// (linked by GNU ld, as in the audit's reproducer).
    #[test]
    fn direct_addresses_of_preemptible_symbols_are_refused_in_a_shared_link_on_every_linker() {
        use trust_cg_codegen::RelocationModel;
        use trust_cg_codegen::link_driver::{LinkError, run_link};
        let dir = scratch("tcg-linux-preemptible-direct-");
        let dir = dir.path();
        let main = cc_object(
            dir,
            "rpd_main",
            "c",
            "extern unsigned long rp_read_data(void);\nint main(void) { return rp_read_data() \
             == 1111 ? 0 : 1; }\n",
        );
        let pic = rpd_object(dir, RelocationModel::Pic);
        for (linker, driver) in linker_drivers(dir) {
            for model in [RelocationModel::Static, RelocationModel::Pie] {
                let object = rpd_object(dir, model);
                let what = format!("{linker} {model}");
                let mut shared = executable(
                    vec![object.clone()],
                    dir.join(format!("librpd-{linker}-{model}.so")),
                );
                shared.kind = LinkOutputKind::SharedLibrary;
                match run_link(&shared, &driver) {
                    Err(LinkError::InputRefused(diagnostics)) => {
                        let subjects: BTreeSet<&str> = diagnostics
                            .iter()
                            .filter_map(|diagnostic| diagnostic.subject.as_deref())
                            .collect();
                        assert_eq!(subjects, BTreeSet::from(["rp_data", "rp_fn"]), "{what}");
                        for diagnostic in &diagnostics {
                            assert_eq!(diagnostic.kind, LinkDiagnosticKind::NonPicRelocation);
                            assert!(
                                diagnostic
                                    .line
                                    .starts_with("[TCG-LINK-PREEMPTIBLE-DIRECT] "),
                                "{what}: {}",
                                diagnostic.line
                            );
                        }
                    }
                    other => panic!("{what}: expected the pre-link refusal, got {other:?}"),
                }
                assert!(!shared.output.exists(), "{what}");
                assert_eq!(staging_left(dir), Vec::<String>::new(), "{what}");
                // The executable twin links and runs.
                let program = dir.join(format!("rpd-main-{linker}-{model}"));
                let mut request = executable(vec![main.clone(), object], program.clone());
                if model == RelocationModel::Static {
                    request.position_independence = PositionIndependence::NoPie;
                }
                run_link(&request, &driver).unwrap_or_else(|error| panic!("{what}: {error}"));
                assert_eq!(run(&program), Some(0), "{what}");
            }
            // The `pic` twin, used by a copy-relocating non-PIE executable.
            let library = dir.join(format!("librpd-{linker}-pic.so"));
            let mut shared = executable(vec![pic.clone()], library.clone());
            shared.kind = LinkOutputKind::SharedLibrary;
            run_link(&shared, &driver).unwrap_or_else(|error| panic!("{linker} pic: {error}"));
            let user = cc_object_with(dir, "rpd_copy_user", "c", RPD_COPY_USER, &["-fno-pic"]);
            let program = dir.join(format!("rpd-copy-user-{linker}"));
            let mut consumer = executable(vec![user, library], program.clone());
            consumer.position_independence = PositionIndependence::NoPie;
            consumer.rpaths = vec![dir.display().to_string()];
            // The executable is linked by GNU ld whatever linked the library:
            // gold 2.42 gives a non-PIE executable no canonical address for a
            // function a shared library defines (LIMITATIONS), so its `&rp_fn`
            // and the library's would differ whatever either object does.
            run_link(&consumer, "cc").unwrap_or_else(|error| panic!("{linker} user: {error}"));
            assert_eq!(run(&program), Some(0), "{linker}: one rp_data, one rp_fn");
        }
    }

    /// The refusal reads every input the linker loads, not only the
    /// positional ones: a `static`-model object that reaches a shared link
    /// as a `-Wl` operand beside a `pic` positional object is read from the
    /// linker's input trace and the image is refused by name
    /// (`[TCG-LINK-PREEMPTIBLE-DIRECT]`, naming the trace) and removed, under
    /// gold, which links it; GNU ld and LLD refuse the link themselves
    /// (`recompile with -fPIC`). Nothing is installed either way.
    #[test]
    fn direct_addresses_reaching_a_shared_link_through_its_trace_are_refused() {
        use trust_cg_codegen::RelocationModel;
        use trust_cg_codegen::link_driver::{LinkError, run_link};
        let dir = scratch("tcg-linux-preemptible-traced-");
        let dir = dir.path();
        let module = trust_cg_codegen::pipeline::parse_trust_ir_text(RPD).unwrap();
        // A `pic` positional object (its word is reached through the GOT).
        let stub = dir.join("stub.o");
        fs::write(
            &stub,
            try_compile_with(&far_word_module(HOST), HOST, |config| {
                config.relocation_model = RelocationModel::Pic;
            })
            .unwrap(),
        )
        .unwrap();
        let object = dir.join("rpd-static.o");
        fs::write(
            &object,
            try_compile_with(&module, HOST, |config| {
                config.relocation_model = RelocationModel::Static;
            })
            .unwrap(),
        )
        .unwrap();
        for (linker, driver) in linker_drivers(dir) {
            let output = dir.join(format!("librpd-traced-{linker}.so"));
            let mut shared = with_wl(
                executable(vec![stub.clone()], output.clone()),
                &object.display().to_string(),
            );
            shared.kind = LinkOutputKind::SharedLibrary;
            match run_link(&shared, &driver) {
                Err(LinkError::OutputRefused {
                    removed,
                    diagnostics,
                    ..
                }) => {
                    assert!(removed, "{linker}");
                    let refused: Vec<&LinkDiagnostic> = diagnostics
                        .iter()
                        .filter(|diagnostic| {
                            diagnostic
                                .line
                                .starts_with("[TCG-LINK-PREEMPTIBLE-DIRECT] ")
                        })
                        .collect();
                    let subjects: BTreeSet<&str> = refused
                        .iter()
                        .filter_map(|diagnostic| diagnostic.subject.as_deref())
                        .collect();
                    assert_eq!(
                        subjects,
                        BTreeSet::from(["rp_data", "rp_fn"]),
                        "{linker}: {diagnostics:#?}"
                    );
                    assert!(
                        refused
                            .iter()
                            .all(|diagnostic| diagnostic.line.contains("its input trace names it")),
                        "{linker}: {refused:#?}"
                    );
                }
                Err(LinkError::Failed(failure)) => {
                    assert_ne!(linker, "gold", "gold links it: {}", failure.stderr);
                    assert!(
                        failure.stderr.contains("recompile with -fPIC"),
                        "{linker}: {}",
                        failure.stderr
                    );
                }
                other => panic!("{linker}: must not link: {other:?}"),
            }
            assert!(!output.exists(), "{linker}");
            assert_eq!(staging_left(dir), Vec::<String>::new(), "{linker}");
        }
    }

    /// The linker gives a symbol the most constraining visibility any
    /// relocatable input states, so a direct address of a symbol another
    /// input defines hidden is a link-time constant in the shared object and
    /// links on every linker: a GCC `-fno-pic` object addressing
    /// `tcg_hidden_word` directly beside the `-fPIC` object that defines it
    /// hidden. Its twin, the same reference to a default-visibility
    /// definition, is refused by name.
    #[test]
    fn a_direct_address_of_a_symbol_another_input_hides_links_into_a_shared_object() {
        use trust_cg_codegen::link_driver::{LinkError, run_link};
        let dir = scratch("tcg-linux-preemptible-hidden-");
        let dir = dir.path();
        let reference = cc_object_with(
            dir,
            "hidden_ref",
            "c",
            "extern int tcg_hidden_word;\nint tcg_read_hidden(void) { return tcg_hidden_word; }\n",
            &["-O1", "-fno-pic"],
        );
        let hidden = cc_object_with(
            dir,
            "hidden_def",
            "c",
            "__attribute__((visibility(\"hidden\"))) int tcg_hidden_word = 42;\n",
            &["-fPIC"],
        );
        let exported = cc_object_with(
            dir,
            "exported_def",
            "c",
            "int tcg_hidden_word = 42;\n",
            &["-fPIC"],
        );
        let records = read_object_records(&fs::read(&reference).unwrap()).unwrap();
        assert!(
            records
                .relocations
                .iter()
                .any(|relocation| relocation.record.reloc_type == 275
                    && records.symbols[relocation.record.symbol_index as usize].name
                        == "tcg_hidden_word"),
            "the reference is a direct ADRP"
        );
        for (linker, driver) in linker_drivers(dir) {
            let output = dir.join(format!("libhidden-{linker}.so"));
            let mut shared = executable(vec![reference.clone(), hidden.clone()], output.clone());
            shared.kind = LinkOutputKind::SharedLibrary;
            run_link(&shared, &driver).unwrap_or_else(|error| panic!("{linker}: {error}"));
            assert!(output.is_file(), "{linker}");

            let output = dir.join(format!("libexported-{linker}.so"));
            let mut shared = executable(vec![reference.clone(), exported.clone()], output.clone());
            shared.kind = LinkOutputKind::SharedLibrary;
            match run_link(&shared, &driver) {
                Err(LinkError::InputRefused(diagnostics)) => assert!(
                    diagnostics.len() == 1
                        && diagnostics[0].subject.as_deref() == Some("tcg_hidden_word")
                        && diagnostics[0]
                            .line
                            .starts_with("[TCG-LINK-PREEMPTIBLE-DIRECT] "),
                    "{linker}: {diagnostics:#?}"
                ),
                other => panic!("{linker}: expected the pre-link refusal, got {other:?}"),
            }
            assert!(!output.exists(), "{linker}");
        }
    }

    /// A GCC object that addresses the linker's `__start_tcgsec` and
    /// defines `tcg_in_sec` in that section.
    const START_REF: &str = "extern char __start_tcgsec[];\n__attribute__((section(\"tcgsec\"), \
                             used)) int tcg_in_sec = 1;\nchar *tcg_start(void) { return \
                             __start_tcgsec; }\n";

    /// L02-P2 round 3 (2026-10-24): a name exempt from
    /// `[TCG-LINK-PREEMPTIBLE-DIRECT]` (bound inside the output by the
    /// linker, or hidden by another input) is not exempt when a link option
    /// or linker script exports or redirects it, on every linker. The
    /// round-3 verifier's reproducer: a GCC `-fno-pic` object's `ADRP`/`ADD`
    /// of `__start_tcgsec`, a `-Wl` operand, under
    /// `-Wl,--defsym=__start_tcgsec=tcg_in_sec`: gold exported it `GLOBAL
    /// DEFAULT` and the driver installed a library that ignored an
    /// interposing executable's definition (GNU ld and LLD refuse it
    /// themselves). Refused now: before the link when the object is
    /// positional (`--defsym` of `__start_tcgsec`, `__stop_tcgsec` and
    /// `__ehdr_start`, `-z start-stop-visibility=default`, and the pieces
    /// whose bindings the driver does not read: `-T` and `-z muldefs`;
    /// `--just-symbols` is refused earlier, as an option), after it from the
    /// input trace, for `--wrap` of the name
    /// and of a hidden one, and, where no option shows it, from the image's
    /// dynamic symbol table (a positional linker script assigning
    /// `__start_tcgsec`). The plain controls of all three names and the
    /// `start-stop-visibility=protected` one link, and the `-fPIC` twins
    /// link under the same options and give an `-rdynamic` executable's
    /// interposing definition to the library.
    #[test]
    fn a_link_option_that_exports_or_redirects_an_exempt_name_voids_its_exemption() {
        use trust_cg_codegen::link_driver::{LinkError, run_link};
        let dir = scratch("tcg-linux-preemptible-rebound-");
        let dir = dir.path();
        let start = cc_object_with(dir, "start_ref", "c", START_REF, &["-O1", "-fno-pic"]);
        let start_pic = cc_object_with(dir, "start_ref_pic", "c", START_REF, &["-O1", "-fPIC"]);
        let foo = "extern char foo[];\nchar *tcg_get(void) { return foo; }\n";
        let foo_ref = cc_object_with(dir, "foo_ref", "c", foo, &["-O1", "-fno-pic"]);
        let foo_ref_pic = cc_object_with(dir, "foo_ref_pic", "c", foo, &["-O1", "-fPIC"]);
        let foo_hidden = cc_object_with(
            dir,
            "foo_hidden",
            "c",
            "__attribute__((visibility(\"hidden\"))) char foo[16] = \"hidden\";\n",
            &["-fPIC"],
        );
        let wrap_foo = cc_object_with(
            dir,
            "wrap_foo",
            "c",
            "char __wrap_foo[16] = \"wrap\";\n",
            &["-fPIC"],
        );
        let wrap_start = cc_object_with(
            dir,
            "wrap_start",
            "c",
            "char __wrap___start_tcgsec[16] = \"wrap\";\n",
            &["-fPIC"],
        );
        let stub = cc_object_with(
            dir,
            "stub",
            "c",
            "int tcg_stub(void) { return 1; }\n",
            &["-fPIC"],
        );
        // The verifier's other linker-defined names: `__stop_tcgsec` and
        // `__ehdr_start`, addressed the same way.
        let stop = cc_object_with(
            dir,
            "stop_ref",
            "c",
            &START_REF.replace("__start_tcgsec", "__stop_tcgsec"),
            &["-O1", "-fno-pic"],
        );
        let ehdr = cc_object_with(
            dir,
            "ehdr_ref",
            "c",
            &START_REF.replace("__start_tcgsec", "__ehdr_start"),
            &["-O1", "-fno-pic"],
        );
        let script = dir.join("assign.ld");
        fs::write(&script, "__start_tcgsec = tcg_in_sec;\n").unwrap();
        for (object, symbol) in [
            (&start, "__start_tcgsec"),
            (&stop, "__stop_tcgsec"),
            (&ehdr, "__ehdr_start"),
        ] {
            let records = read_object_records(&fs::read(object).unwrap()).unwrap();
            assert!(
                records.relocations.iter().any(|relocation| {
                    relocation.record.reloc_type == 275
                        && records.symbols[relocation.record.symbol_index as usize].name == symbol
                }),
                "the reference to {symbol} is a direct ADRP"
            );
        }
        let start_operand = start.display().to_string();
        let wrap_start_operand = wrap_start.display().to_string();
        let defsym = "--defsym=__start_tcgsec=tcg_in_sec";
        let defsym_stop = "--defsym=__stop_tcgsec=tcg_in_sec";
        let defsym_ehdr = "--defsym=__ehdr_start=tcg_in_sec";
        // A `-Wl` linker script, `--just-symbols` and multiple definitions
        // are pieces whose bindings the driver does not read: each voids
        // every exemption, and the refusal names the piece.
        let script_option = format!("-T,{}", script.display());
        let just_symbols = format!("--just-symbols={}", stub.display());
        for (linker, driver) in linker_drivers(dir) {
            let shared = |name: &str, objects: Vec<PathBuf>, groups: &[&str]| {
                let mut request = executable(objects, dir.join(format!("lib{name}-{linker}.so")));
                request.kind = LinkOutputKind::SharedLibrary;
                for group in groups {
                    request = with_wl(request, group);
                }
                request
            };
            // Refused before the link, on every linker, naming the option.
            for (name, objects, groups, symbol, option) in [
                (
                    "defsym",
                    vec![start.clone()],
                    vec![defsym],
                    "__start_tcgsec",
                    defsym,
                ),
                (
                    "defsym-stop",
                    vec![stop.clone()],
                    vec![defsym_stop],
                    "__stop_tcgsec",
                    defsym_stop,
                ),
                (
                    "defsym-ehdr",
                    vec![ehdr.clone()],
                    vec![defsym_ehdr],
                    "__ehdr_start",
                    defsym_ehdr,
                ),
                (
                    "start-stop-default",
                    vec![start.clone()],
                    vec!["-z,start-stop-visibility=default"],
                    "__start_tcgsec",
                    "start-stop-visibility=default",
                ),
                (
                    "wrap-hidden",
                    vec![foo_ref.clone(), foo_hidden.clone(), wrap_foo.clone()],
                    vec!["--wrap=foo"],
                    "foo",
                    "--wrap=foo",
                ),
                (
                    "script-option",
                    vec![start.clone()],
                    vec![script_option.as_str()],
                    "__start_tcgsec",
                    "-T",
                ),
                (
                    "muldefs",
                    vec![foo_ref.clone(), foo_hidden.clone()],
                    vec!["-z,muldefs"],
                    "foo",
                    "-z muldefs",
                ),
            ] {
                let request = shared(name, objects, &groups);
                match run_link(&request, &driver) {
                    Err(LinkError::InputRefused(diagnostics)) => {
                        assert_eq!(diagnostics.len(), 1, "{linker} {name}: {diagnostics:#?}");
                        let line = &diagnostics[0].line;
                        assert_eq!(diagnostics[0].subject.as_deref(), Some(symbol));
                        assert!(
                            line.starts_with("[TCG-LINK-PREEMPTIBLE-DIRECT] ")
                                && line.contains(&format!("the -Wl option `{option}` can")),
                            "{linker} {name}: {line}"
                        );
                    }
                    other => {
                        panic!("{linker} {name}: expected the pre-link refusal, got {other:?}")
                    }
                }
                assert!(!request.output.exists(), "{linker} {name}");
            }
            // `--just-symbols` never reaches the direct-address check (the
            // unit row covers how it voids every exemption there): it
            // abbreviates nothing but is the driver-owned `-R`/`--rpath`
            // family, so the CLI's `-Wl` parser refuses it, and so does
            // `run_link`'s own option check when a caller states the group
            // itself. Nothing is written.
            assert!(
                trust_cg_codegen::link_driver::parse_wl_group(
                    &just_symbols,
                    TargetSpec::parse(HOST).unwrap()
                )
                .is_err()
            );
            let mut request = shared("just-symbols", vec![start.clone()], &[]);
            request.linker_arg_groups.push(vec![just_symbols.clone()]);
            match run_link(&request, &driver) {
                Err(LinkError::Refused(refusals)) => assert!(
                    refusals
                        .iter()
                        .any(|refusal| refusal.flag.contains("--just-symbols")),
                    "{linker}: {refusals:?}"
                ),
                other => {
                    panic!("{linker} just-symbols: expected the option refusal, got {other:?}")
                }
            }
            assert!(!request.output.exists(), "{linker} just-symbols");
            // Refused after the link (gold links them; GNU ld and LLD refuse
            // them themselves): the verifier's `-Wl` operand under
            // `--defsym`, a `--wrap` of the linker-defined name, and a
            // positional linker script, which no option shows, through the
            // image's dynamic symbol table.
            for (name, objects, groups, how) in [
                (
                    "defsym-operand",
                    vec![stub.clone()],
                    vec![defsym, start_operand.as_str()],
                    format!("the -Wl option `{defsym}` can"),
                ),
                (
                    "wrap-start",
                    vec![stub.clone()],
                    vec![
                        "--wrap=__start_tcgsec",
                        start_operand.as_str(),
                        wrap_start_operand.as_str(),
                    ],
                    "the -Wl option `--wrap=__start_tcgsec` can".to_string(),
                ),
                (
                    "script",
                    vec![start.clone(), script.clone()],
                    Vec::new(),
                    "the output's dynamic symbol table exports `__start_tcgsec` with default \
                     visibility"
                        .to_string(),
                ),
            ] {
                let request = shared(name, objects, &groups);
                match run_link(&request, &driver) {
                    Err(LinkError::OutputRefused {
                        removed,
                        diagnostics,
                        ..
                    }) => {
                        assert!(removed, "{linker} {name}");
                        let refused: Vec<&LinkDiagnostic> = diagnostics
                            .iter()
                            .filter(|diagnostic| {
                                diagnostic
                                    .line
                                    .starts_with("[TCG-LINK-PREEMPTIBLE-DIRECT] ")
                            })
                            .collect();
                        assert_eq!(refused.len(), 1, "{linker} {name}: {diagnostics:#?}");
                        assert_eq!(refused[0].subject.as_deref(), Some("__start_tcgsec"));
                        assert!(
                            refused[0].line.contains(&how),
                            "{linker} {name}: {}",
                            refused[0].line
                        );
                    }
                    Err(LinkError::Failed(failure)) => {
                        assert_ne!(linker, "gold", "gold links {name}: {}", failure.stderr);
                        assert!(
                            failure.stderr.contains("recompile with -fPIC"),
                            "{linker} {name}: {}",
                            failure.stderr
                        );
                    }
                    other => panic!("{linker} {name}: must not link: {other:?}"),
                }
                assert!(!request.output.exists(), "{linker} {name}");
                assert_eq!(staging_left(dir), Vec::<String>::new(), "{linker} {name}");
            }
            // The controls link: the linker binds `__start_tcgsec`,
            // `__stop_tcgsec` and `__ehdr_start` inside the output unless an
            // option says otherwise, so each refusal above is the option's.
            for (name, object, groups) in [
                ("plain", &start, Vec::new()),
                (
                    "protected",
                    &start,
                    vec!["-z,start-stop-visibility=protected"],
                ),
                ("plain-stop", &stop, Vec::new()),
                ("plain-ehdr", &ehdr, Vec::new()),
            ] {
                let request = shared(name, vec![object.clone()], &groups);
                run_link(&request, &driver)
                    .unwrap_or_else(|error| panic!("{linker} {name}: {error}"));
                assert!(request.output.is_file(), "{linker} {name}");
            }
            // The `-fPIC` twins link under the same options, and the
            // library takes an `-rdynamic` executable's definition of the
            // name it exports.
            for (name, objects, groups, defined, get) in [
                (
                    "defsym-pic",
                    vec![start_pic.clone()],
                    vec![defsym],
                    "__start_tcgsec",
                    "tcg_start",
                ),
                (
                    "wrap-pic",
                    vec![foo_ref_pic.clone(), foo_hidden.clone(), wrap_foo.clone()],
                    vec!["--wrap=foo"],
                    "__wrap_foo",
                    "tcg_get",
                ),
            ] {
                let request = shared(name, objects, &groups);
                run_link(&request, &driver)
                    .unwrap_or_else(|error| panic!("{linker} {name}: {error}"));
                let main = cc_object(
                    dir,
                    &format!("{name}_main"),
                    "c",
                    &format!(
                        "char {defined}[16] = \"exe\";\nextern char *{get}(void);\nint \
                         main(void) {{ return {get}() == {defined} ? 0 : 1; }}\n"
                    ),
                );
                let program = dir.join(format!("{name}-main-{linker}"));
                let mut consumer = with_wl(
                    executable(vec![main, request.output.clone()], program.clone()),
                    "--export-dynamic",
                );
                consumer.rpaths = vec![dir.display().to_string()];
                run_link(&consumer, "cc")
                    .unwrap_or_else(|error| panic!("{linker} {name} user: {error}"));
                assert_eq!(run(&program), Some(0), "{linker} {name}: one {defined}");
            }
        }
    }

    /// The r1105 verifier's `br.s` (2026-11-05), with one target per
    /// branch: default-visibility functions `ext_cbz`, `ext_tbz` and `ext_b`
    /// (each 7), `call_cbz` (`CBZ`, `R_AARCH64_CONDBR19`) and `call_tbz`
    /// (`TBZ`, `R_AARCH64_TSTBR14`) when `conditional`, and always `call_b`
    /// (`B`, `JUMP26`) and `call_bl` (`BL`, `CALL26`) to `ext_b`. `hidden`
    /// gives the two conditional targets hidden visibility.
    fn branch_source(conditional: bool, hidden: bool) -> String {
        let function = |name: &str, body: &str| {
            format!(
                "\t.globl {name}\n\t.type {name},%function\n{name}:\n{body}\t.size {name}, \
                 .-{name}\n"
            )
        };
        let mut source = String::from("\t.text\n");
        let mut targets = vec!["ext_b"];
        if conditional {
            targets.extend(["ext_cbz", "ext_tbz"]);
        }
        for target in &targets {
            source.push_str(&function(target, "\tmov x0, #7\n\tret\n"));
        }
        if conditional {
            source.push_str(&function(
                "call_cbz",
                "\tmov x0, #0\n\tcbz x0, ext_cbz\n\tmov x0, #99\n\tret\n",
            ));
            source.push_str(&function(
                "call_tbz",
                "\tmov x0, #0\n\ttbz w0, #3, ext_tbz\n\tmov x0, #98\n\tret\n",
            ));
            if hidden {
                source.push_str("\t.hidden ext_cbz\n\t.hidden ext_tbz\n");
            }
        }
        source.push_str(&function("call_b", "\tb ext_b\n"));
        source.push_str(&function(
            "call_bl",
            "\tstp x29, x30, [sp, #-16]!\n\tbl ext_b\n\tldp x29, x30, [sp], #16\n\tret\n",
        ));
        source.push_str("\t.section .note.GNU-stack,\"\",@progbits\n");
        source
    }

    /// A local-dynamic access of the default-visibility thread-local `tv`
    /// (7) when `local_dynamic` (a TLS descriptor of `_TLS_MODULE_BASE_`
    /// plus `TLSLD_ADD_DTPREL_HI12`/`_LO12_NC` of `tv`), else a descriptor
    /// access of `tv` itself; either way `get_tv` returns what it reads.
    fn tls_source(local_dynamic: bool) -> String {
        let (base, offset) = if local_dynamic {
            (
                "_TLS_MODULE_BASE_",
                "\tadd x0, x0, #:dtprel_hi12:tv\n\tadd x0, x0, #:dtprel_lo12_nc:tv\n",
            )
        } else {
            ("tv", "")
        };
        format!(
            "\t.text\n\t.globl get_tv\n\t.type get_tv,%function\nget_tv:\n\tstp x29, x30, [sp, \
             -16]!\n\tmov x29, sp\n\tadrp x0, :tlsdesc:{base}\n\tldr x1, [x0, \
             #:tlsdesc_lo12:{base}]\n\tadd x0, x0, :tlsdesc_lo12:{base}\n\t.tlsdesccall \
             {base}\n\tblr x1\n{offset}\tmrs x1, tpidr_el0\n\tldr x0, [x1, x0]\n\tldp x29, x30, \
             [sp], 16\n\tret\n\t.size get_tv, .-get_tv\n\t.globl tv\n\t.section \
             .tdata,\"awT\",@progbits\n\t.p2align 3\n\t.type tv,%object\n\t.size tv, \
             8\ntv:\n\t.xword 7\n\t.section .note.GNU-stack,\"\",@progbits\n"
        )
    }

    /// r1105 repair (2026-11-05): the r1105 verifier's LOW fail-open. GNU ld
    /// 2.42 and gold 2.42 resolve a `CBZ` (`R_AARCH64_CONDBR19`) and a `TBZ`
    /// (`R_AARCH64_TSTBR14`) to a default-visibility function the same
    /// `-shared` link defines straight to that definition (no PLT) while
    /// exporting it `GLOBAL DEFAULT`, and a local-dynamic access of a
    /// default-visibility thread-local to the library's own TLS block; the
    /// driver installed both libraries, and an `-rdynamic` executable's
    /// interposing definition was ignored (7 where 55 was expected). Refused
    /// now on every linker: before the link when the object is positional,
    /// and from the input trace when it is a `-Wl` operand (LLD links the
    /// branches through the PLT and refuses the `DTPREL` forms itself). The
    /// controls link and take the executable's definition: `B` and `BL`
    /// (`JUMP26`/`CALL26`, routed through the PLT) and a descriptor access
    /// of the thread-local; and the conditional branches to hidden targets
    /// link.
    #[test]
    fn conditional_branches_and_local_dynamic_tls_to_preemptible_symbols_are_refused() {
        use trust_cg_codegen::link_driver::{LinkError, run_link};
        let dir = scratch("tcg-linux-preemptible-branch-");
        let dir = dir.path();
        let branches = cc_object(dir, "branches", "s", &branch_source(true, false));
        let hidden = cc_object(dir, "branches_hidden", "s", &branch_source(true, true));
        let jumps = cc_object(dir, "jumps", "s", &branch_source(false, false));
        let local_dynamic = cc_object(dir, "tls_ld", "s", &tls_source(true));
        let descriptor = cc_object(dir, "tls_desc", "s", &tls_source(false));
        for (object, symbol, kind) in [
            (&branches, "ext_cbz", 280),
            (&branches, "ext_tbz", 279),
            (&local_dynamic, "tv", 528),
            (&local_dynamic, "tv", 530),
        ] {
            let records = read_object_records(&fs::read(object).unwrap()).unwrap();
            assert!(
                records.relocations.iter().any(|relocation| {
                    relocation.record.reloc_type == kind
                        && records.symbols[relocation.record.symbol_index as usize].name == symbol
                }),
                "the object's reference to {symbol} is relocation {kind}"
            );
        }
        let stub = cc_object_with(
            dir,
            "stub",
            "c",
            "int tcg_stub(void) { return 1; }\n",
            &["-fPIC"],
        );
        let refused_subjects = |diagnostics: &[LinkDiagnostic]| -> BTreeSet<(String, String)> {
            diagnostics
                .iter()
                .filter(|diagnostic| {
                    diagnostic
                        .line
                        .starts_with("[TCG-LINK-PREEMPTIBLE-DIRECT] ")
                })
                .map(|diagnostic| {
                    (
                        diagnostic.subject.clone().unwrap_or_default(),
                        diagnostic.relocation.clone().unwrap_or_default(),
                    )
                })
                .collect()
        };
        let branch_refusals = BTreeSet::from([
            ("ext_cbz".to_string(), "R_AARCH64_CONDBR19".to_string()),
            ("ext_tbz".to_string(), "R_AARCH64_TSTBR14".to_string()),
        ]);
        let tls_refusals = BTreeSet::from([(
            "tv".to_string(),
            "R_AARCH64_TLSLD_ADD_DTPREL_HI12".to_string(),
        )]);
        for (linker, driver) in linker_drivers(dir) {
            let shared = |name: &str, objects: Vec<PathBuf>, operand: Option<&Path>| {
                let mut request = executable(objects, dir.join(format!("lib{name}-{linker}.so")));
                request.kind = LinkOutputKind::SharedLibrary;
                if let Some(operand) = operand {
                    request = with_wl(request, &operand.display().to_string());
                }
                request
            };
            // Positional: refused before the linker runs.
            for (name, object, expected) in [
                ("branches", &branches, &branch_refusals),
                ("tls-ld", &local_dynamic, &tls_refusals),
            ] {
                let request = shared(name, vec![object.clone()], None);
                match run_link(&request, &driver) {
                    Err(LinkError::InputRefused(diagnostics)) => {
                        assert_eq!(
                            &refused_subjects(&diagnostics),
                            expected,
                            "{linker} {name}: {diagnostics:#?}"
                        );
                        assert_eq!(
                            refused_subjects(&diagnostics).len(),
                            diagnostics.len(),
                            "{linker} {name}: {diagnostics:#?}"
                        );
                    }
                    other => {
                        panic!("{linker} {name}: expected the pre-link refusal, got {other:?}")
                    }
                }
                assert!(!request.output.exists(), "{linker} {name}");
            }
            // A `-Wl` operand beside a `-fPIC` positional object (the
            // verifier's CLI route): read from the input trace after the
            // link and the image removed.
            for (name, object, expected) in [
                ("branches-operand", &branches, &branch_refusals),
                ("tls-ld-operand", &local_dynamic, &tls_refusals),
            ] {
                let request = shared(name, vec![stub.clone()], Some(object));
                match run_link(&request, &driver) {
                    Err(LinkError::OutputRefused {
                        removed,
                        diagnostics,
                        ..
                    }) => {
                        assert!(removed, "{linker} {name}");
                        assert_eq!(
                            &refused_subjects(&diagnostics),
                            expected,
                            "{linker} {name}: {diagnostics:#?}"
                        );
                        assert!(
                            diagnostics
                                .iter()
                                .filter(|diagnostic| diagnostic
                                    .line
                                    .starts_with("[TCG-LINK-PREEMPTIBLE-DIRECT] "))
                                .all(|diagnostic| diagnostic
                                    .line
                                    .contains("its input trace names it")),
                            "{linker} {name}: {diagnostics:#?}"
                        );
                    }
                    Err(LinkError::Failed(failure)) => {
                        assert!(
                            linker == "lld" && name == "tls-ld-operand",
                            "{linker} {name} must link: {}",
                            failure.stderr
                        );
                        assert!(
                            failure.stderr.contains("unknown relocation"),
                            "{linker} {name}: {}",
                            failure.stderr
                        );
                    }
                    other => panic!("{linker} {name}: must not link: {other:?}"),
                }
                assert!(!request.output.exists(), "{linker} {name}");
                assert_eq!(staging_left(dir), Vec::<String>::new(), "{linker} {name}");
            }
            // Conditional branches to hidden targets are link-time constants.
            let request = shared("branches-hidden", vec![hidden.clone()], None);
            run_link(&request, &driver)
                .unwrap_or_else(|error| panic!("{linker} branches-hidden: {error}"));
            assert!(request.output.is_file(), "{linker} branches-hidden");
            // `B`/`BL` and the descriptor access link, and the library takes
            // an `-rdynamic` executable's definition (55).
            for (name, object, user) in [
                (
                    "jumps",
                    &jumps,
                    "long ext_b(void) { return 55; }\nextern long call_b(void);\nextern long \
                     call_bl(void);\nint main(void) { return call_b() == 55 && call_bl() == 55 \
                     ? 0 : 1; }\n",
                ),
                (
                    "tls-desc",
                    &descriptor,
                    "__thread long tv = 55;\nextern long get_tv(void);\nint main(void) { return \
                     get_tv() == 55 ? 0 : 1; }\n",
                ),
            ] {
                let request = shared(name, vec![object.clone()], None);
                run_link(&request, &driver)
                    .unwrap_or_else(|error| panic!("{linker} {name}: {error}"));
                let main = cc_object(dir, &format!("{name}_main_{linker}"), "c", user);
                let program = dir.join(format!("{name}-main-{linker}"));
                let mut consumer = with_wl(
                    executable(vec![main, request.output.clone()], program.clone()),
                    "--export-dynamic",
                );
                consumer.rpaths = vec![dir.display().to_string()];
                run_link(&consumer, "cc")
                    .unwrap_or_else(|error| panic!("{linker} {name} user: {error}"));
                assert_eq!(
                    run(&program),
                    Some(0),
                    "{linker} {name}: the executable's definition"
                );
            }
        }
    }

    /// The L02-P2 round-2 verifier's library (2026-10-24): a hidden datum,
    /// a default-visibility `rp_fn` (7) and `cp_call` = `rp_fn() + 3`.
    const CALLPRE: &str = r#"module "callpre"
target "aarch64-unknown-linux-gnu" 8 little
functy.0 = () -> (u64)
global mut visibility(hidden) @cp_hidden u64 = 3
fn @rp_fn(functy.0) {
bb0:
    %0 = const u64 7
    ret %0
}
fn @cp_call(functy.0) {
bb0:
    %0 = call @func.0()
    %1 = global_addr @global.0
    %2 = load u64, ptr %1
    %3 = add u64 %0, %2
    ret %3
}
"#;

    /// L02-P2 round 2 (2026-10-24): a `static`-model [`CALLPRE`] at O2 has
    /// `rp_fn` inlined into `cp_call` and addresses only its hidden datum
    /// directly, so no relocation is left for `[TCG-LINK-PREEMPTIBLE-DIRECT]`.
    /// A link that states the objects' model
    /// (`LinkRequest::compiled_relocation_model`, as the CLI does) is refused
    /// by name for each default-visibility definition, before the linker on
    /// a shared-object request and, when a C driver links `-shared` itself
    /// for an executable request, after it, with the image removed
    /// (`[TCG-LINK-PREEMPTIBLE-DEFINITION]`), on GNU ld, gold and LLD. The
    /// same objects link into an executable that runs, and a request that
    /// states no model is not refused for them (the driver does not know
    /// how foreign code was compiled).
    #[test]
    fn default_visibility_definitions_of_static_objects_are_refused_in_a_shared_object() {
        use trust_cg_codegen::RelocationModel;
        use trust_cg_codegen::link_driver::{LinkError, run_link};
        let dir = scratch("tcg-linux-non-pic-definition-");
        let dir = dir.path();
        let module = trust_cg_codegen::pipeline::parse_trust_ir_text(CALLPRE).unwrap();
        let object = dir.join("callpre-static.o");
        fs::write(
            &object,
            try_compile_with(&module, HOST, |config| {
                config.relocation_model = RelocationModel::Static;
                config.opt_level = trust_cg_codegen::pipeline::OptLevel::O2;
            })
            .unwrap(),
        )
        .unwrap();
        let main = cc_object(
            dir,
            "cp_main",
            "c",
            "extern unsigned long cp_call(void);\nint main(void) { return cp_call() == 10 ? 0 : \
             1; }\n",
        );
        let subjects = |diagnostics: &[LinkDiagnostic]| -> BTreeSet<String> {
            diagnostics
                .iter()
                .filter(|diagnostic| {
                    diagnostic
                        .line
                        .starts_with("[TCG-LINK-PREEMPTIBLE-DEFINITION] ")
                })
                .filter_map(|diagnostic| {
                    assert_eq!(diagnostic.kind, LinkDiagnosticKind::NonPicDefinition);
                    diagnostic.subject.clone()
                })
                .collect()
        };
        let both = BTreeSet::from(["cp_call".to_string(), "rp_fn".to_string()]);
        for (linker, driver) in linker_drivers(dir) {
            // A shared-object request: refused before the linker.
            let mut shared =
                executable(vec![object.clone()], dir.join(format!("libcp-{linker}.so")));
            shared.kind = LinkOutputKind::SharedLibrary;
            shared.compiled_relocation_model = Some(RelocationModel::Static);
            match run_link(&shared, &driver) {
                Err(LinkError::InputRefused(diagnostics)) => {
                    assert_eq!(subjects(&diagnostics), both, "{linker}: {diagnostics:#?}");
                    assert_eq!(diagnostics.len(), 2, "{linker}: {diagnostics:#?}");
                }
                other => panic!("{linker}: expected the pre-link refusal, got {other:?}"),
            }
            assert!(!shared.output.exists(), "{linker}");
            // Before the repair: the request names no model, nothing is
            // refused, and the library is installed on every linker.
            shared.compiled_relocation_model = None;
            run_link(&shared, &driver).unwrap_or_else(|error| panic!("{linker}: {error}"));
            assert!(shared.output.is_file(), "{linker}");

            // An executable request a C driver links `-shared` itself:
            // refused after the link, and the image is removed.
            let steering = dir.join(format!("shared-{linker}.sh"));
            let status = Command::new("/bin/sh")
                .arg("-c")
                .arg("printf '%s\\n' \"$2\" > \"$1\" && chmod 755 \"$1\"")
                .arg("sh")
                .arg(&steering)
                .arg(format!("#!/bin/sh\nexec {driver} -shared \"$@\""))
                .status()
                .unwrap();
            assert!(status.success());
            let mut steered = executable(
                vec![object.clone()],
                dir.join(format!("cp-steered-{linker}")),
            );
            steered.compiled_relocation_model = Some(RelocationModel::Static);
            match run_link(&steered, &steering.display().to_string()) {
                Err(LinkError::OutputRefused {
                    removed,
                    diagnostics,
                    ..
                }) => {
                    assert!(removed, "{linker}");
                    assert_eq!(subjects(&diagnostics), both, "{linker}: {diagnostics:#?}");
                    assert!(
                        diagnostics
                            .iter()
                            .filter(|diagnostic| diagnostic.kind
                                == LinkDiagnosticKind::NonPicDefinition)
                            .all(|diagnostic| diagnostic.line.contains(&format!(
                                "the output for {} (an ELF shared object",
                                steered.output.display()
                            ))),
                        "{linker}: {diagnostics:#?}"
                    );
                }
                other => panic!("{linker}: expected the post-link refusal, got {other:?}"),
            }
            assert!(!steered.output.exists(), "{linker}");
            assert_eq!(staging_left(dir), Vec::<String>::new(), "{linker}");

            // The executable twin links and runs.
            let program = dir.join(format!("cp-main-{linker}"));
            let mut request = executable(vec![main.clone(), object.clone()], program.clone());
            request.compiled_relocation_model = Some(RelocationModel::Static);
            request.position_independence = PositionIndependence::NoPie;
            run_link(&request, &driver).unwrap_or_else(|error| panic!("{linker}: {error}"));
            assert_eq!(run(&program), Some(0), "{linker}");
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
