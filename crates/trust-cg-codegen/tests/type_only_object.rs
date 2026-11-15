// Copyright 2026 Andrew Yates | Apache-2.0
//! Type declarations can produce an unverified AArch64 object without
//! inventing executable functions, discarding input, or claiming proofs.
use trust_cg_codegen::{
    CompileError, Compiler, CompilerConfig, pipeline::OptLevel, target::TargetSpec,
};
use trust_ir::{
    BlockId, Constant, FuncId, FuncTy, Function, Global, Linkage, Module, Ty, Visibility,
};

#[path = "common/pinned_target.rs"]
mod pinned_target;

fn fixture() -> Module {
    serde_json::from_str(include_str!(
        "../../../tests/fixtures/trust_ir_binary_container/conformance/single_inhabited_enums.json"
    ))
    .unwrap()
}
fn compiler(triple: &str, opt_level: OptLevel, emit_proofs: bool) -> Compiler {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            emit_proofs,
            emit_debug: false,
            parallel: false,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple).unwrap(),
    )
}

#[test]
fn type_declarations_emit_checked_objects_without_code_or_proofs() {
    for triple in ["aarch64-apple-darwin", "aarch64-unknown-linux-gnu"] {
        for opt in [OptLevel::O0, OptLevel::O3] {
            let result = compiler(triple, opt, false).compile(&fixture()).unwrap();
            assert_eq!(result.metrics.function_count, 0);
            assert_eq!(result.metrics.instruction_count, 0);
            assert_eq!(result.metrics.code_size_bytes, 0);
            assert!(result.proofs.is_none());
            assert!(result.certified_pass_chain.is_none());
            assert!(result.proof_optimization_certificates.is_empty());
            assert!(result.aarch64_frame_inputs.is_empty());
            if triple.ends_with("darwin") {
                let records =
                    trust_cg_codegen::macho::reparse::read_object_records(&result.object_code)
                        .unwrap();
                assert_eq!(records.cputype, 0x0100000c);
                assert!(
                    records
                        .sections
                        .iter()
                        .filter(|s| s.flags & 0x80000400 != 0)
                        .all(|s| s.size == 0)
                );
                assert!(records.symbols.iter().all(|s| !s.is_section_definition()));
                assert!(records.section_relocations.iter().all(Vec::is_empty));
            } else {
                let records =
                    trust_cg_codegen::elf::reparse::read_object_records(&result.object_code)
                        .unwrap();
                assert_eq!(records.machine, 183);
                assert!(
                    records
                        .sections
                        .iter()
                        .filter(|s| s.sh_flags & 4 != 0)
                        .all(|s| s.size == 0)
                );
                assert!(records.symbols.iter().all(|s| s.symbol_type != 2));
                assert!(records.relocations.is_empty());
            }
        }
    }
}

#[test]
fn empty_input_proof_requests_jit_and_other_dispatchers_still_refuse() {
    let darwin = compiler("aarch64-apple-darwin", OptLevel::O0, false);
    assert!(matches!(
        darwin.compile(&Module::new("empty")),
        Err(CompileError::EmptyModule)
    ));
    assert!(matches!(
        compiler("aarch64-apple-darwin", OptLevel::O0, true).compile(&fixture()),
        Err(CompileError::EmptyModule)
    ));
    #[cfg(feature = "verify")]
    assert!(matches!(
        compiler("aarch64-apple-darwin", OptLevel::O0, false)
            .with_production_certified_pass_chain()
            .compile(&fixture()),
        Err(CompileError::EmptyModule)
    ));
    for triple in ["x86_64-apple-darwin", "riscv64-unknown-linux-gnu"] {
        assert!(matches!(
            compiler(triple, OptLevel::O0, false).compile(&fixture()),
            Err(CompileError::EmptyModule)
        ));
    }
    #[cfg(target_arch = "aarch64")]
    assert!(matches!(
        darwin.compile_module_to_jit(&fixture(), &std::collections::HashMap::new()),
        Err(CompileError::EmptyModule)
    ));
}

#[test]
fn declared_functions_and_global_data_cannot_disappear_into_type_only_objects() {
    let driver = compiler("aarch64-apple-darwin", OptLevel::O0, false);
    let mut declared = fixture();
    let signature = declared
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    let mut function = Function::new(FuncId::new(0), "external_body", signature, BlockId::new(0));
    function.blocks.clear();
    declared.try_add_function(function).unwrap();
    pinned_target::pin(&mut declared, "aarch64-apple-darwin");
    assert!(trust_ir_build::validate_module(&declared).is_empty());
    assert!(matches!(
        driver.compile(&declared),
        Err(CompileError::EmptyModule)
    ));
    let mut data = fixture();
    data.globals.push(Global {
        name: "retained_data".into(),
        ty: Ty::U32,
        mutable: false,
        initializer: Some(Constant::Int(1)),
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: true,
    });
    assert!(matches!(
        driver.compile(&data),
        Err(CompileError::EmptyModule)
    ));
}

#[test]
fn malformed_unused_type_declarations_still_fail_ingestion() {
    let mut module = fixture();
    module.enums[1].layout.as_mut().unwrap().encoding =
        trust_ir::EnumTagEncoding::SingleInhabited { variant: 2 };
    assert!(!trust_ir_build::validate_module(&module).is_empty());
    let error = compiler("aarch64-apple-darwin", OptLevel::O0, false)
        .compile(&module)
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("trust-ir codegen admission refused the module"),
        "{error}"
    );
    assert!(
        error
            .to_string()
            .contains("inactive single-inhabited variant"),
        "{error}"
    );
}
