use std::collections::HashMap;
use std::fmt::Display;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::{CodegenLicensePolicy, UnlicensedBodyPolicy, wasm};
use trust_ir::{
    Block, BlockId, BodyGate, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty,
    ValueId,
};

fn literal_return() -> Module {
    let mut module = Module::new("v41_codegen_metadata");
    let signature = module
        .add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "answer", signature, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(42),
        })
        .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    function.blocks.push(block);
    module.functions.push(function);
    module
}

/// The fixture carries no codegen license (`body_gate: None`), which every
/// lane REFUSES by default (roadmap WS7.5, DG-73) — before the metadata this
/// file is about. The metadata lanes therefore state `Permit`;
/// `legacy_metadata_absence_is_refused_by_default_and_compiles_under_permit`
/// pins the default.
fn permit() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit)
}

fn wasm_compile(module: &Module) -> Result<Vec<u8>, wasm::WasmLowerError> {
    wasm::compile_module_with_policy_and_license(
        module,
        &wasm::WasmModulePolicy::closed(),
        &permit(),
    )
}

fn refused<T, E: Display>(result: Result<T, E>, case: usize) {
    match result {
        Err(error) => assert!(
            error.to_string().contains(
                [
                    "ungated",
                    "unrecognized producer",
                    "global_asm",
                    "naked",
                    "sve"
                ][case]
            ),
            "{error}"
        ),
        Ok(_) => panic!("unsupported codegen metadata reached artifact production"),
    }
}

fn set_unsupported_metadata(module: &mut Module, case: usize) {
    match case {
        0 => module.functions[0].body_gate = Some(BodyGate::Ungated),
        1 => {
            module.functions[0].body_gate = Some(BodyGate::gated("unrecognized producer"));
        }
        2 => module.global_asm.push(".globl unhandled_symbol".into()),
        3 => module.functions[0].attrs.naked = true,
        _ => module.functions[0].attrs.target_features.push("sve".into()),
    }
}

#[test]
fn aot_and_host_jit_refuse_metadata_before_artifact_or_cache_use() {
    let compiler = Compiler::new(CompilerConfig::default()).with_codegen_license(permit());
    for case in 0..5 {
        let mut module = literal_return();
        set_unsupported_metadata(&mut module, case);
        refused(compiler.compile(&module), case);
        refused(
            compiler.compile_module_to_jit(&module, &HashMap::new()),
            case,
        );
    }
}

#[test]
fn wasm_module_refuses_the_same_codegen_metadata() {
    for case in 0..5 {
        let mut module = literal_return();
        module.target_info = Some(wasm::wasm32_target_info());
        set_unsupported_metadata(&mut module, case);
        refused(wasm_compile(&module), case);
    }
}

#[test]
fn wasm_single_function_checks_the_argument_and_its_module_context() {
    for case in 0..5 {
        let mut context = literal_return();
        context.target_info = Some(wasm::wasm32_target_info());
        let mut source = context.clone();
        set_unsupported_metadata(&mut source, case);
        // Pass the altered body separately. Only module-level assembly comes
        // from the context, so checking either argument alone is insufficient.
        if case == 2 {
            context.global_asm = source.global_asm.clone();
        }
        let mut output = wasm::WasmModule::new();
        let before = output.finish();
        refused(
            wasm::lower_function_with_license(
                &mut output,
                &source.functions[0],
                &context,
                wasm::WasmFunctionEnv::empty(),
                &permit(),
            ),
            case,
        );
        assert_eq!(output.finish(), before, "case {case} modified output");
    }
}

#[test]
fn wasm_single_function_cannot_emit_an_available_external_body() {
    let mut context = literal_return();
    context.target_info = Some(wasm::wasm32_target_info());
    let mut function = context.functions[0].clone();
    function.linkage = trust_ir::Linkage::AvailableExternally;
    let mut output = wasm::WasmModule::new();
    let before = output.finish();
    let error = wasm::lower_function_with_license(
        &mut output,
        &function,
        &context,
        wasm::WasmFunctionEnv::empty(),
        &permit(),
    )
    .unwrap_err();
    assert!(matches!(error, wasm::WasmLowerError::UnboundDeclaration(_)));
    assert_eq!(output.finish(), before);
}

/// DG-73: the legacy ABSENCE of a codegen license is refused by default on
/// the AOT, JIT and wasm lanes, and compiles only under an explicit `Permit`.
#[test]
fn legacy_metadata_absence_is_refused_by_default_and_compiles_under_permit() {
    let mut module = literal_return();
    let default = Compiler::new(CompilerConfig::default());
    for error in [
        default.compile(&module).err().map(|e| e.to_string()),
        default
            .compile_module_to_jit(&module, &HashMap::new())
            .err()
            .map(|e| e.to_string()),
    ] {
        let error = error.expect("the default refuses a claim-less body");
        assert!(error.contains("carries no codegen license"), "{error}");
    }
    let compiler = Compiler::new(CompilerConfig::default()).with_codegen_license(permit());
    assert!(compiler.compile(&module).is_ok());
    module.target_info = Some(wasm::wasm32_target_info());
    let error = wasm::compile_module(&module).expect_err("the wasm default refuses it too");
    assert!(
        error.to_string().contains("carries no codegen license"),
        "{error}"
    );
    assert!(wasm_compile(&module).is_ok());
}
