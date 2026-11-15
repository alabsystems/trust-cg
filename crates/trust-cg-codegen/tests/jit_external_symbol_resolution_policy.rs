// End-to-end coverage for typed JIT external-symbol resolution policy.

#![cfg(any(
    all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")),
    all(
        target_arch = "x86_64",
        any(target_os = "macos", target_os = "linux", target_os = "windows")
    )
))]

use std::collections::HashMap;

use trust_cg_codegen::{
    CompileError, Compiler, CompilerConfig, JitError, JitExternalSymbolResolutionPolicy,
};
use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Linkage, Module, Ty,
    ValueId,
};

#[cfg(unix)]
const PROCESS_VISIBLE_FUNCTION: &str = "getpid";
#[cfg(windows)]
const PROCESS_VISIBLE_FUNCTION: &str = "GetCurrentProcessId";

fn external_call_module(symbol: &str) -> Module {
    let mut module = Module::new("jit_external_symbol_policy");
    // The bodyless declaration is an FFI boundary, so the module pins the
    // host target it is JIT-compiled for: every ingestion entry refuses what
    // trust-ir's validator refuses (`TargetInfoRequired`, WS7.3).
    module.target_info = Some(
        trust_cg_codegen::CoreHostJitTarget::detect()
            .expect("supported JIT host")
            .trust_ir_target_info()
            .clone(),
    );
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    let mut declaration = Function::new(FuncId::new(0), symbol, signature, BlockId::new(0));
    declaration.linkage = Linkage::External;
    declaration.blocks.clear();
    module
        .try_add_function(declaration)
        .expect("Module::try_add_function: test fixture");

    let mut entry = Function::new(FuncId::new(1), "entry", signature, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![],
        })
        .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    entry.blocks.push(block);
    module
        .try_add_function(entry)
        .expect("Module::try_add_function: test fixture");
    module
}

fn exact_internal_call_module() -> Module {
    let mut module = Module::new("jit_exact_internal_symbol_policy");
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    let mut target = Function::new(
        FuncId::new(0),
        "module_local_target",
        signature,
        BlockId::new(0),
    );
    target.linkage = Linkage::Internal;
    let mut target_block = Block::new(BlockId::new(0));
    target_block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(7),
        })
        .with_result(ValueId::new(0)),
    );
    target_block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    target.blocks.push(target_block);
    module
        .try_add_function(target)
        .expect("Module::try_add_function: test fixture");

    let mut entry = Function::new(FuncId::new(1), "entry", signature, BlockId::new(0));
    let mut entry_block = Block::new(BlockId::new(0));
    entry_block.body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![],
        })
        .with_result(ValueId::new(0)),
    );
    entry_block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    entry.blocks.push(entry_block);
    module
        .try_add_function(entry)
        .expect("Module::try_add_function: test fixture");
    module
}

fn compiler(policy: JitExternalSymbolResolutionPolicy) -> Compiler {
    Compiler::new(CompilerConfig {
        jit_external_symbol_resolution: policy,
        ..CompilerConfig::for_host_jit_unchecked()
    })
    .with_codegen_license(permit_unlicensed())
}

extern "C" fn hostile_same_name_override() -> u32 {
    99
}

#[test]
fn explicit_only_rejects_absent_process_visible_symbol() {
    assert!(
        trust_cg_codegen::jit::lookup_process_symbol(PROCESS_VISIBLE_FUNCTION).is_some(),
        "fixture requires a process-visible symbol"
    );

    let error = compiler(JitExternalSymbolResolutionPolicy::ExplicitOnly)
        .compile_module_to_jit(
            &external_call_module(PROCESS_VISIBLE_FUNCTION),
            &HashMap::new(),
        )
        .expect_err("ExplicitOnly must not fall back to the process symbol table");
    assert!(
        matches!(
            error,
            CompileError::Jit(JitError::UnresolvedSymbol(ref symbol))
                if symbol == PROCESS_VISIBLE_FUNCTION
        ),
        "unexpected explicit-only rejection: {error}"
    );
}

#[test]
fn explicit_only_accepts_supplied_pointer() {
    let pointer = trust_cg_codegen::jit::lookup_process_symbol(PROCESS_VISIBLE_FUNCTION)
        .expect("process-visible fixture symbol");
    let bindings = HashMap::from([(PROCESS_VISIBLE_FUNCTION.to_string(), pointer)]);

    compiler(JitExternalSymbolResolutionPolicy::ExplicitOnly)
        .compile_module_to_jit(&external_call_module(PROCESS_VISIBLE_FUNCTION), &bindings)
        .expect("an explicitly supplied external capability must resolve");
}

#[test]
fn explicit_only_rejects_null_supplied_pointer() {
    let bindings = HashMap::from([(PROCESS_VISIBLE_FUNCTION.to_string(), std::ptr::null())]);

    let error = compiler(JitExternalSymbolResolutionPolicy::ExplicitOnly)
        .compile_module_to_jit(&external_call_module(PROCESS_VISIBLE_FUNCTION), &bindings)
        .expect_err("a null pointer is not an external capability");
    assert!(
        matches!(
            error,
            CompileError::Jit(JitError::UnresolvedSymbol(ref symbol))
                if symbol == PROCESS_VISIBLE_FUNCTION
        ),
        "unexpected null-binding rejection: {error}"
    );
}

#[test]
fn compatibility_default_still_uses_process_fallback() {
    Compiler::new(CompilerConfig::for_host_jit_unchecked())
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(
            &external_call_module(PROCESS_VISIBLE_FUNCTION),
            &HashMap::new(),
        )
        .expect("the compatibility default must retain process-symbol fallback");
}

#[test]
fn explicit_only_never_interposes_exact_internal_symbol() {
    let bindings = HashMap::from([(
        "module_local_target".to_string(),
        hostile_same_name_override as *const () as *const u8,
    )]);
    let result = compiler(JitExternalSymbolResolutionPolicy::ExplicitOnly)
        .compile_module_to_jit(&exact_internal_call_module(), &bindings)
        .expect("exact module-local call must remain internal");
    let entry = unsafe {
        result
            .buffer
            .get_fn_bound::<extern "C" fn() -> u32>("entry")
            .expect("entry symbol")
    };

    assert_eq!(
        entry.as_ref()(),
        7,
        "explicit binding interposed exact call"
    );
}

/// `my_rem(a, b) = a frem b` beside `definition`, a trust-ir text fragment.
fn frem_module_with(definition: &str) -> Module {
    trust_ir::parser::parse_module(&format!(
        "module \"jit_frem\"\nfuncty.0 = (f64, f64) -> (f64)\n{definition}\n\
         fn @my_rem(functy.0) {{\nbb0(%0: f64, %1: f64):\n    %2 = frem f64 %0, %1\n    ret %2\n}}\n"
    ))
    .unwrap_or_else(|error| panic!("fixture parses: {error:?}"))
}

/// The JIT resolves a by-name reference through the module's own functions
/// before the host's symbols, so a module-local `fmod` would receive the call
/// `frem` lowers to (the verifier's in-process run returned 42 at O0 and O2).
/// Executed at O0 and O2: each module either is refused or runs `my_rem(5, 3)`
/// to 2 through the host's `fmod`. Internal and Private functions and
/// Internal data named `fmod` are refused; a module-local `fmod_helper` runs.
#[test]
fn jit_runtime_calls_never_reach_a_module_local_definition() {
    assert!(
        trust_cg_codegen::jit::lookup_process_symbol("fmod").is_some(),
        "fixture requires the host's fmod"
    );
    let local_fmod =
        "fn @fmod(functy.0) {\nbb0(%0: f64, %1: f64):\n    %2 = const f64 42.0\n    ret %2\n}";
    let cases = [
        ("internal fn fmod", format!("internal {local_fmod}"), true),
        ("private fn fmod", format!("private {local_fmod}"), true),
        (
            "internal data fmod",
            "global internal mut @fmod i64 = 42".to_string(),
            true,
        ),
        (
            "internal fn fmod_helper",
            format!("internal {}", local_fmod.replace("@fmod", "@fmod_helper")),
            false,
        ),
    ];
    for opt_level in [
        trust_cg_codegen::pipeline::OptLevel::O0,
        trust_cg_codegen::pipeline::OptLevel::O2,
    ] {
        for (label, definition, refused) in &cases {
            let compiler = Compiler::new(CompilerConfig {
                opt_level,
                ..CompilerConfig::for_host_jit_unchecked()
            })
            .with_codegen_license(permit_unlicensed());
            match compiler.compile_module_to_jit(&frem_module_with(definition), &HashMap::new()) {
                Err(error) => {
                    assert!(refused, "{label} {opt_level:?}: {error}");
                    assert!(
                        matches!(
                            error,
                            CompileError::ModuleLocalFunctionShadowsRuntimeSymbol { .. }
                                | CompileError::DataShadowsBackendSymbol { .. }
                        ),
                        "{label} {opt_level:?}: {error}"
                    );
                }
                Ok(result) => {
                    let my_rem = unsafe {
                        result
                            .buffer
                            .get_fn_bound::<extern "C" fn(f64, f64) -> f64>("my_rem")
                            .expect("my_rem")
                    };
                    assert_eq!(my_rem.as_ref()(5.0, 3.0), 2.0, "{label} {opt_level:?}");
                }
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
