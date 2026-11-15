// Copyright 2026 Andrew Yates | Apache-2.0
//! Every lowering entry refuses a variadic function DEFINITION with the one
//! shared diagnostic `[TCG-VARIADIC-DEFINITION]`, a `byval` parameter with
//! `[TCG-BYVAL-ABI]`, and a call through an unsigned `(...)` declaration with
//! `[TCG-UNSIGNED-VARIADIC]`, while variadic CALLS through a declaration that
//! states its fixed prefix keep compiling.
//!
//! Entries covered here: the AOT `Compiler` for AArch64 (Darwin and Linux
//! ELF), x86-64 and RISC-V targets; the host JIT (`compile_module_to_jit`);
//! the `Pipeline`'s TrustIR-sourced instruction-selection entry; and the wasm
//! lane. The native adapter entries, the compile service and the CLI have
//! their own tests (trust-cg-lower `tests/abi_definition_refusals.rs`,
//! `compile_service` unit tests, trust-cg-cli `tests/abi_refusals.rs`).
//! va_start/va_arg lowering itself (the AAPCS64 va_list record and register
//! save areas, the DarwinPCS char* cursor) remains unimplemented.

#[path = "common/pinned_target.rs"]
mod pinned_target;

use std::collections::HashMap;

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::wasm;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::{
    Block, BlockId, CallingConv, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Linkage,
    Module, ParamAttrs, Ty, ValueId,
};

const VARIADIC_TAG: &str = "[TCG-VARIADIC-DEFINITION]";
const BYVAL_TAG: &str = "[TCG-BYVAL-ABI]";
const UNSIGNED_VARIADIC_TAG: &str = "[TCG-UNSIGNED-VARIADIC]";

/// `i64 first(i64 x[, ...]) { return x; }` with the given param type.
fn single_function_module(name: &str, param: Ty, is_vararg: bool, byval: bool) -> Module {
    let mut module = Module::new(name);
    let returns = if param == Ty::Ptr {
        vec![]
    } else {
        vec![param.clone()]
    };
    let ty = module
        .add_func_type(FuncTy {
            params: vec![param.clone()],
            returns: returns.clone(),
            abi: None,
            is_vararg,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "first", ty, BlockId::new(0));
    if byval {
        function.attrs.params = vec![ParamAttrs {
            byval: true,
            ..ParamAttrs::default()
        }];
    }
    let values = if returns.is_empty() {
        vec![]
    } else {
        vec![ValueId::new(0)]
    };
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), param)],
        body: vec![InstrNode::new(Inst::Return { values })],
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn variadic_definition(name: &str, param: Ty) -> Module {
    single_function_module(name, param, true, false)
}

fn byval_definition(name: &str) -> Module {
    single_function_module(name, Ty::Ptr, false, true)
}

/// A caller of a bodyless variadic external declaration.
fn variadic_call_module() -> Module {
    let mut module = Module::new("variadic_call_control");
    let callee_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: true,
        })
        .expect("Module::add_func_type: test fixture");
    let mut callee = Function::new(FuncId::new(0), "printf_like", callee_ty, BlockId::new(0));
    callee.linkage = Linkage::External;
    callee.blocks = Vec::new();
    module
        .try_add_function(callee)
        .expect("Module::try_add_function: test fixture");
    let caller_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut caller = Function::new(FuncId::new(1), "caller", caller_ty, BlockId::new(0));
    caller.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(7),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![ValueId::new(0), ValueId::new(0), ValueId::new(1)],
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module
        .try_add_function(caller)
        .expect("Module::try_add_function: test fixture");
    module
}

/// [`variadic_call_module`] with the callee published as the producer's
/// unsigned `(...)` (no fixed parameter), the spelling the Trust producer
/// gives a C callee it cannot sign (`fcntl`).
fn unsigned_variadic_call_module() -> Module {
    let mut module = variadic_call_module();
    let callee_ty = module.functions[0].ty;
    module.func_types[callee_ty.as_usize()].params.clear();
    module
}

fn aot_compile(module: &Module, triple: &str) -> Result<Vec<u8>, String> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple).unwrap_or_else(|error| panic!("{triple}: {error:?}")),
    )
    // The fixtures declare bodyless callees: an FFI boundary needs the
    // pinned target (`TargetInfoRequired`; WS7.3 ingestion admission).
    .with_codegen_license(permit_unlicensed())
    .compile(&pinned_target::pinned(module, triple))
    .map(|result| result.object_code)
    .map_err(|error| format!("{error}"))
}

const AOT_TRIPLES: [&str; 5] = [
    "aarch64-apple-darwin",
    "aarch64-unknown-linux-gnu",
    "x86_64-unknown-linux-gnu",
    "x86_64-apple-darwin",
    "riscv64-unknown-linux-gnu",
];

#[test]
fn aot_compiler_refuses_variadic_definitions_on_every_target() {
    for triple in AOT_TRIPLES {
        let module = variadic_definition("aot_variadic", Ty::I64);
        let error =
            aot_compile(&module, triple).expect_err("a variadic definition must not compile");
        assert!(error.contains(VARIADIC_TAG), "{triple}: {error}");
    }
}

#[test]
fn aot_compiler_refuses_byval_parameters_on_every_target() {
    for triple in AOT_TRIPLES {
        let error = aot_compile(&byval_definition("aot_byval"), triple)
            .expect_err("a byval parameter must not compile");
        assert!(error.contains(BYVAL_TAG), "{triple}: {error}");
        // Control: the same function without the attribute compiles.
        let plain = single_function_module("aot_plain", Ty::Ptr, false, false);
        aot_compile(&plain, triple)
            .unwrap_or_else(|error| panic!("{triple}: plain pointer parameter: {error}"));
    }
}

#[test]
fn variadic_calls_keep_compiling_for_darwin_and_linux() {
    for triple in ["aarch64-apple-darwin", "aarch64-unknown-linux-gnu"] {
        let object = aot_compile(&variadic_call_module(), triple)
            .unwrap_or_else(|error| panic!("{triple}: variadic call: {error}"));
        assert!(!object.is_empty());
    }
}

/// A call through an unsigned `(...)` declaration has no known argument
/// placement (DarwinPCS would put every argument on the stack), so `compile`
/// refuses it by name on every target instead of lowering it with zero fixed
/// arguments. The refusal is the adapter's, before any output gate.
#[test]
fn aot_compiler_refuses_unsigned_variadic_calls_on_every_target() {
    for triple in AOT_TRIPLES {
        let error = aot_compile(&unsigned_variadic_call_module(), triple)
            .expect_err("a call through an unsigned `(...)` declaration must not compile");
        assert!(error.contains(UNSIGNED_VARIADIC_TAG), "{triple}: {error}");
        assert!(error.contains("printf_like"), "{triple}: {error}");
    }
}

/// The in-process JIT for the HOST's architecture (`CompilerConfig::default()`
/// targets AArch64, which an x86-64 host refuses to JIT before any ABI rule
/// is reached; decision LD-W7-7).
#[cfg(any(
    all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")),
    all(target_arch = "x86_64", any(target_os = "macos", target_os = "linux"))
))]
fn host_jit_compiler() -> Compiler {
    Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        target: trust_cg_codegen::Target::host(),
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed())
}

#[cfg(any(
    all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")),
    all(target_arch = "x86_64", any(target_os = "macos", target_os = "linux"))
))]
#[test]
fn host_jit_refuses_unsigned_variadic_calls() {
    let compiler = host_jit_compiler();
    // The fixture's bodyless callee is an FFI boundary, which the JIT's
    // ingestion admission (WS7.3) refuses without a pinned target
    // (`TargetInfoRequired`); pinned to the host, as `aot_compile` pins
    // each triple, the call reaches the adapter's ABI refusal.
    let module = pinned_target::pinned(
        &unsigned_variadic_call_module(),
        pinned_target::host_triple(),
    );
    let error = compiler
        .compile_module_to_jit(&module, &HashMap::new())
        .map(|_| ())
        .expect_err("the JIT must not install a call through an unsigned `(...)`");
    assert!(
        format!("{error}").contains(UNSIGNED_VARIADIC_TAG),
        "{error}"
    );
}

#[test]
fn wasm_lane_refuses_unsigned_variadic_calls() {
    // Bind body-less declarations to host imports, so the declaration is
    // reached rather than refused as unbound.
    let policy = wasm::WasmModulePolicy::island("unsigned_variadic");
    let mut module = unsigned_variadic_call_module();
    module.target_info = Some(wasm::wasm32_target_info());
    let error =
        wasm::compile_module_with_policy_and_license(&module, &policy, &permit_unlicensed())
            .expect_err("wasm: a call through an unsigned `(...)` must not compile");
    assert!(
        matches!(error, wasm::WasmLowerError::UnsupportedAbi(_)),
        "{error:?}"
    );
    assert!(error.to_string().contains(UNSIGNED_VARIADIC_TAG), "{error}");
}

/// [`variadic_call_module`] with the call an `Invoke` that unwinds to a
/// cleanup pad.
fn variadic_invoke_module() -> Module {
    let mut module = variadic_call_module();
    let caller = &mut module.functions[1];
    caller.blocks = vec![
        Block {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(7),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::Invoke {
                    callee: FuncId::new(0),
                    args: vec![ValueId::new(0), ValueId::new(0), ValueId::new(1)],
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
                .with_results(vec![ValueId::new(10), ValueId::new(11)]),
                InstrNode::new(Inst::Resume {
                    exn: ValueId::new(10),
                }),
            ],
        },
    ];
    module
}

/// OD-56: an invoke carries no fixed-argument count or variadic flag, so its
/// arguments are placed as named ones. Only base AAPCS64 places anonymous
/// arguments that way; the AOT compiler refuses a variadic invoke for x86-64
/// (whose selection would write no `AL`) and DarwinPCS, and keeps compiling
/// it for AArch64 Linux.
#[test]
fn aot_compiler_refuses_variadic_invokes_off_aapcs64() {
    for triple in [
        "x86_64-unknown-linux-gnu",
        "x86_64-apple-darwin",
        "aarch64-apple-darwin",
    ] {
        let error = aot_compile(&variadic_invoke_module(), triple)
            .expect_err("a variadic invoke off AAPCS64 must not compile");
        assert!(
            error.contains("[TCG-VARARG-ABI]")
                && error.contains("invoke of variadic callee `printf_like`"),
            "{triple}: {error}"
        );
    }
    let object = aot_compile(&variadic_invoke_module(), "aarch64-unknown-linux-gnu")
        .unwrap_or_else(|error| panic!("AAPCS64 variadic invoke: {error}"));
    assert!(!object.is_empty());
}

/// [`variadic_call_module`] with the call made through a function pointer:
/// `SymbolAddr("printf_like")` called by the non-variadic edge
/// `(i64, i64, i64) -> i64`. `unsigned` publishes the callee as `(...)`.
fn variadic_pointer_call_module(unsigned: bool) -> Module {
    let mut module = if unsigned {
        unsigned_variadic_call_module()
    } else {
        variadic_call_module()
    };
    let edge = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module.functions[1].blocks[0].body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::Ptr,
            value: Constant::SymbolAddr {
                symbol: "printf_like".into(),
                addend: 0,
            },
        })
        .with_result(ValueId::new(3)),
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(7),
        })
        .with_result(ValueId::new(1)),
        InstrNode::new(Inst::CallIndirect {
            callee: ValueId::new(3),
            sig: edge,
            args: vec![ValueId::new(0), ValueId::new(0), ValueId::new(1)],
            calling_conv: CallingConv::C,
        })
        .with_result(ValueId::new(2)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(2)],
        }),
    ];
    module
}

/// OD-56: a non-variadic function-pointer edge to a variadic declaration
/// places every argument as a named one, so the AOT compiler refuses it on
/// every native target: by `[TCG-UNSIGNED-VARIADIC]` for the producer's
/// `(...)`, by `[TCG-VARARG-ABI]` for a declaration with a fixed prefix.
#[test]
fn aot_compiler_refuses_pointer_calls_to_variadic_declarations() {
    for triple in &AOT_TRIPLES[..4] {
        let error = aot_compile(&variadic_pointer_call_module(true), triple)
            .expect_err("a pointer call to an unsigned `(...)` must not compile");
        assert!(
            error.contains(UNSIGNED_VARIADIC_TAG) && error.contains("printf_like"),
            "{triple}: {error}"
        );
        let error = aot_compile(&variadic_pointer_call_module(false), triple)
            .expect_err("a non-variadic pointer call to a variadic callee must not compile");
        assert!(
            error.contains("[TCG-VARARG-ABI]")
                && error.contains("function pointer to variadic `printf_like`"),
            "{triple}: {error}"
        );
    }
}

#[cfg(any(
    all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")),
    all(target_arch = "x86_64", any(target_os = "macos", target_os = "linux"))
))]
#[test]
fn host_jit_refuses_variadic_definitions_and_byval() {
    let compiler = host_jit_compiler();
    let error = compiler
        .compile_module_to_jit(
            &variadic_definition("jit_variadic", Ty::I64),
            &HashMap::new(),
        )
        .map(|_| ())
        .expect_err("the JIT must not install a variadic definition");
    assert!(format!("{error}").contains(VARIADIC_TAG), "{error}");
    let error = compiler
        .compile_module_to_jit(&byval_definition("jit_byval"), &HashMap::new())
        .map(|_| ())
        .expect_err("the JIT must not install a byval parameter");
    assert!(format!("{error}").contains(BYVAL_TAG), "{error}");
}

#[test]
fn pipeline_trust_ir_sourced_selection_refuses_variadic_definition_and_byval() {
    // The LIR signature cannot express either property, so the pipeline must
    // consult the attached source function. Lower a plain twin to LIR, then
    // present the variadic / byval source alongside it.
    let plain = single_function_module("pipeline_plain", Ty::I64, false, false);
    let (lir, proofs) = trust_cg_lower::translate_function_with_license(
        &plain.functions[0],
        &plain,
        &permit_unlicensed(),
    )
    .expect("plain twin lowers");
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O0,
        target_triple: "aarch64-apple-darwin".to_string(),
        ..PipelineConfig::default()
    });
    pipeline
        .prepare_function_with_metrics_and_trust_ir_module(
            &lir,
            Some(&proofs),
            &plain,
            &plain.functions[0],
        )
        .expect("control: the non-variadic source prepares");

    let variadic = variadic_definition("pipeline_variadic", Ty::I64);
    let error = pipeline
        .prepare_function_with_metrics_and_trust_ir_module(
            &lir,
            Some(&proofs),
            &variadic,
            &variadic.functions[0],
        )
        .map(|_| ())
        .expect_err("a variadic source definition must not be selected");
    assert!(error.to_string().contains(VARIADIC_TAG), "{error}");

    let mut byval = plain.clone();
    byval.functions[0].attrs.params = vec![ParamAttrs {
        byval: true,
        ..ParamAttrs::default()
    }];
    for result in [
        pipeline
            .prepare_function_with_metrics_and_trust_ir_module(
                &lir,
                Some(&proofs),
                &byval,
                &byval.functions[0],
            )
            .map(|_| ()),
        pipeline
            .prepare_function_with_metrics_and_trust_ir_provenance(
                &lir,
                Some(&proofs),
                &byval.functions[0],
            )
            .map(|_| ()),
    ] {
        let error = result.expect_err("a byval source parameter must not be selected");
        assert!(error.to_string().contains(BYVAL_TAG), "{error}");
    }
}

#[test]
fn wasm_lane_refuses_variadic_definitions_and_byval() {
    let mut variadic = variadic_definition("wasm_variadic", Ty::I32);
    variadic.target_info = Some(wasm::wasm32_target_info());
    let error = wasm::compile_module_with_policy_and_license(
        &variadic,
        &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
    )
    .expect_err("wasm variadic definition");
    assert!(
        matches!(error, wasm::WasmLowerError::UnsupportedAbi(_)),
        "{error:?}"
    );
    assert!(error.to_string().contains(VARIADIC_TAG), "{error}");

    let mut byval = byval_definition("wasm_byval");
    byval.target_info = Some(wasm::wasm32_target_info());
    let error = wasm::compile_module_with_policy_and_license(
        &byval,
        &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
    )
    .expect_err("wasm byval parameter");
    assert!(error.to_string().contains(BYVAL_TAG), "{error}");

    // Control: the same shapes without the refused property compile.
    let mut plain = single_function_module("wasm_plain", Ty::I32, false, false);
    plain.target_info = Some(wasm::wasm32_target_info());
    wasm::compile_module_with_policy_and_license(
        &plain,
        &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
    )
    .expect("plain wasm function compiles");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
