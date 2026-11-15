// Copyright 2026 Andrew Yates | Apache-2.0
//! Signature-level ABI refusals at the native adapter.
//!
//! * A variadic function DEFINITION has no `va_start`/`va_arg` lowering on any
//!   target (no AAPCS64 `va_list` record or register save areas, no DarwinPCS
//!   `char *` cursor, no x86-64 SysV save area). Every adapter entry refuses it
//!   with `[TCG-VARIADIC-DEFINITION]`, while variadic CALLS to external
//!   declarations keep lowering to `CallVariadic`.
//! * `ParamAttrs::byval` changes the call's byte-level ABI (a caller-made copy
//!   in the outgoing argument area). No lowering implements it, so a byval
//!   parameter on a lowered function or a direct callee is refused with
//!   `[TCG-BYVAL-ABI]` whatever the calling convention. The sret and Swift
//!   preparation refusals keep their own diagnostics.

use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::{AdapterError, GuardCarrierArch, prepare_module_for_lir};
use trust_ir::{
    Block, BlockId, CallingConv, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Linkage,
    Module, ParamAttrs, Ty, ValueId,
};

const VARIADIC_TAG: &str = "[TCG-VARIADIC-DEFINITION]";
const BYVAL_TAG: &str = "[TCG-BYVAL-ABI]";

fn signature(
    module: &mut Module,
    params: Vec<Ty>,
    returns: Vec<Ty>,
    is_vararg: bool,
) -> trust_ir::FuncTyId {
    module
        .add_func_type(FuncTy {
            params,
            returns,
            abi: None,
            is_vararg,
        })
        .expect("Module::add_func_type: test fixture")
}

/// `i64 name(i64 x, ...)` returning `x`.
fn variadic_definition_module() -> Module {
    let mut module = Module::new("variadic_definition");
    let ty = signature(&mut module, vec![Ty::I64], vec![Ty::I64], true);
    let mut function = Function::new(FuncId::new(0), "sum_all", ty, BlockId::new(0));
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        })],
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

/// `i64 caller(i64 x) { return printf_like(x, x, 7); }` with `printf_like`
/// a bodyless variadic external declaration.
fn variadic_call_module() -> Module {
    let mut module = Module::new("variadic_call");
    let callee_ty = signature(&mut module, vec![Ty::I64], vec![Ty::I64], true);
    let mut callee = Function::new(FuncId::new(0), "printf_like", callee_ty, BlockId::new(0));
    callee.linkage = Linkage::External;
    callee.blocks = Vec::new();
    module
        .try_add_function(callee)
        .expect("Module::try_add_function: test fixture");
    let caller_ty = signature(&mut module, vec![Ty::I64], vec![Ty::I64], false);
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

/// `i64 load_first(ptr p)` whose parameter carries `byval` (or `sret` too).
fn byval_definition_module(convention: CallingConv, sret: bool) -> Module {
    let mut module = Module::new("byval_definition");
    let returns = if sret { vec![] } else { vec![Ty::I64] };
    let ty = signature(&mut module, vec![Ty::Ptr], returns, false);
    let mut function = Function::new(FuncId::new(0), "load_first", ty, BlockId::new(0));
    function.calling_conv = convention;
    function.attrs.params = vec![ParamAttrs {
        byval: true,
        sret,
        ..ParamAttrs::default()
    }];
    let body = if sret {
        vec![InstrNode::new(Inst::Return { values: vec![] })]
    } else {
        vec![
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
        ]
    };
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr)],
        body,
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

/// `i64 caller(ptr p) { return take(p); }` where the external declaration
/// `take` marks its pointer parameter byval.
fn byval_callee_module() -> Module {
    let mut module = Module::new("byval_callee");
    let ty = signature(&mut module, vec![Ty::Ptr], vec![Ty::I64], false);
    let mut callee = Function::new(FuncId::new(0), "take", ty, BlockId::new(0));
    callee.linkage = Linkage::External;
    callee.blocks = Vec::new();
    callee.attrs.params = vec![ParamAttrs {
        byval: true,
        ..ParamAttrs::default()
    }];
    module
        .try_add_function(callee)
        .expect("Module::try_add_function: test fixture");
    let mut caller = Function::new(FuncId::new(1), "caller", ty, BlockId::new(0));
    caller.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr)],
        body: vec![
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module
        .try_add_function(caller)
        .expect("Module::try_add_function: test fixture");
    module
}

fn assert_refused(label: &str, result: Result<impl std::fmt::Debug, AdapterError>, tag: &str) {
    let error = result.expect_err(label);
    assert!(error.to_string().contains(tag), "{label}: {error}");
}

#[test]
fn variadic_definitions_are_refused_by_every_adapter_entry() {
    let module = variadic_definition_module();
    let error = permit_translate_module(&module).expect_err("translate_module");
    assert!(
        matches!(&error, AdapterError::VariadicDefinitionUnsupported { function } if function == "sum_all"),
        "{error:?}"
    );
    assert!(error.to_string().contains(VARIADIC_TAG), "{error}");
    for arch in [
        GuardCarrierArch::AArch64,
        GuardCarrierArch::X86_64,
        GuardCarrierArch::Riscv64,
    ] {
        assert_refused(
            &format!("translate_module_for_arch({arch:?})"),
            permit_translate_module_for_arch(&module, arch),
            VARIADIC_TAG,
        );
    }
    assert_refused(
        "translate_function",
        trust_cg_lower::translate_function_with_license(
            &module.functions[0],
            &module,
            &permit_unlicensed(),
        ),
        VARIADIC_TAG,
    );
    // Any calling convention the adapter otherwise admits gets the same
    // diagnostic, rather than a convention-specific one.
    for convention in [CallingConv::Fast, CallingConv::Cold, CallingConv::Swift] {
        let mut variant = module.clone();
        variant.functions[0].calling_conv = convention;
        assert_refused(
            &format!("{convention:?}"),
            permit_translate_module(&variant),
            VARIADIC_TAG,
        );
    }
    // The shared helper itself accepts declarations.
    let mut declaration = module.clone();
    declaration.functions[0].blocks.clear();
    declaration.functions[0].linkage = Linkage::External;
    assert!(
        trust_cg_lower::reject_variadic_definition(&declaration.functions[0], &declaration).is_ok()
    );
}

#[test]
fn variadic_calls_to_declarations_still_lower() {
    let module = variadic_call_module();
    let lowered = permit_translate_module(&module).expect("a variadic CALL must keep lowering");
    let (caller, _) = &lowered[0];
    let call = caller.blocks[&caller.entry_block]
        .instructions
        .iter()
        .find(|inst| matches!(inst.opcode, Opcode::CallVariadic { .. }))
        .expect("CallVariadic");
    assert!(matches!(
        &call.opcode,
        Opcode::CallVariadic { name, fixed_args: 1 } if name == "printf_like"
    ));
}

#[test]
fn byval_parameters_are_refused_on_definitions_and_direct_callees() {
    for convention in [
        CallingConv::C,
        CallingConv::Rust,
        CallingConv::Fast,
        CallingConv::Cold,
    ] {
        let module = byval_definition_module(convention, false);
        let error = permit_translate_module(&module).expect_err("byval definition");
        assert!(
            matches!(
                &error,
                AdapterError::ByvalParamUnsupported { function, index: 0 } if function == "load_first"
            ),
            "{convention:?}: {error:?}"
        );
        assert!(error.to_string().contains(BYVAL_TAG));
        assert_refused(
            "translate_function",
            trust_cg_lower::translate_function_with_license(
                &module.functions[0],
                &module,
                &permit_unlicensed(),
            ),
            BYVAL_TAG,
        );
    }
    assert_refused(
        "direct call to a byval callee",
        permit_translate_module(&byval_callee_module()),
        BYVAL_TAG,
    );

    // Controls: without the attribute both shapes lower.
    let mut plain = byval_definition_module(CallingConv::C, false);
    plain.functions[0].attrs.params.clear();
    permit_translate_module(&plain).expect("a plain pointer parameter lowers");
    let mut plain_callee = byval_callee_module();
    plain_callee.functions[0].attrs.params.clear();
    permit_translate_module(&plain_callee).expect("a plain pointer callee lowers");
}

#[test]
fn byval_keeps_the_sret_and_swift_preparation_diagnostics() {
    // byval on the hidden return buffer is an invalid sret declaration and
    // keeps that named diagnostic.
    let error = permit_translate_module(&byval_definition_module(CallingConv::C, true))
        .expect_err("byval sret");
    assert!(error.to_string().contains("[TCG-SRET-ABI]"), "{error}");

    // Swift compatibility preparation still refuses an aggregate byval
    // parameter before scalarization, with its own message.
    let mut swift = Module::new("swift_byval");
    let pair = Ty::Tuple(vec![Ty::I64, Ty::I64]);
    let ty = signature(&mut swift, vec![pair.clone()], vec![], false);
    let mut function = Function::new(FuncId::new(0), "swift_pair", ty, BlockId::new(0));
    function.calling_conv = CallingConv::Swift;
    function.attrs.params = vec![ParamAttrs {
        byval: true,
        ..ParamAttrs::default()
    }];
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), pair)],
        body: vec![InstrNode::new(Inst::Return { values: vec![] })],
    }];
    swift
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    let error = prepare_module_for_lir(&swift, GuardCarrierArch::AArch64)
        .map(|_| ())
        .expect_err("Swift aggregate byval");
    assert!(
        error.to_string().contains("byval/sret ABI attributes"),
        "{error}"
    );
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

/// `translate_module_for_arch` under [`permit_unlicensed`].
fn permit_translate_module_for_arch(
    module: &trust_ir::Module,
    arch: trust_cg_lower::GuardCarrierArch,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        arch,
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}
