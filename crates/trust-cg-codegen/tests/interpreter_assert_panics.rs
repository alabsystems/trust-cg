// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Diagnostic interpreter agreement with TrustIR's structured v52 panic
//! outcomes. This target executes no native code and grants no proof credit.

use trust_cg_codegen::interpreter::{InterpreterError, InterpreterValue, interpret};
use trust_ir::{
    AssertKind, AssertOverflowOp, Block, BlockId, Endianness, FuncId, FuncTy, Function, Inst,
    InstrNode, InterpretValue, Module, StructPassingPolicy, TargetInfo, Ty, ValueId,
};

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn kinds() -> Vec<AssertKind> {
    let mut kinds = vec![AssertKind::Unspecified];
    kinds.extend(AssertOverflowOp::ALL.map(AssertKind::Overflow));
    kinds.extend([
        AssertKind::DivByZero,
        AssertKind::RemByZero,
        AssertKind::BoundsCheck {
            index: v(1),
            len: v(2),
        },
        AssertKind::MisalignedPtr {
            required: v(1),
            found: v(2),
        },
        AssertKind::NullPtr,
    ]);
    kinds
}

fn module(kind: AssertKind, pointer_size: u32) -> Module {
    let mut module = Module::new("diagnostic_assert_panic");
    module.target_info = Some(TargetInfo {
        triple: if pointer_size == 4 {
            "wasm32-unknown-unknown"
        } else {
            "aarch64-apple-darwin"
        }
        .to_owned(),
        pointer_size,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    });
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Bool, Ty::Usize, Ty::Usize],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "check", signature, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(v(0), Ty::Bool), (v(1), Ty::Usize), (v(2), Ty::Usize)];
    block.body = vec![
        InstrNode::new(Inst::Assert {
            cond: v(0),
            kind,
            site: None,
        }),
        InstrNode::new(Inst::Return { values: vec![] }),
    ];
    function.blocks.push(block);
    module.functions.push(function);
    module
}

#[test]
fn native_compilers_and_wasm_refuse_every_panic_kind_and_accept_assert_free_controls() {
    use trust_cg_codegen::pipeline::OptLevel;
    use trust_cg_codegen::target::TargetSpec;
    use trust_cg_codegen::{Compiler, CompilerConfig};
    fn check_reason(message: &str, kind: AssertKind) {
        if kind.is_unspecified() {
            assert!(message.contains("unspecified panic kind"), "{message}");
            assert!(message.contains("require_assert_panic_kinds"), "{message}");
        } else {
            assert!(message.contains(&format!("{kind:?}")), "{message}");
            assert!(
                message.contains("never lowered to a generic trap"),
                "{message}"
            );
        }
    }
    for triple in ["aarch64-apple-darwin", "x86_64-apple-darwin"] {
        for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let compiler = Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level,
                    ..CompilerConfig::default()
                },
                TargetSpec::parse(triple).unwrap(),
            )
            .with_codegen_license(permit_unlicensed());
            for kind in kinds() {
                let mut module = module(kind, 8);
                module.target_info.as_mut().unwrap().triple = triple.to_owned();
                let err = compiler.compile(&module).unwrap_err();
                check_reason(&err.to_string(), kind);
                module.functions[0].blocks[0].body.remove(0);
                assert!(!compiler.compile(&module).unwrap().object_code.is_empty());
            }
        }
    }
    for kind in kinds() {
        let mut module = module(kind, 4);
        let err = trust_cg_codegen::wasm::lower::compile_module_with_license(
            &module,
            &permit_unlicensed(),
        )
        .unwrap_err();
        check_reason(&err.to_string(), kind);
        module.functions[0].blocks[0].body.remove(0);
        // The wasm32 lane lowers `usize` as its 32-bit integer, so the
        // Assert-free control with the two unused payload parameters
        // compiles: only the source Assert above was refused.
        let artifact = trust_cg_codegen::wasm::lower::compile_module_with_license(
            &module,
            &permit_unlicensed(),
        )
        .unwrap();
        assert!(artifact.starts_with(b"\0asm"));
        // A bool-only signature is the narrower control.
        module.func_types[0].params.truncate(1);
        module.functions[0].blocks[0].params.truncate(1);
        let artifact = trust_cg_codegen::wasm::lower::compile_module_with_license(
            &module,
            &permit_unlicensed(),
        )
        .unwrap();
        assert!(artifact.starts_with(b"\0asm"));
    }
}

#[test]
fn all_kinds_match_the_reference_panic_identity_payload_and_message() {
    for pointer_size in [4, 8] {
        for kind in kinds() {
            let module = module(kind, pointer_size);
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{errors:?}");
            for (a, b) in [(9, 4), (-1, 16), (1i128 << 63, 4096)] {
                let result = interpret(
                    &module,
                    "check",
                    &[
                        InterpreterValue::Bool(false),
                        InterpreterValue::Int(a),
                        InterpreterValue::Int(b),
                    ],
                )
                .unwrap_err();
                let reference = trust_ir::interpret::Interpreter::with_module(&module)
                    .execute_func(
                        FuncId::new(0),
                        [
                            InterpretValue::bool(false),
                            InterpretValue::int_at(Ty::Usize, a, module.pointer_bits()).unwrap(),
                            InterpretValue::int_at(Ty::Usize, b, module.pointer_bits()).unwrap(),
                        ],
                    )
                    .unwrap_err();
                let InterpreterError::AssertPanic(actual) = &result else {
                    panic!("{result:?}")
                };
                assert_eq!(Some(actual), reference.panic());
                assert_eq!(result.to_string(), reference.message);
                let passing = interpret(
                    &module,
                    "check",
                    &[
                        InterpreterValue::Bool(true),
                        InterpreterValue::Int(a),
                        InterpreterValue::Int(b),
                    ],
                )
                .unwrap();
                assert!(passing.is_empty());
            }
        }
    }
}

#[test]
fn passing_checks_do_not_inspect_poison_panic_payloads() {
    for kind in [
        AssertKind::BoundsCheck {
            index: v(1),
            len: v(2),
        },
        AssertKind::MisalignedPtr {
            required: v(1),
            found: v(2),
        },
    ] {
        let module = module(kind, 8);
        let passing = interpret(
            &module,
            "check",
            &[
                InterpreterValue::Bool(true),
                InterpreterValue::Undef,
                InterpreterValue::Undef,
            ],
        )
        .unwrap();
        assert!(passing.is_empty());
        assert!(matches!(
            interpret(
                &module,
                "check",
                &[
                    InterpreterValue::Bool(false),
                    InterpreterValue::Undef,
                    InterpreterValue::Int(8),
                ]
            ),
            Err(InterpreterError::TypeMismatch(_))
        ));
        assert!(matches!(
            interpret(
                &module,
                "check",
                &[
                    InterpreterValue::Bool(false),
                    InterpreterValue::Int(1),
                    InterpreterValue::Undef,
                ]
            ),
            Err(InterpreterError::TypeMismatch(_))
        ));
    }
}

#[test]
fn constant_panic_kinds_never_inspect_unrelated_payload_parameters() {
    for kind in kinds().into_iter().filter(|kind| kind.operands().is_none()) {
        let module = module(kind, 8);
        let error = interpret(
            &module,
            "check",
            &[
                InterpreterValue::Bool(false),
                InterpreterValue::Undef,
                InterpreterValue::Undef,
            ],
        )
        .unwrap_err();
        assert!(matches!(error, InterpreterError::AssertPanic(ref panic)
            if panic.kind == kind && panic.operands.is_none()));
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
