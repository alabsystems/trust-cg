// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Real WASM admission controls for IR's normative call unwind boundaries.
//! These establish named refusals and ordinary-call compilation, not host
//! unwind enforcement, execution, or NoPanic evidence.

use trust_cg_codegen::wasm::{self, WasmFunctionEnv, WasmLowerError, WasmModule};
use trust_ir::{
    Block, BlockId, CallingConv, Constant, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode,
    Module, Ty, ValueId,
};
use trust_ir_build::{ValidationError, validate_module};

fn fixture(indirect: bool, result: bool, nonexecuted: bool, boundary: bool) -> Module {
    let mut module = Module::new("wasm_call_boundary");
    module.target_info = Some(wasm::wasm32_target_info());
    let returns = if result { vec![Ty::I32] } else { vec![] };
    let callee_sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: returns.clone(),
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let caller_sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I32],
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut callee = Function::new(FuncId::new(0), "callee", callee_sig, BlockId::new(0));
    callee.calling_conv = CallingConv::C;
    let mut body = Block::new(BlockId::new(0));
    body.params.push((ValueId::new(0), Ty::I32));
    body.body.push(InstrNode::new(Inst::Return {
        values: if result {
            vec![ValueId::new(0)]
        } else {
            vec![]
        },
    }));
    callee.blocks.push(body);
    let mut caller = Function::new(FuncId::new(1), "caller", caller_sig, BlockId::new(10));
    caller.calling_conv = CallingConv::C;
    let mut entry = Block::new(BlockId::new(10));
    entry.params = vec![(ValueId::new(0), Ty::Ptr), (ValueId::new(1), Ty::I32)];
    let (mut call_block, pointer, argument, destination) = if nonexecuted {
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(false),
            })
            .with_result(ValueId::new(2)),
        );
        entry.body.push(InstrNode::new(Inst::CondBr {
            cond: ValueId::new(2),
            then_target: BlockId::new(11),
            then_args: vec![ValueId::new(0), ValueId::new(1)],
            else_target: BlockId::new(12),
            else_args: if result {
                vec![ValueId::new(1)]
            } else {
                vec![]
            },
        }));
        let mut untaken = Block::new(BlockId::new(11));
        untaken.params = vec![(ValueId::new(3), Ty::Ptr), (ValueId::new(4), Ty::I32)];
        (untaken, ValueId::new(3), ValueId::new(4), ValueId::new(5))
    } else {
        (
            entry.clone(),
            ValueId::new(0),
            ValueId::new(1),
            ValueId::new(2),
        )
    };
    let args = vec![argument];
    let inst = match (indirect, boundary) {
        (false, false) => Inst::Call {
            callee: callee.id,
            args,
        },
        (false, true) => Inst::CallCannotUnwind {
            callee: callee.id,
            args,
        },
        (true, false) => Inst::CallIndirect {
            callee: pointer,
            sig: callee_sig,
            args,
            calling_conv: CallingConv::C,
        },
        (true, true) => Inst::CallIndirectCannotUnwind {
            callee: pointer,
            sig: callee_sig,
            args,
            calling_conv: CallingConv::C,
        },
    };
    let mut node = InstrNode::new(inst);
    if result {
        node.results.push(destination);
    }
    call_block.body.push(node);
    call_block.body.push(InstrNode::new(Inst::Return {
        values: if result { vec![destination] } else { vec![] },
    }));
    if nonexecuted {
        caller.blocks.push(entry);
    }
    caller.blocks.push(call_block);
    if nonexecuted {
        let mut exit = Block::new(BlockId::new(12));
        if result {
            exit.params.push((ValueId::new(8), Ty::I32));
        }
        exit.body.push(InstrNode::new(Inst::Return {
            values: if result {
                vec![ValueId::new(8)]
            } else {
                vec![]
            },
        }));
        caller.blocks.push(exit);
    }
    module.functions = vec![callee, caller];
    module
}

fn validated(module: &Module) {
    let errors = validate_module(module);
    assert!(errors.is_empty(), "fixture is not valid IR: {errors:#?}");
    assert!(!module.instructions().any(|node| matches!(
        node.inst,
        Inst::Invoke { .. } | Inst::LandingPad { .. } | Inst::Resume { .. }
    )));
}

fn call_mut(module: &mut Module) -> &mut Inst {
    &mut module.functions[1].blocks[0].body[0].inst
}

fn omit_boundary(module: &Module) -> Module {
    // A deliberately wrong source twin for the detached-function control.
    // Preserve all result definitions so it is independently valid IR.
    let mut omitted = module.clone();
    for block in &mut omitted.functions[1].blocks {
        block.body.retain_mut(|node| {
            let argument = match &node.inst {
                Inst::CallCannotUnwind { args, .. }
                | Inst::CallIndirectCannotUnwind { args, .. } => args[0],
                _ => return true,
            };
            if node.results.is_empty() {
                false
            } else {
                node.inst = Inst::Copy {
                    ty: Ty::I32,
                    operand: argument,
                };
                true
            }
        });
    }
    omitted
}

/// The refusal names the actual constructor. Module, object and module-held
/// function routes refuse on the shared native floor (`ContractSurface`); a
/// detached function body and the pre-layout policy refuse in the wasm lane's
/// own whole-body scan (`UnsupportedInst`).
fn require_boundary_refusal(result: Result<(), WasmLowerError>, indirect: bool, route: &str) {
    let error = result.expect_err(route);
    let (WasmLowerError::ContractSurface(detail) | WasmLowerError::UnsupportedInst(detail)) = error
    else {
        panic!("{route}: wrong refusal: {error:?}");
    };
    let construct = if indirect {
        "Inst::CallIndirectCannotUnwind"
    } else {
        "Inst::CallCannotUnwind"
    };
    assert!(detail.contains(construct), "{route}: {detail}");
    assert!(
        detail.contains("non-propagating call boundary"),
        "{route}: {detail}"
    );
}

#[test]
fn validated_no_eh_boundaries_refuse_before_module_object_and_cfg_projection() {
    let mut cells = 0;
    let mut refusals = 0;
    for indirect in [false, true] {
        for result in [false, true] {
            for nonexecuted in [false, true] {
                let module = fixture(indirect, result, nonexecuted, true);
                validated(&module);
                let omitted = omit_boundary(&module);
                validated(&omitted);
                let mut standalone = WasmModule::new();
                let mut detached = WasmModule::new();
                // The omitted twin is lowerable under this same public env;
                // the boundary refusal must inspect the requested actual body.
                wasm::lower_function_with_license(
                    &mut WasmModule::new(),
                    &omitted.functions[1],
                    &omitted,
                    WasmFunctionEnv::empty(),
                    &permit_unlicensed(),
                )
                .expect("omitted-call public-function control");
                let outcomes = [
                    (
                        "closed module",
                        wasm::compile_module_with_license(&module, &permit_unlicensed())
                            .map(|_| ()),
                    ),
                    (
                        "island module",
                        wasm::compile_module_with_policy_and_license(
                            &module,
                            &wasm::WasmModulePolicy::island("boundary"),
                            &permit_unlicensed(),
                        )
                        .map(|_| ()),
                    ),
                    (
                        "module evidence",
                        wasm::compile_module_with_evidence_policy_and_license(
                            &module,
                            &wasm::WasmModulePolicy::closed(),
                            &permit_unlicensed(),
                        )
                        .map(|_| ()),
                    ),
                    (
                        "relocatable object",
                        wasm::compile_object_with_license(&module, &permit_unlicensed())
                            .map(|_| ()),
                    ),
                    (
                        "object evidence",
                        wasm::compile_object_with_evidence_and_license(
                            &module,
                            &permit_unlicensed(),
                        )
                        .map(|_| ()),
                    ),
                    (
                        "pre-layout policy",
                        wasm::sized_closed_policy(&module).map(|_| ()),
                    ),
                    (
                        "public function",
                        wasm::lower_function_with_license(
                            &mut standalone,
                            &module.functions[1],
                            &module,
                            WasmFunctionEnv::empty(),
                            &permit_unlicensed(),
                        )
                        .map(|_| ()),
                    ),
                    (
                        "detached function",
                        wasm::lower_function_with_license(
                            &mut detached,
                            &module.functions[1],
                            &omitted,
                            WasmFunctionEnv::empty(),
                            &permit_unlicensed(),
                        )
                        .map(|_| ()),
                    ),
                ];
                for (route, outcome) in outcomes {
                    require_boundary_refusal(outcome, indirect, route);
                    refusals += 1;
                }
                assert_eq!(standalone.func_count(), 0, "refused function emitted code");
                assert_eq!(
                    detached.func_count(),
                    0,
                    "refused detached body emitted code"
                );
                cells += 1;
            }
        }
    }
    assert_eq!((cells, refusals), (8, 64));
}

#[test]
fn ordinary_calls_keep_module_object_and_evidence_compilation() {
    let mut cells = 0;
    for indirect in [false, true] {
        for result in [false, true] {
            for nonexecuted in [false, true] {
                let module = fixture(indirect, result, nonexecuted, false);
                validated(&module);
                assert!(
                    !wasm::compile_module_with_license(&module, &permit_unlicensed())
                        .expect("ordinary module")
                        .is_empty()
                );
                assert!(
                    !wasm::compile_object_with_license(&module, &permit_unlicensed())
                        .expect("ordinary object")
                        .is_empty()
                );
                assert!(
                    !wasm::compile_module_with_evidence_policy_and_license(
                        &module,
                        &wasm::WasmModulePolicy::closed(),
                        &permit_unlicensed()
                    )
                    .expect("ordinary module evidence")
                    .0
                    .is_empty()
                );
                cells += 1;
            }
        }
    }
    assert_eq!(cells, 8);
}

#[test]
fn malformed_call_fields_keep_their_structural_errors() {
    for indirect in [false, true] {
        for boundary in [false, true] {
            let control = fixture(indirect, true, false, boundary);
            validated(&control);
            let mut wrong = control.clone();
            match call_mut(&mut wrong) {
                Inst::Call { args, .. }
                | Inst::CallCannotUnwind { args, .. }
                | Inst::CallIndirect { args, .. }
                | Inst::CallIndirectCannotUnwind { args, .. } => args.clear(),
                _ => panic!("actual call fixture"),
            }
            let errors = validate_module(&wrong);
            assert!(
                errors.iter().any(|error| matches!(
                    error,
                    ValidationError::CallArgCountMismatch { .. }
                        | ValidationError::CallIndirectArgCountMismatch { .. }
                )),
                "wrong argument count: {errors:?}"
            );
            let mut wrong = control;
            match call_mut(&mut wrong) {
                Inst::Call { callee, .. } | Inst::CallCannotUnwind { callee, .. } => {
                    *callee = FuncId::new(999)
                }
                Inst::CallIndirect { sig, .. } | Inst::CallIndirectCannotUnwind { sig, .. } => {
                    *sig = FuncTyId::new(999)
                }
                _ => panic!("actual call fixture"),
            }
            let errors = validate_module(&wrong);
            assert!(
                errors.iter().any(|error| matches!(
                    error,
                    ValidationError::CalleeNotFound { callee_id: 999, .. }
                        | ValidationError::CallIndirectSigNotFound { sig_id: 999, .. }
                )),
                "unresolved actual callee/signature: {errors:?}"
            );
        }
    }
}

#[test]
fn disconnected_mutants_keep_structural_error_and_stored_boundary_floor() {
    let mut cells = 0;
    let mut refusals = 0;
    for indirect in [false, true] {
        for result in [false, true] {
            let mut mutant = fixture(indirect, result, true, true);
            validated(&mutant);
            mutant.functions[1].blocks[0].body = vec![InstrNode::new(Inst::Br {
                target: BlockId::new(12),
                args: if result {
                    vec![ValueId::new(1)]
                } else {
                    vec![]
                },
            })];
            assert_eq!(
                validate_module(&mutant),
                vec![ValidationError::UnreachableBlock(11)]
            );
            // These are malformed controls, not valid compilation inputs.
            // The existing stored-body floor must still name the boundary.
            for (route, outcome) in [
                (
                    "disconnected module",
                    wasm::compile_module_with_license(&mutant, &permit_unlicensed()).map(drop),
                ),
                (
                    "disconnected object",
                    wasm::compile_object_with_license(&mutant, &permit_unlicensed()).map(drop),
                ),
                (
                    "disconnected function",
                    wasm::lower_function_with_license(
                        &mut WasmModule::new(),
                        &mutant.functions[1],
                        &mutant,
                        WasmFunctionEnv::empty(),
                        &permit_unlicensed(),
                    )
                    .map(drop),
                ),
            ] {
                require_boundary_refusal(outcome, indirect, route);
                refusals += 1;
            }
            cells += 1;
        }
    }
    assert_eq!((cells, refusals), (4, 12));
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
