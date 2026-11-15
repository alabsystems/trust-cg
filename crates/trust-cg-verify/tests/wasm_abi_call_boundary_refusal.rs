// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Standalone WASM ABI-model refusal controls. The source is validated and
//! the supplied bytes come from the real compiler, including an intentionally
//! omitted-call twin. No host unwinding or NoPanic authority is claimed.
//!
//! The ABI family checks the LOWERING, so every byte control here is the O0
//! compile ([`lowered`]): the input of the lane's local emission pass, which
//! at O1 and above emits a rewrite of a function only when `wasm_local_tv`
//! validates it against exactly these bytes (`wasm_abi_proofs_gate.rs`
//! states the same split). The ordinary controls also require that every
//! function's O2 rewrite was validated, with no fallback.

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::wasm::{self, WasmModulePolicy};
use trust_cg_verify::wasm_abi_proofs::{
    AbiModelError, decode_module, intended_module, wasm_abi_evidence,
};
use trust_ir::{
    Block, BlockId, CallingConv, Constant, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode,
    Module, Ty, ValueId,
};
use trust_ir_build::{ValidationError, validate_module};

/// The lowering's own bytes for `module` (closed policy, O0): the bytes the
/// ABI family is about.
fn lowered(module: &Module, label: &str) -> Vec<u8> {
    wasm::compile_module_with_evidence_policy_license_optimized(
        module,
        &WasmModulePolicy::closed(),
        &permit_unlicensed(),
        OptLevel::O0,
    )
    .map(|(bytes, _)| bytes)
    .unwrap_or_else(|error| panic!("{label}: O0 compile failed: {error}"))
}

fn fixture(indirect: bool, result: bool, nonexecuted: bool, boundary: bool) -> Module {
    let mut module = Module::new("wasm_abi_call_boundary");
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
    let mut callee_body = Block::new(BlockId::new(0));
    callee_body.params.push((ValueId::new(0), Ty::I32));
    callee_body.body.push(InstrNode::new(Inst::Return {
        values: if result {
            vec![ValueId::new(0)]
        } else {
            vec![]
        },
    }));
    callee.blocks.push(callee_body);
    let mut caller = Function::new(FuncId::new(1), "caller", caller_sig, BlockId::new(10));
    caller.calling_conv = CallingConv::C;
    let mut entry = Block::new(BlockId::new(10));
    entry.params = vec![(ValueId::new(0), Ty::Ptr), (ValueId::new(1), Ty::I32)];
    let (mut body, pointer, argument, destination) = if nonexecuted {
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
    let mut call = InstrNode::new(inst);
    if result {
        call.results.push(destination);
    }
    body.body.push(call);
    body.body.push(InstrNode::new(Inst::Return {
        values: if result { vec![destination] } else { vec![] },
    }));
    if nonexecuted {
        caller.blocks.push(entry);
    }
    caller.blocks.push(body);
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

fn omitted_twin(source: &Module) -> Module {
    // Wrong-program bytes must be genuinely compiler-emitted, not a synthetic
    // hand-coded binary. Keep SSA/results well-typed while removing the call.
    let mut twin = source.clone();
    for block in &mut twin.functions[1].blocks {
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
    twin
}

fn assert_boundary_detail(detail: &str, indirect: bool) {
    let construct = if indirect {
        "Inst::CallIndirectCannotUnwind"
    } else {
        "Inst::CallCannotUnwind"
    };
    assert!(detail.contains(construct), "{detail}");
    assert!(detail.contains("non-propagating call boundary"), "{detail}");
}

#[test]
fn validated_boundaries_refuse_in_standalone_model_and_real_byte_evidence() {
    let mut cells = 0;
    let mut refusals = 0;
    for indirect in [false, true] {
        for result in [false, true] {
            for nonexecuted in [false, true] {
                let source = fixture(indirect, result, nonexecuted, true);
                validated(&source);
                let error = intended_module(&source).expect_err("boundary model must refuse");
                let AbiModelError::Unsupported(detail) = error else {
                    panic!("wrong source-model refusal: {error:?}");
                };
                assert_boundary_detail(&detail, indirect);
                refusals += 1;
                let ordinary = fixture(indirect, result, nonexecuted, false);
                let omitted = omitted_twin(&source);
                for (label, twin) in [
                    ("ordinary call twin", ordinary),
                    ("omitted call twin", omitted),
                ] {
                    validated(&twin);
                    intended_module(&twin).expect("ordinary/omitted source model control");
                    let bytes = lowered(&twin, label);
                    decode_module(&bytes).expect("actual emitted bytes decode");
                    let detail = wasm_abi_evidence(&bytes, &source)
                        .expect_err("boundary source must not obtain evidence for twin bytes");
                    assert!(detail.starts_with("intended model:"), "{label}: {detail}");
                    assert_boundary_detail(&detail, indirect);
                    refusals += 1;
                }
                cells += 1;
            }
        }
    }
    assert_eq!((cells, refusals), (8, 24));
}

#[test]
fn ordinary_call_models_and_reachable_evidence_remain_admitted() {
    let mut models = 0;
    let mut evidence_controls = 0;
    for indirect in [false, true] {
        for result in [false, true] {
            for nonexecuted in [false, true] {
                let source = fixture(indirect, result, nonexecuted, false);
                validated(&source);
                let model = intended_module(&source).expect("ordinary call model");
                let caller = model
                    .defined
                    .iter()
                    .find(|function| function.name == "caller")
                    .expect("actual caller model");
                assert_eq!(caller.calls.len(), usize::from(!indirect));
                assert_eq!(caller.indirects.len(), usize::from(indirect));
                if indirect {
                    assert_eq!(
                        caller.const_callees.len(),
                        0,
                        "callee is a dynamic parameter"
                    );
                }
                models += 1;
                // The nonexecuted old-call cells are valid source models, not
                // malformed unreachable blocks. Byte-call correspondence is
                // checked here for the four entry-call ordinary controls.
                if !nonexecuted {
                    let bytes = lowered(&source, "ordinary compilation");
                    let evidence = wasm_abi_evidence(&bytes, &source).expect("ordinary evidence");
                    assert!(evidence.refusals.is_empty(), "{:?}", evidence.refusals);
                    assert!(
                        evidence.failed_structural().is_empty(),
                        "{:?}",
                        evidence.structural
                    );
                    assert!(!evidence.structural.is_empty(), "vacuous ABI checks");
                    // At O2 every function is a validated rewrite of these
                    // bytes (or these bytes unchanged), never a fallback.
                    let (_, o2) = wasm::compile_module_with_evidence_policy_license_optimized(
                        &source,
                        &WasmModulePolicy::closed(),
                        &permit_unlicensed(),
                        OptLevel::O2,
                    )
                    .expect("ordinary O2 compilation");
                    let emission = &o2.local_emission;
                    assert!(emission.enabled, "{emission:?}");
                    assert_eq!(emission.functions, 2, "{emission:?}");
                    assert_eq!(emission.fallback_count(), 0, "{emission:?}");
                    evidence_controls += 1;
                }
            }
        }
    }
    assert_eq!((models, evidence_controls), (8, 4));
}

#[test]
fn unresolved_ordinary_callees_and_malformed_bytes_keep_their_refusals() {
    for indirect in [false, true] {
        let mut source = fixture(indirect, true, false, false);
        validated(&source);
        match &mut source.functions[1].blocks[0].body[0].inst {
            Inst::Call { callee, .. } => *callee = FuncId::new(999),
            Inst::CallIndirect { sig, .. } => *sig = FuncTyId::new(999),
            _ => panic!("actual ordinary call"),
        }
        let errors = validate_module(&source);
        assert!(
            errors.iter().any(|error| matches!(
                error,
                ValidationError::CalleeNotFound { callee_id: 999, .. }
                    | ValidationError::CallIndirectSigNotFound { sig_id: 999, .. }
            )),
            "{errors:?}"
        );
        assert!(matches!(
            intended_module(&source),
            Err(AbiModelError::Unresolved(_))
        ));
    }
    let source = fixture(false, false, false, false);
    validated(&source);
    let detail = wasm_abi_evidence(&[0], &source).expect_err("malformed bytes");
    assert!(detail.starts_with("decode:"), "{detail}");
    assert!(!detail.contains("non-propagating call boundary"));
}

#[test]
fn disconnected_mutants_remain_malformed_and_cannot_obtain_boundary_evidence() {
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
            let error =
                intended_module(&mutant).expect_err("stored malformed boundary is not modeled");
            let AbiModelError::Unsupported(detail) = error else {
                panic!("wrong malformed-boundary floor: {error:?}");
            };
            assert_boundary_detail(&detail, indirect);
            refusals += 1;
            // Compile independently valid, genuinely emitted bytes. The
            // malformed source remains invalid and may acquire no evidence.
            let ordinary = fixture(indirect, result, false, false);
            validated(&ordinary);
            let bytes = lowered(&ordinary, "valid ordinary byte control");
            let detail =
                wasm_abi_evidence(&bytes, &mutant).expect_err("malformed boundary evidence");
            assert!(detail.starts_with("intended model:"), "{detail}");
            assert_boundary_detail(&detail, indirect);
            refusals += 1;
            cells += 1;
        }
    }
    assert_eq!((cells, refusals), (4, 8));
}

/// trust-ir v55 / v56 (amendment D): the unwinding twins of a drop and of an
/// indirect call are refused by the standalone model's pre-scan by name,
/// before any frame or call site is extracted (none for them would erase the
/// call).
#[test]
fn v55_v56_unwinding_twins_refuse_in_the_standalone_model() {
    for (terminator, construct) in [
        (
            Inst::InvokeIndirect {
                callee: ValueId::new(0),
                sig: FuncTyId::new(0),
                args: vec![ValueId::new(1)],
                calling_conv: CallingConv::C,
                normal_dest: BlockId::new(11),
                normal_args: vec![],
                unwind_dest: BlockId::new(12),
            },
            "Inst::InvokeIndirect",
        ),
        (
            Inst::DropInvoke {
                ty: Ty::Struct(trust_ir::StructId::new(0)),
                ptr: ValueId::new(0),
                normal_dest: BlockId::new(11),
                normal_args: vec![],
                unwind_dest: BlockId::new(12),
            },
            "Inst::DropInvoke",
        ),
    ] {
        let mut module = fixture(true, false, false, false);
        let caller = &mut module.functions[1];
        let mut entry = Block::new(BlockId::new(10));
        entry.params = vec![(ValueId::new(0), Ty::Ptr), (ValueId::new(1), Ty::I32)];
        entry.body.push(InstrNode::new(terminator));
        let mut normal = Block::new(BlockId::new(11));
        normal
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        let mut pad = Block::new(BlockId::new(12));
        pad.body.push(
            InstrNode::new(Inst::LandingPad {
                is_cleanup: true,
                catch_type_indices: vec![],
            })
            .with_results([ValueId::new(20), ValueId::new(21)]),
        );
        pad.body.push(InstrNode::new(Inst::Resume {
            exn: ValueId::new(20),
        }));
        caller.blocks = vec![entry, normal, pad];
        let error = intended_module(&module).expect_err("an unwinding twin must be refused");
        let AbiModelError::Unsupported(detail) = error else {
            panic!("wrong refusal: {error:?}");
        };
        assert!(detail.contains(construct), "{detail}");
        assert!(detail.contains("unwinding call"), "{detail}");
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
