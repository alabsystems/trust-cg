// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Real native-adapter admission controls for normative call boundaries.
//! These establish typed source refusals and ordinary LIR lowering, not
//! target unwind enforcement, native execution, or a NoPanic fact.

use std::collections::HashMap;

use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::{
    AdapterError, GuardCarrierArch, ObjectAccessModel, TlsDialect, prepare_module_for_lir,
    prepare_module_for_lir_with_tls, reject_unconsumed_v41_surface,
    reject_unconsumed_v41_target_neutral_surface, translate_body_template,
    translate_function_with_license, translate_inline_only_bodies,
    translate_validated_module_strict_for_arch_with_tls_and_validation_with_license,
};
use trust_ir::{
    Block, BlockId, CallingConv, Constant, Endianness, FuncId, FuncTy, FuncTyId, Function, Inst,
    InstrNode, Linkage, Module, StructPassingPolicy, TargetInfo, Ty, ValueId,
};
use trust_ir_build::{ValidationError, validate_module, validate_module_report};

const ARCHES: [GuardCarrierArch; 3] = [
    GuardCarrierArch::AArch64,
    GuardCarrierArch::X86_64,
    GuardCarrierArch::Riscv64,
];

fn fixture(indirect: bool, result: bool, nonexecuted: bool, boundary: bool) -> Module {
    let mut module = Module::new("native_call_boundary");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    let returns = if result { vec![Ty::I64] } else { vec![] };
    let callee_sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: returns.clone(),
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let parameters = if indirect {
        vec![Ty::Func(callee_sig), Ty::I64]
    } else {
        vec![Ty::I64]
    };
    let caller_sig = module
        .add_func_type(FuncTy {
            params: parameters.clone(),
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut callee = Function::new(
        FuncId::new(0),
        "boundary_target",
        callee_sig,
        BlockId::new(0),
    );
    callee.calling_conv = CallingConv::C;
    let mut body = Block::new(BlockId::new(0));
    body.params.push((ValueId::new(0), Ty::I64));
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
    let parameters_for = |base: u32| {
        parameters
            .iter()
            .enumerate()
            .map(|(index, ty)| (ValueId::new(base + index as u32), ty.clone()))
            .collect()
    };
    let mut entry = Block::new(BlockId::new(10));
    entry.params = parameters_for(0);
    let argument_index = u32::from(indirect);
    let (mut call_block, base) = if nonexecuted {
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
            then_args: (0..parameters.len())
                .map(|index| ValueId::new(index as u32))
                .collect(),
            else_target: BlockId::new(12),
            else_args: if result {
                vec![ValueId::new(argument_index)]
            } else {
                vec![]
            },
        }));
        let mut untaken = Block::new(BlockId::new(11));
        untaken.params = parameters_for(4);
        (untaken, 4)
    } else {
        (entry.clone(), 0)
    };
    let argument = ValueId::new(base + argument_index);
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
            callee: ValueId::new(base),
            sig: callee_sig,
            args,
            calling_conv: CallingConv::C,
        },
        (true, true) => Inst::CallIndirectCannotUnwind {
            callee: ValueId::new(base),
            sig: callee_sig,
            args,
            calling_conv: CallingConv::C,
        },
    };
    let mut node = InstrNode::new(inst);
    if result {
        node.results.push(ValueId::new(base + 2));
    }
    call_block.body.push(node);
    call_block.body.push(InstrNode::new(Inst::Return {
        values: if result {
            vec![ValueId::new(base + 2)]
        } else {
            vec![]
        },
    }));
    if nonexecuted {
        caller.blocks.push(entry);
    }
    caller.blocks.push(call_block);
    if nonexecuted {
        let mut exit = Block::new(BlockId::new(12));
        if result {
            exit.params.push((ValueId::new(8), Ty::I64));
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
    assert!(errors.is_empty(), "fixture is invalid: {errors:#?}");
    assert!(!module.instructions().any(|node| matches!(
        node.inst,
        Inst::Invoke { .. } | Inst::LandingPad { .. } | Inst::Resume { .. }
    )));
}

fn expected_construct(indirect: bool) -> &'static str {
    if indirect {
        "Inst::CallIndirectCannotUnwind"
    } else {
        "Inst::CallCannotUnwind"
    }
}

/// The shared floor's by-name refusal (`AdapterError::UnmodeledTrustIrConstruct`
/// with the native lane's `CALL_UNWIND_BOUNDARY_UNMODELED` reason).
fn boundary_detail(detail: &str, indirect: bool, route: &str) {
    assert!(
        detail.contains(expected_construct(indirect)),
        "{route}: {detail}"
    );
    assert!(
        detail.contains("does not model") && detail.contains("non-propagating call boundary"),
        "{route}: {detail}"
    );
}

fn require_refusal(outcome: Result<(), AdapterError>, indirect: bool, route: &str) {
    let error = outcome.expect_err(route);
    boundary_detail(&error.to_string(), indirect, route);
    let AdapterError::UnmodeledTrustIrConstruct {
        location,
        construct,
        reason,
    } = error
    else {
        panic!("{route}: wrong boundary refusal: {error:?}");
    };
    assert_eq!(construct, expected_construct(indirect), "{route}");
    assert!(location.contains("caller"), "{route}: {location}");
    assert!(
        reason.contains("non-propagating call boundary"),
        "{route}: {reason}"
    );
}

fn omit_boundary(source: &Module) -> Module {
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
                    ty: Ty::I64,
                    operand: argument,
                };
                true
            }
        });
    }
    twin
}

#[test]
fn validated_no_eh_boundaries_refuse_on_public_native_admission_routes() {
    let license = permit_unlicensed();
    let mut cells = 0;
    let mut adapter_refusals = 0;
    let mut helper_refusals = 0;
    for indirect in [false, true] {
        for result in [false, true] {
            for nonexecuted in [false, true] {
                let module = fixture(indirect, result, nonexecuted, true);
                validated(&module);
                let report = validate_module_report(&module);
                assert!(
                    report.is_ok(),
                    "typed boundary must be carryable: {:?}",
                    report.errors()
                );
                let names: HashMap<_, _> = module
                    .functions
                    .iter()
                    .map(|func| (func.id, func.name.clone()))
                    .collect();
                let omitted = omit_boundary(&module);
                validated(&omitted);
                trust_cg_lower::translate_function_with_license(
                    &omitted.functions[1],
                    &omitted,
                    &permit_unlicensed(),
                )
                .expect("detached-body baseline");
                for (route, outcome) in [
                    (
                        "target-neutral function",
                        trust_cg_lower::translate_function_with_license(&module.functions[1], &module, &permit_unlicensed()).map(drop),
                    ),
                    (
                        "explicit license",
                        translate_function_with_license(&module.functions[1], &module, &license)
                            .map(drop),
                    ),
                    (
                        "explicit actual names",
                        trust_cg_lower::translate_function_with_names_and_license(&module.functions[1], &module, &names, &permit_unlicensed())
                            .map(drop),
                    ),
                    (
                        "actual detached body",
                        trust_cg_lower::translate_function_with_license(&module.functions[1], &omitted, &permit_unlicensed()).map(drop),
                    ),
                    ("legacy module", trust_cg_lower::translate_module_for_arch_with_tls_with_license(&module, trust_cg_lower::GuardCarrierArch::default(), trust_cg_lower::TlsDialect::default(), &permit_unlicensed()).map(drop)),
                    (
                        "explicit target TLS",
                        trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                            &module,
                            GuardCarrierArch::AArch64,
                            TlsDialect::default(),
                            &permit_unlicensed(),
                        )
                        .map(drop),
                    ),
                    (
                        "module call-identity report",
                        trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
                            &module,
                            GuardCarrierArch::AArch64,
                            TlsDialect::default(),
                            &permit_unlicensed(),
                        )
                        .map(drop),
                    ),
                    (
                        "identity-only strict module",
                        trust_cg_lower::translate_module_strict_for_arch_with_tls_and_validation_with_license(
                            &module,
                            GuardCarrierArch::AArch64,
                            TlsDialect::default(),
                            &permit_unlicensed(),
                        )
                        .map(drop),
                    ),
                    (
                        "actual complete validation report",
                        translate_validated_module_strict_for_arch_with_tls_and_validation_with_license(
                            &report,
                            GuardCarrierArch::AArch64,
                            TlsDialect::default(),
                            &permit_unlicensed(),
                        )
                        .map(drop),
                    ),
                    (
                        "preparation",
                        prepare_module_for_lir(&module, GuardCarrierArch::AArch64).map(drop),
                    ),
                    (
                        "explicit TLS preparation",
                        prepare_module_for_lir_with_tls(
                            &module,
                            GuardCarrierArch::AArch64,
                            TlsDialect::default(),
                        )
                        .map(drop),
                    ),
                    (
                        "shared target-neutral floor",
                        reject_unconsumed_v41_target_neutral_surface(&module),
                    ),
                ] {
                    require_refusal(outcome, indirect, route);
                    adapter_refusals += 1;
                }
                for arch in ARCHES {
                    for (route, outcome) in [
                        (
                            format!("{arch} module"),
                            trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                                &module,
                                arch,
                                trust_cg_lower::TlsDialect::default(),
                                &permit_unlicensed(),
                            )
                            .map(drop),
                        ),
                        (
                            format!("{arch} surface floor"),
                            reject_unconsumed_v41_surface(&module, arch),
                        ),
                    ] {
                        require_refusal(outcome, indirect, &route);
                        adapter_refusals += 1;
                    }
                }
                let template_error = translate_body_template(
                    &module,
                    &module.functions[1],
                    GuardCarrierArch::AArch64,
                    ObjectAccessModel::default(),
                    &license,
                )
                .expect_err("body-template backstop");
                boundary_detail(&template_error, indirect, "body-template backstop");
                helper_refusals += 1;

                // AvailableExternally is skipped as a codegen definition, but
                // the stored-body module floor must not skip its contract.
                let mut inline = module.clone();
                inline.functions[1].linkage = Linkage::AvailableExternally;
                validated(&inline);
                require_refusal(
                    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                        &inline,
                        trust_cg_lower::GuardCarrierArch::default(),
                        trust_cg_lower::TlsDialect::default(),
                        &permit_unlicensed(),
                    )
                    .map(drop),
                    indirect,
                    "inline-only stored-body module floor",
                );
                adapter_refusals += 1;
                // Deliberate defensive helper invocation, NOT an assertion
                // that this floor-refused module met the helper's documented
                // admitted-module precondition. No body may be returned.
                let withheld = translate_inline_only_bodies(
                    &inline,
                    GuardCarrierArch::AArch64,
                    ObjectAccessModel::default(),
                    &license,
                );
                assert!(withheld.bodies.is_empty(), "boundary template escaped");
                assert_eq!(withheld.withheld.len(), 1);
                assert_eq!(withheld.withheld[0].name, "caller");
                boundary_detail(
                    &withheld.withheld[0].reason,
                    indirect,
                    "defensive inline-only backstop",
                );
                helper_refusals += 1;
                cells += 1;
            }
        }
    }
    assert_eq!((cells, adapter_refusals, helper_refusals), (8, 152, 16));
}

fn require_ordinary_call(function: &trust_cg_lower::Function, indirect: bool, result: bool) {
    let calls: Vec<_> = function.blocks.values().flat_map(|block| &block.instructions).filter(|instruction| {
        if indirect { matches!(instruction.opcode, Opcode::CallIndirect) } else {
            matches!(&instruction.opcode, Opcode::Call { name, .. } if name == "boundary_target")
        }
    }).collect();
    assert_eq!(
        calls.len(),
        1,
        "ordinary source call was erased/reclassified"
    );
    assert_eq!(calls[0].results.len(), usize::from(result));
    assert_eq!(calls[0].args.len(), 1 + usize::from(indirect));
}

#[test]
fn ordinary_calls_keep_lowering_and_prepared_report_replay() {
    let mut cells = 0;
    let mut lowered_routes = 0;
    let mut retained_reachable_calls = 0;
    for indirect in [false, true] {
        for result in [false, true] {
            for nonexecuted in [false, true] {
                let module = fixture(indirect, result, nonexecuted, false);
                validated(&module);
                let single = trust_cg_lower::translate_function_with_license(
                    &module.functions[1],
                    &module,
                    &permit_unlicensed(),
                )
                .expect("ordinary function")
                .0;
                let legacy = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                    &module,
                    trust_cg_lower::GuardCarrierArch::default(),
                    trust_cg_lower::TlsDialect::default(),
                    &permit_unlicensed(),
                )
                .expect("ordinary module");
                let (strict, strict_report) =
                    trust_cg_lower::translate_module_strict_for_arch_with_tls_and_validation_with_license(
                        &module,
                        GuardCarrierArch::AArch64,
                        TlsDialect::default(),
                        &permit_unlicensed(),
                    )
                    .expect("ordinary strict module");
                strict_report
                    .replay_exact_module_bindings(&strict)
                    .expect("actual strict call-identity replay");
                let report = validate_module_report(&module);
                assert!(report.is_ok());
                let (validated_lir, validated_report) =
                    translate_validated_module_strict_for_arch_with_tls_and_validation_with_license(
                        &report,
                        GuardCarrierArch::AArch64,
                        TlsDialect::default(),
                        &permit_unlicensed(),
                    )
                    .expect("ordinary validated strict module");
                validated_report
                    .replay_exact_module_bindings(&validated_lir)
                    .expect("actual full-report lowering replay");
                let prepared = prepare_module_for_lir(&module, GuardCarrierArch::AArch64)
                    .expect("ordinary preparation");
                assert_eq!(
                    prepared.module(),
                    &module,
                    "simple fixture triggered a source rewrite"
                );
                let (prepared_lir, prepared_report) = prepared
                    .translate_with_tls_and_validation_with_license(
                        TlsDialect::default(),
                        &permit_unlicensed(),
                    )
                    .expect("ordinary prepared translation");
                prepared_report
                    .replay_exact_module_bindings(&prepared_lir)
                    .expect("actual prepared call-identity replay");
                let template = translate_body_template(
                    &module,
                    &module.functions[1],
                    GuardCarrierArch::AArch64,
                    ObjectAccessModel::default(),
                    &permit_unlicensed(),
                )
                .expect("ordinary body template")
                .0;
                lowered_routes += 6;
                if !nonexecuted {
                    require_ordinary_call(&single, indirect, result);
                    require_ordinary_call(&template, indirect, result);
                    for functions in [&legacy, &strict, &validated_lir, &prepared_lir] {
                        let caller = functions
                            .iter()
                            .find(|(function, _)| function.name == "caller")
                            .expect("actual caller");
                        require_ordinary_call(&caller.0, indirect, result);
                    }
                    retained_reachable_calls += 6;
                }
                cells += 1;
            }
        }
    }
    assert_eq!(
        (cells, lowered_routes, retained_reachable_calls),
        (8, 48, 24)
    );
}

fn call_mut(module: &mut Module) -> &mut Inst {
    &mut module.functions[1].blocks[0].body[0].inst
}

fn require_invalid_report(module: &Module, expected: impl Fn(&ValidationError) -> bool) {
    let errors = validate_module(module);
    assert!(
        errors.iter().any(&expected),
        "wrong structural refusal: {errors:#?}"
    );
    let report = validate_module_report(module);
    assert!(
        !report.is_ok(),
        "malformed source obtained complete validation"
    );
    let error = translate_validated_module_strict_for_arch_with_tls_and_validation_with_license(
        &report,
        GuardCarrierArch::AArch64,
        TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect_err("invalid full report must not authorize lowering");
    let AdapterError::InvalidTrustIr(detail) = error else {
        panic!("wrong invalid-report refusal: {error:?}");
    };
    assert!(
        detail.contains("successful full-module validation report"),
        "{detail}"
    );
    assert!(
        !detail.contains("non-propagating call boundary"),
        "malformed typing counted as a boundary refusal: {detail}"
    );
}

#[test]
fn disconnected_mutants_keep_unreachable_block_and_full_report_refusals() {
    let mut cells = 0;
    let mut boundary_refusals = 0;
    for indirect in [false, true] {
        for result in [false, true] {
            let mut mutant = fixture(indirect, result, true, true);
            validated(&mutant);
            // Remove exactly the edge to bb11. The exit remains reachable
            // with its authentic argument; bb11 is now genuinely malformed.
            mutant.functions[1].blocks[0].body = vec![InstrNode::new(Inst::Br {
                target: BlockId::new(12),
                args: if result {
                    vec![ValueId::new(u32::from(indirect))]
                } else {
                    vec![]
                },
            })];
            assert_eq!(
                validate_module(&mutant),
                vec![ValidationError::UnreachableBlock(11)]
            );
            require_invalid_report(&mutant, |error| {
                matches!(error, ValidationError::UnreachableBlock(11))
            });
            // Compatibility lowering retains its existing selective
            // diagnostic tolerance, but may never erase the stored boundary.
            for (route, outcome) in [
                (
                    "disconnected function floor",
                    trust_cg_lower::translate_function_with_license(
                        &mutant.functions[1],
                        &mutant,
                        &permit_unlicensed(),
                    )
                    .map(drop),
                ),
                (
                    "disconnected module floor",
                    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                        &mutant,
                        trust_cg_lower::GuardCarrierArch::default(),
                        trust_cg_lower::TlsDialect::default(),
                        &permit_unlicensed(),
                    )
                    .map(drop),
                ),
            ] {
                require_refusal(outcome, indirect, route);
                boundary_refusals += 1;
            }
            cells += 1;
        }
    }
    assert_eq!((cells, boundary_refusals), (4, 8));
}

#[test]
fn malformed_callee_signature_arguments_and_ssa_keep_structural_refusals() {
    let mut controls = 0;
    for indirect in [false, true] {
        for boundary in [false, true] {
            let control = fixture(indirect, true, false, boundary);
            validated(&control);
            let mut missing = control.clone();
            match call_mut(&mut missing) {
                Inst::Call { callee, .. } | Inst::CallCannotUnwind { callee, .. } => {
                    *callee = FuncId::new(999)
                }
                Inst::CallIndirect { sig, .. } | Inst::CallIndirectCannotUnwind { sig, .. } => {
                    *sig = FuncTyId::new(999)
                }
                _ => panic!("actual call fixture"),
            }
            require_invalid_report(&missing, |error| {
                matches!(
                    error,
                    ValidationError::CalleeNotFound { callee_id: 999, .. }
                        | ValidationError::CallIndirectSigNotFound { sig_id: 999, .. }
                )
            });
            let mut wrong_arity = control.clone();
            match call_mut(&mut wrong_arity) {
                Inst::Call { args, .. }
                | Inst::CallCannotUnwind { args, .. }
                | Inst::CallIndirect { args, .. }
                | Inst::CallIndirectCannotUnwind { args, .. } => args.clear(),
                _ => panic!("actual call fixture"),
            }
            require_invalid_report(&wrong_arity, |error| {
                matches!(
                    error,
                    ValidationError::CallArgCountMismatch { .. }
                        | ValidationError::CallIndirectArgCountMismatch { .. }
                )
            });
            let mut undefined = control.clone();
            match call_mut(&mut undefined) {
                Inst::Call { args, .. }
                | Inst::CallCannotUnwind { args, .. }
                | Inst::CallIndirect { args, .. }
                | Inst::CallIndirectCannotUnwind { args, .. } => args[0] = ValueId::new(999),
                _ => panic!("actual call fixture"),
            }
            require_invalid_report(&undefined, |error| {
                matches!(error, ValidationError::UseBeforeDef { value: 999, .. })
            });
            let mut duplicate = control;
            let argument = ValueId::new(u32::from(indirect));
            duplicate.functions[1].blocks[0].body.insert(
                0,
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(argument),
            );
            require_invalid_report(&duplicate, |error| {
                matches!(error, ValidationError::DuplicateValueDef { .. })
            });
            // Compatibility lowering already consumes duplicate-SSA validity
            // by name; preserve that guard instead of hiding behind the floor.
            for outcome in [
                trust_cg_lower::translate_function_with_license(
                    &duplicate.functions[1],
                    &duplicate,
                    &permit_unlicensed(),
                )
                .map(drop),
                trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                    &duplicate,
                    trust_cg_lower::GuardCarrierArch::default(),
                    trust_cg_lower::TlsDialect::default(),
                    &permit_unlicensed(),
                )
                .map(drop),
            ] {
                assert!(
                    matches!(outcome, Err(AdapterError::InvalidTrustIr(_))),
                    "duplicate SSA escaped the existing prerequisite: {outcome:?}"
                );
            }
            controls += 4;
        }
    }
    assert_eq!(controls, 16);
}

#[test]
fn statically_authenticated_indirect_cc_mismatch_is_not_a_boundary_control() {
    for boundary in [false, true] {
        let mut source = fixture(true, true, false, boundary);
        // A dynamic parameter has no statically authenticatable convention.
        // Use a real typed FnDef of this module's C callee for this mutation.
        let signature = source.functions[0].ty;
        let callee_id = source.functions[0].id;
        match call_mut(&mut source) {
            Inst::CallIndirect { callee, .. } | Inst::CallIndirectCannotUnwind { callee, .. } => {
                *callee = ValueId::new(7)
            }
            _ => panic!("actual indirect fixture"),
        }
        source.functions[1].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::Const {
                ty: Ty::Func(signature),
                value: Constant::FnDef(callee_id),
            })
            .with_result(ValueId::new(7)),
        );
        validated(&source);
        // Independently ordinary-call input: this test twin authenticates the
        // same literal C signature/target without claiming that dropping a
        // boundary is a compiler transformation or that its callee is NoPanic.
        let mut ordinary = source.clone();
        ordinary.functions[1].blocks[0].body[1].inst = Inst::CallIndirect {
            callee: ValueId::new(7),
            sig: signature,
            args: vec![ValueId::new(1)],
            calling_conv: CallingConv::C,
        };
        validated(&ordinary);
        trust_cg_lower::translate_function_with_license(
            &ordinary.functions[1],
            &ordinary,
            &permit_unlicensed(),
        )
        .expect("matching C metadata control");
        match &mut source.functions[1].blocks[0].body[1].inst {
            Inst::CallIndirect { calling_conv, .. }
            | Inst::CallIndirectCannotUnwind { calling_conv, .. } => {
                *calling_conv = CallingConv::Rust
            }
            _ => panic!("actual statically authenticated indirect call"),
        }
        require_invalid_report(&source, |error| {
            matches!(error, ValidationError::CallEdgeConvMismatch { .. })
        });
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
