// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Replay actual ordinary conditional pipeline DATA at all four UInt widths.
//! Fixture bytes arrive from the qualified producer; no equation/proof is
//! reconstructed here. The production consumer independently rebuilds its
//! judgment from the full module and caller-selected original source inputs.

use super::{DefinitionData, Fixture, load};
use trust_ir::inst::{ICmpOp, Inst};
use trust_ir::{Constant, FuncTyId, Ty};
use trust_ir_build::clean_kernel::{BinderInfo, Declaration, Expr, ExprKind};
use trust_ir_build::{SourceValueEquationError, check_uint_source_value_equation};

macro_rules! conditional_raw {
    ($case:literal, $file:literal) => {
        include_bytes!(concat!(
            "../../../../tests/fixtures/trust_ir_source_value/conditionals/",
            $case,
            "/",
            $file
        ))
    };
}
macro_rules! conditional_fixture {
    ($case:literal) => {
        Fixture {
            expected_source: $case,
            module: conditional_raw!($case, "module.bin"),
            definitions: vec![DefinitionData {
                name: conditional_raw!($case, "definition-0.name.bin"),
                type_: conditional_raw!($case, "definition-0.type.bin"),
                value: conditional_raw!($case, "definition-0.value.bin"),
                is_reducible: false,
            }],
            theorem_name: conditional_raw!($case, "theorem.name.bin"),
            theorem_type: conditional_raw!($case, "theorem.type.bin"),
            theorem_value: conditional_raw!($case, "theorem.value.bin"),
            original_source_digest: conditional_raw!($case, "source-closure-digest.bin"),
        }
    };
}

fn fixtures() -> [(Ty, Fixture); 4] {
    [
        (Ty::U8, conditional_fixture!("boundConditional8")),
        (Ty::U16, conditional_fixture!("boundConditional16")),
        (Ty::U32, conditional_fixture!("boundConditional32")),
        (Ty::U64, conditional_fixture!("boundConditional64")),
    ]
}

#[test]
fn conditional_actual_producer_equations_pass_at_all_four_uint_widths() {
    for (expected_type, fixture) in fixtures() {
        let (module, environment, source, proposed, function) = load(&fixture);
        let before = module.clone();
        let checked =
            check_uint_source_value_equation(&module, function, &environment, &source, &proposed)
                .unwrap_or_else(|error| panic!("{}: {error}", fixture.expected_source));
        let signature = &module.func_types[checked.function().ty.as_usize()];
        assert_eq!(
            signature.params,
            [expected_type.clone(), expected_type.clone()]
        );
        assert_eq!(signature.returns, [expected_type]);
        let Declaration::Theorem { type_, value, .. } = &proposed else {
            unreachable!()
        };
        assert_eq!(checked.judgment(), type_);
        assert_eq!(checked.proof(), value);
        let audit = environment.audit_certification(checked.judgment(), checked.proof());
        assert!(
            audit.is_certified(),
            "{}: {:?}",
            fixture.expected_source,
            audit.issues
        );
        assert!(core::ptr::eq(checked.module(), &module));
        assert_eq!(
            module, before,
            "the value check preserves every body/license/grade"
        );
    }
}

#[test]
fn conditional_actual_module_comparison_arms_operands_and_literals_refuse() {
    for (_, fixture) in fixtures() {
        let (module, environment, source, proposed, function) = load(&fixture);
        for label in [
            "comparison",
            "comparison operands",
            "arms",
            "literal",
            "parameter order",
        ] {
            let mut changed = module.clone();
            let selected = changed
                .functions
                .iter_mut()
                .find(|f| f.id == function)
                .unwrap();
            match label {
                "comparison" | "comparison operands" => {
                    let node = selected
                        .blocks
                        .iter_mut()
                        .flat_map(|b| &mut b.body)
                        .find(|n| matches!(n.inst, Inst::ICmp { .. }))
                        .expect("actual source comparison");
                    let Inst::ICmp { op, lhs, rhs, .. } = &mut node.inst else {
                        unreachable!()
                    };
                    assert_eq!(
                        *op,
                        ICmpOp::Ult,
                        "the actual ordinary source uses strict unsigned LT"
                    );
                    if label == "comparison" {
                        *op = ICmpOp::Ule;
                    } else {
                        core::mem::swap(lhs, rhs);
                    }
                }
                "arms" => {
                    let node = selected
                        .blocks
                        .iter_mut()
                        .flat_map(|b| &mut b.body)
                        .find(|n| matches!(n.inst, Inst::CondBr { .. }))
                        .expect("actual Bool CondBr");
                    let Inst::CondBr {
                        then_target,
                        then_args,
                        else_target,
                        else_args,
                        ..
                    } = &mut node.inst
                    else {
                        unreachable!()
                    };
                    core::mem::swap(then_target, else_target);
                    core::mem::swap(then_args, else_args);
                }
                "literal" => {
                    let node = selected
                        .blocks
                        .iter_mut()
                        .flat_map(|b| &mut b.body)
                        .find(|n| {
                            matches!(
                                n.inst,
                                Inst::Const {
                                    value: Constant::Int(1),
                                    ..
                                }
                            )
                        })
                        .expect("the actual then arm adds literal one");
                    let Inst::Const {
                        value: Constant::Int(value),
                        ..
                    } = &mut node.inst
                    else {
                        unreachable!()
                    };
                    *value = 2;
                }
                "parameter order" => {
                    selected
                        .blocks
                        .iter_mut()
                        .find(|b| b.id == selected.entry)
                        .unwrap()
                        .params
                        .swap(0, 1);
                }
                _ => unreachable!(),
            }
            assert!(
                check_uint_source_value_equation(
                    &changed,
                    function,
                    &environment,
                    &source,
                    &proposed
                )
                .is_err(),
                "{}: changed actual {label} must refuse; unchanged producer certificate metadata also remains subject to canonical validation",
                fixture.expected_source
            );
        }
    }
}

#[test]
fn conditional_actual_source_binding_and_carried_proof_are_rechecked() {
    for (_, fixture) in fixtures() {
        let (module, mut environment, source, proposed, function) = load(&fixture);
        let Declaration::Theorem {
            name, type_, value, ..
        } = &proposed
        else {
            unreachable!()
        };
        for (label, forged) in [
            (
                "goal",
                Declaration::Theorem {
                    name: name.clone(),
                    level_params: vec![],
                    type_: Expr::prop(),
                    value: value.clone(),
                },
            ),
            (
                "proof",
                Declaration::Theorem {
                    name: name.clone(),
                    level_params: vec![],
                    type_: type_.clone(),
                    value: Expr::const_str("True.intro"),
                },
            ),
        ] {
            assert!(
                matches!(
                    check_uint_source_value_equation(
                        &module,
                        function,
                        &environment,
                        &source,
                        &forged
                    ),
                    Err(SourceValueEquationError::Rejected(_))
                ),
                "{}: producer-written {label} has no authority",
                fixture.expected_source
            );
        }
        let original_type = environment.get_const(&source).unwrap().type_.clone();
        let ExprKind::Pi(_, uint, _) = original_type.kind() else {
            panic!("actual UInt input signature")
        };
        let uint = uint.as_ref().clone();
        assert!(environment.forget_decl(&source));
        environment
            .add_decl(Declaration::Definition {
                name: source.clone(),
                level_params: vec![],
                type_: original_type,
                value: Expr::lam(
                    BinderInfo::Default,
                    uint.clone(),
                    Expr::lam(BinderInfo::Default, uint, Expr::bvar(1)),
                ),
                is_reducible: true,
            })
            .expect("a different same-name source body kernel-checks at the actual width");
        let result =
            check_uint_source_value_equation(&module, function, &environment, &source, &proposed);
        assert!(
            matches!(result, Err(SourceValueEquationError::Rejected(ref message)) if message.contains("strict certification audit")),
            "{}: unchanged claimed goal/proof must fail against its changed original source",
            fixture.expected_source
        );
    }
}

#[test]
fn conditional_complete_actual_module_keeps_unselected_bodies_and_helper_refusals() {
    for (_, fixture) in fixtures() {
        let (module, environment, source, proposed, function) = load(&fixture);
        let helper_name = format!("l_{}___boxed", fixture.expected_source);
        let helper = module
            .functions
            .iter()
            .find(|f| f.name == helper_name && !f.is_declaration())
            .expect("the original generated boxed helper remains in the full module");
        let strict = trust_ir_build::validate_module_for_codegen(&module);
        assert!(strict.iter().any(|error| matches!(error,
            trust_ir_build::ValidationError::UngatedBodyForCodegen { function, .. } if *function == helper.id.index())),
            "{}: actual helper still refuses codegen: {strict:?}", fixture.expected_source);
        let mut changed = module.clone();
        changed
            .functions
            .iter_mut()
            .find(|f| f.id == helper.id)
            .unwrap()
            .ty = FuncTyId::new(u32::MAX);
        assert!(
            matches!(
                check_uint_source_value_equation(
                    &changed,
                    function,
                    &environment,
                    &source,
                    &proposed
                ),
                Err(SourceValueEquationError::InvalidModule(_))
            ),
            "{}: an invalid unselected helper cannot be filtered out",
            fixture.expected_source
        );
    }
}

#[test]
fn checked_source_equations_do_not_license_the_native_backend_or_remove_helpers() {
    use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
    use trust_cg_codegen::target::TargetSpec;
    use trust_cg_lower::CodegenLicensePolicy;
    use trust_cg_lower::adapter::AdapterError;

    for (_, fixture) in fixtures() {
        let (module, environment, source, proposed, function) = load(&fixture);
        let before = module.clone();
        let checked =
            check_uint_source_value_equation(&module, function, &environment, &source, &proposed)
                .expect("actual source equation checks in the native consumer dependency graph");
        assert!(core::ptr::eq(checked.module(), &module));
        let helper_name = format!("l_{}___boxed", fixture.expected_source);
        let helper = module
            .functions
            .iter()
            .find(|f| f.name == helper_name)
            .expect("retain the generated boxed helper");
        assert!(
            matches!(CodegenLicensePolicy::default().verdict(&module, helper.id),
            Err(AdapterError::UngatedBody { function }) if function == helper_name),
            "equation checking cannot authorize the helper body"
        );
        let target = TargetSpec::parse("aarch64-apple-darwin").unwrap();
        assert!(
            Compiler::new_for_target_spec(CompilerConfig::default(), target)
                .compile(&module)
                .is_err(),
            "the full original module must still refuse emission"
        );
        assert_eq!(
            module, before,
            "source equation checks and native refusal do not rewrite evidence"
        );
    }
}
