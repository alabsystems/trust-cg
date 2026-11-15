// trust-cg-codegen/dialect_legalization_tests.rs - unit tests for dialect legalization
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Ledger L05-P11. Registry construction refusals, exact-name legalization
// refusals, the proof policy, one positive case per registered op and type
// lowering kind, the payload descriptor's exact bytes, and corruption controls
// on receipts. Native execution lives in
// tests/dialect_legalization_corpus.rs.

use super::*;
use trust_ir::dialect::schema::{AttributeKind, AttributeSchema, OperandType, OperationSchema};
use trust_ir::dialect::{AttrValue, DialectInst};
use trust_ir::{BinOp, Block, ICmpOp, StructId};

const NS: &str = "acme";
const NS_VERSION: u32 = 2;

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn aarch64() -> LegalizationOptions {
    LegalizationOptions::new(Target::Aarch64, false)
}

fn proof_required() -> LegalizationOptions {
    LegalizationOptions::new(Target::Aarch64, true)
}

fn handle_ty() -> Ty {
    Ty::Dialect(Box::new(DialectTy::new(NS, "handle", 1)))
}

fn op_node(op: DialectInst, result: Option<u32>) -> InstrNode {
    let node = InstrNode::new(Inst::DialectOp(Box::new(op)));
    match result {
        Some(result) => node.with_result(v(result)),
        None => node,
    }
}

fn ret(values: &[u32]) -> InstrNode {
    InstrNode::new(Inst::Return {
        values: values.iter().map(|value| v(*value)).collect(),
    })
}

/// A module with one function `f(params) -> returns` whose entry block binds
/// the parameters to values `0..params.len()`.
fn module_with(params: Vec<Ty>, returns: Vec<Ty>, body: Vec<InstrNode>) -> Module {
    let mut module = Module::new("unit");
    let ty = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "f", ty, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = params
        .into_iter()
        .enumerate()
        .map(|(index, ty)| (v(index as u32), ty))
        .collect();
    block.body = body;
    function.blocks.push(block);
    module.functions.push(function);
    module
}

fn scale_op(operand: u32, factor: i64) -> DialectInst {
    let mut op = DialectInst::new(NS, "scale")
        .with_operand(v(operand))
        .with_result_ty(Ty::I64)
        .with_attr("factor", AttrValue::I64(factor));
    op.version = NS_VERSION;
    op
}

fn twice_op(operand: u32) -> DialectInst {
    let mut op = DialectInst::new(NS, "twice")
        .with_operand(v(operand))
        .with_result_ty(Ty::I64);
    op.version = NS_VERSION;
    op
}

/// `acme.twice(x)` -> `x + x`.
fn twice_rewrite(
    _node: &InstrNode,
    op: &DialectInst,
    results: &[ValueId],
    _context: &mut LoweringContext<'_>,
) -> RewriteOutcome {
    let ([result], [operand]) = (results, op.operands.as_slice()) else {
        return RewriteOutcome::Err("acme.twice needs one operand and one result".to_string());
    };
    RewriteOutcome::Replace(vec![
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: *operand,
            rhs: *operand,
        })
        .with_result(*result),
    ])
}

fn acme_schema(
    name: &str,
    operands: Vec<Ty>,
    results: Vec<Ty>,
    attrs: &[(&str, AttributeKind)],
) -> OperationSchema {
    OperationSchema {
        name: name.to_string(),
        operands: operands.into_iter().map(OperandType::Exact).collect(),
        results,
        attributes: attrs
            .iter()
            .map(|(name, kind)| AttributeSchema {
                name: name.to_string(),
                kind: *kind,
            })
            .collect(),
    }
}

/// A test-owned exact-grammar dialect exercising every lowering kind.
fn acme_registration() -> DialectRegistration {
    DialectRegistration {
        namespace: NS.to_string(),
        version: NS_VERSION,
        owner: "trust-cg unit tests (acme)".to_string(),
        grammar: DialectGrammar::Exact(vec![
            acme_schema(
                "scale",
                vec![Ty::I64],
                vec![Ty::I64],
                &[("factor", AttributeKind::I64)],
            ),
            acme_schema("twice", vec![Ty::I64], vec![Ty::I64], &[]),
            acme_schema("noop", vec![Ty::I64], vec![], &[]),
            acme_schema("touch", vec![handle_ty()], vec![], &[]),
        ]),
        ops: vec![
            OpRule::single(
                "twice",
                "acme.twice/add-self",
                OpLowering::Rewrite(RewriteRule {
                    name: "x + x",
                    targets: RuleTargets::Any,
                    rewrite: twice_rewrite,
                }),
                LegalizationEvidence::TestedOnly {
                    tests: "dialect_legalization_tests.rs".to_string(),
                },
            ),
            OpRule::single(
                "noop",
                "acme.noop/unbound",
                OpLowering::Unbound {
                    reason: "acme.noop has no runtime".to_string(),
                },
                LegalizationEvidence::Unbound,
            ),
            OpRule::single(
                "touch",
                "acme.touch/adapter-native",
                OpLowering::AdapterNative,
                LegalizationEvidence::AdapterInstructionLowering,
            ),
        ],
        types: vec![
            TypeRule {
                name: "handle".to_string(),
                version: 1,
                carrier: Ty::Ptr,
                rule: "acme.handle@1/ptr-carrier".to_string(),
                evidence: LegalizationEvidence::CheckedTransportSubstitution,
            },
            TypeRule {
                name: "tested".to_string(),
                version: 1,
                carrier: Ty::I32,
                rule: "acme.tested@1/i32-carrier".to_string(),
                evidence: LegalizationEvidence::TestedOnly {
                    tests: "dialect_legalization_tests.rs".to_string(),
                },
            },
        ],
    }
    .bind_runtime_call("scale", "acme_scale", "the acme test runtime")
}

fn registry_with(extra: Vec<DialectRegistration>) -> DialectLegalizationRegistry {
    let mut registrations = DialectLegalizationRegistry::default_registrations();
    registrations.extend(extra);
    DialectLegalizationRegistry::new(registrations).expect("test registry is well-formed")
}

fn acme_registry() -> DialectLegalizationRegistry {
    registry_with(vec![acme_registration()])
}

fn refusal(registrations: Vec<DialectRegistration>) -> RegistrationError {
    DialectLegalizationRegistry::new(registrations).expect_err("malformed registration")
}

fn first_rule(registration: &mut DialectRegistration) -> &mut RuleAlternative {
    &mut registration.ops[0].alternatives[0]
}

// ---------------------------------------------------------------------------
// The registry
// ---------------------------------------------------------------------------

#[test]
fn default_registry_declares_the_backend_dialects() {
    let registry = DialectLegalizationRegistry::trust_cg_default();
    let namespaces: Vec<(&str, u32)> = registry
        .registrations()
        .iter()
        .map(|registration| (registration.namespace.as_str(), registration.version))
        .collect();
    assert_eq!(
        namespaces,
        vec![
            ("trust-cg", 1),
            ("trust-cg-aarch64-fp", 1),
            ("vector", 1),
            ("verif", 1)
        ]
    );
    let vector = registry.get("vector").expect("vector registered");
    let mut ops: Vec<&str> = vector.ops.iter().map(|rule| rule.op.as_str()).collect();
    ops.sort_unstable();
    let mut declared: Vec<&str> = trust_ir::dialect::vector::VectorDialect.ops().to_vec();
    declared.sort_unstable();
    assert_eq!(ops, declared, "every vector op has exactly one rule");
    assert_eq!(registry.digest().len(), 64);
    assert!(
        registry
            .digest()
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit())
    );
    assert_eq!(
        registry.digest(),
        DialectLegalizationRegistry::new(DialectLegalizationRegistry::default_registrations())
            .unwrap()
            .digest(),
        "the digest is a function of the registrations"
    );
    let mut changed = DialectLegalizationRegistry::default_registrations();
    changed[0].owner.push('!');
    assert_ne!(
        registry.digest(),
        DialectLegalizationRegistry::new(changed).unwrap().digest(),
        "the digest covers the owner statement"
    );
    assert!(acme_registry().get(NS).is_some());
    assert!(registry.get(NS).is_none());
}

#[test]
fn malformed_registrations_are_refused_by_name() {
    type Mutation = fn(&mut Vec<DialectRegistration>);
    let cases: Vec<(&str, Mutation, &str)> = vec![
        (
            "dotted namespace",
            |r| r[0].namespace = "a.b".into(),
            "InvalidNamespace",
        ),
        (
            "empty namespace",
            |r| r[0].namespace = String::new(),
            "InvalidNamespace",
        ),
        ("version 0", |r| r[0].version = 0, "ZeroVersion"),
        ("blank owner", |r| r[0].owner = "  ".into(), "MissingOwner"),
        (
            "duplicate namespace",
            |r| r.push(acme_registration()),
            "DuplicateNamespace",
        ),
        (
            "validator for another dialect",
            |r| r[0].grammar = DialectGrammar::Validator(Arc::new(LenientVectorDialect)),
            "ValidatorMismatch",
        ),
        (
            "non-closed exact type",
            |r| {
                if let DialectGrammar::Exact(ops) = &mut r[0].grammar {
                    ops[0].results = vec![Ty::Struct(StructId::new(0))];
                }
            },
            "Schema",
        ),
        (
            "declared op without rule",
            |r| {
                r[0].ops.retain(|rule| rule.op != "noop");
            },
            "OpWithoutRule",
        ),
        (
            "rule for an undeclared op",
            |r| {
                let mut rule = r[0].ops[0].clone();
                rule.op = "ghost".into();
                rule.alternatives[0].rule = "acme.ghost/x".into();
                r[0].ops.push(rule);
            },
            "RuleWithoutOp",
        ),
        (
            "two rules for one op",
            |r| {
                let mut rule = r[0].ops[0].clone();
                rule.alternatives[0].rule = "acme.twice/again".into();
                r[0].ops.push(rule);
            },
            "DuplicateOpRule",
        ),
        (
            "no alternative",
            |r| r[0].ops[0].alternatives.clear(),
            "Alternatives",
        ),
        (
            "guarded last alternative",
            |r| {
                first_rule(&mut r[0]).guard = Some(SiteGuard {
                    name: "always",
                    admits: |_| true,
                })
            },
            "Alternatives",
        ),
        (
            "unguarded alternative before the last",
            |r| {
                let mut second = r[0].ops[0].alternatives[0].clone();
                second.rule = "acme.twice/second".into();
                r[0].ops[0].alternatives.push(second);
            },
            "Alternatives",
        ),
        (
            "unbound without a reason",
            |r| {
                let rule = r[0].ops.iter_mut().find(|rule| rule.op == "noop").unwrap();
                rule.alternatives[0].lowering = OpLowering::Unbound { reason: " ".into() };
            },
            "Alternatives",
        ),
        (
            "rule id with whitespace",
            |r| first_rule(&mut r[0]).rule = "acme twice".into(),
            "InvalidRuleId",
        ),
        (
            "duplicate rule id",
            |r| first_rule(&mut r[0]).rule = "acme.noop/unbound".into(),
            "DuplicateRuleId",
        ),
        (
            "runtime symbol that is not a C identifier",
            |r| {
                let rule = r[0].ops.iter_mut().find(|rule| rule.op == "scale").unwrap();
                rule.alternatives[0].lowering = OpLowering::RuntimeCall {
                    symbol: "acme-scale".into(),
                };
            },
            "RuntimeBinding",
        ),
        (
            "runtime call on a validator grammar",
            |r| r[0] = vector_registration().bind_runtime_call("reduce", "vector_reduce", "x"),
            "RuntimeBinding",
        ),
        (
            "runtime call with two results",
            |r| {
                if let DialectGrammar::Exact(ops) = &mut r[0].grammar {
                    let scale = ops.iter_mut().find(|op| op.name == "scale").unwrap();
                    scale.results = vec![Ty::I64, Ty::I64];
                }
            },
            "RuntimeBinding",
        ),
        (
            "runtime call with a variadic operand",
            |r| {
                if let DialectGrammar::Exact(ops) = &mut r[0].grammar {
                    let scale = ops.iter_mut().find(|op| op.name == "scale").unwrap();
                    scale.operands = vec![OperandType::VariadicExact(Ty::I64)];
                }
            },
            "RuntimeBinding",
        ),
        (
            "type name with a dot",
            |r| r[0].types[0].name = "a.b".into(),
            "TypeRule",
        ),
        ("type version 0", |r| r[0].types[0].version = 0, "TypeRule"),
        (
            "type registered twice",
            |r| {
                let mut again = r[0].types[0].clone();
                again.rule = "acme.handle@1/again".into();
                r[0].types.push(again);
            },
            "TypeRule",
        ),
        (
            "float carrier",
            |r| r[0].types[0].carrier = Ty::F64,
            "TypeRule",
        ),
        (
            "128-bit carrier",
            |r| r[0].types[0].carrier = Ty::I128,
            "TypeRule",
        ),
        (
            "nominal type in a namespace trust-ir cannot spell",
            |r| {
                let mut typed = bitfield_registration();
                typed.types.push(r[0].types[0].clone());
                r[0] = typed;
            },
            "TypeRule",
        ),
        (
            "empty cited theorem",
            |r| {
                first_rule(&mut r[0]).evidence = LegalizationEvidence::CitedUpstreamTheorem {
                    theorem: String::new(),
                    source: "s".into(),
                }
            },
            "Evidence",
        ),
        (
            "empty test list",
            |r| {
                first_rule(&mut r[0]).evidence =
                    LegalizationEvidence::TestedOnly { tests: " ".into() }
            },
            "Evidence",
        ),
        (
            "empty runtime owner",
            |r| {
                let rule = r[0].ops.iter_mut().find(|rule| rule.op == "scale").unwrap();
                rule.alternatives[0].evidence = LegalizationEvidence::RuntimeContract {
                    runtime: String::new(),
                };
            },
            "Evidence",
        ),
        (
            "rewrite claiming the transport class",
            |r| first_rule(&mut r[0]).evidence = LegalizationEvidence::CheckedTransportSubstitution,
            "Evidence",
        ),
        (
            "rewrite claiming adapter lowering",
            |r| first_rule(&mut r[0]).evidence = LegalizationEvidence::AdapterInstructionLowering,
            "Evidence",
        ),
        (
            "adapter-native claiming tests",
            |r| {
                let rule = r[0].ops.iter_mut().find(|rule| rule.op == "touch").unwrap();
                rule.alternatives[0].evidence =
                    LegalizationEvidence::TestedOnly { tests: "t".into() };
            },
            "Evidence",
        ),
        (
            "runtime call claiming tests",
            |r| {
                let rule = r[0].ops.iter_mut().find(|rule| rule.op == "scale").unwrap();
                rule.alternatives[0].evidence =
                    LegalizationEvidence::TestedOnly { tests: "t".into() };
            },
            "Evidence",
        ),
        (
            "unbound claiming tests",
            |r| {
                let rule = r[0].ops.iter_mut().find(|rule| rule.op == "noop").unwrap();
                rule.alternatives[0].evidence =
                    LegalizationEvidence::TestedOnly { tests: "t".into() };
            },
            "Evidence",
        ),
        (
            "type rule claiming adapter lowering",
            |r| r[0].types[0].evidence = LegalizationEvidence::AdapterInstructionLowering,
            "Evidence",
        ),
    ];
    for (label, mutate, variant) in cases {
        let mut registrations = vec![acme_registration()];
        mutate(&mut registrations);
        let error = refusal(registrations);
        assert!(
            format!("{error:?}").starts_with(variant),
            "{label}: expected {variant}, got {error:?}"
        );
        assert!(
            error.to_string().starts_with("[TCG-DIALECT-REGISTRATION]"),
            "{label}: {error}"
        );
    }
}

// ---------------------------------------------------------------------------
// Exact-name refusals
// ---------------------------------------------------------------------------

fn legalize_err(
    module: &Module,
    registry: &DialectLegalizationRegistry,
    options: LegalizationOptions,
) -> DialectPipelineError {
    legalize_module(module, registry, options).expect_err("legalization must refuse")
}

#[test]
fn unregistered_dialects_ops_and_types_are_refused_by_exact_name() {
    let registry = acme_registry();

    let ghost_op = module_with(
        vec![],
        vec![Ty::I64],
        vec![
            op_node(
                DialectInst::new("ghost", "op").with_result_ty(Ty::I64),
                Some(0),
            ),
            ret(&[0]),
        ],
    );
    let error = legalize_err(&ghost_op, &registry, aarch64());
    assert!(
        matches!(&error, DialectPipelineError::UnregisteredDialect { namespace, usage }
            if namespace == "ghost" && usage.contains("`ghost.op`") && usage.contains("`f`")),
        "{error:?}"
    );
    assert!(error.to_string().starts_with("[TCG-DIALECT-UNREGISTERED]"));

    let ghost_ty = Ty::Dialect(Box::new(DialectTy::new("ghost", "t", 1)));
    let ghost_type = module_with(vec![ghost_ty.clone()], vec![ghost_ty], vec![ret(&[0])]);
    let error = legalize_err(&ghost_type, &registry, aarch64());
    assert!(
        matches!(&error, DialectPipelineError::UnregisteredDialect { namespace, usage }
            if namespace == "ghost" && usage == "nominal type `ghost.t@1`"),
        "{error:?}"
    );

    let mut frob = DialectInst::new(NS, "frobnicate").with_operand(v(0));
    frob.version = NS_VERSION;
    let unknown_op = module_with(vec![Ty::I64], vec![], vec![op_node(frob, None), ret(&[])]);
    let error = legalize_err(&unknown_op, &registry, aarch64());
    assert!(
        matches!(&error, DialectPipelineError::UnregisteredOp { dialect, version, op, function }
            if dialect == NS && *version == NS_VERSION && op == "frobnicate" && function == "f"),
        "{error:?}"
    );

    for (name, version) in [("handle", 2), ("other", 1)] {
        let ty = Ty::Dialect(Box::new(DialectTy::new(NS, name, version)));
        let module = module_with(vec![ty.clone()], vec![ty], vec![ret(&[0])]);
        let error = legalize_err(&module, &registry, aarch64());
        assert!(
            matches!(&error, DialectPipelineError::UnregisteredType { namespace, name: n, type_version, .. }
                if namespace == NS && n == name && *type_version == version),
            "{error:?}"
        );
    }

    let malformed = Ty::Dialect(Box::new(DialectTy::new("bad.ns", "t", 1)));
    let module = module_with(vec![malformed.clone()], vec![malformed], vec![ret(&[0])]);
    let error = legalize_err(&module, &registry, aarch64());
    assert!(
        matches!(&error, DialectPipelineError::MalformedType { namespace, .. } if namespace == "bad.ns"),
        "{error:?}"
    );
}

#[test]
fn grammar_violations_are_refused_with_the_op_name() {
    let registry = acme_registry();
    let cases: Vec<(&str, Module)> = vec![
        (
            "operand type",
            module_with(
                vec![Ty::I32],
                vec![Ty::I64],
                vec![op_node(scale_op(0, 3), Some(1)), ret(&[1])],
            ),
        ),
        ("missing attribute", {
            let mut op = scale_op(0, 3);
            op.attrs.clear();
            module_with(
                vec![Ty::I64],
                vec![Ty::I64],
                vec![op_node(op, Some(1)), ret(&[1])],
            )
        }),
        ("payload version", {
            let mut op = scale_op(0, 3);
            op.version = NS_VERSION + 1;
            module_with(
                vec![Ty::I64],
                vec![Ty::I64],
                vec![op_node(op, Some(1)), ret(&[1])],
            )
        }),
    ];
    for (label, module) in cases {
        let error = legalize_err(&module, &registry, aarch64());
        assert!(
            matches!(&error, DialectPipelineError::Grammar { dialect, op, function, .. }
                if dialect == NS && op == "scale" && function == "f"),
            "{label}: {error:?}"
        );
        assert!(
            error.to_string().starts_with("[TCG-DIALECT-GRAMMAR]"),
            "{label}"
        );
    }

    let odd = Ty::Vector(Box::new(Ty::I8), 3);
    let module = module_with(
        vec![Ty::I8; 3],
        vec![odd.clone()],
        vec![
            op_node(
                trust_ir::dialect::vector::pack_lanes(odd, [v(0), v(1), v(2)]),
                Some(3),
            ),
            ret(&[3]),
        ],
    );
    let error = legalize_err(&module, &registry, aarch64());
    assert!(
        matches!(&error, DialectPipelineError::Grammar { dialect, op, .. }
            if dialect == "vector" && op == "pack_lanes"),
        "{error:?}"
    );
}

#[test]
fn nominal_values_outside_transport_are_refused() {
    let registry = acme_registry();
    // Arithmetic on a nominal value: trust-ir's nominal rule refuses it, so a
    // carrier substitution would give it a meaning the source never had.
    let module = module_with(
        vec![handle_ty()],
        vec![],
        vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: handle_ty(),
                lhs: v(0),
                rhs: v(0),
            })
            .with_result(v(1)),
            ret(&[]),
        ],
    );
    let error = legalize_err(&module, &registry, aarch64());
    assert!(
        matches!(error, DialectPipelineError::NominalUse { .. }),
        "{error:?}"
    );
    assert!(error.to_string().starts_with("[TCG-DIALECT-NOMINAL]"));

    // A dialect op may touch only its own namespace's nominal types.
    let other = DialectRegistration {
        namespace: "other".to_string(),
        version: 1,
        owner: "trust-cg unit tests (other)".to_string(),
        grammar: DialectGrammar::Exact(vec![acme_schema("make", vec![], vec![handle_ty()], &[])]),
        ops: vec![OpRule::single(
            "make",
            "other.make/adapter-native",
            OpLowering::AdapterNative,
            LegalizationEvidence::AdapterInstructionLowering,
        )],
        types: Vec::new(),
    };
    let registry = registry_with(vec![acme_registration(), other]);
    let module = module_with(
        vec![],
        vec![handle_ty()],
        vec![
            op_node(
                DialectInst::new("other", "make").with_result_ty(handle_ty()),
                Some(0),
            ),
            ret(&[0]),
        ],
    );
    let error = legalize_err(&module, &registry, aarch64());
    assert!(
        matches!(&error, DialectPipelineError::NominalUse { detail }
            if detail.contains("`other.make`") && detail.contains("`acme.handle@1`")),
        "{error:?}"
    );
}

#[test]
fn unbound_and_target_unsupported_rules_are_refused_by_name() {
    let registry = acme_registry();
    let mut noop = DialectInst::new(NS, "noop").with_operand(v(0));
    noop.version = NS_VERSION;
    let module = module_with(vec![Ty::I64], vec![], vec![op_node(noop, None), ret(&[])]);
    let error = legalize_err(&module, &registry, aarch64());
    assert!(
        matches!(&error, DialectPipelineError::Unbound { dialect, op, reason, .. }
            if dialect == NS && op == "noop" && reason == "acme.noop has no runtime"),
        "{error:?}"
    );

    let v4f32 = Ty::Vector(Box::new(Ty::F32), 4);
    let fma = module_with(
        vec![v4f32.clone(); 3],
        vec![v4f32.clone()],
        vec![
            op_node(
                trust_ir::dialect::vector::fma(v4f32, v(0), v(1), v(2)),
                Some(3),
            ),
            ret(&[3]),
        ],
    );
    let error = legalize_err(
        &fma,
        &registry,
        LegalizationOptions::new(Target::X86_64, false),
    );
    assert!(
        matches!(&error, DialectPipelineError::TargetUnsupported { op, rule, target, .. }
            if op == "fma" && rule == "vector.fma/aarch64-per-lane-fmadd" && target == "X86_64"),
        "{error:?}"
    );
    legalize_module(&fma, &registry, aarch64()).expect("AArch64 implements the fma rule");

    // trust-ir's lane expansions emit core trust-ir, but their output has
    // been executed on AArch64 only: every other target refuses them by name.
    use trust_ir::dialect::vector as vd;
    let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
    let reduce = module_with(
        vec![v4i32.clone()],
        vec![Ty::I32],
        vec![
            op_node(
                vd::reduce(v4i32.clone(), v(0), vd::ReduceKind::Add),
                Some(1),
            ),
            ret(&[1]),
        ],
    );
    let shuffle = module_with(
        vec![v4i32.clone()],
        vec![v4i32.clone()],
        vec![
            op_node(vd::shuffle(v4i32, v(0), vec![3u8, 2, 1, 0]), Some(1)),
            ret(&[1]),
        ],
    );
    let default = DialectLegalizationRegistry::trust_cg_default();
    for target in [Target::X86_64, Target::Riscv64] {
        for (module, op, rule) in [
            (&reduce, "reduce", "vector.reduce/trust-ir-lane-fold"),
            (&shuffle, "shuffle", "vector.shuffle/trust-ir-lane-gather"),
        ] {
            let error = legalize_err(module, &default, LegalizationOptions::new(target, false));
            assert!(
                matches!(&error, DialectPipelineError::TargetUnsupported { op: o, rule: r, supported, .. }
                    if o == op && r == rule && *supported == "AArch64"),
                "{target:?}: {error:?}"
            );
            assert!(error.to_string().starts_with("[TCG-DIALECT-TARGET]"));
        }
    }
    legalize_module(&reduce, &default, aarch64()).expect("AArch64 admits the lane fold");
    legalize_module(&shuffle, &default, aarch64()).expect("AArch64 admits the lane gather");
}

#[test]
fn opaque_masks_are_refused_before_the_adapter() {
    let v4bool = Ty::Vector(Box::new(Ty::Bool), 4);
    let module = module_with(
        vec![v4bool.clone()],
        vec![Ty::I32],
        vec![
            op_node(
                trust_ir::dialect::vector::mask_to_bits(v4bool, v(0), Ty::I32),
                Some(1),
            ),
            ret(&[1]),
        ],
    );
    let error = legalize_err(
        &module,
        &DialectLegalizationRegistry::trust_cg_default(),
        aarch64(),
    );
    assert!(
        matches!(&error, DialectPipelineError::Unbound { dialect, op, reason, .. }
            if dialect == "vector" && op == "mask_to_bits" && reason == OPAQUE_MASK_UNBOUND_REASON),
        "{error:?}"
    );
}

#[test]
fn proof_required_compilation_refuses_unchecked_rules_by_name() {
    let registry = acme_registry();
    let runtime = module_with(
        vec![Ty::I64],
        vec![Ty::I64],
        vec![op_node(scale_op(0, 3), Some(1)), ret(&[1])],
    );
    let error = legalize_err(&runtime, &registry, proof_required());
    assert!(
        matches!(&error, DialectPipelineError::ProofPolicy { rule, evidence, subject, .. }
            if rule == "acme.scale/runtime-call:acme_scale"
                && evidence.starts_with("runtime-contract")
                && subject.contains("`acme.scale`")),
        "{error:?}"
    );
    assert!(error.to_string().starts_with("[TCG-DIALECT-PROOF]"));
    legalize_module(&runtime, &registry, aarch64()).expect("admitted without a proof requirement");

    let rewrite = module_with(
        vec![Ty::I64],
        vec![Ty::I64],
        vec![op_node(twice_op(0), Some(1)), ret(&[1])],
    );
    let error = legalize_err(&rewrite, &registry, proof_required());
    assert!(
        matches!(&error, DialectPipelineError::ProofPolicy { rule, evidence, .. }
            if rule == "acme.twice/add-self" && evidence.starts_with("tested-only")),
        "{error:?}"
    );

    let tested = Ty::Dialect(Box::new(DialectTy::new(NS, "tested", 1)));
    let typed = module_with(vec![tested.clone()], vec![tested], vec![ret(&[0])]);
    let error = legalize_err(&typed, &registry, proof_required());
    assert!(
        matches!(&error, DialectPipelineError::ProofPolicy { rule, subject, .. }
            if rule == "acme.tested@1/i32-carrier" && subject == "type `acme.tested@1`"),
        "{error:?}"
    );

    // The checked classes are admitted.
    let handle = module_with(vec![handle_ty()], vec![handle_ty()], vec![ret(&[0])]);
    let legalized =
        legalize_module(&handle, &registry, proof_required()).expect("transport admitted");
    assert!(legalized.report.unwrap().proof_required);
    let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
    let kept = module_with(
        vec![Ty::I32; 4],
        vec![v4i32.clone()],
        vec![
            op_node(
                trust_ir::dialect::vector::pack_lanes(v4i32, [v(0), v(1), v(2), v(3)]),
                Some(4),
            ),
            ret(&[4]),
        ],
    );
    legalize_module(&kept, &registry, proof_required()).expect("adapter-native admitted");
}

#[test]
fn runtime_bindings_never_reuse_a_mismatched_symbol() {
    let registry = acme_registry();
    let base = module_with(
        vec![Ty::I64],
        vec![Ty::I64],
        vec![op_node(scale_op(0, 3), Some(1)), ret(&[1])],
    );

    let mut clash = base.clone();
    let wrong = clash
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    clash.functions.push(Function::new(
        FuncId::new(1),
        "acme_scale",
        wrong,
        BlockId::new(0),
    ));
    let error = legalize_err(&clash, &registry, aarch64());
    assert!(
        matches!(&error, DialectPipelineError::RuntimeBinding { op, detail, .. }
            if op == "scale" && detail.contains("already has a function `acme_scale`")),
        "{error:?}"
    );

    let mut global = base.clone();
    global.globals.push(Global {
        name: "acme_scale".into(),
        ty: Ty::I64,
        mutable: false,
        initializer: Some(Constant::Int(0)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });
    let error = legalize_err(&global, &registry, aarch64());
    assert!(
        matches!(&error, DialectPipelineError::RuntimeBinding { detail, .. }
            if detail.contains("already names a global")),
        "{error:?}"
    );

    // An existing declaration with the binding's exact signature is reused.
    let mut declared = base.clone();
    let exact = declared
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    declared.functions.push(Function::new(
        FuncId::new(1),
        "acme_scale",
        exact,
        BlockId::new(0),
    ));
    let legalized = legalize_module(&declared, &registry, aarch64()).expect("exact declaration");
    assert_eq!(
        legalized
            .module
            .functions
            .iter()
            .filter(|function| function.name == "acme_scale")
            .count(),
        1
    );
}

// ---------------------------------------------------------------------------
// Positive cases, one per lowering kind
// ---------------------------------------------------------------------------

fn dialect_ops(module: &Module) -> Vec<String> {
    module
        .instructions()
        .filter_map(|node| match &node.inst {
            Inst::DialectOp(op) => Some(op.qualified_name()),
            _ => None,
        })
        .collect()
}

#[test]
fn modules_without_dialect_constructs_are_borrowed_without_a_report() {
    let module = module_with(vec![Ty::I64], vec![Ty::I64], vec![ret(&[0])]);
    let legalized = legalize_module(&module, &acme_registry(), proof_required()).unwrap();
    assert!(matches!(legalized.module, Cow::Borrowed(_)));
    assert!(legalized.report.is_none());
}

#[test]
fn adapter_native_ops_are_kept_byte_for_byte_with_receipts() {
    let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
    let v4bool = Ty::Vector(Box::new(Ty::Bool), 4);
    let module = module_with(
        vec![Ty::I32, Ty::I32, Ty::I32, Ty::I32, Ty::I64, Ty::F64],
        vec![Ty::I32, Ty::I32, Ty::I64, Ty::F64],
        vec![
            op_node(
                trust_ir::dialect::vector::pack_lanes(v4i32.clone(), [v(0), v(1), v(2), v(3)]),
                Some(10),
            ),
            op_node(
                trust_ir::dialect::vector::insert_lane(v4i32.clone(), v(10), 1, v(0)),
                Some(11),
            ),
            op_node(
                trust_ir::dialect::vector::extract_lane(v4i32.clone(), v(11), 2),
                Some(12),
            ),
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Sgt,
                ty: v4i32,
                lhs: v(10),
                rhs: v(11),
            })
            .with_result(v(13)),
            InstrNode::new(Inst::Copy {
                ty: v4bool.clone(),
                operand: v(13),
            })
            .with_result(v(14)),
            op_node(
                trust_ir::dialect::vector::mask_to_bits(v4bool, v(14), Ty::I32),
                Some(15),
            ),
            op_node(
                trust_cg_lower::bitfield_dialect::extract_bits(Ty::I64, v(4), 3, 9),
                Some(16),
            ),
            op_node(
                trust_cg_lower::aarch64_fp_dialect::instruction(
                    trust_cg_lower::aarch64_fp_dialect::Operation::Fsqrt,
                    Ty::F64,
                    &[v(5)],
                ),
                Some(17),
            ),
            ret(&[12, 15, 16, 17]),
        ],
    );
    let legalized = legalize_module(
        &module,
        &DialectLegalizationRegistry::trust_cg_default(),
        proof_required(),
    )
    .expect("adapter-native ops legalize under proof");
    assert!(
        matches!(legalized.module, Cow::Borrowed(_)),
        "a kept-only module reaches the adapter unchanged (no clone)"
    );
    let report = legalized.report.expect("report");
    assert_eq!(report.rewritten_op_sites(), 0);
    let rules: Vec<(&str, &str)> = report
        .receipts
        .iter()
        .map(|receipt| (receipt.dialect.as_str(), receipt.rule.as_str()))
        .collect();
    assert_eq!(
        rules,
        vec![
            ("vector", "vector.pack_lanes/adapter-native"),
            ("vector", "vector.insert_lane/adapter-native"),
            ("vector", "vector.extract_lane/adapter-native"),
            ("vector", "vector.mask_to_bits/adapter-native-compare-mask"),
            ("trust-cg", "trust-cg.bitfield.extract/adapter-native"),
            (
                "trust-cg-aarch64-fp",
                "trust-cg-aarch64-fp.fsqrt/adapter-native"
            ),
        ]
    );
    for receipt in &report.receipts {
        assert_eq!(
            receipt.evidence,
            LegalizationEvidence::AdapterInstructionLowering
        );
        assert_eq!(receipt.input_digest, receipt.output_digest);
        assert_eq!(receipt.dialect_version, 1);
        assert!(
            matches!(receipt.site, LegalizationSite::Instruction { ref function, .. } if function == "f")
        );
    }
    assert!(report.provenance_invalidated.is_empty());
}

#[test]
fn trust_ir_vector_rewrites_and_per_lane_fma_leave_core_trust_ir() {
    use trust_ir::dialect::vector as vec_dialect;
    let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
    let v2f64 = Ty::Vector(Box::new(Ty::F64), 2);
    let module = module_with(
        vec![v4i32.clone(), v2f64.clone(), v2f64.clone(), v2f64.clone()],
        vec![Ty::I32, v4i32.clone(), v2f64.clone()],
        vec![
            op_node(
                vec_dialect::reduce(v4i32.clone(), v(0), vec_dialect::ReduceKind::Add),
                Some(4),
            ),
            op_node(
                vec_dialect::shuffle(v4i32, v(0), vec![3u8, 2, 1, 0]),
                Some(5),
            ),
            op_node(vec_dialect::fma(v2f64, v(1), v(2), v(3)), Some(6)),
            ret(&[4, 5, 6]),
        ],
    );
    let registry = DialectLegalizationRegistry::trust_cg_default();
    let legalized = legalize_module(&module, &registry, aarch64()).expect("legalizes");
    let report = legalized.report.clone().expect("report");
    assert_eq!(report.rewritten_op_sites(), 3);
    assert_eq!(
        report
            .receipts
            .iter()
            .map(|r| r.rule.as_str())
            .collect::<Vec<_>>(),
        vec![
            "vector.reduce/trust-ir-lane-fold",
            "vector.shuffle/trust-ir-lane-gather",
            "vector.fma/aarch64-per-lane-fmadd",
        ]
    );
    assert!(matches!(
        &report.receipts[0].evidence,
        LegalizationEvidence::CitedUpstreamTheorem { theorem, .. }
            if theorem == "TrustIr.Proofs.VectorDialectProps.runsAgreeFrom_reduce"
    ));
    assert_eq!(report.receipts[2].evidence.class(), "tested-only");
    assert_eq!(report.provenance_invalidated, vec!["f".to_string()]);
    let remaining = dialect_ops(&legalized.module);
    assert_eq!(
        remaining,
        vec!["trust-cg-aarch64-fp.fmadd".to_string(); 2],
        "reduce and shuffle reach core trust-ir; fma becomes one fused typed op per lane"
    );
    for node in legalized.module.instructions() {
        if let Inst::DialectOp(op) = &node.inst {
            assert_eq!(op.result_tys, vec![Ty::F64]);
            assert_eq!(op.operands.len(), 3);
        }
    }
    assert!(legalized.module.functions[0].source_provenance.is_none());
    verify_legalization(&module, &legalized.module, &report, &registry, aarch64())
        .expect("replay agrees");
}

#[test]
fn runtime_calls_pass_the_exact_payload_descriptor() {
    let registry = acme_registry();
    let module = module_with(
        vec![Ty::I64],
        vec![Ty::I64, Ty::I64, Ty::I64],
        vec![
            op_node(scale_op(0, 3), Some(1)),
            op_node(scale_op(1, 3), Some(2)),
            op_node(scale_op(2, -5), Some(3)),
            ret(&[1, 2, 3]),
        ],
    );
    let legalized = legalize_module(&module, &registry, aarch64()).expect("legalizes");
    let out = legalized.module.as_ref();
    assert!(dialect_ops(out).is_empty());
    let declarations: Vec<&Function> = out
        .functions
        .iter()
        .filter(|f| f.name == "acme_scale")
        .collect();
    assert_eq!(declarations.len(), 1, "one declaration for every site");
    assert!(declarations[0].blocks.is_empty());
    assert_eq!(
        out.func_type(declarations[0].ty),
        Some(&FuncTy {
            params: vec![Ty::Ptr, Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
    );
    let descriptors: Vec<&Global> = out
        .globals
        .iter()
        .filter(|g| g.name.starts_with("__tcg_dialect_payload_"))
        .collect();
    assert_eq!(descriptors.len(), 2, "equal payloads share one descriptor");
    for descriptor in &descriptors {
        assert!(!descriptor.mutable);
        assert_eq!(descriptor.linkage, Linkage::Internal);
    }
    let expected = encode_payload_descriptor(&scale_op(0, 3)).unwrap();
    assert!(descriptors.iter().any(|g| g.initializer
        == Some(Constant::Bytes {
            data: expected.clone(),
            utf8: false,
        })));
    let body = &out.functions[0].blocks[0].body;
    let calls: Vec<&Vec<ValueId>> = body
        .iter()
        .filter_map(|node| match &node.inst {
            Inst::Call { callee, args } if *callee == declarations[0].id => Some(args),
            _ => None,
        })
        .collect();
    assert_eq!(calls.len(), 3);
    assert_eq!(calls[0][2], v(0));
    assert!(body.iter().any(|node| matches!(
        &node.inst,
        Inst::Const { ty: Ty::I64, value: Constant::Int(len) } if *len == expected.len() as i128
    )));
    let report = legalized.report.expect("report");
    assert_eq!(report.receipts.len(), 3);
    assert!(report.receipts.iter().all(|receipt| receipt.rule
        == "acme.scale/runtime-call:acme_scale"
        && receipt.evidence
            == LegalizationEvidence::RuntimeContract {
                runtime: "the acme test runtime".to_string()
            }));
}

#[test]
fn runtime_payload_never_reuses_a_mutable_same_bytes_source_global() {
    let registry = acme_registry();
    let mut source = module_with(
        vec![Ty::I64],
        vec![Ty::I64],
        vec![op_node(scale_op(0, 3), Some(1)), ret(&[1])],
    );
    source.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    let control = legalize_module(&source, &registry, aarch64()).expect("fresh descriptor");
    let mut descriptor = control.module.globals[0].clone();
    let name = descriptor.name.clone();
    let bytes = encode_payload_descriptor(&scale_op(0, 3)).expect("payload descriptor");
    let len = u64::try_from(bytes.len()).expect("descriptor length");
    assert_eq!(
        descriptor.initializer,
        Some(Constant::Bytes {
            data: bytes,
            utf8: false,
        })
    );
    assert!(!descriptor.mutable);
    assert_eq!(descriptor.linkage, Linkage::Internal);
    assert_eq!(descriptor.tls, None);
    assert_eq!(descriptor.section, None);

    // The source owns a different type table from the legalized control.
    // Recreate the exact byte-array shape before copying the descriptor in.
    let byte = source.add_type(Ty::U8).expect("fixture byte type");
    descriptor.ty = Ty::Array(byte, len);
    source.globals.push(descriptor);
    let validate_source = |module: &Module| {
        let findings =
            trust_ir_build::validate_module_with_dialect_schemas(module, &registry.inner.exact);
        assert!(findings.is_empty(), "source must validate: {findings:?}");
    };
    validate_source(&source);
    let reused = legalize_module(&source, &registry, aarch64()).expect("immutable exact reuse");
    assert_eq!(reused.module.globals, source.globals);
    assert!(reused.module.instructions().any(|node| matches!(
        &node.inst,
        Inst::GlobalAddr { global } if *global == GlobalId::new(0)
    )));

    // This is valid, writable source storage, not a malformed initializer.
    // A source store before the dialect op can clobber its purportedly
    // read-only runtime payload if legalization aliases this descriptor.
    let mut mutable = source.clone();
    mutable.globals[0].mutable = true;
    mutable.functions[0].blocks[0].body.splice(
        0..0,
        [
            InstrNode::new(Inst::GlobalAddr {
                global: GlobalId::new(0),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Const {
                ty: Ty::U8,
                value: Constant::Int(0),
            })
            .with_result(v(3)),
            InstrNode::new(Inst::Store {
                ty: Ty::U8,
                ptr: v(2),
                value: v(3),
                volatile: false,
                align: None,
            }),
        ],
    );
    validate_source(&mutable);
    let error = legalize_err(&mutable, &registry, aarch64());
    assert!(
        matches!(&error, DialectPipelineError::RuntimeBinding { dialect, op, detail }
            if dialect == NS && op == "scale" && detail.contains(&name)),
        "writable payload alias must be refused by name: {error}"
    );

    // A descriptor is one private, ordinary, read-only byte-array image.
    // Source-owned cross-object, per-thread or explicitly placed storage
    // cannot take over that generated identity just by sharing its bytes.
    let mut external = source.clone();
    external.globals[0].linkage = Linkage::External;
    let mut tls = source.clone();
    tls.globals[0].tls = Some(trust_ir::TlsModel::GeneralDynamic);
    let mut section = source.clone();
    section.globals[0].section = Some(".data".into());
    for (case, module) in [("external", external), ("TLS", tls), ("section", section)] {
        validate_source(&module);
        let error = legalize_err(&module, &registry, aarch64());
        assert!(
            matches!(&error, DialectPipelineError::RuntimeBinding { detail, .. }
                if detail.contains(&name)),
            "{case} payload storage must be refused: {error}"
        );
    }

    // Legalization compares new validator findings with its source baseline.
    // It must still refuse to reuse a preexisting malformed descriptor type.
    let mut wrong_length = source.clone();
    wrong_length.globals[0].ty = Ty::Array(byte, len + 1);
    let mut wrong_element = source.clone();
    let signed_byte = wrong_element
        .add_type(Ty::I8)
        .expect("fixture signed byte type");
    wrong_element.globals[0].ty = Ty::Array(signed_byte, len);
    for (case, module) in [("length", wrong_length), ("element", wrong_element)] {
        let findings =
            trust_ir_build::validate_module_with_dialect_schemas(&module, &registry.inner.exact);
        assert!(!findings.is_empty(), "{case} source type must be malformed");
        let error = legalize_err(&module, &registry, aarch64());
        assert!(
            matches!(&error, DialectPipelineError::RuntimeBinding { detail, .. }
                if detail.contains(&name)),
            "malformed {case} payload type must be refused: {error}"
        );
    }
}

#[test]
fn nominal_types_take_their_carrier_everywhere_with_one_receipt() {
    let registry = acme_registry();
    let mut touch = DialectInst::new(NS, "touch").with_operand(v(1));
    touch.version = NS_VERSION;
    let module = module_with(
        vec![handle_ty()],
        vec![handle_ty()],
        vec![
            InstrNode::new(Inst::Copy {
                ty: handle_ty(),
                operand: v(0),
            })
            .with_result(v(1)),
            op_node(touch, None),
            ret(&[1]),
        ],
    );
    let legalized = legalize_module(&module, &registry, proof_required()).expect("legalizes");
    let mut survivors = 0;
    legalized
        .module
        .visit_types(|ty| survivors += usize::from(matches!(ty, Ty::Dialect(_))));
    assert_eq!(survivors, 0);
    let function = &legalized.module.functions[0];
    assert_eq!(function.blocks[0].params[0].1, Ty::Ptr);
    assert_eq!(
        legalized.module.func_type(function.ty).unwrap().params,
        vec![Ty::Ptr]
    );
    let report = legalized.report.expect("report");
    // Receipts: the kept `acme.touch` site, then the type.
    assert_eq!(report.receipts.len(), 2);
    let ty_receipt = &report.receipts[1];
    assert_eq!(ty_receipt.dialect, NS);
    assert_eq!(ty_receipt.dialect_version, NS_VERSION);
    assert_eq!(ty_receipt.rule, "acme.handle@1/ptr-carrier");
    assert_eq!(
        ty_receipt.subject,
        LegalizationSubject::Type {
            name: "handle".into(),
            version: 1,
            carrier: "ptr".into(),
        }
    );
    // Parameter and return of the signature, the block parameter and the copy.
    assert_eq!(ty_receipt.site, LegalizationSite::Module { occurrences: 4 });
    assert_eq!(report.provenance_invalidated, vec!["f".to_string()]);
    assert_eq!(
        report.to_json()["receipts"][1]["evidence_class"],
        "checked-transport-substitution"
    );
}

#[test]
fn payload_descriptor_bytes_are_exact() {
    let mut op = DialectInst::new("d", "o")
        .with_attr("a", AttrValue::I64(-2))
        .with_attr("b", AttrValue::U64(7))
        .with_attr("c", AttrValue::F64(1.5))
        .with_attr("e", AttrValue::Bool(true))
        .with_attr("s", AttrValue::Str("hi".into()))
        .with_attr("x", AttrValue::Bytes(vec![0xde, 0xad]))
        .with_attr("t", AttrValue::Ty(Ty::I32));
    op.version = 3;
    let mut expected = Vec::new();
    expected.extend_from_slice(b"TCGD");
    expected.extend_from_slice(&1u32.to_le_bytes());
    for text in ["d", "o"] {
        expected.extend_from_slice(&(text.len() as u32).to_le_bytes());
        expected.extend_from_slice(text.as_bytes());
    }
    expected.extend_from_slice(&3u32.to_le_bytes());
    expected.extend_from_slice(&7u32.to_le_bytes());
    let name = |out: &mut Vec<u8>, n: &str| {
        out.extend_from_slice(&(n.len() as u32).to_le_bytes());
        out.extend_from_slice(n.as_bytes());
    };
    name(&mut expected, "a");
    expected.push(0);
    expected.extend_from_slice(&(-2i64).to_le_bytes());
    name(&mut expected, "b");
    expected.push(1);
    expected.extend_from_slice(&7u64.to_le_bytes());
    name(&mut expected, "c");
    expected.push(2);
    expected.extend_from_slice(&1.5f64.to_bits().to_le_bytes());
    name(&mut expected, "e");
    expected.extend_from_slice(&[3, 1]);
    name(&mut expected, "s");
    expected.push(4);
    name(&mut expected, "hi");
    name(&mut expected, "x");
    expected.push(5);
    expected.extend_from_slice(&2u32.to_le_bytes());
    expected.extend_from_slice(&[0xde, 0xad]);
    name(&mut expected, "t");
    expected.push(6);
    name(&mut expected, "i32");
    assert_eq!(encode_payload_descriptor(&op).unwrap(), expected);

    let open =
        DialectInst::new("d", "o").with_attr("t", AttrValue::Ty(Ty::Struct(StructId::new(0))));
    let error =
        encode_payload_descriptor(&open).expect_err("a module-relative type has no spelling");
    assert!(error.contains("module table"), "{error}");
}

// ---------------------------------------------------------------------------
// Receipt corruption controls
// ---------------------------------------------------------------------------

/// A module whose legalization has a kept op, a rewrite, a runtime call and
/// a nominal type: every receipt shape.
fn mixed_module() -> Module {
    let mut touch = DialectInst::new(NS, "touch").with_operand(v(1));
    touch.version = NS_VERSION;
    module_with(
        vec![Ty::I64, handle_ty()],
        vec![Ty::I64, Ty::I64, handle_ty()],
        vec![
            op_node(twice_op(0), Some(2)),
            op_node(scale_op(2, 4), Some(3)),
            op_node(touch, None),
            ret(&[2, 3, 1]),
        ],
    )
}

#[test]
fn receipts_replay_exactly_and_every_corruption_is_named() {
    let registry = acme_registry();
    let source = mixed_module();
    let legalized = legalize_module(&source, &registry, aarch64()).expect("legalizes");
    let module = legalized.module.into_owned();
    let report = legalized.report.expect("report");
    assert_eq!(report.receipts.len(), 4);
    verify_legalization(&source, &module, &report, &registry, aarch64()).expect("genuine report");

    type Corruption = fn(&mut DialectLegalizationReport);
    let report_fields: Vec<(Corruption, &str)> = vec![
        (
            |r| r.registry_digest.replace_range(0..1, "x"),
            "registry_digest",
        ),
        (|r| r.target = "X86_64".into(), "target"),
        (|r| r.proof_required = true, "proof_required"),
        (
            |r| r.provenance_invalidated.clear(),
            "provenance_invalidated",
        ),
    ];
    for (corrupt, field) in report_fields {
        let mut forged = report.clone();
        corrupt(&mut forged);
        let error = verify_legalization(&source, &module, &forged, &registry, aarch64())
            .expect_err("corrupted report");
        assert!(
            matches!(&error, ReceiptError::ReportField { field: f, .. } if *f == field),
            "{field}: {error:?}"
        );
        assert!(error.to_string().starts_with("[TCG-DIALECT-RECEIPT]"));
    }

    let mut dropped = report.clone();
    dropped.receipts.pop();
    assert!(matches!(
        verify_legalization(&source, &module, &dropped, &registry, aarch64()),
        Err(ReceiptError::ReceiptCount {
            expected: 4,
            found: 3
        })
    ));
    let mut added = report.clone();
    added.receipts.push(report.receipts[0].clone());
    assert!(matches!(
        verify_legalization(&source, &module, &added, &registry, aarch64()),
        Err(ReceiptError::ReceiptCount {
            expected: 4,
            found: 5
        })
    ));
    let mut reordered = report.clone();
    reordered.receipts.swap(0, 1);
    assert!(matches!(
        verify_legalization(&source, &module, &reordered, &registry, aarch64()),
        Err(ReceiptError::ReceiptField { index: 0, .. })
    ));

    type ReceiptCorruption = fn(&mut LegalizationReceipt);
    let receipt_fields: Vec<(ReceiptCorruption, &str)> = vec![
        (|r| r.dialect = "other".into(), "dialect"),
        (|r| r.dialect_version += 1, "dialect_version"),
        (|r| r.owner.push('.'), "owner"),
        (
            |r| {
                r.subject = LegalizationSubject::Op {
                    op: "scale".into(),
                    payload_version: NS_VERSION,
                }
            },
            "subject",
        ),
        (|r| r.rule = "acme.twice/other".into(), "rule"),
        (
            |r| r.evidence = LegalizationEvidence::CheckedTransportSubstitution,
            "evidence",
        ),
        (
            |r| {
                r.site = LegalizationSite::Instruction {
                    function: "f".into(),
                    block: 0,
                    index: 1,
                }
            },
            "site",
        ),
        (|r| r.input_digest.replace_range(0..1, "x"), "input_digest"),
        (
            |r| r.output_digest.replace_range(0..1, "x"),
            "output_digest",
        ),
    ];
    for (corrupt, field) in receipt_fields {
        let mut forged = report.clone();
        corrupt(&mut forged.receipts[0]);
        let error = verify_legalization(&source, &module, &forged, &registry, aarch64())
            .expect_err("corrupted receipt");
        assert!(
            matches!(&error, ReceiptError::ReceiptField { index: 0, field: f, .. } if *f == field),
            "{field}: {error:?}"
        );
    }

    let mut tampered = module.clone();
    for node in &mut tampered.functions[0].blocks[0].body {
        if let Inst::BinOp { op, .. } = &mut node.inst {
            *op = BinOp::Sub;
        }
    }
    assert_eq!(
        verify_legalization(&source, &tampered, &report, &registry, aarch64()),
        Err(ReceiptError::ModuleMismatch)
    );

    let other_registry = registry_with(vec![acme_registration(), {
        let mut extra = acme_registration();
        extra.namespace = "acme2".into();
        for rule in &mut extra.ops {
            for alternative in &mut rule.alternatives {
                alternative.rule = alternative.rule.replacen("acme", "acme2", 1);
            }
        }
        for rule in &mut extra.types {
            rule.rule = rule.rule.replacen("acme", "acme2", 1);
        }
        extra
    }]);
    assert!(matches!(
        verify_legalization(&source, &module, &report, &other_registry, aarch64()),
        Err(ReceiptError::ReportField {
            field: "registry_digest",
            ..
        })
    ));
    assert!(matches!(
        verify_legalization(
            &source,
            &module,
            &report,
            &DialectLegalizationRegistry::trust_cg_default(),
            aarch64()
        ),
        Err(ReceiptError::ReplayRefused(
            DialectPipelineError::UnregisteredDialect { .. }
        ))
    ));
    let core = module_with(vec![Ty::I64], vec![Ty::I64], vec![ret(&[0])]);
    assert_eq!(
        verify_legalization(&core, &core, &report, &registry, aarch64()),
        Err(ReceiptError::NoDialectConstructs)
    );
}

// ---------------------------------------------------------------------------
// Runtime calls over nominal types
// ---------------------------------------------------------------------------

fn peek_op(operand: u32) -> DialectInst {
    let mut op = DialectInst::new(NS, "peek")
        .with_operand(v(operand))
        .with_result_ty(Ty::I64);
    op.version = NS_VERSION;
    op
}

/// `acme` plus `peek(acme.handle@1) -> i64`, bound to the runtime `acme_peek`.
fn acme_peek_registration() -> DialectRegistration {
    let mut registration = acme_registration();
    if let DialectGrammar::Exact(ops) = &mut registration.grammar {
        ops.push(acme_schema("peek", vec![handle_ty()], vec![Ty::I64], &[]));
    }
    registration.bind_runtime_call("peek", "acme_peek", "the acme test runtime")
}

#[test]
fn runtime_calls_over_a_nominal_type_are_declared_in_carriers() {
    let registry = registry_with(vec![acme_peek_registration()]);
    let source = module_with(
        vec![handle_ty()],
        vec![Ty::I64],
        vec![op_node(peek_op(0), Some(1)), ret(&[1])],
    );
    let legalized = legalize_module(&source, &registry, aarch64()).expect("legalizes");
    let out = legalized.module.as_ref();
    let mut survivors = 0;
    out.visit_types(|ty| survivors += usize::from(matches!(ty, Ty::Dialect(_))));
    assert_eq!(survivors, 0);
    let declaration = out
        .functions
        .iter()
        .find(|function| function.name == "acme_peek")
        .expect("the runtime is declared");
    assert_eq!(
        out.func_type(declaration.ty),
        Some(&FuncTy {
            params: vec![Ty::Ptr, Ty::I64, Ty::Ptr],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        }),
        "the nominal operand crosses the runtime ABI as its carrier"
    );
    let report = legalized.report.clone().expect("report");
    assert_eq!(
        report.provenance_invalidated,
        vec!["f".to_string()],
        "the appended declaration is not a source function"
    );
    assert_eq!(report.receipts.len(), 2);
    assert_eq!(report.receipts[0].rule, "acme.peek/runtime-call:acme_peek");
    // Source occurrences: the signature's parameter and the block parameter.
    assert_eq!(
        report.receipts[1].site,
        LegalizationSite::Module { occurrences: 2 }
    );
    verify_legalization(&source, out, &report, &registry, aarch64()).expect("replay agrees");

    // A source declaration of the runtime spelled with the nominal type is the
    // binding's declaration once its types take their carriers: reused, and
    // its provenance (a source function) is invalidated with the body's.
    let mut declared = source.clone();
    let nominal = declared
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I64, handle_ty()],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    declared.functions.push(Function::new(
        FuncId::new(1),
        "acme_peek",
        nominal,
        BlockId::new(0),
    ));
    let legalized = legalize_module(&declared, &registry, aarch64()).expect("reused");
    let out = legalized.module.as_ref();
    assert_eq!(
        out.functions
            .iter()
            .filter(|function| function.name == "acme_peek")
            .count(),
        1
    );
    let report = legalized.report.expect("report");
    assert_eq!(
        report.provenance_invalidated,
        vec!["f".to_string(), "acme_peek".to_string()]
    );
    assert_eq!(
        report.receipts[1].site,
        LegalizationSite::Module { occurrences: 3 }
    );
}

#[test]
fn a_dialect_op_consuming_another_namespaces_nominal_value_is_refused() {
    let other_ty = Ty::Dialect(Box::new(DialectTy::new("other", "t", 1)));
    let other = DialectRegistration {
        namespace: "other".to_string(),
        version: 1,
        owner: "trust-cg unit tests (other)".to_string(),
        grammar: DialectGrammar::Exact(Vec::new()),
        ops: Vec::new(),
        types: vec![TypeRule {
            name: "t".to_string(),
            version: 1,
            carrier: Ty::I64,
            rule: "other.t@1/i64-carrier".to_string(),
            evidence: LegalizationEvidence::CheckedTransportSubstitution,
        }],
    };
    let mut acme = acme_registration();
    if let DialectGrammar::Exact(ops) = &mut acme.grammar {
        ops.push(acme_schema(
            "peek",
            vec![other_ty.clone()],
            vec![Ty::I64],
            &[],
        ));
    }
    let acme = acme.bind_runtime_call("peek", "acme_peek", "the acme test runtime");
    let registry = registry_with(vec![acme, other]);
    let module = module_with(
        vec![other_ty],
        vec![Ty::I64],
        vec![op_node(peek_op(0), Some(1)), ret(&[1])],
    );
    let error = legalize_err(&module, &registry, aarch64());
    assert!(
        matches!(&error, DialectPipelineError::NominalUse { detail }
            if detail.contains("`acme.peek`")
                && detail.contains("consumes a value of nominal type `other.t@1`")),
        "{error:?}"
    );
}

// ---------------------------------------------------------------------------
// Receipts describe the legalized module
// ---------------------------------------------------------------------------

#[test]
fn rewrite_receipts_digest_the_nodes_spliced_into_the_module() {
    use trust_ir::dialect::vector as vd;
    let span = trust_ir::SourceSpan {
        file: 1,
        line: 7,
        col: 3,
    };
    let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
    let cases: Vec<(&str, DialectLegalizationRegistry, Module)> = vec![
        (
            "acme.twice (one node)",
            acme_registry(),
            module_with(
                vec![Ty::I64],
                vec![Ty::I64],
                vec![op_node(twice_op(0), Some(1)), ret(&[1])],
            ),
        ),
        (
            "vector.shuffle (a lane-gather chain)",
            DialectLegalizationRegistry::trust_cg_default(),
            module_with(
                vec![v4i32.clone()],
                vec![v4i32.clone()],
                vec![
                    op_node(vd::shuffle(v4i32, v(0), vec![3u8, 2, 1, 0]), Some(1)),
                    ret(&[1]),
                ],
            ),
        ),
    ];
    for (label, registry, mut source) in cases {
        let function = &mut source.functions[0];
        function.scopes = Some(vec![
            trust_ir::ScopeData::new(None, None),
            trust_ir::ScopeData::new(Some(0), None),
        ]);
        let node = &mut function.blocks[0].body[0];
        node.span = Some(span);
        node.scope = Some(1);
        let legalized = legalize_module(&source, &registry, aarch64()).expect(label);
        let body = &legalized.module.functions[0].blocks[0].body;
        let replacement = &body[..body.len() - 1];
        let last = replacement.last().expect("a replacement");
        assert_eq!(
            (last.span, last.scope),
            (Some(span), Some(1)),
            "{label}: the last node inherits the diagnostic metadata"
        );
        let report = legalized.report.expect("report");
        assert_eq!(
            report.receipts[0].output_digest,
            digest_parts(&[b"rewritten", format!("{replacement:?}").as_bytes()]),
            "{label}: the output digest covers the nodes in the legalized module"
        );
    }
}

// ---------------------------------------------------------------------------
// The legalized module meets the validator
// ---------------------------------------------------------------------------

#[test]
fn a_legalized_module_the_validator_refuses_is_refused_by_name() {
    use trust_ir::dialect::vector as vd;
    let registry = DialectLegalizationRegistry::trust_cg_default();
    let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
    let v16i8 = Ty::Vector(Box::new(Ty::I8), 16);
    let v4f32 = Ty::Vector(Box::new(Ty::F32), 4);
    let v2f64 = Ty::Vector(Box::new(Ty::F64), 2);
    // Each payload passes its grammar (which reads the payload only), but
    // names a vector type its operands do not have; the rewrite's lane reads
    // then fail trust-ir-build's type checks.
    let cases: Vec<(&str, Module)> = vec![
        (
            "reduce of <16 x i8> over a <4 x i32>",
            module_with(
                vec![v4i32.clone()],
                vec![Ty::I8],
                vec![
                    op_node(vd::reduce(v16i8, v(0), vd::ReduceKind::Add), Some(1)),
                    ret(&[1]),
                ],
            ),
        ),
        (
            "fma of <4 x f32> over <2 x f64>",
            module_with(
                vec![v2f64.clone(); 3],
                vec![v4f32.clone()],
                vec![
                    op_node(vd::fma(v4f32, v(0), v(1), v(2)), Some(3)),
                    ret(&[3]),
                ],
            ),
        ),
    ];
    for (label, module) in cases {
        let error = legalize_err(&module, &registry, aarch64());
        assert!(
            matches!(&error, DialectPipelineError::LegalizedModuleInvalid { findings }
                if !findings.is_empty()),
            "{label}: {error:?}"
        );
        assert!(
            error.to_string().starts_with("[TCG-DIALECT-VALIDATION]"),
            "{label}: {error}"
        );
    }
}

// ---------------------------------------------------------------------------
// What the registry digest identifies
// ---------------------------------------------------------------------------

/// `acme.twice(x)` -> `x - x`: a different rule under `twice_rewrite`'s names.
fn twice_impostor_rewrite(
    _node: &InstrNode,
    op: &DialectInst,
    results: &[ValueId],
    _context: &mut LoweringContext<'_>,
) -> RewriteOutcome {
    let ([result], [operand]) = (results, op.operands.as_slice()) else {
        return RewriteOutcome::Err("acme.twice needs one operand and one result".to_string());
    };
    RewriteOutcome::Replace(vec![
        InstrNode::new(Inst::BinOp {
            op: BinOp::Sub,
            ty: Ty::I64,
            lhs: *operand,
            rhs: *operand,
        })
        .with_result(*result),
    ])
}

#[test]
fn the_registry_digest_names_rules_and_the_replay_checks_what_they_do() {
    let genuine = acme_registry();
    let mut impostor = acme_registration();
    for rule in &mut impostor.ops {
        for alternative in &mut rule.alternatives {
            if let OpLowering::Rewrite(rewrite) = &mut alternative.lowering {
                rewrite.rewrite = twice_impostor_rewrite;
            }
        }
    }
    let impostor = registry_with(vec![impostor]);
    assert_eq!(
        genuine.digest(),
        impostor.digest(),
        "the digest identifies a rule by its names, not its code"
    );
    let source = module_with(
        vec![Ty::I64],
        vec![Ty::I64],
        vec![op_node(twice_op(0), Some(1)), ret(&[1])],
    );
    let legalized = legalize_module(&source, &impostor, aarch64()).expect("legalizes");
    let report = legalized.report.clone().expect("report");
    verify_legalization(&source, &legalized.module, &report, &impostor, aarch64())
        .expect("the impostor replays itself");
    let error = verify_legalization(&source, &legalized.module, &report, &genuine, aarch64())
        .expect_err("the genuine rule replays to another module");
    assert!(
        matches!(
            &error,
            ReceiptError::ReceiptField {
                index: 0,
                field: "output_digest",
                ..
            }
        ),
        "{error:?}"
    );
}
