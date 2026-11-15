// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Char is deliberately OUTSIDE bounded fsym until Unicode validity is modeled.
//! Interpreter executions below distinguish real UB from this conservative
//! scope refusal. Refused valid inputs are never counted as verified or clean.

use trust_cg_verify::fsym_trust_ir::{
    FSYM_CHAR_BINDING_REFUSAL, FsymTrustIrSkipReason, scan_function_in_module,
};
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::{
    Block, BlockId, CastOp, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty,
    ValueId,
};

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}
fn value(index: u32, inst: Inst) -> InstrNode {
    InstrNode::new(inst).with_result(v(index))
}
fn constant(index: u32, ty: Ty, raw: i128) -> InstrNode {
    value(
        index,
        Inst::Const {
            ty,
            value: Constant::Int(raw),
        },
    )
}
fn ret(index: u32) -> InstrNode {
    InstrNode::new(Inst::Return {
        values: vec![v(index)],
    })
}
fn module(params: Vec<Ty>, returns: Vec<Ty>, body: Vec<InstrNode>) -> Module {
    let mut module = Module::new("char_scope");
    let ty = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "f", ty, BlockId::new(0));
    function.blocks.push(Block {
        id: BlockId::new(0),
        params: params
            .into_iter()
            .enumerate()
            .map(|(i, ty)| (v(i as u32), ty))
            .collect(),
        body,
    });
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}
fn cast(raw: u32) -> Module {
    module(
        vec![],
        vec![Ty::Char],
        vec![
            constant(0, Ty::U32, i128::from(raw)),
            value(
                1,
                Inst::Cast {
                    op: CastOp::Trunc,
                    src_ty: Ty::U32,
                    dst_ty: Ty::Char,
                    operand: v(0),
                },
            ),
            ret(1),
        ],
    )
}
fn refused(module: &Module) {
    let report = scan_function_in_module(module, &module.functions[0]);
    assert_eq!(report.scanned_functions, 0);
    assert!(report.scanned_function_names.is_empty());
    let [skip] = report.skipped_functions.as_slice() else {
        panic!("exactly one explicit scope refusal: {report:?}")
    };
    assert_eq!(skip.reason, FsymTrustIrSkipReason::UnsupportedInstruction);
    assert_eq!(skip.detail, FSYM_CHAR_BINDING_REFUSAL);
}
fn assert_ub(module: &Module, args: Vec<InterpretValue>) {
    let error = Interpreter::with_module(module)
        .execute_func(FuncId::new(0), args)
        .expect_err("invalid Char must raise the new interpreter UB");
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
    assert!(
        error.message.contains("not a Unicode scalar value"),
        "{error}"
    );
}

#[test]
fn invalid_char_boundaries_are_named_refusals_not_clean() {
    for raw in [0xD800, 0xDFFF, 0x110000, u32::MAX] {
        let module = cast(raw);
        assert_ub(&module, vec![]);
        refused(&module);
    }
}

#[test]
fn valid_char_boundaries_remain_explicitly_out_of_scope() {
    for raw in [0, 0x41, 0xD7FF, 0xE000, 0x10FFFF] {
        let module = cast(raw);
        let result = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), vec![])
            .expect("Unicode scalar value executes");
        assert_eq!(
            result.returns[0].as_int().unwrap().as_unsigned(),
            u128::from(raw)
        );
        refused(&module);
    }
    // The ordinary carrier remains admitted, including the surrogate pattern.
    let module = module(
        vec![],
        vec![Ty::U32],
        vec![constant(0, Ty::U32, 0xD800), ret(0)],
    );
    let result = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), vec![])
        .expect("ordinary U32 executes");
    assert_eq!(result.returns[0].as_int().unwrap().as_unsigned(), 0xD800);
    let report = scan_function_in_module(&module, &module.functions[0]);
    assert_eq!(report.scanned_functions, 1);
    assert!(report.skipped_functions.is_empty());
    assert!(report.diagnostics.is_empty());
    assert!(report.unknown_obligations.is_empty());
    assert!(report.coverage_errors.is_empty());
}

#[test]
fn entry_and_dead_block_parameters_are_checked() {
    let entry = module(vec![Ty::Char], vec![Ty::Char], vec![ret(0)]);
    let invalid = InterpretValue::int(Ty::Char, 0xD800).expect("32-bit carrier");
    assert_ub(&entry, vec![invalid]);
    refused(&entry);
    let mut dead = module(vec![], vec![Ty::U32], vec![constant(0, Ty::U32, 0), ret(0)]);
    dead.functions[0].blocks.push(Block {
        id: BlockId::new(1),
        params: vec![(v(3), Ty::Char)],
        body: vec![constant(4, Ty::U32, 0), ret(4)],
    });
    Interpreter::with_module(&dead)
        .execute_func(FuncId::new(0), vec![])
        .expect("dead Char parameter is not executed");
    refused(&dead);
}

#[test]
fn unused_and_dead_char_results_are_checked() {
    let mut unused = cast(0xD800);
    unused.func_types[0].returns = vec![Ty::U32];
    unused.functions[0].blocks[0].body[2] = ret(0);
    assert_ub(&unused, vec![]);
    refused(&unused);
    let mut dead = module(vec![], vec![Ty::U32], vec![constant(0, Ty::U32, 0), ret(0)]);
    dead.functions[0].blocks.push(Block {
        id: BlockId::new(1),
        params: vec![],
        body: vec![
            constant(1, Ty::U32, 0xD800),
            value(
                2,
                Inst::Cast {
                    op: CastOp::Trunc,
                    src_ty: Ty::U32,
                    dst_ty: Ty::Char,
                    operand: v(1),
                },
            ),
            ret(1),
        ],
    });
    Interpreter::with_module(&dead)
        .execute_func(FuncId::new(0), vec![])
        .expect("dead cast is not executed");
    refused(&dead);
}

#[test]
fn direct_call_results_and_unresolved_result_metadata_are_not_omitted() {
    let mut called = module(
        vec![],
        vec![Ty::U32],
        vec![
            value(
                0,
                Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![],
                },
            ),
            constant(1, Ty::U32, 0),
            ret(1),
        ],
    );
    let ty = called
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Char],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut callee = Function::new(FuncId::new(1), "char_callee", ty, BlockId::new(0));
    callee.blocks.push(Block {
        id: BlockId::new(0),
        params: vec![],
        body: vec![constant(0, Ty::Char, 0x41), ret(0)],
    });
    called
        .try_add_function(callee)
        .expect("Module::try_add_function: test fixture");
    Interpreter::with_module(&called)
        .execute_func(FuncId::new(0), vec![])
        .expect("valid Char from an actual direct callee executes");
    refused(&called);

    for missing_signature in [false, true] {
        let mut unresolved = called.clone();
        if missing_signature {
            unresolved.functions[1].ty = trust_ir::FuncTyId::new(99);
        } else {
            unresolved.functions.pop();
        }
        let report = scan_function_in_module(&unresolved, &unresolved.functions[0]);
        assert_eq!(report.scanned_functions, 0);
        let [skip] = report.skipped_functions.as_slice() else {
            panic!("{report:?}")
        };
        assert_eq!(skip.reason, FsymTrustIrSkipReason::MalformedCfg);
        assert!(
            skip.detail
                .contains("result typing unresolved or arity mismatch")
        );
    }
}

#[test]
fn char_extracted_from_an_aggregate_is_checked_at_the_scalar_binding() {
    let tuple = Ty::Tuple(vec![Ty::Char]);
    let module = module(
        vec![tuple.clone()],
        vec![Ty::Char],
        vec![
            value(
                1,
                Inst::ExtractField {
                    ty: Ty::Char,
                    aggregate: v(0),
                    field: 0,
                },
            ),
            ret(1),
        ],
    );
    let input = InterpretValue {
        ty: tuple,
        kind: InterpretValueKind::Aggregate(vec![
            InterpretValue::int(Ty::Char, 0xD800).expect("32-bit carrier"),
        ]),
    };
    assert_ub(&module, vec![input]);
    refused(&module);
}

#[test]
fn nested_invalid_char_is_checked_at_entry_before_malformed_extraction() {
    let tuple = Ty::Tuple(vec![Ty::Char]);
    let module = module(
        vec![tuple.clone()],
        vec![Ty::U32],
        vec![
            value(
                1,
                Inst::ExtractField {
                    ty: Ty::U32,
                    aggregate: v(0),
                    field: 0,
                },
            ),
            ret(1),
        ],
    );
    let input = InterpretValue {
        ty: tuple,
        kind: InterpretValueKind::Aggregate(vec![
            InterpretValue::int(Ty::Char, 0xD800).expect("32-bit carrier"),
        ]),
    };

    // A source Char-bearing entry is refused independently of a malformed
    // instruction annotation. Its invalid Unicode payload traps at entry.
    refused(&module);
    assert_ub(&module, vec![input]);
}

#[test]
fn forged_char_payload_under_char_free_entry_stays_a_scanned_type_error() {
    for ty in [Ty::Ptr, Ty::Tuple(vec![Ty::U64])] {
        let module = module(
            vec![ty.clone()],
            vec![Ty::U32],
            vec![constant(1, Ty::U32, 7), ret(1)],
        );
        let report = scan_function_in_module(&module, &module.functions[0]);
        assert_eq!(report.scanned_functions, 1, "{report:?}");
        assert!(report.skipped_functions.is_empty());
        let input = InterpretValue {
            ty,
            kind: InterpretValueKind::Aggregate(vec![
                InterpretValue::int(Ty::Char, 0xD800).expect("carrier"),
            ]),
        };
        let error = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), vec![input])
            .expect_err("forged Char");
        assert_eq!(error.code, InterpretErrorCode::TypeError, "{error}");
        assert!(error.message.contains("not declared"), "{error}");
    }
}

#[test]
fn malformed_char_extraction_as_u32_still_refuses_a_valid_unicode_lane() {
    let tuple = Ty::Tuple(vec![Ty::Char]);
    let module = module(
        vec![tuple.clone()],
        vec![Ty::U32],
        vec![
            value(
                1,
                Inst::ExtractField {
                    ty: Ty::U32,
                    aggregate: v(0),
                    field: 0,
                },
            ),
            ret(1),
        ],
    );
    refused(&module);
    let input = InterpretValue {
        ty: tuple,
        kind: InterpretValueKind::Aggregate(vec![
            InterpretValue::int(Ty::Char, 0x41).expect("valid Unicode carrier"),
        ]),
    };
    let error = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), vec![input])
        .expect_err("wrong result annotation");
    assert_eq!(error.code, InterpretErrorCode::TypeError, "{error}");
    assert!(error.message.contains("expected value of type"), "{error}");
}
