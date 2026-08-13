#![cfg(feature = "trust-types-bridge")]

use trust_cg_verify::smt::trust_formula_adapter::{
    FormulaAdapterContext, FormulaAdapterError, FormulaAdapterVarSort,
    formula_context_from_trust_ir_function, formula_to_smt, smt_to_formula,
    trust_ir_value_var_name,
};
use trust_cg_verify::{RoundingMode, SmtExpr, SmtSort};
use trust_ir::{
    BinOp, Block, CallingConv, Constant, Endianness, FuncId, FuncTy, Function, Inst, InstrNode,
    Linkage, Module as TrustIrModule, ProofAnnotation, SourceSpan, TargetInfo, Ty, ValueId,
    ValueMetadataOrigin,
};
use trust_types::{Formula, Sort};

fn var(name: &str, sort: Sort) -> Formula {
    Formula::Var(name.to_string(), sort)
}

#[test]
fn signed_integer_scalar_formula_round_trips() {
    let ctx = FormulaAdapterContext::new()
        .with_signed_int_var("x", 32)
        .with_signed_int_var("y", 32);

    let formula = Formula::And(vec![
        Formula::Eq(
            Box::new(Formula::Add(
                Box::new(var("x", Sort::Int)),
                Box::new(Formula::Int(-1)),
            )),
            Box::new(var("y", Sort::Int)),
        ),
        Formula::Lt(Box::new(var("x", Sort::Int)), Box::new(Formula::Int(7))),
        Formula::Ge(Box::new(var("y", Sort::Int)), Box::new(Formula::Int(-3))),
    ]);

    let smt = formula_to_smt(&formula, &ctx).unwrap();
    let round_trip = smt_to_formula(&smt, &ctx).unwrap();

    assert_eq!(round_trip, formula);
}

#[test]
fn bitvector_formula_round_trips() {
    let ctx = FormulaAdapterContext::new()
        .with_bv_var("a", 32)
        .with_bv_var("b", 32);

    let formula = Formula::And(vec![
        Formula::Eq(
            Box::new(Formula::BvAdd(
                Box::new(var("a", Sort::BitVec(32))),
                Box::new(Formula::BitVec {
                    value: 1,
                    width: 32,
                }),
                32,
            )),
            Box::new(Formula::BvXor(
                Box::new(var("b", Sort::BitVec(32))),
                Box::new(Formula::BitVec {
                    value: 0xff,
                    width: 32,
                }),
                32,
            )),
        ),
        Formula::BvULt(
            Box::new(var("a", Sort::BitVec(32))),
            Box::new(var("b", Sort::BitVec(32))),
            32,
        ),
    ]);

    let smt = formula_to_smt(&formula, &ctx).unwrap();
    let round_trip = smt_to_formula(&smt, &ctx).unwrap();

    assert_eq!(round_trip, formula);
}

#[test]
fn bool_variables_round_trip_through_one_bit_encoding() {
    let ctx = FormulaAdapterContext::new()
        .with_bool_var("p")
        .with_bool_var("q");

    let formula = Formula::Or(vec![
        var("p", Sort::Bool),
        Formula::Not(Box::new(var("q", Sort::Bool))),
    ]);

    let smt = formula_to_smt(&formula, &ctx).unwrap();
    let round_trip = smt_to_formula(&smt, &ctx).unwrap();

    assert_eq!(round_trip, formula);
}

#[test]
fn width_mismatch_is_rejected() {
    let ctx = FormulaAdapterContext::new().with_bv_var("a", 32);
    let formula = Formula::BvAdd(
        Box::new(var("a", Sort::BitVec(32))),
        Box::new(Formula::BitVec {
            value: 1,
            width: 16,
        }),
        32,
    );

    let err = formula_to_smt(&formula, &ctx).unwrap_err();
    assert!(matches!(
        err,
        FormulaAdapterError::WidthMismatch {
            context: "BitVec literal",
            expected: 16,
            actual: 32
        }
    ));
}

#[test]
fn unsupported_formula_construct_is_rejected() {
    let ctx = FormulaAdapterContext::new().with_bv_var("a", 32);
    let formula = Formula::BvURem(
        Box::new(var("a", Sort::BitVec(32))),
        Box::new(Formula::BitVec {
            value: 3,
            width: 32,
        }),
        32,
    );

    let err = formula_to_smt(&formula, &ctx).unwrap_err();
    assert_eq!(err, FormulaAdapterError::UnsupportedFormula("BvURem"));
}

#[test]
fn ambiguous_integer_literal_formula_is_rejected() {
    let ctx = FormulaAdapterContext::new();
    let formula = Formula::Eq(Box::new(Formula::Int(1)), Box::new(Formula::Int(2)));

    let err = formula_to_smt(&formula, &ctx).unwrap_err();
    assert_eq!(err, FormulaAdapterError::AmbiguousLiteral("Int"));
}

#[test]
fn undeclared_variable_is_rejected() {
    let ctx = FormulaAdapterContext::new();
    let formula = var("x", Sort::Int);

    let err = formula_to_smt(&formula, &ctx).unwrap_err();
    assert_eq!(
        err,
        FormulaAdapterError::UndeclaredVariable("x".to_string())
    );
}

#[test]
fn unsupported_smt_construct_is_rejected() {
    let ctx = FormulaAdapterContext::new();
    let expr = SmtExpr::uf("opaque", Vec::new(), SmtSort::Bool);

    let err = smt_to_formula(&expr, &ctx).unwrap_err();
    assert_eq!(err, FormulaAdapterError::UnsupportedSmtExpr("UF"));
}

#[test]
fn unsupported_memory_and_new_fp_smt_constructs_fail_closed() {
    let ctx = FormulaAdapterContext::new();
    let expressions = [
        (
            SmtExpr::mem_load(SmtExpr::bv_const(0, 64), 32, false, 32),
            FormulaAdapterError::UnsupportedSmtExpr("MemLoad"),
        ),
        (
            SmtExpr::fp_round_to_integral(
                RoundingMode::RNE,
                SmtExpr::FPConst {
                    bits: 0,
                    eb: 8,
                    sb: 24,
                },
            ),
            FormulaAdapterError::UnsupportedSmtExpr("FloatingPoint"),
        ),
        (
            SmtExpr::bv_bits_to_fp(SmtExpr::bv_const(0, 32), 8, 24),
            FormulaAdapterError::UnsupportedSmtExpr("FloatingPoint"),
        ),
    ];

    for (expr, expected) in expressions {
        assert_eq!(smt_to_formula(&expr, &ctx).unwrap_err(), expected);
    }
}

#[test]
fn trust_ir_typed_metadata_builds_formula_context() {
    let mut module = TrustIrModule::new("rustc-mir-canonical");
    module.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".to_string(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });

    let func_ty = module.add_func_type(FuncTy {
        params: vec![Ty::I32, Ty::I32, Ty::Bool, Ty::PtrMut(Box::new(Ty::I32))],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut func = Function {
        id: FuncId::new(0),
        name: "rust_add_checked".to_string(),
        ty: func_ty,
        entry: trust_ir::BlockId::new(0),
        blocks: Vec::new(),
        proofs: vec![ProofAnnotation::Pure],
        calling_conv: CallingConv::Rust,
        linkage: Linkage::External,
        attrs: Default::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let mut block = Block::new(trust_ir::BlockId::new(0))
        .with_param(ValueId::new(0), Ty::I32)
        .with_param(ValueId::new(1), Ty::I32)
        .with_param(ValueId::new(2), Ty::Bool)
        .with_param(ValueId::new(3), Ty::PtrMut(Box::new(Ty::I32)));
    block.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(ValueId::new(4))
        .with_proof(ProofAnnotation::NoOverflow)
        .with_span(SourceSpan {
            file: 9,
            line: 27,
            col: 5,
        }),
    );
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(0),
        })
        .with_result(ValueId::new(5)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(4)],
    }));
    func.blocks.push(block);
    module.add_function(func);

    let metadata = module
        .typed_values_for_function(FuncId::new(0))
        .expect("typed trust_ir metadata");
    let add_result = metadata
        .iter()
        .find(|entry| entry.value == ValueId::new(4))
        .expect("add result metadata");
    assert_eq!(add_result.ty, Ty::I32);
    assert_eq!(add_result.proofs, vec![ProofAnnotation::NoOverflow]);
    assert_eq!(
        add_result.origin,
        ValueMetadataOrigin::InstrResult {
            block: trust_ir::BlockId::new(0),
            instruction_index: 0,
            result_index: 0,
        }
    );
    assert_eq!(
        add_result.span,
        Some(SourceSpan {
            file: 9,
            line: 27,
            col: 5,
        })
    );

    let ctx = formula_context_from_trust_ir_function(&module, FuncId::new(0)).unwrap();
    assert_eq!(
        ctx.var_sort(&trust_ir_value_var_name(ValueId::new(0)))
            .unwrap(),
        FormulaAdapterVarSort::SignedInt { width: 32 }
    );
    assert_eq!(
        ctx.var_sort(&trust_ir_value_var_name(ValueId::new(2)))
            .unwrap(),
        FormulaAdapterVarSort::Bool
    );
    assert_eq!(
        ctx.var_sort(&trust_ir_value_var_name(ValueId::new(3)))
            .unwrap(),
        FormulaAdapterVarSort::BitVec(64)
    );
    assert_eq!(
        ctx.var_sort(&trust_ir_value_var_name(ValueId::new(4)))
            .unwrap(),
        FormulaAdapterVarSort::SignedInt { width: 32 }
    );

    let formula = Formula::Eq(
        Box::new(var(&trust_ir_value_var_name(ValueId::new(4)), Sort::Int)),
        Box::new(Formula::Add(
            Box::new(var(&trust_ir_value_var_name(ValueId::new(0)), Sort::Int)),
            Box::new(var(&trust_ir_value_var_name(ValueId::new(1)), Sort::Int)),
        )),
    );
    let smt = formula_to_smt(&formula, &ctx).unwrap();
    assert_eq!(smt.sort(), SmtSort::Bool);
}
