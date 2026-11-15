// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{Constant, TrustIrTy, const_leaf_constant, typed_integer_constant};
use trust_cg_lower::adapter::{AdapterError, validate_codegen_prerequisites};
use trust_ir::{Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, ValueId};

fn bool_module(value: Constant) -> Module {
    let mut module = Module::new("bool_constant_producer");
    let signature = module
        .add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![TrustIrTy::Bool],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "bool_value", signature, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: TrustIrTy::Bool,
            value,
        })
        .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    function.blocks.push(block);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

#[test]
fn exact_boolean_leaf_and_synthetic_producers_keep_false_and_true_distinct() {
    for (bits, expected) in [(0, false), (1, true)] {
        let leaf = const_leaf_constant(&TrustIrTy::Bool, bits, 1)
            .unwrap()
            .expect("a valid original Boolean image");
        let synthetic = typed_integer_constant(&TrustIrTy::Bool, bits as i128);
        for value in [leaf, synthetic] {
            assert_eq!(value, Constant::Bool(expected));
            assert!(value.value_matches_ty(&TrustIrTy::Bool, 64));
            let module = bool_module(value);
            assert!(validate_codegen_prerequisites(&module).is_ok());
            assert_eq!(
                module.functions[0].blocks[0].body[1].inst,
                Inst::Return {
                    values: vec![ValueId::new(0)],
                }
            );
        }
    }
}

#[test]
fn invalid_boolean_images_and_synthetic_integers_never_coerce_to_truth() {
    for bits in [2, 127, 128, 255, u128::MAX] {
        assert_eq!(
            const_leaf_constant(&TrustIrTy::Bool, bits, 1).unwrap(),
            None
        );
    }
    for integer in [i128::MIN, -128, -1, 2, 127, 128, 255, i128::MAX] {
        let value = typed_integer_constant(&TrustIrTy::Bool, integer);
        assert_eq!(value, Constant::Int(integer));
        assert!(!value.value_matches_ty(&TrustIrTy::Bool, 64));
        let error = validate_codegen_prerequisites(&bool_module(value)).unwrap_err();
        assert!(
            matches!(&error, AdapterError::TrustIrAdmissionRefused { error }
                if error == "function 'bool_value' bb0: const type mismatch: expected bool, got int"),
            "invalid Boolean integer {integer}: {error:?}"
        );
    }
    // Even historically used Int(0)/Int(1) are not canonical Bool literals.
    for integer in [0, 1] {
        let error =
            validate_codegen_prerequisites(&bool_module(Constant::Int(integer))).unwrap_err();
        assert!(
            matches!(&error, AdapterError::TrustIrAdmissionRefused { error }
                if error == "function 'bool_value' bb0: const type mismatch: expected bool, got int"),
            "historical Boolean integer {integer}: {error:?}"
        );
    }
}

#[test]
fn boolean_construction_does_not_reinterpret_other_scalar_carriers() {
    for (ty, value) in [
        (TrustIrTy::I8, i128::from(i8::MIN)),
        (TrustIrTy::I64, i128::from(i64::MIN)),
        (TrustIrTy::U8, i128::from(u8::MAX)),
        (TrustIrTy::U64, i128::from(u64::MAX)),
        (TrustIrTy::U32, 0),
        (TrustIrTy::F32, 1),
        (TrustIrTy::F64, 0),
        (TrustIrTy::Ptr, 0),
    ] {
        assert_eq!(typed_integer_constant(&ty, value), Constant::Int(value));
    }
    assert_eq!(
        typed_integer_constant(&TrustIrTy::U128, -1),
        Constant::u128(u128::MAX)
    );
    assert_eq!(
        typed_integer_constant(&TrustIrTy::I128, -1),
        Constant::Int(-1)
    );
    assert_eq!(
        const_leaf_constant(&TrustIrTy::U8, 255, 1).unwrap(),
        Some(Constant::Int(255))
    );
    assert_eq!(
        const_leaf_constant(&TrustIrTy::I8, 255, 1).unwrap(),
        Some(Constant::Int(-1))
    );
    assert_eq!(
        const_leaf_constant(&TrustIrTy::F64, 0, 8).unwrap(),
        Some(Constant::Float(0.0))
    );
    assert_eq!(
        const_leaf_constant(&TrustIrTy::F32, 0x7f80_0001, 4).unwrap(),
        None
    );
}
