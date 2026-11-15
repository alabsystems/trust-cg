// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! `typed_integer_constant` for a signed type spells an unsigned bit pattern
//! as that type's signed value. trust-ir's typed admission takes an `I8`..`I64`
//! constant only in the type's own range, so a pattern held as its unsigned
//! value (`u64::MAX`, the `0xAAAA_..` masks of `u64::reverse_bits`) refused
//! the whole module ("const type mismatch: expected i64, got int"):
//! `u64::reverse_bits` at -O0..-O3 on trust-cg main 4f5020306
//! (`m110_bitmanip_x86`'s `rb_u64` in `bridge_feature_suites_aarch64`).

use super::{
    Constant, TrustIrTy, canonicalize_signed_constant_spellings, signed_pattern_spelling,
    typed_integer_constant,
};
use trust_cg_lower::adapter::{AdapterError, validate_codegen_prerequisites};
use trust_ir::{Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, ValueId};

fn i64_module(value: Constant) -> Module {
    const_module(TrustIrTy::I64, value)
}

fn const_module(ty: TrustIrTy, value: Constant) -> Module {
    let mut module = Module::new("signed_constant_producer");
    let signature = module
        .add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "signed_value", signature, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block
        .body
        .push(InstrNode::new(Inst::Const { ty, value }).with_result(ValueId::new(0)));
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
fn an_unsigned_pattern_is_spelled_as_the_signed_value_with_the_same_bits() {
    let cells = [
        (TrustIrTy::I8, 0xFF, -1),
        (TrustIrTy::I8, 0x80, i128::from(i8::MIN)),
        (TrustIrTy::I16, 0xFFFE, -2),
        (TrustIrTy::I32, i128::from(u32::MAX), -1),
        (TrustIrTy::I64, i128::from(u64::MAX), -1),
        (
            TrustIrTy::I64,
            10_000_000_000_000_000_000,
            -8_446_744_073_709_551_616,
        ),
        (
            TrustIrTy::I64,
            0xAAAA_AAAA_AAAA_AAAA,
            0xAAAA_AAAA_AAAA_AAAAu64 as i64 as i128,
        ),
    ];
    for (ty, pattern, signed) in cells {
        let value = typed_integer_constant(&ty, pattern);
        assert_eq!(value, Constant::Int(signed), "{ty:?} {pattern:#x}");
        assert!(value.value_matches_ty(&ty, 64), "{ty:?} {pattern:#x}");
    }
}

#[test]
fn in_range_values_and_impossible_integers_are_not_rewritten() {
    // In range for the signed type: unchanged.
    for (ty, value) in [
        (TrustIrTy::I8, -128),
        (TrustIrTy::I8, 127),
        (TrustIrTy::I64, i128::from(i64::MIN)),
        (TrustIrTy::I64, i128::from(i64::MAX)),
    ] {
        assert_eq!(signed_pattern_spelling(&ty, value), value);
    }
    // Neither a signed nor an unsigned value of the width: left for the
    // admission to refuse, never truncated into some other integer.
    for (ty, value) in [
        (TrustIrTy::I8, 256),
        (TrustIrTy::I8, -129),
        (TrustIrTy::I64, i128::from(u64::MAX) + 1),
        (TrustIrTy::I64, i128::MIN),
    ] {
        assert_eq!(signed_pattern_spelling(&ty, value), value);
        assert!(!Constant::Int(value).value_matches_ty(&ty, 64));
    }
    // Unsigned types keep their own (unsigned) spelling.
    assert_eq!(
        typed_integer_constant(&TrustIrTy::U64, i128::from(u64::MAX)),
        Constant::Int(i128::from(u64::MAX))
    );
}

#[test]
fn an_i64_module_with_a_u64_pattern_constant_is_admitted() {
    // The raw unsigned spelling is what the admission refuses ...
    let raw = Constant::Int(i128::from(u64::MAX));
    let error = validate_codegen_prerequisites(&i64_module(raw)).unwrap_err();
    assert!(
        matches!(&error, AdapterError::TrustIrAdmissionRefused { error }
            if error.contains("const type mismatch: expected i64, got int")),
        "{error:?}"
    );
    // ... and `typed_integer_constant`'s spelling, which `emit_i64_const`
    // and `emit_typed_const` use, is admitted.
    let spelled = typed_integer_constant(&TrustIrTy::I64, i128::from(u64::MAX));
    assert!(validate_codegen_prerequisites(&i64_module(spelled)).is_ok());
}

#[test]
fn a_raw_unsigned_pattern_constant_is_respelled_before_admission() {
    // A producer that writes `Constant::Int` itself (not through
    // `typed_integer_constant`): a niche or tag value of an `I32` lane.
    for (ty, raw, signed) in [
        (TrustIrTy::I32, i128::from(u32::MAX), -1),
        (TrustIrTy::I16, 0x8000, i128::from(i16::MIN)),
        (TrustIrTy::I64, 1i128 << 63, i128::from(i64::MIN)),
    ] {
        let mut module = const_module(ty.clone(), Constant::Int(raw));
        assert!(
            validate_codegen_prerequisites(&module).is_err(),
            "{ty:?} {raw:#x}"
        );
        canonicalize_signed_constant_spellings(&mut module);
        assert!(
            matches!(
                &module.functions[0].blocks[0].body[0].inst,
                Inst::Const { value: Constant::Int(v), .. } if *v == signed
            ),
            "{ty:?} {raw:#x}"
        );
        assert!(
            validate_codegen_prerequisites(&module).is_ok(),
            "{ty:?} {raw:#x}"
        );
    }
    // An impossible value stays and is still refused.
    let mut module = const_module(TrustIrTy::I8, Constant::Int(300));
    canonicalize_signed_constant_spellings(&mut module);
    assert!(validate_codegen_prerequisites(&module).is_err());
}
