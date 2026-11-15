// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{
    Constant, Inst, TrustIrTy, decode_scalar_int_constant, entry_call_trust_ir_module,
    i8_image_byte_constant, itoa_divisor_word,
};
use trust_cg_lower::adapter::{AdapterError, validate_codegen_prerequisites};

#[test]
fn all_image_bytes_have_independent_signed_values_identical_bits_and_canonical_types() {
    let mut module = entry_call_trust_ir_module(
        "image_byte_constants",
        "main",
        trust_ir::Visibility::Default,
        "rust_main",
        "lang_start",
        0,
    )
    .unwrap();
    for byte in 0_u8..=u8::MAX {
        let literal = i8_image_byte_constant(byte);
        // Host byte decoding is independent of rustc's Size::sign_extend and
        // the bridge's helper. It states the exact fixed eight-bit value.
        let expected = i128::from(i8::from_ne_bytes([byte]));
        assert_eq!(literal, Constant::Int(expected), "byte {byte:#04x}");
        let Constant::Int(value) = &literal else {
            panic!("I8 requires an integer literal")
        };
        assert_eq!(
            value.to_le_bytes()[0],
            byte,
            "all image bits survive spelling"
        );
        assert!(literal.value_matches_ty(&TrustIrTy::I8, 64));
        module.functions[0].blocks[0].body[2].inst = Inst::Const {
            ty: TrustIrTy::I8,
            value: literal,
        };
        assert!(
            validate_codegen_prerequisites(&module).is_ok(),
            "byte {byte:#04x}"
        );
    }
}

#[test]
fn decimal_divisor_words_retain_their_exact_unsigned_bits_and_canonical_i64_spelling() {
    let mut module = entry_call_trust_ir_module(
        "decimal_divisors",
        "main",
        trust_ir::Visibility::Default,
        "rust_main",
        "lang_start",
        0,
    )
    .unwrap();
    for exponent in 0..20 {
        let mathematical = 10_i128.pow(exponent);
        let value = itoa_divisor_word(exponent).unwrap();
        let literal = Constant::Int(value);
        assert!(literal.value_matches_ty(&TrustIrTy::I64, 64));
        assert_eq!(&value.to_le_bytes()[..8], &mathematical.to_le_bytes()[..8]);
        assert_eq!(u128::from(value as u64), mathematical as u128);
        module.functions[0].blocks[0].body[2].inst = Inst::Const {
            ty: TrustIrTy::I64,
            value: literal,
        };
        assert!(validate_codegen_prerequisites(&module).is_ok());
        for magnitude in [0_u64, 1, 10, i64::MAX as u64, 1_u64 << 63, u64::MAX] {
            assert_eq!(
                magnitude / (value as u64),
                (i128::from(magnitude) / mathematical) as u64
            );
            assert_eq!(
                magnitude % (value as u64),
                (i128::from(magnitude) % mathematical) as u64
            );
        }
    }
    assert_eq!(itoa_divisor_word(19), Some(-8_446_744_073_709_551_616));
    for exponent in [20, 21, 127, u32::MAX] {
        assert_eq!(itoa_divisor_word(exponent), None);
    }
}

#[test]
fn the_old_unsigned_high_byte_spelling_still_refuses_at_the_shared_typed_floor() {
    let mut module = entry_call_trust_ir_module(
        "image_byte_constants",
        "main",
        trust_ir::Visibility::Default,
        "rust_main",
        "lang_start",
        0,
    )
    .unwrap();
    for byte in [128_u8, 255] {
        let wrong = Constant::Int(i128::from(byte));
        assert!(!wrong.value_matches_ty(&TrustIrTy::I8, 64));
        module.functions[0].blocks[0].body[2].inst = Inst::Const {
            ty: TrustIrTy::I8,
            value: wrong,
        };
        let error = validate_codegen_prerequisites(&module).unwrap_err();
        assert!(
            matches!(&error, AdapterError::TrustIrAdmissionRefused { error }
            if error == "function 'main' bb0: const type mismatch: expected i8, got int"),
            "{error:?}"
        );
    }
}

#[test]
fn existing_signed_leaf_endpoints_and_unsigned_maxima_preserve_their_ranges() {
    let signed = [
        (
            TrustIrTy::I8,
            1,
            0x80,
            i128::from(i8::MIN),
            0x7f,
            i128::from(i8::MAX),
        ),
        (
            TrustIrTy::I16,
            2,
            0x8000,
            i128::from(i16::MIN),
            0x7fff,
            i128::from(i16::MAX),
        ),
        (
            TrustIrTy::I32,
            4,
            0x8000_0000,
            i128::from(i32::MIN),
            0x7fff_ffff,
            i128::from(i32::MAX),
        ),
        (
            TrustIrTy::I64,
            8,
            0x8000_0000_0000_0000,
            i128::from(i64::MIN),
            0x7fff_ffff_ffff_ffff,
            i128::from(i64::MAX),
        ),
        (
            TrustIrTy::I128,
            16,
            1_u128 << 127,
            i128::MIN,
            i128::MAX as u128,
            i128::MAX,
        ),
    ];
    for (ty, bytes, min_bits, minimum, max_bits, maximum) in signed {
        for (bits, expected) in [(min_bits, minimum), (max_bits, maximum)] {
            let value = decode_scalar_int_constant(&ty, bits, bytes).unwrap();
            assert_eq!(value, expected, "{ty:?}");
            assert!(Constant::Int(value).value_matches_ty(&ty, 64));
        }
    }
    for (ty, bytes, bits) in [
        (TrustIrTy::U8, 1, u128::from(u8::MAX)),
        (TrustIrTy::U16, 2, u128::from(u16::MAX)),
        (TrustIrTy::U32, 4, u128::from(u32::MAX)),
        (TrustIrTy::U64, 8, u128::from(u64::MAX)),
    ] {
        let value = decode_scalar_int_constant(&ty, bits, bytes).unwrap();
        assert_eq!(value, i128::try_from(bits).unwrap());
        assert!(Constant::Int(value).value_matches_ty(&ty, 64));
    }
    assert_eq!(Constant::u128(u128::MAX), Constant::U128(u128::MAX));
    assert!(Constant::u128(u128::MAX).value_matches_ty(&TrustIrTy::U128, 64));
}

#[test]
fn compiler_signed_pointer_width_interpretation_is_source_width_not_host_width() {
    // This is the exact existing bare Rust Int/Isize producer operation, not
    // an admission of pointer-sized aggregate leaves (which still refuse).
    for (bytes, min_bits, minimum, max_bits, maximum) in [
        (
            4,
            0x8000_0000_u128,
            i128::from(i32::MIN),
            0x7fff_ffff_u128,
            i128::from(i32::MAX),
        ),
        (
            8,
            0x8000_0000_0000_0000_u128,
            i128::from(i64::MIN),
            0x7fff_ffff_ffff_ffff_u128,
            i128::from(i64::MAX),
        ),
    ] {
        let size = rustc_abi::Size::from_bytes(bytes);
        assert_eq!(size.sign_extend(min_bits), minimum);
        assert_eq!(size.sign_extend(max_bits), maximum);
        assert_eq!(size.sign_extend(min_bits | max_bits), -1);
    }
}
