// Copyright 2026 Andrew Yates | Apache-2.0
//! Independent ABI layout regression model, not formal proof authority.
//! AAPCS64 2025Q4 B.4/B.6, C.4, C.14-C.15 require the stack copy's
//! alignment, including when earlier parameters have already advanced NSAA.
//! Apple retains natural alignment for named arguments. Anonymous arguments
//! use eight-byte slots except that `i128`, 128-bit vectors and
//! non-homogeneous 16-aligned aggregates of at most 16 bytes start 16-aligned
//! (clang arm64-apple-darwin caller placement). Expectations never use the ABI
//! classifier.

use trust_cg_lower::abi::{AArch64AbiVariant, AppleAArch64ABI, ArgLocation};
use trust_cg_lower::types::Type;

fn check_stack(actual: &[ArgLocation], expected: &[(i64, u32)]) -> Result<(), String> {
    let observed: Vec<_> = actual
        .iter()
        .filter_map(|arg| match arg {
            ArgLocation::Stack { offset, size } => Some((*offset, *size)),
            _ => None,
        })
        .collect();
    if observed == expected {
        Ok(())
    } else {
        Err(format!("expected {expected:?}, observed {observed:?}"))
    }
}

#[test]
fn aggregates_align_after_every_stack_residue_and_do_not_overalign_indirect_pointers() {
    // The size/alignment table is explicit: changing Type::align or bytes must
    // not silently change the expected ABI. Both nested aggregates and arrays
    // containing i128 share the natural sixteen-byte alignment rule.
    let cases = [
        (Type::Struct(vec![Type::I128]), 16, 16),
        (Type::Array(Box::new(Type::I128), 1), 16, 16),
        (Type::Struct(vec![Type::Struct(vec![Type::I128])]), 16, 16),
        (Type::Struct(vec![Type::I64; 2]), 16, 8),
        (Type::Struct(vec![Type::I64]), 8, 8),
        // Large aggregate arguments become eight-aligned pointers, regardless
        // of the original copy's sixteen-byte alignment.
        (Type::Struct(vec![Type::I128, Type::I64]), 8, 8),
    ];
    for variant in [AArch64AbiVariant::Aapcs64, AArch64AbiVariant::Darwin] {
        for prefix in 8..=24 {
            for (aggregate, size, alignment) in &cases {
                let mut types = vec![Type::I8; prefix];
                types.extend([aggregate.clone(), Type::I64]);
                let stride = if variant == AArch64AbiVariant::Darwin {
                    1
                } else {
                    8
                };
                let consumed = (prefix - 8) as i64 * stride;
                let aligned = (consumed + alignment - 1) / alignment * alignment;
                let mut expected: Vec<_> = (0..prefix - 8)
                    .map(|index| (index as i64 * stride, stride as u32))
                    .collect();
                expected.extend([(aligned, *size), (aligned + i64::from(*size), 8)]);
                let actual = AppleAArch64ABI::classify_params_with(variant, &types);
                assert!(
                    check_stack(&actual, &expected).is_ok(),
                    "{variant:?}, prefix={prefix}, {aggregate:?}: {:?}",
                    check_stack(&actual, &expected)
                );
                if variant == AArch64AbiVariant::Aapcs64 {
                    for fixed in 0..=types.len() {
                        assert!(
                            check_stack(
                                &AppleAArch64ABI::classify_params_variadic_with(
                                    variant, fixed, &types
                                ),
                                &expected
                            )
                            .is_ok()
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn spilled_hfa_alignment_respects_prior_integer_stack_arguments() {
    for variant in [AArch64AbiVariant::Aapcs64, AArch64AbiVariant::Darwin] {
        for residue in 1..=16 {
            for (element, alignment, size) in [(Type::F32, 4, 8), (Type::F64, 8, 16)] {
                let mut types = vec![Type::I8; 8 + residue];
                types.extend(vec![Type::F64; 7]);
                types.extend([Type::Struct(vec![element; 2]), Type::F64]);
                let stride = if variant == AArch64AbiVariant::Darwin {
                    1
                } else {
                    8
                };
                let alignment = if variant == AArch64AbiVariant::Darwin {
                    alignment
                } else {
                    8
                };
                let consumed = residue as i64 * stride;
                let aligned = (consumed + alignment - 1) / alignment * alignment;
                let following = (aligned + size + 7) / 8 * 8;
                let mut expected: Vec<_> = (0..residue)
                    .map(|index| (index as i64 * stride, stride as u32))
                    .collect();
                expected.extend([(aligned, size as u32), (following, 8)]);
                assert!(
                    check_stack(
                        &AppleAArch64ABI::classify_params_with(variant, &types),
                        &expected
                    )
                    .is_ok(),
                    "{variant:?}, residue={residue}, size={size}"
                );
            }
        }
    }
}

#[test]
fn darwin_anonymous_aggregates_follow_clang_slot_alignment() {
    // clang's caller for `take9(1, ..., 9, (struct { __int128 x; }){..}, 10L)`
    // stores the fixed ninth argument at [sp], the anonymous struct at
    // [sp, #16] and the trailing long at [sp, #32]: the struct is coerced to
    // i128, whose split halves are assigned 16-aligned.
    let mut types = vec![Type::I64; 9];
    types.extend([Type::Struct(vec![Type::I128]), Type::I64]);
    let actual =
        AppleAArch64ABI::classify_params_variadic_with(AArch64AbiVariant::Darwin, 9, &types);
    assert!(
        check_stack(&actual, &[(0, 8), (16, 16), (32, 8)]).is_ok(),
        "{:?}",
        check_stack(&actual, &[(0, 8), (16, 16), (32, 8)])
    );
    // An eight-aligned pair and a floating-point HFA (inline even above 16
    // bytes) are eight-aligned blocks: clang places `struct { int64_t a, b; }`
    // and `struct { double a, b, c; }` at [sp, #8] after one 8-byte vararg.
    // Short-vector HVAs are refused by the selector instead (clang's own
    // caller and `va_arg` disagree for them).
    for aggregate in [
        Type::Struct(vec![Type::I64, Type::I64]),
        Type::Struct(vec![Type::F64, Type::F64, Type::F64]),
    ] {
        let mut types = vec![Type::I64; 9];
        let size = aggregate.bytes();
        types.extend([aggregate.clone(), Type::I64]);
        let actual =
            AppleAArch64ABI::classify_params_variadic_with(AArch64AbiVariant::Darwin, 9, &types);
        let expected = [(0, 8), (8, size), (8 + i64::from(size), 8)];
        assert!(
            check_stack(&actual, &expected).is_ok(),
            "{aggregate:?}: {:?}",
            check_stack(&actual, &expected)
        );
    }
}

#[test]
fn layout_gate_refutes_missing_alignment_overlap_and_overaligned_pointer() {
    let expected = [(0, 8), (16, 16), (32, 8)];
    let good = expected.map(|(offset, size)| ArgLocation::Stack { offset, size });
    assert!(check_stack(&good, &expected).is_ok());
    let mut missing_alignment = good.clone();
    missing_alignment[1] = ArgLocation::Stack {
        offset: 8,
        size: 16,
    };
    missing_alignment[2] = ArgLocation::Stack {
        offset: 24,
        size: 8,
    };
    assert!(check_stack(&missing_alignment, &expected).is_err());
    let mut overlap = good.clone();
    overlap[2] = ArgLocation::Stack {
        offset: 24,
        size: 8,
    };
    assert!(check_stack(&overlap, &expected).is_err());
    assert!(check_stack(&good[..2], &expected).is_err());
    assert!(check_stack(&good, &[(0, 8), (8, 8), (16, 8)]).is_err());
}
