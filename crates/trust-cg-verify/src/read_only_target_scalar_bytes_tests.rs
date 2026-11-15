// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Concrete final-word observation controls, not discharged source relations.
//! Words below are architectural literals/field mutations, never obtained from
//! the compiler encoder or allocated MachIR hints. All expected addresses and
//! transferred values are independently computed integer formulas.

use super::*;
use crate::smt::EvalEnv;

const RET_X30: u32 = 0xd65f_03c0;
const CAPTURED_STR_W7_X0_X3_LSL2: u32 = 0xb823_7807;
const CAPTURED_LDP_W3_W2_X1_16: u32 = 0x2942_0823;

fn code(words: &[u32]) -> Vec<u8> {
    words.iter().flat_map(|word| word.to_le_bytes()).collect()
}

fn one(word: u32) -> Step {
    adapt_word_profile(word, 0, 2, Profile::ScalarMemory).unwrap()
}

fn evaluate(expr: &E, registers: &[(usize, u64)]) -> u64 {
    let mut env = EvalEnv::default();
    for &(index, value) in registers {
        env.insert(format!("x{index}"), value);
    }
    expr.try_eval(&env).unwrap().as_u64()
}

fn refused(word: u32) {
    assert!(
        matches!(
            adapt_word_profile(word, 0, 2, Profile::ScalarMemory),
            Err(ReadOnlyTargetError::Bytes(_))
        ),
        "must structurally refuse {word:#010x}"
    );
}

#[test]
fn original_readonly_entry_point_keeps_its_memory_floor() {
    for word in [
        0xb940_0020, // LDR W0,[X1]
        0xb900_0020, // STR W0,[X1]
        0xf900_0020, // STR X0,[X1]
        CAPTURED_STR_W7_X0_X3_LSL2,
        CAPTURED_LDP_W3_W2_X1_16,
        0xf862_6820, // LDR X0,[X1,X2]
    ] {
        assert!(adapt(&code(&[word, RET_X30])).is_err(), "{word:#010x}");
        assert!(adapt_profile(&code(&[word, RET_X30]), Profile::ScalarMemory).is_ok());
    }
    let steps = adapt(&code(&[0xf940_0421, RET_X30])).unwrap();
    assert!(matches!(
        steps[0],
        Step::Load {
            destination: 1,
            alignment: 1,
            ..
        }
    ));
    let steps = adapt_profile(&code(&[0xf940_0421, RET_X30]), Profile::ScalarMemory).unwrap();
    assert!(matches!(
        steps[0],
        Step::MemoryLoad {
            destination: 1,
            byte_width: 8,
            alignment: 1,
            ..
        }
    ));
}

#[test]
fn actual_captured_store_has_exact_index_scale_and_low_word_payload() {
    let Step::MemoryStore {
        address,
        value,
        byte_width,
        alignment,
    } = one(CAPTURED_STR_W7_X0_X3_LSL2)
    else {
        panic!("captured STR W required")
    };
    assert_eq!((byte_width, alignment), (4, 1));
    assert_eq!(value.try_bv_width().unwrap(), 32);
    for base in [0, 1, 0x1000, u64::MAX] {
        for index in [0, 1, 1 << 32, 0x8000_0000_0000_0001, u64::MAX] {
            for payload in [0, 1, 0xfeed_face_1234_5678, u64::MAX] {
                let regs = [(0, base), (3, index), (7, payload)];
                assert_eq!(
                    evaluate(&address, &regs),
                    base.wrapping_add(index.wrapping_shl(2))
                );
                assert_eq!(evaluate(&value, &regs), payload & u64::from(u32::MAX));
            }
        }
    }
}

#[test]
fn all_register_offset_modes_use_real_width_signedness_and_shift_fields() {
    for bytes in [4_u32, 8] {
        for load in [false, true] {
            for mode in [4_u32, 5, 6, 7, 12, 13, 14, 15] {
                // Register-offset fixed bits, then actual size/L/Rm/option/S/Rn/Rt fields.
                let word = 0x3820_0800
                    | (bytes.trailing_zeros() << 30)
                    | (u32::from(load) << 22)
                    | (3 << 16)
                    | ((mode >> 1) << 13)
                    | ((mode & 1) << 12)
                    | 7;
                let step = one(word);
                let (address, observed_width, alignment) = match &step {
                    Step::MemoryLoad {
                        destination,
                        address,
                        byte_width,
                        alignment,
                    } => {
                        assert!(load);
                        assert_eq!(*destination, 7);
                        (address, *byte_width, *alignment)
                    }
                    Step::MemoryStore {
                        address,
                        value,
                        byte_width,
                        alignment,
                    } => {
                        assert!(!load);
                        assert_eq!(value.try_bv_width().unwrap(), bytes * 8);
                        (address, *byte_width, *alignment)
                    }
                    _ => panic!("ordinary scalar memory required"),
                };
                assert_eq!((observed_width, alignment), (bytes, 1));
                for index in [0, 1, 0x8000_0000, 0xffff_ffff, 1 << 32, u64::MAX] {
                    let extended = match mode >> 1 {
                        2 => index & u64::from(u32::MAX),
                        6 => (index as i32 as i64) as u64,
                        3 | 7 => index,
                        _ => unreachable!(),
                    };
                    let offset = if mode & 1 == 1 {
                        extended.wrapping_mul(u64::from(bytes))
                    } else {
                        extended
                    };
                    for base in [0_u64, 0x1020, u64::MAX] {
                        assert_eq!(
                            evaluate(address, &[(0, base), (3, index)]),
                            base.wrapping_add(offset),
                            "mode={mode} bytes={bytes}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn immediate_scalar_memory_decodes_signed_and_scaled_boundary_offsets() {
    for (word, width, offset, load) in [
        (0xb940_0827, 4, 8_i64, true),
        (0xf940_0827, 8, 16, true),
        (0xb93f_fc27, 4, 16380, false),
        (0xf93f_fc27, 8, 32760, false),
        (0xb850_0027, 4, -256, true),
        (0xf84f_f027, 8, 255, true),
        (0xb81f_f027, 4, -1, false),
        (0xf810_0027, 8, -256, false),
    ] {
        let step = one(word);
        let (address, byte_width, alignment) = match &step {
            Step::MemoryLoad {
                destination: 7,
                address,
                byte_width,
                alignment,
            } if load => (address, *byte_width, *alignment),
            Step::MemoryStore {
                address,
                byte_width,
                alignment,
                ..
            } if !load => (address, *byte_width, *alignment),
            _ => panic!("incorrect decoded transfer {word:#010x}"),
        };
        assert_eq!((byte_width, alignment), (width, 1));
        for base in [0_u64, 1, u64::MAX] {
            assert_eq!(
                evaluate(address, &[(1, base)]),
                base.wrapping_add(offset as u64)
            );
        }
    }
}

#[test]
fn loads_snapshot_aliased_bases_and_keep_discarded_destination_demands() {
    for word in [0xb940_0421, 0xf940_0421] {
        let Step::MemoryLoad {
            destination,
            address,
            byte_width,
            alignment,
        } = one(word)
        else {
            panic!("load required")
        };
        assert_eq!(destination, 1);
        assert_eq!(alignment, 1);
        assert_eq!(
            evaluate(&address, &[(1, 0x1000)]),
            0x1000 + u64::from(byte_width)
        );
    }
    for word in [0xb940_043f, 0xf940_043f, 0xf862_683f] {
        let Step::MemoryLoad {
            destination,
            address,
            alignment,
            ..
        } = one(word)
        else {
            panic!("discarded load is still a read")
        };
        assert_eq!((destination, alignment), (31, 1));
        assert!(address.to_string().contains("x1"));
    }
    let Step::MemoryStore {
        value, byte_width, ..
    } = one(0xf900_003f)
    else {
        panic!("ZR store required")
    };
    assert_eq!(byte_width, 8);
    assert_eq!(evaluate(&value, &[]), 0);
    // Rm=31 is ZR, never SP. It contributes no input and leaves the base unchanged.
    let Step::MemoryStore { address, .. } = one(0xb83f_7827) else {
        panic!("ZR-index store required")
    };
    assert_eq!(evaluate(&address, &[(1, 0x1020)]), 0x1020);
}

#[test]
fn paired_load_is_one_pc_with_two_distinct_width_exact_destinations() {
    let Step::LoadPair {
        destinations,
        address,
        byte_width,
        alignment,
    } = one(CAPTURED_LDP_W3_W2_X1_16)
    else {
        panic!("captured pair required")
    };
    assert_eq!((destinations, byte_width, alignment), ([3, 2], 4, 1));
    assert_eq!(evaluate(&address, &[(1, 0x1000)]), 0x1010);
    let stream = code(&[0x1400_0002, CAPTURED_LDP_W3_W2_X1_16, RET_X30]);
    let steps = adapt_profile(&stream, Profile::ScalarMemory).unwrap();
    assert_eq!(steps.len(), 3);
    assert!(matches!(steps[0], Step::Jump(2)));
    assert!(matches!(steps[1], Step::LoadPair { .. }));
    assert!(matches!(steps[2], Step::Return));
    // Offset-mode base overlap is defined; the address still reads PRE-state X1.
    let Step::LoadPair {
        destinations,
        address,
        ..
    } = one(0x2942_0821)
    else {
        panic!("aliased pair required")
    };
    assert_eq!(destinations, [1, 2]);
    assert_eq!(evaluate(&address, &[(1, 0x2000)]), 0x2010);
    // One discarded lane remains an actual read; it does not erase the other lane.
    assert!(matches!(
        one(0x2942_083f),
        Step::LoadPair {
            destinations: [31, 2],
            ..
        }
    ));
}

#[test]
fn paired_signed_scaled_offsets_include_full_architectural_range() {
    for width in [4_u32, 8] {
        for scaled in [-64_i64, -1, 0, 1, 63] {
            let base = if width == 4 { 0x2940_0000 } else { 0xa940_0000 };
            let word = base | (((scaled as u32) & 0x7f) << 15) | (2 << 10) | (1 << 5) | 3;
            let Step::LoadPair {
                destinations,
                address,
                byte_width,
                alignment,
            } = one(word)
            else {
                panic!("pair required")
            };
            assert_eq!((destinations, byte_width, alignment), ([3, 2], width, 1));
            for pointer in [0_u64, 1, u64::MAX] {
                assert_eq!(
                    evaluate(&address, &[(1, pointer)]),
                    pointer.wrapping_add((scaled * i64::from(width)) as u64)
                );
            }
        }
    }
}

#[test]
fn independent_field_mutations_change_real_store_addresses_and_values() {
    let Step::MemoryStore {
        address: original_address,
        value: original_value,
        ..
    } = one(CAPTURED_STR_W7_X0_X3_LSL2)
    else {
        panic!("store required")
    };
    let regs = [
        (0, 0x1000),
        (1, 0x2000),
        (3, 0x1_8000_0001),
        (4, 9),
        (7, 0xfeed_face_1234_5678),
        (8, 0x0102_0304),
    ];
    let expected_address = evaluate(&original_address, &regs);
    let expected_value = evaluate(&original_value, &regs);
    for word in [
        CAPTURED_STR_W7_X0_X3_LSL2 ^ (1 << 12), // remove scale
        (CAPTURED_STR_W7_X0_X3_LSL2 & !(7 << 13)) | (2 << 13), // UXTW
        (CAPTURED_STR_W7_X0_X3_LSL2 & !(7 << 13)) | (6 << 13), // SXTW
        (CAPTURED_STR_W7_X0_X3_LSL2 & !(31 << 16)) | (4 << 16), // different index
        CAPTURED_STR_W7_X0_X3_LSL2 | (1 << 5),  // different base
    ] {
        let Step::MemoryStore { address, .. } = one(word) else {
            panic!("mutant remains a valid store")
        };
        assert_ne!(
            evaluate(&address, &regs),
            expected_address,
            "semantic address counterexample {word:#010x}"
        );
    }
    let Step::MemoryStore { value, .. } = one((CAPTURED_STR_W7_X0_X3_LSL2 & !31) | 8) else {
        panic!("different-data store required")
    };
    assert_ne!(evaluate(&value, &regs), expected_value);
    let Step::MemoryStore {
        address,
        value,
        byte_width,
        ..
    } = one(CAPTURED_STR_W7_X0_X3_LSL2 | (1 << 30))
    else {
        panic!("X store width mutant required")
    };
    assert_eq!(byte_width, 8);
    assert_ne!(evaluate(&address, &regs), expected_address);
    assert_ne!(evaluate(&value, &regs), expected_value);
}

#[test]
fn scalar_memory_refuses_writeback_noninteger_and_unallocated_index_words() {
    for word in [
        0xb840_0c20,
        0xf840_0420, // pre/post indexed loads
        0xb800_0c20,
        0xf800_0420, // pre/post indexed stores
        0xfd40_0020,
        0xbd00_0020, // floating transfers
        0x3940_0020,
        0x7900_0020, // narrow transfers
        0xb980_0020,
        0x3980_0020, // signed loads
        0xc85f_7c20,
        0xc89f_fc20, // exclusive/acquire/release family
        0xf940_03e0,
        0xf900_03e0, // SP base
        0xf940_0240,
        0xf900_0240, // X18 base
        0xf872_6820, // X18 index
        0xf940_0032,
        0xf900_0032, // X18 data
        0xf862_0820,
        0xf862_2820,
        0xf862_8820,
        0xf862_a820, // option<1>=0
        0x9400_0001,
        0xd63f_0020, // calls
        0xd53b_4200,
        0xd51b_4200, // system/NZCV accesses
    ] {
        refused(word);
    }
}

#[test]
fn pair_memory_refuses_effects_reserved_banks_and_duplicate_destinations() {
    for word in [
        0x2902_0823, // STP W3,W2,[X1,#16]
        0x29c2_0823,
        0x28c2_0823, // pre/post indexed LDP
        0x2842_0823, // non-temporal LDNP
        0x6942_0823, // LDPSW
        0x2d42_0823,
        0xad42_0823, // SIMD pair
        0xe942_0823, // unallocated opc
        0x2942_0be3, // SP base
        0x2942_0a43, // X18 base
        0x2942_0832, // W18 destination
        0x2942_4823, // W18 second destination
        0x2942_0822, // duplicate W2/W2
        0x2942_7c3f, // duplicate WZR/WZR
    ] {
        refused(word);
    }
    // Bit25 moves this word into the data-processing class. A valid scalar
    // instruction must get ITS effects, not be refused or treated as a pair.
    let different_class = CAPTURED_LDP_W3_W2_X1_16 | (1 << 25);
    assert!(decode_pair_memory_word(different_class).is_none());
    assert!(matches!(
        one(different_class),
        Step::Scalar { flags: Some(_), .. }
    ));
}

#[test]
fn scalar_byte_profile_preserves_fullstatus_integer_decoder_and_return() {
    for (word, expected) in [
        (0x9b05_10c7, 11_u64.wrapping_mul(13).wrapping_add(17)), // MADD X7,X6,X5,X4
        (0xd340_7c43, 0x1234_5678),                              // UXTW X3,W2
        (0x8b06_0c82, 17 + (11 << 3)),                           // ADD X2,X4,X6,LSL #3
        (0xd280_0060, 3),                                        // full-X0 status word
        (0xf2c0_0020, (1_u64 << 32) | 1), // MOVK X0,#1,LSL #32 retains low status
    ] {
        let Step::Scalar { value, flags, .. } = one(word) else {
            panic!("shared integer decoder required")
        };
        assert_eq!(value.try_bv_width().unwrap(), 64);
        assert!(flags.is_none());
        assert_eq!(
            evaluate(
                &value,
                &[
                    (0, 1),
                    (2, 0xffff_eeee_1234_5678),
                    (4, 17),
                    (5, 13),
                    (6, 11)
                ]
            ),
            expected
        );
        // These integer classes were already in the read-only byte profile.
        assert!(adapt_word(word, 0, 2).is_ok());
    }
    assert!(matches!(one(RET_X30), Step::Return));
    refused(0xd65f_0020);
}

#[test]
fn byte_stream_shape_and_resource_limits_apply_before_profile_observation() {
    for profile in [Profile::ReadOnly, Profile::ScalarMemory] {
        assert!(adapt_profile(&[], profile).is_err());
        assert!(adapt_profile(&[0; 3], profile).is_err());
        assert!(matches!(
            adapt_profile(&code(&[NOP; MAX_WORDS + 1]), profile),
            Err(ReadOnlyTargetError::Budget("final-word count"))
        ));
        assert_eq!(
            adapt_profile(&code(&[NOP; MAX_WORDS]), profile)
                .unwrap()
                .len(),
            MAX_WORDS
        );
    }
    // An invalid memory word is inspected even if a preceding branch skips it.
    assert!(
        adapt_profile(
            &code(&[0x1400_0002, 0xf900_03e0, RET_X30]),
            Profile::ScalarMemory
        )
        .is_err()
    );
}

#[test]
fn pure_extend_reg_helper_is_bounded_and_preserves_original_expression_shape() {
    let input = E::var("x3", 64);
    for option in 0..=7_u32 {
        for shift in 0..=4_u32 {
            let width = [8_u32, 16, 32, 64][(option & 3) as usize];
            let len = width.min(64 - shift);
            // Independent reconstruction of the old Roles::read/concat/extend AST.
            let mut expected = if len == 64 {
                input.clone()
            } else {
                input.clone().extract(len - 1, 0)
            };
            if shift != 0 {
                expected = expected.concat(E::bv_const(0, shift));
            }
            let remaining = 64 - len - shift;
            if remaining != 0 {
                expected = if option & 4 == 0 {
                    expected.zero_ext(remaining)
                } else {
                    expected.sign_ext(remaining)
                };
            }
            let observed = extend_reg_value(input.clone(), option, shift).unwrap();
            assert_eq!(observed, expected, "option={option} shift={shift}");
            for raw in [0, 1, 0x80, 0x8000, 0x8000_0000, u64::MAX] {
                let kept = if len == 64 {
                    raw
                } else {
                    raw & ((1_u64 << len) - 1)
                };
                let extended = if len < 64 && option & 4 != 0 && kept & (1_u64 << (len - 1)) != 0 {
                    kept | (u64::MAX << len)
                } else {
                    kept
                };
                assert_eq!(
                    evaluate(&observed, &[(3, raw)]),
                    extended.wrapping_shl(shift)
                );
            }
        }
    }
    assert!(extend_reg_value(E::BoolConst(true), 3, 0).is_none());
    assert!(extend_reg_value(E::var("w3", 32), 3, 0).is_none());
    assert!(
        extend_reg_value(
            E::uf("memory", vec![], crate::memory_proofs::memory_sort()),
            3,
            0
        )
        .is_none()
    );
    assert!(extend_reg_value(input.clone(), 8, 0).is_none());
    assert!(extend_reg_value(input, 3, 5).is_none());
}
