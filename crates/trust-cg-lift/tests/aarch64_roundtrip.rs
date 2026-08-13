// trust-cg-lift/tests/aarch64_roundtrip - AArch64 decode round-trip tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_lift::disasm::aarch64::{
    AddSubCarry, AddSubImm, AddSubShiftedReg, BitfieldMove, BranchReg, Brk, CompareAndSwap,
    CompareBranch, CondBranch, ConditionalSelect, DataProcessing2Source, DataProcessing3Source,
    DecodeError, FpArith, FpCompare, FpImmediate, FpIntConversion, FpPrecisionConvert, FpUnary,
    Instruction, LoadLiteral, LoadStoreAcquireRelease, LoadStoreExclusiveAcquireRelease,
    LoadStoreIndexMode, LoadStoreIndexed, LoadStorePair, LoadStorePairAddressMode,
    LoadStoreRegister, LoadStoreUnscaled, LoadStoreUnsignedImm, LogicalImm, LogicalShiftedReg,
    LseAtomicRmw, LseAtomicRmwOp, MoveWide, NeonAcrossLanes, NeonDupElement, NeonDupGeneral,
    NeonElementSize, NeonFpVec3Same, NeonInsGeneral, NeonIntVec3Same, NeonLdStSinglePostImm,
    NeonMoviByte, NeonVecLogic, NeonVecNot, PcRelAddress, SystemBarrier, SystemBarrierKind,
    SystemRegisterRead, TestBranch, UncondBranch, decode,
};

#[allow(dead_code, clippy::too_many_arguments)]
#[path = "../../trust-cg-codegen/src/aarch64/encoding.rs"]
mod encoding;

#[allow(dead_code, clippy::too_many_arguments, clippy::unusual_byte_groupings)]
#[path = "../../trust-cg-codegen/src/aarch64/encoding_mem.rs"]
mod encoding_mem;

#[allow(dead_code)]
#[path = "../../trust-cg-codegen/src/aarch64/encoding_fp.rs"]
mod encoding_fp;

#[allow(dead_code)]
#[path = "../../trust-cg-codegen/src/aarch64/encoding_neon.rs"]
mod encoding_neon;

fn encode_data_processing_2_source(sf: u32, opcode: u32, rm: u32, rn: u32, rd: u32) -> u32 {
    (sf << 31) | (0b0_0011010110 << 21) | (rm << 16) | (opcode << 10) | (rn << 5) | rd
}

fn encode_add_sub_carry(sf: u32, op: u32, set_flags: bool, rm: u32, rn: u32, rd: u32) -> u32 {
    (sf << 31)
        | (op << 30)
        | ((set_flags as u32) << 29)
        | (0b11010000 << 21)
        | (rm << 16)
        | (rn << 5)
        | rd
}

fn encode_logical_imm(sf: u32, opc: u32, n: bool, immr: u32, imms: u32, rn: u32, rd: u32) -> u32 {
    (sf << 31)
        | (opc << 29)
        | (0b100100 << 23)
        | ((n as u32) << 22)
        | ((immr & 0x3f) << 16)
        | ((imms & 0x3f) << 10)
        | (rn << 5)
        | rd
}

fn encode_data_processing_3_source(
    sf: u32,
    op31: u32,
    o0: bool,
    rm: u32,
    ra: u32,
    rn: u32,
    rd: u32,
) -> u32 {
    (sf << 31)
        | (0b11011 << 24)
        | (op31 << 21)
        | (rm << 16)
        | ((o0 as u32) << 15)
        | (ra << 10)
        | (rn << 5)
        | rd
}

fn encode_conditional_select(
    sf: u32,
    op: bool,
    o2: bool,
    rm: u32,
    cond: u32,
    rn: u32,
    rd: u32,
) -> u32 {
    (sf << 31)
        | ((op as u32) << 30)
        | (0b11010100 << 21)
        | (rm << 16)
        | (cond << 12)
        | ((o2 as u32) << 10)
        | (rn << 5)
        | rd
}

fn encode_bitfield_move(sf: u32, opc: u32, immr: u32, imms: u32, rn: u32, rd: u32) -> u32 {
    (sf << 31)
        | (opc << 29)
        | (0b100110 << 23)
        | (sf << 22)
        | (immr << 16)
        | (imms << 10)
        | (rn << 5)
        | rd
}

fn encode_fmov_immediate(ftype: u32, imm8: u32, rd: u32) -> u32 {
    (0b00011110 << 24) | (ftype << 22) | (1 << 21) | (imm8 << 13) | (0b100 << 10) | rd
}

fn encode_system_barrier(op2: u32, crm: u32) -> u32 {
    0xd503_3000 | ((crm & 0xf) << 8) | (op2 << 5) | 0b11111
}

fn encode_mrs(sysreg: u32, rt: u32) -> u32 {
    0xd520_0000 | ((sysreg & 0xffff) << 5) | rt
}

fn encode_nop() -> u32 {
    0xd503_201f
}

fn encode_brk(imm16: u32) -> u32 {
    0xd420_0000 | ((imm16 & 0xffff) << 5)
}

fn encode_load_literal(opc: u32, vector: bool, imm19: u32, rt: u32) -> u32 {
    (opc << 30) | (0b011 << 27) | ((vector as u32) << 26) | ((imm19 & 0x7ffff) << 5) | rt
}

fn encode_test_branch(nonzero: bool, bit: u32, imm14: u32, rt: u32) -> u32 {
    (((bit >> 5) & 1) << 31)
        | (0b011011 << 25)
        | ((nonzero as u32) << 24)
        | ((bit & 0x1f) << 19)
        | ((imm14 & 0x3fff) << 5)
        | rt
}

fn encode_load_acquire(size: u32, rn: u32, rt: u32) -> u32 {
    (size << 30)
        | (0b001000 << 24)
        | (1 << 23)
        | (1 << 22)
        | (0b11111 << 16)
        | (1 << 15)
        | (0b11111 << 10)
        | (rn << 5)
        | rt
}

fn encode_store_release(size: u32, rn: u32, rt: u32) -> u32 {
    (size << 30)
        | (0b001000 << 24)
        | (1 << 23)
        | (0b11111 << 16)
        | (1 << 15)
        | (0b11111 << 10)
        | (rn << 5)
        | rt
}

fn encode_load_acquire_exclusive(size: u32, rn: u32, rt: u32) -> u32 {
    (size << 30)
        | (0b001000 << 24)
        | (1 << 22)
        | (0b11111 << 16)
        | (1 << 15)
        | (0b11111 << 10)
        | (rn << 5)
        | rt
}

fn encode_store_release_exclusive(size: u32, rs: u32, rn: u32, rt: u32) -> u32 {
    (size << 30) | (0b001000 << 24) | (rs << 16) | (1 << 15) | (0b11111 << 10) | (rn << 5) | rt
}

fn encode_cas(size: u32, acquire: bool, release: bool, rs: u32, rn: u32, rt: u32) -> u32 {
    (size << 30)
        | (0b001000 << 24)
        | (1 << 23)
        | ((acquire as u32) << 22)
        | (1 << 21)
        | (rs << 16)
        | ((release as u32) << 15)
        | (0b11111 << 10)
        | (rn << 5)
        | rt
}

#[allow(clippy::too_many_arguments)]
fn encode_lse_rmw(
    size: u32,
    acquire: bool,
    release: bool,
    rs: u32,
    o3: bool,
    opc: u32,
    rn: u32,
    rt: u32,
) -> u32 {
    (size << 30)
        | (0b111 << 27)
        | ((acquire as u32) << 23)
        | ((release as u32) << 22)
        | (1 << 21)
        | (rs << 16)
        | ((o3 as u32) << 15)
        | (opc << 12)
        | (rn << 5)
        | rt
}

#[test]
fn decodes_add_sub_shifted_reg_round_trip() {
    let word = encoding::encode_add_sub_shifted_reg(1, 0, 1, 0b10, 7, 12, 3, 2);

    assert_eq!(
        decode(word),
        Ok(Instruction::AddSubShiftedReg(AddSubShiftedReg {
            sf: 1,
            op: 0,
            set_flags: true,
            shift: 0b10,
            rm: 7,
            imm6: 12,
            rn: 3,
            rd: 2,
        }))
    );
}

#[test]
fn rejects_reserved_add_sub_shift() {
    let word = (1 << 31) | (0b01011 << 24) | (0b11 << 22) | (2 << 16) | (1 << 5);

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "add/sub shifted register uses reserved shift field 0b11",
        })
    );
}

#[test]
fn decodes_logical_shifted_reg_round_trip() {
    let word = encoding::encode_logical_shifted_reg(0, 0b10, 0b11, 1, 9, 4, 5, 6);

    assert_eq!(
        decode(word),
        Ok(Instruction::LogicalShiftedReg(LogicalShiftedReg {
            sf: 0,
            opc: 0b10,
            shift: 0b11,
            n: true,
            rm: 9,
            imm6: 4,
            rn: 5,
            rd: 6,
        }))
    );
}

#[test]
fn decodes_logical_immediate_round_trips() {
    let cases = [
        (
            encode_logical_imm(1, 0b00, true, 0, 7, 1, 0),
            1,
            0b00,
            true,
            0,
            7,
            1,
            0,
        ),
        (
            encode_logical_imm(1, 0b01, false, 0, 0, 31, 0),
            1,
            0b01,
            false,
            0,
            0,
            31,
            0,
        ),
        (
            encode_logical_imm(1, 0b10, true, 16, 31, 1, 0),
            1,
            0b10,
            true,
            16,
            31,
            1,
            0,
        ),
        (
            encode_logical_imm(0, 0b00, false, 0, 3, 1, 0),
            0,
            0b00,
            false,
            0,
            3,
            1,
            0,
        ),
    ];

    for (word, sf, opc, n, immr, imms, rn, rd) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::LogicalImm(LogicalImm {
                sf,
                opc,
                n,
                immr,
                imms,
                rn,
                rd,
            }))
        );
    }
}

#[test]
fn logical_immediate_known_encodings_round_trip() {
    assert_eq!(encode_logical_imm(1, 0b00, true, 0, 7, 1, 0), 0x9240_1c20);
    assert_eq!(encode_logical_imm(1, 0b01, false, 0, 0, 31, 0), 0xb200_03e0);
    assert_eq!(encode_logical_imm(1, 0b10, true, 16, 31, 1, 0), 0xd250_7c20);
    assert_eq!(encode_logical_imm(0, 0b00, false, 0, 3, 1, 0), 0x1200_0c20);
}

#[test]
fn logical_immediate_ands_decodes() {
    // ANDS (immediate) — `tst Xn, #imm` when Rd==31 — decodes exactly like the
    // other three logical-immediate forms; the only difference is that it
    // writes NZCV, which the consumer reads off `opc`. This pinned a
    // fail-closed rejection while the a64 interpreter already implemented the
    // semantics (sets N/Z, clears C/V, treats Rd==31 as a discard), which left
    // the select/cmov corpus sweep red on every tst-bearing program. The pin
    // now asserts the decode rather than the refusal.
    let word = encode_logical_imm(1, 0b11, true, 0, 7, 1, 0);

    match decode(word) {
        Ok(Instruction::LogicalImm(l)) => {
            assert_eq!(l.sf, 1);
            assert_eq!(l.opc, 0b11, "ANDS");
            assert!(l.n);
            assert_eq!(l.immr, 0);
            assert_eq!(l.imms, 7);
            assert_eq!(l.rn, 1);
            assert_eq!(l.rd, 0);
        }
        other => panic!("expected LogicalImm ANDS, got {other:?}"),
    }
}

#[test]
fn rejects_unallocated_32_bit_logical_immediate_n() {
    let word = encode_logical_imm(0, 0b00, true, 0, 7, 1, 0);

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "32-bit logical immediate cannot set N",
        })
    );
}

#[test]
fn rejects_unallocated_logical_immediate_all_ones_masks() {
    for word in [
        encode_logical_imm(1, 0b00, true, 0, 0x3f, 1, 0),
        encode_logical_imm(0, 0b00, false, 0, 0x1f, 1, 0),
    ] {
        assert_eq!(
            decode(word),
            Err(DecodeError::Unallocated {
                word,
                reason: "logical immediate bitmask encoding is unallocated",
            })
        );
    }
}

#[test]
fn decodes_add_sub_imm_round_trip() {
    let word = encoding::encode_add_sub_imm(1, 1, 0, 1, 0xabc, 29, 0);

    assert_eq!(
        decode(word),
        Ok(Instruction::AddSubImm(AddSubImm {
            sf: 1,
            op: 1,
            set_flags: false,
            shift12: true,
            imm12: 0xabc,
            rn: 29,
            rd: 0,
        }))
    );
}

#[test]
fn decodes_adc_sbc_round_trips() {
    let cases = [
        (encode_add_sub_carry(1, 0, false, 2, 1, 0), 1, 0, 2, 1, 0),
        (encode_add_sub_carry(1, 1, false, 7, 6, 5), 1, 1, 7, 6, 5),
        (encode_add_sub_carry(0, 0, false, 10, 9, 8), 0, 0, 10, 9, 8),
        (
            encode_add_sub_carry(0, 1, false, 13, 12, 11),
            0,
            1,
            13,
            12,
            11,
        ),
    ];

    for (word, sf, op, rm, rn, rd) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::AddSubCarry(AddSubCarry {
                sf,
                op,
                set_flags: false,
                rm,
                rn,
                rd,
            }))
        );
    }
}

#[test]
fn adc_sbc_known_encodings_round_trip() {
    assert_eq!(encode_add_sub_carry(1, 0, false, 2, 1, 0), 0x9a02_0020);
    assert_eq!(encode_add_sub_carry(1, 1, false, 2, 1, 0), 0xda02_0020);
}

#[test]
fn unsupported_adc_sbc_set_flags_neighbors_fail_closed() {
    let words = [
        encode_add_sub_carry(1, 0, true, 2, 1, 0),
        encode_add_sub_carry(1, 1, true, 2, 1, 0),
    ];

    for word in words {
        assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
    }
}

#[test]
fn decodes_move_wide_round_trip() {
    let word = encoding::encode_move_wide(1, 0b11, 2, 0xbeef, 10);

    assert_eq!(
        decode(word),
        Ok(Instruction::MoveWide(MoveWide {
            sf: 1,
            opc: 0b11,
            hw: 2,
            imm16: 0xbeef,
            rd: 10,
        }))
    );
}

#[test]
fn decodes_bitfield_move_round_trips() {
    let cases = [
        (1, 0b10, 16, 31, 1, 0),
        (1, 0b00, 0, 31, 2, 3),
        (1, 0b01, 4, 11, 5, 6),
        (0, 0b10, 0, 7, 8, 9),
    ];

    for (sf, opc, immr, imms, rn, rd) in cases {
        let word = encode_bitfield_move(sf, opc, immr, imms, rn, rd);

        assert_eq!(
            decode(word),
            Ok(Instruction::BitfieldMove(BitfieldMove {
                sf: sf as u8,
                opc: opc as u8,
                immr: immr as u8,
                imms: imms as u8,
                rn: rn as u8,
                rd: rd as u8,
            }))
        );
    }
}

#[test]
fn decodes_bitfield_alias_shapes() {
    let cases = [
        (encode_bitfield_move(1, 0b10, 62, 61, 1, 0), 1, 0b10, 62, 61),
        (encode_bitfield_move(0, 0b10, 3, 31, 2, 3), 0, 0b10, 3, 31),
        (encode_bitfield_move(1, 0b00, 3, 63, 4, 5), 1, 0b00, 3, 63),
        (encode_bitfield_move(1, 0b00, 0, 7, 6, 7), 1, 0b00, 0, 7),
    ];

    for (word, sf, opc, immr, imms) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::BitfieldMove(BitfieldMove {
                sf,
                opc,
                immr,
                imms,
                rn: bits(word, 5, 5) as u8,
                rd: bits(word, 0, 5) as u8,
            }))
        );
    }
}

#[test]
fn decodes_pc_relative_address_round_trip() {
    let adr = encoding_mem::encode_adr(-17, 9).unwrap();
    assert_eq!(
        decode(adr),
        Ok(Instruction::PcRelAddress(PcRelAddress {
            page: false,
            imm21: -17,
            rd: 9,
        }))
    );

    let adrp = encoding_mem::encode_adrp(1_048_575, 30).unwrap();
    assert_eq!(
        decode(adrp),
        Ok(Instruction::PcRelAddress(PcRelAddress {
            page: true,
            imm21: 1_048_575,
            rd: 30,
        }))
    );
}

#[test]
fn rejects_unallocated_move_wide_opc() {
    let word = (1 << 31) | (0b01 << 29) | (0b100101 << 23) | (0x1234 << 5) | 3;

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "move-wide opc field 0b01 is unallocated",
        })
    );
}

#[test]
fn rejects_unallocated_32bit_move_wide_high_halfwords() {
    for opc in [0b00, 0b10, 0b11] {
        for hw in [0b10, 0b11] {
            let word = encoding::encode_move_wide(0, opc, hw, 0x1234, 3);

            assert_eq!(
                decode(word),
                Err(DecodeError::Unallocated {
                    word,
                    reason: "32-bit move-wide hw field selects a nonexistent halfword lane",
                }),
                "opc={opc:#04b}, hw={hw:#04b}"
            );
        }
    }
}

#[test]
fn decodes_allocated_move_wide_halfword_boundaries() {
    for opc in [0b00, 0b10, 0b11] {
        for (sf, hw) in [(0, 0b01), (1, 0b10), (1, 0b11)] {
            let word = encoding::encode_move_wide(sf, opc, hw, 0xabcd, 17);

            assert_eq!(
                decode(word),
                Ok(Instruction::MoveWide(MoveWide {
                    sf: sf as u8,
                    opc: opc as u8,
                    hw: hw as u8,
                    imm16: 0xabcd,
                    rd: 17,
                })),
                "sf={sf}, opc={opc:#04b}, hw={hw:#04b}"
            );
        }
    }
}

#[test]
fn rejects_unallocated_bitfield_n_mismatch() {
    let word = (0b10 << 29) | (0b100110 << 23) | (1 << 22) | (7 << 10) | (1 << 5);

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "bitfield move N bit must match sf",
        })
    );
}

#[test]
fn rejects_unallocated_32bit_bitfield_high_immediate() {
    let word = encode_bitfield_move(0, 0b10, 32, 7, 1, 0);

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "32-bit bitfield move immediates must be in 0..32",
        })
    );
}

#[test]
fn unsupported_bitfield_opc_11_fails_closed() {
    let word = encode_bitfield_move(1, 0b11, 0, 0, 1, 0);

    assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
}

#[test]
fn decodes_cond_branch_round_trip() {
    let word = encoding::encode_cond_branch(0x1_2345, 0b1010);

    assert_eq!(
        decode(word),
        Ok(Instruction::CondBranch(CondBranch {
            imm19: 0x1_2345,
            cond: 0b1010,
        }))
    );
}

#[test]
fn decodes_uncond_branch_round_trip() {
    let word = encoding::encode_uncond_branch(1, 0x02_3456);

    assert_eq!(
        decode(word),
        Ok(Instruction::UncondBranch(UncondBranch {
            link: true,
            imm26: 0x02_3456,
        }))
    );
}

#[test]
fn decodes_branch_reg_round_trip() {
    let word = encoding::encode_branch_reg(0b0010, 30);

    assert_eq!(
        decode(word),
        Ok(Instruction::BranchReg(BranchReg {
            opc: 0b0010,
            rn: 30,
        }))
    );
}

#[test]
fn decodes_load_store_unsigned_round_trip() {
    let word = encoding::encode_load_store_ui(0b11, 0, 0b01, 0x321, 31, 8);
    let expected = Instruction::LoadStoreUnsignedImm(LoadStoreUnsignedImm {
        size: 0b11,
        vector: false,
        opc: 0b01,
        imm12: 0x321,
        rn: 31,
        rt: 8,
    });

    assert_eq!(decode(word), Ok(expected));
}

#[test]
fn decodes_load_store_unscaled_round_trip() {
    let word = encoding::encode_load_store_unscaled(0b10, 0, 0b00, -16, 29, 11);

    assert_eq!(
        decode(word),
        Ok(Instruction::LoadStoreUnscaled(LoadStoreUnscaled {
            size: 0b10,
            vector: false,
            opc: 0b00,
            imm9: -16,
            rn: 29,
            rt: 11,
        }))
    );
}

#[test]
fn decodes_load_store_pre_index_round_trip() {
    let word = encoding_mem::encode_ldr_str_pre_index(
        encoding_mem::LoadStoreSize::Double,
        false,
        encoding_mem::LoadStoreOp::Store,
        -16,
        31,
        2,
    )
    .unwrap();

    assert_eq!(
        decode(word),
        Ok(Instruction::LoadStoreIndexed(LoadStoreIndexed {
            size: 0b11,
            vector: false,
            opc: 0b00,
            imm9: -16,
            mode: LoadStoreIndexMode::PreIndex,
            rn: 31,
            rt: 2,
        }))
    );
}

#[test]
fn decodes_load_store_post_index_round_trip() {
    let word = encoding_mem::encode_ldr_str_post_index(
        encoding_mem::LoadStoreSize::Byte,
        false,
        encoding_mem::LoadStoreOp::Load,
        255,
        0,
        30,
    )
    .unwrap();

    assert_eq!(
        decode(word),
        Ok(Instruction::LoadStoreIndexed(LoadStoreIndexed {
            size: 0b00,
            vector: false,
            opc: 0b01,
            imm9: 255,
            mode: LoadStoreIndexMode::PostIndex,
            rn: 0,
            rt: 30,
        }))
    );
}

#[test]
fn decodes_load_store_register_round_trip() {
    let word = encoding_mem::encode_ldr_str_register(
        encoding_mem::LoadStoreSize::Double,
        false,
        encoding_mem::LoadStoreOp::Load,
        12,
        encoding_mem::RegExtend::Lsl,
        true,
        31,
        2,
    )
    .unwrap();

    assert_eq!(
        decode(word),
        Ok(Instruction::LoadStoreRegister(LoadStoreRegister {
            size: 0b11,
            vector: false,
            opc: 0b01,
            rm: 12,
            option: 0b011,
            shift: true,
            rn: 31,
            rt: 2,
        }))
    );
}

#[test]
fn decodes_ldr_literal_round_trips() {
    let cases = [(0, 0), (0x12_345, 7), (0x7_ffff, 31)];

    for (imm19, rt) in cases {
        let word = encode_load_literal(0b01, false, imm19, rt);

        assert_eq!(
            decode(word),
            Ok(Instruction::LoadLiteral(LoadLiteral {
                opc: 0b01,
                vector: false,
                imm19,
                rt: rt as u8,
            }))
        );
    }
}

#[test]
fn unsupported_ldr_literal_neighbors_fail_closed() {
    let words = [
        encode_load_literal(0b00, false, 0x123, 4),
        encode_load_literal(0b10, false, 0x123, 4),
        encode_load_literal(0b11, false, 0x123, 4),
        encode_load_literal(0b01, true, 0x123, 4),
    ];

    for word in words {
        assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
    }
}

#[test]
fn decodes_ldrsw_register_round_trip() {
    let word = encoding_mem::encode_ldrsw_register(4, 5, 6).unwrap();

    assert_eq!(
        decode(word),
        Ok(Instruction::LoadStoreRegister(LoadStoreRegister {
            size: 0b10,
            vector: false,
            opc: 0b10,
            rm: 4,
            option: 0b011,
            shift: true,
            rn: 5,
            rt: 6,
        }))
    );
}

#[test]
fn rejects_unallocated_load_store_register_option() {
    let word = (0b11 << 30) | (0b111 << 27) | (1 << 21) | (7 << 16) | (0b10 << 10) | (5 << 5) | 4;

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "load/store register-offset option field is unallocated",
        })
    );
}

#[test]
fn decodes_load_store_pair_round_trip() {
    let word = encoding::encode_load_store_pair(0b10, 0, 1, 0x7c, 20, 29, 19);

    assert_eq!(
        decode(word),
        Ok(Instruction::LoadStorePair(LoadStorePair {
            opc: 0b10,
            vector: false,
            load: true,
            mode: LoadStorePairAddressMode::SignedOffset,
            imm7: 0x7c,
            rt2: 20,
            rn: 29,
            rt: 19,
        }))
    );
}

#[test]
fn decodes_load_store_pair_pre_index_round_trip() {
    let word = encoding_mem::encode_ldp_stp_pre_index(
        encoding_mem::PairSize::X64,
        false,
        encoding_mem::PairOp::StorePair,
        -2,
        30,
        31,
        29,
    )
    .unwrap();

    assert_eq!(
        decode(word),
        Ok(Instruction::LoadStorePair(LoadStorePair {
            opc: 0b10,
            vector: false,
            load: false,
            mode: LoadStorePairAddressMode::PreIndex,
            imm7: 0x7e,
            rt2: 30,
            rn: 31,
            rt: 29,
        }))
    );
}

#[test]
fn decodes_load_store_pair_post_index_round_trip() {
    let word = encoding_mem::encode_ldp_stp_post_index(
        encoding_mem::PairSize::X64,
        false,
        encoding_mem::PairOp::LoadPair,
        2,
        30,
        31,
        29,
    )
    .unwrap();

    assert_eq!(
        decode(word),
        Ok(Instruction::LoadStorePair(LoadStorePair {
            opc: 0b10,
            vector: false,
            load: true,
            mode: LoadStorePairAddressMode::PostIndex,
            imm7: 2,
            rt2: 30,
            rn: 31,
            rt: 29,
        }))
    );
}

/// STGP is refused in every addressing mode.
///
/// The verdict is `Unallocated`, not `Unsupported`: this word is not a family
/// the decoder declines to cover, it is a pair-space row that is NOT STP, and
/// the reason names which one. `validate_load_store_pair` decides it centrally
/// for all three modes, so the rejection no longer depends on an inline check
/// in one arm.
#[test]
fn unsupported_stgp_addressing_modes_fail_closed() {
    let signed_offset = encoding::encode_load_store_pair(0b01, 0, 0, 0x7e, 20, 29, 19);

    for mode in [0b001, 0b010, 0b011] {
        let word = (signed_offset & !(0b111 << 23)) | (mode << 23);
        assert_eq!(
            decode(word),
            Err(DecodeError::Unallocated {
                word,
                reason: "load/store pair opc 0b01 with V=0, L=0 is STGP, not STP",
            }),
            "STGP mode={mode:#05b}"
        );
    }
}

#[test]
fn decodes_ldpsw_and_vector_d_store_pair_neighbors() {
    let ldpsw = encoding::encode_load_store_pair(0b01, 0, 1, 0x7e, 20, 29, 19);
    assert_eq!(
        decode(ldpsw),
        Ok(Instruction::LoadStorePair(LoadStorePair {
            opc: 0b01,
            vector: false,
            load: true,
            mode: LoadStorePairAddressMode::SignedOffset,
            imm7: 0x7e,
            rt2: 20,
            rn: 29,
            rt: 19,
        }))
    );

    let vector_store = encoding::encode_load_store_pair(0b01, 1, 0, 0x7e, 20, 29, 19);
    assert_eq!(
        decode(vector_store),
        Ok(Instruction::LoadStorePair(LoadStorePair {
            opc: 0b01,
            vector: true,
            load: false,
            mode: LoadStorePairAddressMode::SignedOffset,
            imm7: 0x7e,
            rt2: 20,
            rn: 29,
            rt: 19,
        }))
    );
}

#[test]
fn unsupported_load_store_pair_mode_000_fails_closed() {
    let word = (0b10 << 30) | (0b101 << 27) | (1 << 22) | (2 << 15) | (30 << 10) | (31 << 5) | 29;

    assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
}

#[test]
fn decodes_load_store_acquire_release_round_trips() {
    let cases = [
        (encode_load_acquire(0b00, 1, 2), 0b00, true, 1, 2),
        (encode_load_acquire(0b01, 3, 4), 0b01, true, 3, 4),
        (encode_load_acquire(0b10, 5, 6), 0b10, true, 5, 6),
        (encode_load_acquire(0b11, 31, 7), 0b11, true, 31, 7),
        (encode_store_release(0b00, 8, 9), 0b00, false, 8, 9),
        (encode_store_release(0b01, 10, 11), 0b01, false, 10, 11),
        (encode_store_release(0b10, 12, 13), 0b10, false, 12, 13),
        (encode_store_release(0b11, 30, 14), 0b11, false, 30, 14),
    ];

    for (word, size, load, rn, rt) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::LoadStoreAcquireRelease(
                LoadStoreAcquireRelease { size, load, rn, rt }
            ))
        );
    }
}

#[test]
fn unsupported_load_store_acquire_release_rs_neighbor_fails_closed() {
    let word = encode_load_acquire(0b11, 1, 0) & !(1 << 16);

    assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
}

#[test]
fn unsupported_load_store_acquire_release_rt2_neighbor_fails_closed() {
    let word = encode_store_release(0b10, 2, 1) & !(1 << 10);

    assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
}

#[test]
fn decodes_load_store_exclusive_acquire_release_round_trips() {
    let cases = [
        (
            encode_load_acquire_exclusive(0b10, 5, 4),
            0b10,
            true,
            0b11111,
            5,
            4,
        ),
        (
            encode_load_acquire_exclusive(0b11, 6, 7),
            0b11,
            true,
            0b11111,
            6,
            7,
        ),
        (
            encode_store_release_exclusive(0b10, 9, 10, 11),
            0b10,
            false,
            9,
            10,
            11,
        ),
        (
            encode_store_release_exclusive(0b11, 12, 31, 13),
            0b11,
            false,
            12,
            31,
            13,
        ),
    ];

    for (word, size, load, rs, rn, rt) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::LoadStoreExclusiveAcquireRelease(
                LoadStoreExclusiveAcquireRelease {
                    size,
                    load,
                    rs,
                    rn,
                    rt,
                }
            ))
        );
    }
}

#[test]
fn unsupported_load_store_exclusive_without_ordering_neighbors_fail_closed() {
    let words = [
        encode_load_acquire_exclusive(0b11, 5, 4) & !(1 << 15),
        encode_store_release_exclusive(0b10, 3, 2, 1) & !(1 << 15),
    ];

    for word in words {
        assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
    }
}

#[test]
fn unsupported_load_store_exclusive_byte_half_neighbors_fail_closed() {
    let words = [
        encode_load_acquire_exclusive(0b00, 1, 2),
        encode_load_acquire_exclusive(0b01, 3, 4),
        encode_store_release_exclusive(0b00, 5, 6, 7),
        encode_store_release_exclusive(0b01, 8, 9, 10),
    ];

    for word in words {
        assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
    }
}

#[test]
fn decodes_compare_and_swap_round_trips() {
    let cases = [
        (
            encode_cas(0b10, false, false, 1, 2, 3),
            0b10,
            false,
            false,
            1,
            2,
            3,
        ),
        (
            encode_cas(0b11, false, false, 4, 5, 6),
            0b11,
            false,
            false,
            4,
            5,
            6,
        ),
        (
            encode_cas(0b10, true, false, 7, 8, 9),
            0b10,
            true,
            false,
            7,
            8,
            9,
        ),
        (
            encode_cas(0b11, true, false, 10, 11, 12),
            0b11,
            true,
            false,
            10,
            11,
            12,
        ),
        (
            encode_cas(0b10, true, true, 13, 14, 15),
            0b10,
            true,
            true,
            13,
            14,
            15,
        ),
        (
            encode_cas(0b11, true, true, 16, 17, 18),
            0b11,
            true,
            true,
            16,
            17,
            18,
        ),
        // A=0, R=1 is the release-only CASL (caslb/caslh/casl by size): the
        // emit side (isel/encode) now produces it for a release-only
        // compare-exchange, so lift must read it back symmetrically as
        // acquire: false, release: true. casl x2, x0, [x1] = 0xC8A2FC20
        // (llvm-objdump ground truth).
        (
            encode_cas(0b11, false, true, 2, 1, 0),
            0b11,
            false,
            true,
            2,
            1,
            0,
        ),
        (
            encode_cas(0b10, false, true, 19, 20, 21),
            0b10,
            false,
            true,
            19,
            20,
            21,
        ),
        (
            encode_cas(0b00, false, true, 22, 23, 24),
            0b00,
            false,
            true,
            22,
            23,
            24,
        ),
        (
            encode_cas(0b01, false, true, 25, 26, 27),
            0b01,
            false,
            true,
            25,
            26,
            27,
        ),
    ];

    for (word, size, acquire, release, rs, rn, rt) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::CompareAndSwap(CompareAndSwap {
                size,
                acquire,
                release,
                rs,
                rn,
                rt,
            }))
        );
    }

    // Byte-exact pin of the release-only X form against the assembler:
    // `casl x2, x0, [x1]` == 0xC8A2FC20 (clang/llvm-objdump ground truth).
    assert_eq!(encode_cas(0b11, false, true, 2, 1, 0), 0xC8A2_FC20);
}

#[test]
fn compare_and_swap_release_only_decodes_exactly() {
    // Was `unsupported_..._fails_closed`: the release-only CASL (A=0, R=1)
    // used to be refused because the emit side never produced it. The isel
    // now selects CASL for a release-only compare-exchange, so lift decodes
    // it — decode/emit symmetric, ordering bits verbatim.
    let word = encode_cas(0b11, false, true, 1, 2, 3);

    assert_eq!(
        decode(word),
        Ok(Instruction::CompareAndSwap(CompareAndSwap {
            size: 0b11,
            acquire: false,
            release: true,
            rs: 1,
            rn: 2,
            rt: 3,
        }))
    );
}

#[test]
fn compare_and_swap_byte_half_decode_exactly() {
    // Was `unsupported_..._fail_closed`: byte/half CAS (CASB/CASH families,
    // size 00/01) used to be refused. The emit side produces them for i8/i16
    // compare-exchange (the access-size immediate on Cas/Casa/Casal/Casl),
    // so lift decodes all four sizes — CASP is o2=0 space, no collision.
    let cases = [
        (
            encode_cas(0b00, false, false, 1, 2, 3),
            0b00,
            false,
            false,
            1,
            2,
            3,
        ),
        (
            encode_cas(0b01, true, true, 4, 5, 6),
            0b01,
            true,
            true,
            4,
            5,
            6,
        ),
        (
            encode_cas(0b00, false, true, 7, 8, 9),
            0b00,
            false,
            true,
            7,
            8,
            9,
        ),
        (
            encode_cas(0b01, false, true, 10, 11, 12),
            0b01,
            false,
            true,
            10,
            11,
            12,
        ),
    ];

    for (word, size, acquire, release, rs, rn, rt) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::CompareAndSwap(CompareAndSwap {
                size,
                acquire,
                release,
                rs,
                rn,
                rt,
            }))
        );
    }
}

#[test]
fn unsupported_compare_and_swap_rt2_neighbor_fails_closed() {
    let word = encode_cas(0b11, true, true, 1, 2, 3) & !(1 << 10);

    assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
}

#[test]
fn decodes_lse_ldadd_round_trips() {
    let cases = [
        (
            encode_lse_rmw(0b10, false, false, 1, false, 0b000, 2, 3),
            0b10,
            false,
            false,
            1,
            2,
            3,
        ),
        (
            encode_lse_rmw(0b11, false, false, 4, false, 0b000, 5, 6),
            0b11,
            false,
            false,
            4,
            5,
            6,
        ),
        (
            encode_lse_rmw(0b10, true, false, 7, false, 0b000, 8, 9),
            0b10,
            true,
            false,
            7,
            8,
            9,
        ),
        (
            encode_lse_rmw(0b11, true, false, 10, false, 0b000, 11, 12),
            0b11,
            true,
            false,
            10,
            11,
            12,
        ),
        (
            encode_lse_rmw(0b10, true, true, 13, false, 0b000, 14, 15),
            0b10,
            true,
            true,
            13,
            14,
            15,
        ),
        (
            encode_lse_rmw(0b11, true, true, 16, false, 0b000, 17, 18),
            0b11,
            true,
            true,
            16,
            17,
            18,
        ),
    ];

    for (word, size, acquire, release, rs, rn, rt) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::LseAtomicRmw(LseAtomicRmw {
                size,
                acquire,
                release,
                op: LseAtomicRmwOp::Add,
                rs,
                rn,
                rt,
            }))
        );
    }
}

#[test]
fn decodes_lse_ldclr_round_trips() {
    let cases = [
        (
            encode_lse_rmw(0b10, false, false, 1, false, 0b001, 2, 3),
            0b10,
            false,
            false,
            1,
            2,
            3,
        ),
        (
            encode_lse_rmw(0b11, false, false, 4, false, 0b001, 5, 6),
            0b11,
            false,
            false,
            4,
            5,
            6,
        ),
        (
            encode_lse_rmw(0b10, true, true, 7, false, 0b001, 8, 9),
            0b10,
            true,
            true,
            7,
            8,
            9,
        ),
        (
            encode_lse_rmw(0b11, true, true, 10, false, 0b001, 11, 12),
            0b11,
            true,
            true,
            10,
            11,
            12,
        ),
    ];

    for (word, size, acquire, release, rs, rn, rt) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::LseAtomicRmw(LseAtomicRmw {
                size,
                acquire,
                release,
                op: LseAtomicRmwOp::Clr,
                rs,
                rn,
                rt,
            }))
        );
    }
}

#[test]
fn decodes_lse_ldeor_round_trips() {
    let cases = [
        (
            encode_lse_rmw(0b10, false, false, 1, false, 0b010, 2, 3),
            0b10,
            false,
            false,
            1,
            2,
            3,
        ),
        (
            encode_lse_rmw(0b11, false, false, 4, false, 0b010, 5, 6),
            0b11,
            false,
            false,
            4,
            5,
            6,
        ),
        (
            encode_lse_rmw(0b10, true, true, 7, false, 0b010, 8, 9),
            0b10,
            true,
            true,
            7,
            8,
            9,
        ),
        (
            encode_lse_rmw(0b11, true, true, 10, false, 0b010, 11, 12),
            0b11,
            true,
            true,
            10,
            11,
            12,
        ),
    ];

    for (word, size, acquire, release, rs, rn, rt) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::LseAtomicRmw(LseAtomicRmw {
                size,
                acquire,
                release,
                op: LseAtomicRmwOp::Eor,
                rs,
                rn,
                rt,
            }))
        );
    }
}

#[test]
fn decodes_lse_ldset_round_trips() {
    let cases = [
        (
            encode_lse_rmw(0b10, false, false, 1, false, 0b011, 2, 3),
            0b10,
            false,
            false,
            1,
            2,
            3,
        ),
        (
            encode_lse_rmw(0b11, false, false, 4, false, 0b011, 5, 6),
            0b11,
            false,
            false,
            4,
            5,
            6,
        ),
        (
            encode_lse_rmw(0b10, true, true, 7, false, 0b011, 8, 9),
            0b10,
            true,
            true,
            7,
            8,
            9,
        ),
        (
            encode_lse_rmw(0b11, true, true, 10, false, 0b011, 11, 12),
            0b11,
            true,
            true,
            10,
            11,
            12,
        ),
    ];

    for (word, size, acquire, release, rs, rn, rt) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::LseAtomicRmw(LseAtomicRmw {
                size,
                acquire,
                release,
                op: LseAtomicRmwOp::Set,
                rs,
                rn,
                rt,
            }))
        );
    }
}

#[test]
fn decodes_lse_swp_round_trips() {
    let cases = [
        (
            encode_lse_rmw(0b10, false, false, 1, true, 0b000, 2, 3),
            0b10,
            false,
            false,
            1,
            2,
            3,
        ),
        (
            encode_lse_rmw(0b11, false, false, 4, true, 0b000, 5, 6),
            0b11,
            false,
            false,
            4,
            5,
            6,
        ),
        (
            encode_lse_rmw(0b10, true, true, 7, true, 0b000, 8, 9),
            0b10,
            true,
            true,
            7,
            8,
            9,
        ),
        (
            encode_lse_rmw(0b11, true, true, 10, true, 0b000, 11, 12),
            0b11,
            true,
            true,
            10,
            11,
            12,
        ),
    ];

    for (word, size, acquire, release, rs, rn, rt) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::LseAtomicRmw(LseAtomicRmw {
                size,
                acquire,
                release,
                op: LseAtomicRmwOp::Swp,
                rs,
                rn,
                rt,
            }))
        );
    }
}

#[test]
fn decodes_lse_ldsmax_round_trips() {
    // opc=0b100, o3=0. Plain (A=0,R=0) and AL (A=1,R=1); the L (A=0,R=1) form
    // is exercised by decodes_lse_rmw_release_only_round_trips. The isel emits
    // Ldsmax/Ldsmaxl/Ldsmaxal for AtomicRmwOp::Max, so lift reads all three.
    let cases = [
        (
            encode_lse_rmw(0b10, false, false, 1, false, 0b100, 2, 3),
            0b10,
            false,
            false,
            1,
            2,
            3,
        ),
        (
            encode_lse_rmw(0b11, false, false, 4, false, 0b100, 5, 6),
            0b11,
            false,
            false,
            4,
            5,
            6,
        ),
        (
            encode_lse_rmw(0b10, true, true, 7, false, 0b100, 8, 9),
            0b10,
            true,
            true,
            7,
            8,
            9,
        ),
        (
            encode_lse_rmw(0b11, true, true, 10, false, 0b100, 11, 12),
            0b11,
            true,
            true,
            10,
            11,
            12,
        ),
    ];

    for (word, size, acquire, release, rs, rn, rt) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::LseAtomicRmw(LseAtomicRmw {
                size,
                acquire,
                release,
                op: LseAtomicRmwOp::Smax,
                rs,
                rn,
                rt,
            }))
        );
    }
}

#[test]
fn decodes_lse_ldsmin_round_trips() {
    // opc=0b101, o3=0 -> AtomicRmwOp::Min (Ldsmin/Ldsminl/Ldsminal).
    let cases = [
        (
            encode_lse_rmw(0b10, false, false, 1, false, 0b101, 2, 3),
            0b10,
            false,
            false,
            1,
            2,
            3,
        ),
        (
            encode_lse_rmw(0b11, false, false, 4, false, 0b101, 5, 6),
            0b11,
            false,
            false,
            4,
            5,
            6,
        ),
        (
            encode_lse_rmw(0b10, true, true, 7, false, 0b101, 8, 9),
            0b10,
            true,
            true,
            7,
            8,
            9,
        ),
        (
            encode_lse_rmw(0b11, true, true, 10, false, 0b101, 11, 12),
            0b11,
            true,
            true,
            10,
            11,
            12,
        ),
    ];

    for (word, size, acquire, release, rs, rn, rt) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::LseAtomicRmw(LseAtomicRmw {
                size,
                acquire,
                release,
                op: LseAtomicRmwOp::Smin,
                rs,
                rn,
                rt,
            }))
        );
    }
}

#[test]
fn decodes_lse_ldumax_round_trips() {
    // opc=0b110, o3=0 -> AtomicRmwOp::UMax (Ldumax/Ldumaxl/Ldumaxal).
    let cases = [
        (
            encode_lse_rmw(0b10, false, false, 1, false, 0b110, 2, 3),
            0b10,
            false,
            false,
            1,
            2,
            3,
        ),
        (
            encode_lse_rmw(0b11, false, false, 4, false, 0b110, 5, 6),
            0b11,
            false,
            false,
            4,
            5,
            6,
        ),
        (
            encode_lse_rmw(0b10, true, true, 7, false, 0b110, 8, 9),
            0b10,
            true,
            true,
            7,
            8,
            9,
        ),
        (
            encode_lse_rmw(0b11, true, true, 10, false, 0b110, 11, 12),
            0b11,
            true,
            true,
            10,
            11,
            12,
        ),
    ];

    for (word, size, acquire, release, rs, rn, rt) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::LseAtomicRmw(LseAtomicRmw {
                size,
                acquire,
                release,
                op: LseAtomicRmwOp::Umax,
                rs,
                rn,
                rt,
            }))
        );
    }
}

#[test]
fn decodes_lse_ldumin_round_trips() {
    // opc=0b111, o3=0 -> AtomicRmwOp::UMin (Ldumin/Lduminl/Lduminal).
    let cases = [
        (
            encode_lse_rmw(0b10, false, false, 1, false, 0b111, 2, 3),
            0b10,
            false,
            false,
            1,
            2,
            3,
        ),
        (
            encode_lse_rmw(0b11, false, false, 4, false, 0b111, 5, 6),
            0b11,
            false,
            false,
            4,
            5,
            6,
        ),
        (
            encode_lse_rmw(0b10, true, true, 7, false, 0b111, 8, 9),
            0b10,
            true,
            true,
            7,
            8,
            9,
        ),
        (
            encode_lse_rmw(0b11, true, true, 10, false, 0b111, 11, 12),
            0b11,
            true,
            true,
            10,
            11,
            12,
        ),
    ];

    for (word, size, acquire, release, rs, rn, rt) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::LseAtomicRmw(LseAtomicRmw {
                size,
                acquire,
                release,
                op: LseAtomicRmwOp::Umin,
                rs,
                rn,
                rt,
            }))
        );
    }
}

#[test]
fn decodes_lse_rmw_release_only_round_trips() {
    // A=0, R=1 is the L-suffixed (release-only) ordering: ldaddl / ldclrl /
    // ldeorl / ldsetl / swpl / ldsmaxl / ldsminl / ldumaxl / lduminl. The emit
    // side (isel/encode, commit e29c011) produces these for
    // AtomicRmw { ordering: Release }, so lift must read them back
    // symmetrically as acquire: false, release: true.
    let cases = [
        (
            encode_lse_rmw(0b10, false, true, 1, false, 0b000, 2, 3),
            0b10,
            LseAtomicRmwOp::Add,
            1,
            2,
            3,
        ),
        (
            encode_lse_rmw(0b11, false, true, 4, false, 0b000, 5, 6),
            0b11,
            LseAtomicRmwOp::Add,
            4,
            5,
            6,
        ),
        (
            encode_lse_rmw(0b11, false, true, 7, false, 0b001, 8, 9),
            0b11,
            LseAtomicRmwOp::Clr,
            7,
            8,
            9,
        ),
        (
            encode_lse_rmw(0b11, false, true, 10, false, 0b010, 11, 12),
            0b11,
            LseAtomicRmwOp::Eor,
            10,
            11,
            12,
        ),
        (
            encode_lse_rmw(0b11, false, true, 13, false, 0b011, 14, 15),
            0b11,
            LseAtomicRmwOp::Set,
            13,
            14,
            15,
        ),
        (
            encode_lse_rmw(0b11, false, true, 16, true, 0b000, 17, 18),
            0b11,
            LseAtomicRmwOp::Swp,
            16,
            17,
            18,
        ),
        (
            encode_lse_rmw(0b11, false, true, 19, false, 0b100, 20, 21),
            0b11,
            LseAtomicRmwOp::Smax,
            19,
            20,
            21,
        ),
        (
            encode_lse_rmw(0b11, false, true, 22, false, 0b101, 23, 24),
            0b11,
            LseAtomicRmwOp::Smin,
            22,
            23,
            24,
        ),
        (
            encode_lse_rmw(0b11, false, true, 25, false, 0b110, 26, 27),
            0b11,
            LseAtomicRmwOp::Umax,
            25,
            26,
            27,
        ),
        (
            encode_lse_rmw(0b11, false, true, 28, false, 0b111, 29, 30),
            0b11,
            LseAtomicRmwOp::Umin,
            28,
            29,
            30,
        ),
    ];

    for (word, size, op, rs, rn, rt) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::LseAtomicRmw(LseAtomicRmw {
                size,
                acquire: false,
                release: true,
                op,
                rs,
                rn,
                rt,
            }))
        );
    }
}

#[test]
fn decodes_lse_rmw_acquire_only_round_trips() {
    // A=1, R=0 is the A-suffixed (load-acquire-only) ordering: ldadda /
    // ldclra / ldeora / ldseta / swpa / ldsmaxa / ldsmina / ldumaxa /
    // ldumina. The emit side (isel/encode) now selects these for
    // AtomicRmw { ordering: Acquire } — the exact requested ordering, no AL
    // strengthening — so lift must read them back symmetrically as
    // acquire: true, release: false. The X-form words are ground-truthed
    // against llvm-objdump (`ldadda x2, x0, [x1]` = 0xF8A20020 ..
    // `swpa x2, x0, [x1]` = 0xF8A28020).
    let cases = [
        (
            encode_lse_rmw(0b10, true, false, 1, false, 0b000, 2, 3),
            0b10,
            LseAtomicRmwOp::Add,
            1,
            2,
            3,
        ),
        (
            encode_lse_rmw(0b11, true, false, 4, false, 0b000, 5, 6),
            0b11,
            LseAtomicRmwOp::Add,
            4,
            5,
            6,
        ),
        (
            encode_lse_rmw(0b11, true, false, 7, false, 0b001, 8, 9),
            0b11,
            LseAtomicRmwOp::Clr,
            7,
            8,
            9,
        ),
        (
            encode_lse_rmw(0b11, true, false, 10, false, 0b010, 11, 12),
            0b11,
            LseAtomicRmwOp::Eor,
            10,
            11,
            12,
        ),
        (
            encode_lse_rmw(0b11, true, false, 13, false, 0b011, 14, 15),
            0b11,
            LseAtomicRmwOp::Set,
            13,
            14,
            15,
        ),
        (
            encode_lse_rmw(0b11, true, false, 16, true, 0b000, 17, 18),
            0b11,
            LseAtomicRmwOp::Swp,
            16,
            17,
            18,
        ),
        (
            encode_lse_rmw(0b11, true, false, 19, false, 0b100, 20, 21),
            0b11,
            LseAtomicRmwOp::Smax,
            19,
            20,
            21,
        ),
        (
            encode_lse_rmw(0b11, true, false, 22, false, 0b101, 23, 24),
            0b11,
            LseAtomicRmwOp::Smin,
            22,
            23,
            24,
        ),
        (
            encode_lse_rmw(0b11, true, false, 25, false, 0b110, 26, 27),
            0b11,
            LseAtomicRmwOp::Umax,
            25,
            26,
            27,
        ),
        (
            encode_lse_rmw(0b11, true, false, 28, false, 0b111, 29, 30),
            0b11,
            LseAtomicRmwOp::Umin,
            28,
            29,
            30,
        ),
    ];

    for (word, size, op, rs, rn, rt) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::LseAtomicRmw(LseAtomicRmw {
                size,
                acquire: true,
                release: false,
                op,
                rs,
                rn,
                rt,
            }))
        );
    }

    // Byte-exact pins of the X forms against the assembler (llvm-objdump):
    // ldadda x2, x0, [x1] = 0xF8A20020; swpa x2, x0, [x1] = 0xF8A28020.
    assert_eq!(
        encode_lse_rmw(0b11, true, false, 2, false, 0b000, 1, 0),
        0xF8A2_0020
    );
    assert_eq!(
        encode_lse_rmw(0b11, true, false, 2, true, 0b000, 1, 0),
        0xF8A2_8020
    );
}

#[test]
fn decodes_lse_ldclr_ldeor_ldset_swp_acquire_only_round_trips() {
    // A=1,R=0 is the A-suffixed (acquire-only) ordering: ldclra / ldeora /
    // ldseta / swpa. These are valid ISA encodings, so the ISA-complete
    // disassembler reads them back as acquire: true, release: false — even
    // though our own isel does not emit acquire-only logical/swap forms.
    let cases = [
        (
            encode_lse_rmw(0b11, true, false, 1, false, 0b001, 2, 3),
            0b11,
            LseAtomicRmwOp::Clr,
            1,
            2,
            3,
        ),
        (
            encode_lse_rmw(0b11, true, false, 4, false, 0b010, 5, 6),
            0b11,
            LseAtomicRmwOp::Eor,
            4,
            5,
            6,
        ),
        (
            encode_lse_rmw(0b11, true, false, 7, false, 0b011, 8, 9),
            0b11,
            LseAtomicRmwOp::Set,
            7,
            8,
            9,
        ),
        (
            encode_lse_rmw(0b11, true, false, 10, true, 0b000, 11, 12),
            0b11,
            LseAtomicRmwOp::Swp,
            10,
            11,
            12,
        ),
    ];

    for (word, size, op, rs, rn, rt) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::LseAtomicRmw(LseAtomicRmw {
                size,
                acquire: true,
                release: false,
                op,
                rs,
                rn,
                rt,
            }))
        );
    }
}

#[test]
fn decodes_lse_rmw_byte_half_round_trips() {
    // Was `unsupported_lse_rmw_byte_half_neighbors_fail_closed`: byte/half
    // LSE RMW (size 00/01 — the ..B/..H mnemonic families) used to be
    // refused. All nine ops (Add/Clr/Eor/Set/Smax/Smin/Umax/Umin/Swp) are
    // architecturally allocated at every A/R ordering for byte and half
    // access sizes, and the emit side produces the narrow ldaddab/ldaddah/
    // swpalb/... forms for i8/i16 atomics, so lift decodes the FULL
    // op x ordering matrix at both narrow sizes — mirroring the word/dword
    // round-trips above and the CASB/CASH decode.
    let ops = [
        (false, 0b000, LseAtomicRmwOp::Add),
        (false, 0b001, LseAtomicRmwOp::Clr),
        (false, 0b010, LseAtomicRmwOp::Eor),
        (false, 0b011, LseAtomicRmwOp::Set),
        (false, 0b100, LseAtomicRmwOp::Smax),
        (false, 0b101, LseAtomicRmwOp::Smin),
        (false, 0b110, LseAtomicRmwOp::Umax),
        (false, 0b111, LseAtomicRmwOp::Umin),
        (true, 0b000, LseAtomicRmwOp::Swp),
    ];
    let orderings = [(false, false), (true, false), (false, true), (true, true)];

    // Golden anchor (independent of the encode_lse_rmw helper):
    // ldaddab w2, w0, [x1] = 0x38A20020 (assembler-verified byte encoding).
    assert_eq!(
        encode_lse_rmw(0b00, true, false, 2, false, 0b000, 1, 0),
        0x38A2_0020
    );
    assert_eq!(
        decode(0x38A2_0020),
        Ok(Instruction::LseAtomicRmw(LseAtomicRmw {
            size: 0b00,
            acquire: true,
            release: false,
            op: LseAtomicRmwOp::Add,
            rs: 2,
            rn: 1,
            rt: 0,
        }))
    );

    for size in [0b00u32, 0b01] {
        for (o3, opc, op) in ops {
            for (acquire, release) in orderings {
                let word = encode_lse_rmw(size, acquire, release, 7, o3, opc, 8, 9);
                assert_eq!(
                    decode(word),
                    Ok(Instruction::LseAtomicRmw(LseAtomicRmw {
                        size: size as u8,
                        acquire,
                        release,
                        op,
                        rs: 7,
                        rn: 8,
                        rt: 9,
                    })),
                    "size={size:#04b} o3={o3} opc={opc:#05b} A={acquire} R={release}"
                );
            }
        }
    }
}

#[test]
fn unsupported_lse_rmw_reserved_o3_opcodes_fail_closed() {
    // o3=1 is allocated only for SWP (opc=0b000). With o3=1 all opc != 0b000
    // are reserved and must stay fail-closed at every ordering. (o3=0 now
    // covers the full opc=0b000..=0b111 op set: Add/Clr/Eor/Set/Smax/Smin/
    // Umax/Umin, so there are no reserved o3=0 opcodes left to test here.)
    let words = [
        encode_lse_rmw(0b11, true, true, 4, true, 0b001, 5, 6),
        encode_lse_rmw(0b11, true, true, 7, true, 0b010, 8, 9),
        encode_lse_rmw(0b11, true, true, 10, true, 0b011, 11, 12),
        encode_lse_rmw(0b11, true, true, 13, true, 0b100, 14, 15),
        encode_lse_rmw(0b11, true, true, 16, true, 0b111, 17, 18),
        // Release-only (A=0,R=1) o3=1 non-swp opcodes are equally reserved.
        encode_lse_rmw(0b11, false, true, 19, true, 0b001, 20, 21),
        // Plain (A=0,R=0) o3=1 non-swp opcode.
        encode_lse_rmw(0b11, false, false, 22, true, 0b110, 23, 24),
        // Byte/half (size 00/01) o3=1 non-swp opcodes are reserved too: the
        // narrow-size lift covers only allocated encodings, never these.
        encode_lse_rmw(0b00, true, true, 25, true, 0b011, 26, 27),
        encode_lse_rmw(0b01, false, false, 28, true, 0b101, 29, 30),
    ];

    for word in words {
        assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
    }
}

#[test]
fn decodes_lse_smax_smin_umax_umin_acquire_only_round_trips() {
    // A=1,R=0 (acquire-only) ldsmaxa/ldsmina/ldumaxa/ldumina are valid ISA
    // encodings. The isel never emits them (the emit opcode set has
    // Ldsmax/Ldsmaxl/Ldsmaxal and min/umax/umin analogues but no acquire-only
    // `*a` form), yet an ISA-complete disassembler still reads them back as
    // acquire: true, release: false — exactly as it does for ldclr/ldeor/ldset/
    // swp, and as it already did for the Add op.
    let cases = [
        (
            encode_lse_rmw(0b11, true, false, 1, false, 0b100, 2, 3),
            0b11,
            LseAtomicRmwOp::Smax,
            1,
            2,
            3,
        ),
        (
            encode_lse_rmw(0b11, true, false, 4, false, 0b101, 5, 6),
            0b11,
            LseAtomicRmwOp::Smin,
            4,
            5,
            6,
        ),
        (
            encode_lse_rmw(0b11, true, false, 7, false, 0b110, 8, 9),
            0b11,
            LseAtomicRmwOp::Umax,
            7,
            8,
            9,
        ),
        (
            encode_lse_rmw(0b11, true, false, 10, false, 0b111, 11, 12),
            0b11,
            LseAtomicRmwOp::Umin,
            10,
            11,
            12,
        ),
    ];

    for (word, size, op, rs, rn, rt) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::LseAtomicRmw(LseAtomicRmw {
                size,
                acquire: true,
                release: false,
                op,
                rs,
                rn,
                rt,
            }))
        );
    }
}

#[test]
fn decodes_compare_branch_round_trip() {
    let word = encoding::encode_cmp_branch(1, 1, 0x7_fffe, 4);

    assert_eq!(
        decode(word),
        Ok(Instruction::CompareBranch(CompareBranch {
            sf: 1,
            nonzero: true,
            imm19: 0x7_fffe,
            rt: 4,
        }))
    );
}

#[test]
fn decodes_test_branch_round_trips() {
    let cases = [
        (encode_test_branch(false, 3, 2, 0), false, 3, 2, 0),
        (encode_test_branch(true, 3, 2, 0), true, 3, 2, 0),
        (encode_test_branch(false, 32, 5, 0), false, 32, 5, 0),
        (encode_test_branch(true, 63, 10, 1), true, 63, 10, 1),
    ];

    for (word, nonzero, bit, imm14, rt) in cases {
        assert_eq!(
            decode(word),
            Ok(Instruction::TestBranch(TestBranch {
                nonzero,
                bit,
                imm14,
                rt,
            }))
        );
    }
}

#[test]
fn test_branch_known_encodings_round_trip() {
    assert_eq!(encode_test_branch(false, 0, 0, 0), 0x3600_0000);
    assert_eq!(encode_test_branch(true, 0, 0, 0), 0x3700_0000);

    assert_eq!(
        decode(0x3600_0000),
        Ok(Instruction::TestBranch(TestBranch {
            nonzero: false,
            bit: 0,
            imm14: 0,
            rt: 0,
        }))
    );
    assert_eq!(
        decode(0x3700_0000),
        Ok(Instruction::TestBranch(TestBranch {
            nonzero: true,
            bit: 0,
            imm14: 0,
            rt: 0,
        }))
    );
}

#[test]
fn decodes_data_processing_2_source_div_round_trips() {
    let cases = [(1, 0b000010, 2, 1, 0), (0, 0b000011, 5, 4, 3)];

    for (sf, opcode, rm, rn, rd) in cases {
        let word = encode_data_processing_2_source(sf, opcode, rm, rn, rd);

        assert_eq!(
            decode(word),
            Ok(Instruction::DataProcessing2Source(DataProcessing2Source {
                sf: sf as u8,
                opcode: opcode as u8,
                rm: rm as u8,
                rn: rn as u8,
                rd: rd as u8,
            }))
        );
    }
}

#[test]
fn decodes_data_processing_2_source_shift_round_trips() {
    let cases = [
        (1, 0b001000, 9, 8, 7),
        (0, 0b001001, 12, 11, 10),
        (1, 0b001010, 15, 14, 13),
    ];

    for (sf, opcode, rm, rn, rd) in cases {
        let word = encode_data_processing_2_source(sf, opcode, rm, rn, rd);

        assert_eq!(
            decode(word),
            Ok(Instruction::DataProcessing2Source(DataProcessing2Source {
                sf: sf as u8,
                opcode: opcode as u8,
                rm: rm as u8,
                rn: rn as u8,
                rd: rd as u8,
            }))
        );
    }
}

#[test]
fn unsupported_data_processing_2_source_opcode_fails_closed() {
    let word = encode_data_processing_2_source(1, 0b001011, 2, 1, 0);

    assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
}

#[test]
fn decodes_data_processing_3_source_madd_msub_round_trips() {
    let cases = [
        (1, 0b000, false, 2, 3, 1, 0),
        (0, 0b000, false, 5, 31, 4, 3),
        (1, 0b000, true, 8, 9, 7, 6),
    ];

    for (sf, op31, o0, rm, ra, rn, rd) in cases {
        let word = encode_data_processing_3_source(sf, op31, o0, rm, ra, rn, rd);

        assert_eq!(
            decode(word),
            Ok(Instruction::DataProcessing3Source(DataProcessing3Source {
                sf: sf as u8,
                op31: op31 as u8,
                o0,
                rm: rm as u8,
                ra: ra as u8,
                rn: rn as u8,
                rd: rd as u8,
            }))
        );
    }
}

#[test]
fn decodes_data_processing_3_source_long_and_high_multiply_round_trips() {
    let cases = [
        (0b001, 2, 1, 0),
        (0b101, 5, 4, 3),
        (0b010, 8, 7, 6),
        (0b110, 11, 10, 9),
    ];

    for (op31, rm, rn, rd) in cases {
        let word = encode_data_processing_3_source(1, op31, false, rm, 31, rn, rd);

        assert_eq!(
            decode(word),
            Ok(Instruction::DataProcessing3Source(DataProcessing3Source {
                sf: 1,
                op31: op31 as u8,
                o0: false,
                rm: rm as u8,
                ra: 31,
                rn: rn as u8,
                rd: rd as u8,
            }))
        );
    }
}

#[test]
fn rejects_unallocated_data_processing_3_source_high_multiply_sf0() {
    let word = encode_data_processing_3_source(0, 0b010, false, 2, 31, 1, 0);

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "data-processing 3-source high multiply requires sf=1",
        })
    );
}

#[test]
fn rejects_unallocated_data_processing_3_source_high_multiply_ra() {
    let word = encode_data_processing_3_source(1, 0b110, false, 2, 30, 1, 0);

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "data-processing 3-source high multiply requires o0=0 and ra=31",
        })
    );
}

#[test]
fn unsupported_data_processing_3_source_opcode_fails_closed() {
    let word = encode_data_processing_3_source(1, 0b011, false, 2, 31, 1, 0);

    assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
}

#[test]
fn decodes_conditional_select_round_trips() {
    let cases = [
        (1, false, false, 2, 0, 1, 0),
        (0, false, true, 5, 1, 4, 3),
        (1, true, false, 8, 11, 7, 6),
        (0, true, true, 12, 10, 11, 9),
    ];

    for (sf, op, o2, rm, cond, rn, rd) in cases {
        let word = encode_conditional_select(sf, op, o2, rm, cond, rn, rd);

        assert_eq!(
            decode(word),
            Ok(Instruction::ConditionalSelect(ConditionalSelect {
                sf: sf as u8,
                op,
                o2,
                rm: rm as u8,
                cond: cond as u8,
                rn: rn as u8,
                rd: rd as u8,
            }))
        );
    }
}

#[test]
fn decodes_cset_alias_shape_as_conditional_select() {
    let word = encode_conditional_select(1, false, true, 31, 1, 31, 13);

    assert_eq!(
        decode(word),
        Ok(Instruction::ConditionalSelect(ConditionalSelect {
            sf: 1,
            op: false,
            o2: true,
            rm: 31,
            cond: 1,
            rn: 31,
            rd: 13,
        }))
    );
}

#[test]
fn rejects_unallocated_conditional_select_s_bit() {
    let word = encode_conditional_select(1, false, false, 2, 0, 1, 0) | (1 << 29);

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "conditional select S bit must be zero",
        })
    );
}

#[test]
fn rejects_unallocated_conditional_select_bit11() {
    let word = encode_conditional_select(1, true, false, 2, 0, 1, 0) | (1 << 11);

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "conditional select bit 11 must be zero",
        })
    );
}

#[test]
fn decodes_fp_arith_round_trip() {
    let word = encoding_fp::encode_fp_arith(
        encoding_fp::FpSize::Double,
        encoding_fp::FpArithOp::Div,
        2,
        1,
        0,
    )
    .unwrap();

    assert_eq!(
        decode(word),
        Ok(Instruction::FpArith(FpArith {
            ftype: 0b01,
            opcode: 0b0001,
            rm: 2,
            rn: 1,
            rd: 0,
        }))
    );
}

#[test]
fn decodes_fp_compare_zero_round_trip() {
    let word = encoding_fp::encode_fcmp(
        encoding_fp::FpSize::Double,
        encoding_fp::FpCmpOp::CmpZero,
        31,
        4,
    )
    .unwrap();

    assert_eq!(
        decode(word),
        Ok(Instruction::FpCompare(FpCompare {
            ftype: 0b01,
            rm: 0,
            rn: 4,
            opc: 0b01000,
        }))
    );
}

#[test]
fn decodes_fp_int_conversion_round_trip() {
    let word = encoding_fp::encode_fp_int_conv(
        true,
        encoding_fp::FpSize::Single,
        encoding_fp::FpConvOp::FcvtzsToInt,
        3,
        2,
    )
    .unwrap();

    assert_eq!(
        decode(word),
        Ok(Instruction::FpIntConversion(FpIntConversion {
            sf64: true,
            ftype: 0b00,
            rmode: 0b11,
            opcode: 0b000,
            rn: 3,
            rd: 2,
        }))
    );
}

#[test]
fn decodes_fp_unary_round_trip() {
    let word = encoding_fp::encode_fp_unary(
        encoding_fp::FpSize::Single,
        encoding_fp::FpUnaryOp::Fneg,
        6,
        5,
    )
    .unwrap();

    assert_eq!(
        decode(word),
        Ok(Instruction::FpUnary(FpUnary {
            ftype: 0b00,
            opcode: 0b10,
            rn: 6,
            rd: 5,
        }))
    );
}

#[test]
fn decodes_fp_precision_convert_round_trip() {
    let word = encoding_fp::encode_fp_precision_cvt(
        encoding_fp::FpSize::Single,
        encoding_fp::FpSize::Double,
        8,
        9,
    )
    .unwrap();

    assert_eq!(
        decode(word),
        Ok(Instruction::FpPrecisionConvert(FpPrecisionConvert {
            src_ftype: 0b00,
            dst_ftype: 0b01,
            rn: 8,
            rd: 9,
        }))
    );
}

#[test]
fn decodes_fmov_immediate_round_trips() {
    let cases = [
        (0b00, 0x00, 0),
        (0b01, 0x70, 5),
        (0b01, 0xf0, 31),
        (0b11, 0x78, 9),
    ];

    for (ftype, imm8, rd) in cases {
        let word = encode_fmov_immediate(ftype, imm8, rd);

        assert_eq!(
            decode(word),
            Ok(Instruction::FpImmediate(FpImmediate {
                ftype: ftype as u8,
                imm8: imm8 as u8,
                rd: rd as u8,
            }))
        );
    }
}

#[test]
fn rejects_unallocated_fp_ftype() {
    let word = (0b11110 << 24) | (0b10 << 22) | (1 << 21) | (0b0010 << 12) | (0b10 << 10);

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "scalar FP ftype field 0b10 is unallocated",
        })
    );
}

#[test]
fn rejects_fp_compare_zero_with_nonzero_rm() {
    let word = encoding_fp::encode_fcmp(
        encoding_fp::FpSize::Single,
        encoding_fp::FpCmpOp::CmpeZero,
        0,
        1,
    )
    .unwrap()
        | (7 << 16);

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "FP compare zero form requires rm == 0",
        })
    );
}

#[test]
fn unsupported_fp_arith_opcode_fails_closed() {
    let word = (0b11110 << 24) | (1 << 21) | (0b0100 << 12) | (0b10 << 10);

    assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
}

#[test]
fn rejects_unallocated_fmov_immediate_sf_bit() {
    let word = encode_fmov_immediate(0b01, 0x70, 0) | (1 << 31);

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "FP immediate bit 31 must be zero",
        })
    );
}

#[test]
fn rejects_unallocated_fmov_immediate_fixed_zero_field() {
    let word = encode_fmov_immediate(0b01, 0x70, 0) | (7 << 5);

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "FP immediate bits 9:5 must be zero",
        })
    );
}

#[test]
fn unsupported_fmov_immediate_neighbor_fails_closed() {
    let word = encode_fmov_immediate(0b01, 0x70, 0) | (1 << 10);

    assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
}

#[test]
fn decodes_system_barriers_round_trip() {
    let cases = [
        (0b100, SystemBarrierKind::Dsb, 0xf),
        (0b101, SystemBarrierKind::Dmb, 0xb),
        (0b110, SystemBarrierKind::Isb, 0x0),
    ];

    for (op2, kind, crm) in cases {
        let word = encode_system_barrier(op2, crm);

        assert_eq!(
            decode(word),
            Ok(Instruction::SystemBarrier(SystemBarrier {
                kind,
                crm: crm as u8,
            }))
        );
    }
}

#[test]
fn decodes_system_register_read_round_trip() {
    let cases = [(0xde82, 0), (0xda20, 7), (0xffff, 31)];

    for (sysreg, rt) in cases {
        let word = encode_mrs(sysreg, rt);

        assert_eq!(
            decode(word),
            Ok(Instruction::SystemRegisterRead(SystemRegisterRead {
                sysreg: sysreg as u16,
                rt: rt as u8,
            }))
        );
    }
}

#[test]
fn decodes_system_pseudo_words_round_trip() {
    let cases = [
        (encode_nop(), Instruction::Nop),
        (encode_brk(1), Instruction::Brk(Brk { imm16: 1 })),
    ];

    for (word, expected) in cases {
        assert_eq!(decode(word), Ok(expected));
    }
}

#[test]
fn unsupported_system_hint_neighbor_fails_closed() {
    let word = 0xd503_203f;

    assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
}

#[test]
fn unsupported_system_brk_immediate_neighbors_fail_closed() {
    for word in [encode_brk(0), encode_brk(2)] {
        assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
    }
}

#[test]
fn unsupported_system_barrier_op2_fails_closed() {
    let word = encode_system_barrier(0b111, 0xf);

    assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
}

#[test]
fn unsupported_system_register_write_neighbor_fails_closed() {
    let word = encode_mrs(0xde82, 0) & !(1 << 21);

    assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
}

#[test]
fn decodes_neon_int_vec3_same_round_trips() {
    let cases = [
        (
            encoding_neon::VectorArrangement::S4,
            encoding_neon::IntVec3Op::Add,
            true,
            false,
            0b10,
            0b10000,
        ),
        (
            encoding_neon::VectorArrangement::H8,
            encoding_neon::IntVec3Op::Sub,
            true,
            true,
            0b01,
            0b10000,
        ),
        (
            encoding_neon::VectorArrangement::B16,
            encoding_neon::IntVec3Op::Mul,
            true,
            false,
            0b00,
            0b10011,
        ),
        (
            encoding_neon::VectorArrangement::S2,
            encoding_neon::IntVec3Op::Cmeq,
            false,
            true,
            0b10,
            0b10001,
        ),
        (
            encoding_neon::VectorArrangement::H4,
            encoding_neon::IntVec3Op::Cmgt,
            false,
            false,
            0b01,
            0b00110,
        ),
        (
            encoding_neon::VectorArrangement::D2,
            encoding_neon::IntVec3Op::Cmge,
            true,
            false,
            0b11,
            0b00111,
        ),
    ];

    for (arr, op, q, u, size, opcode) in cases {
        let word = encoding_neon::encode_int_vec3_same(arr, op, 2, 1, 0).unwrap();

        assert_eq!(
            decode(word),
            Ok(Instruction::NeonIntVec3Same(NeonIntVec3Same {
                q,
                u,
                size,
                opcode,
                rm: 2,
                rn: 1,
                rd: 0,
            }))
        );
    }
}

#[test]
fn decodes_neon_vec_logic_round_trips() {
    let cases = [
        (0, encoding_neon::VecLogicOp::And, false, 0b00),
        (1, encoding_neon::VecLogicOp::Orr, false, 0b10),
        (0, encoding_neon::VecLogicOp::Eor, true, 0b00),
        (1, encoding_neon::VecLogicOp::Bic, false, 0b01),
    ];

    for (q, op, u, size) in cases {
        let word = encoding_neon::encode_vec_logic(q, op, 4, 3, 2).unwrap();

        assert_eq!(
            decode(word),
            Ok(Instruction::NeonVecLogic(NeonVecLogic {
                q: q != 0,
                u,
                size,
                rm: 4,
                rn: 3,
                rd: 2,
            }))
        );
    }
}

#[test]
fn decodes_neon_fp_vec3_same_round_trips() {
    let cases = [
        (
            encoding_neon::FpVectorArrangement::S2,
            encoding_neon::FpVec3Op::Fadd,
            false,
            false,
            false,
            0,
            0b110101,
        ),
        (
            encoding_neon::FpVectorArrangement::S4,
            encoding_neon::FpVec3Op::Fsub,
            true,
            false,
            true,
            0,
            0b110101,
        ),
        (
            encoding_neon::FpVectorArrangement::D2,
            encoding_neon::FpVec3Op::Fmul,
            true,
            true,
            false,
            1,
            0b110111,
        ),
        (
            encoding_neon::FpVectorArrangement::S4,
            encoding_neon::FpVec3Op::Fdiv,
            true,
            true,
            false,
            0,
            0b111111,
        ),
    ];

    for (arr, op, q, u, bit23, sz, opcode) in cases {
        let word = encoding_neon::encode_fp_vec3_same(arr, op, 7, 6, 5).unwrap();

        assert_eq!(
            decode(word),
            Ok(Instruction::NeonFpVec3Same(NeonFpVec3Same {
                q,
                u,
                bit23,
                sz,
                opcode,
                rm: 7,
                rn: 6,
                rd: 5,
            }))
        );
    }
}

#[test]
fn decodes_neon_vec_not_round_trips() {
    for q in [0, 1] {
        let word = encoding_neon::encode_vec_not(q, 9, 8).unwrap();

        assert_eq!(
            decode(word),
            Ok(Instruction::NeonVecNot(NeonVecNot {
                q: q != 0,
                rn: 9,
                rd: 8,
            }))
        );
    }
}

#[test]
fn decodes_neon_umaxv_4s_round_trip() {
    let word = encoding_neon::encode_umaxv_4s(11, 10).unwrap();

    assert_eq!(
        decode(word),
        Ok(Instruction::NeonAcrossLanes(NeonAcrossLanes {
            q: true,
            u: true,
            size: 0b10,
            opcode: 0b01010,
            rn: 11,
            rd: 10,
        }))
    );
}

#[test]
fn decodes_neon_dup_element_round_trips() {
    let cases = [
        (0, encoding_neon::ElementSize::B, 15, NeonElementSize::B),
        (1, encoding_neon::ElementSize::S, 2, NeonElementSize::S),
        (1, encoding_neon::ElementSize::D, 1, NeonElementSize::D),
    ];

    for (q, elem, lane, element_size) in cases {
        let word = encoding_neon::encode_dup_element(q, elem, lane, 4, 3).unwrap();

        assert_eq!(
            decode(word),
            Ok(Instruction::NeonDupElement(NeonDupElement {
                q: q != 0,
                element_size,
                lane,
                rn: 4,
                rd: 3,
            }))
        );
    }
}

#[test]
fn decodes_neon_dup_general_round_trips() {
    let cases = [
        (0, encoding_neon::ElementSize::B, NeonElementSize::B),
        (1, encoding_neon::ElementSize::S, NeonElementSize::S),
        (1, encoding_neon::ElementSize::D, NeonElementSize::D),
    ];

    for (q, elem, element_size) in cases {
        let word = encoding_neon::encode_dup_general(q, elem, 4, 3).unwrap();

        assert_eq!(
            decode(word),
            Ok(Instruction::NeonDupGeneral(NeonDupGeneral {
                q: q != 0,
                element_size,
                rn: 4,
                rd: 3,
            }))
        );
    }
}

#[test]
fn decodes_neon_ins_general_round_trips() {
    let cases = [
        (encoding_neon::ElementSize::B, 15, NeonElementSize::B, 4, 3),
        (encoding_neon::ElementSize::S, 0, NeonElementSize::S, 2, 1),
        (encoding_neon::ElementSize::S, 2, NeonElementSize::S, 6, 5),
        (encoding_neon::ElementSize::D, 1, NeonElementSize::D, 8, 7),
    ];

    for (elem, lane, element_size, rn, rd) in cases {
        let word = encoding_neon::encode_ins_general(elem, lane, rn, rd).unwrap();

        assert_eq!(
            decode(word),
            Ok(Instruction::NeonInsGeneral(NeonInsGeneral {
                element_size,
                lane,
                rn,
                rd,
            }))
        );
    }
}

#[test]
fn decodes_neon_movi_byte_round_trips() {
    let cases = [(0, 0x42, 5), (1, 0xab, 0)];

    for (q, imm8, rd) in cases {
        let word = encoding_neon::encode_movi_byte(q, imm8, rd).unwrap();

        assert_eq!(
            decode(word),
            Ok(Instruction::NeonMoviByte(NeonMoviByte {
                q: q != 0,
                imm8,
                rd,
            }))
        );
    }
}

#[test]
fn decodes_neon_ld1_st1_post_imm_round_trips() {
    let ld1 =
        encoding_neon::encode_ld1_post_imm(encoding_neon::VectorArrangement::D2, 29, 0).unwrap();
    assert_eq!(
        decode(ld1),
        Ok(Instruction::NeonLdStSinglePostImm(NeonLdStSinglePostImm {
            q: true,
            load: true,
            size: 0b11,
            rn: 29,
            rt: 0,
        },))
    );

    let st1 =
        encoding_neon::encode_st1_post_imm(encoding_neon::VectorArrangement::H4, 5, 6).unwrap();
    assert_eq!(
        decode(st1),
        Ok(Instruction::NeonLdStSinglePostImm(NeonLdStSinglePostImm {
            q: false,
            load: false,
            size: 0b01,
            rn: 5,
            rt: 6,
        },))
    );
}

#[test]
fn rejects_unallocated_neon_vector_arrangement() {
    let word = encoding_neon::encode_int_vec3_same(
        encoding_neon::VectorArrangement::D2,
        encoding_neon::IntVec3Op::Add,
        2,
        1,
        0,
    )
    .unwrap()
        & !(1 << 30);

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "NEON vector q=0 size=0b11 arrangement is unallocated",
        })
    );
}

#[test]
fn rejects_unallocated_neon_fp_vector_arrangement() {
    let word = encoding_neon::encode_fp_vec3_same(
        encoding_neon::FpVectorArrangement::D2,
        encoding_neon::FpVec3Op::Fadd,
        2,
        1,
        0,
    )
    .unwrap()
        & !(1 << 30);

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "NEON FP vector q=0 sz=1 arrangement is unallocated",
        })
    );
}

#[test]
fn unsupported_neon_three_same_opcode_fails_closed() {
    let word = (0b01110 << 24) | (1 << 21) | (1 << 10);

    assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
}

#[test]
fn unsupported_neon_vec_not_size_fails_closed() {
    let word = encoding_neon::encode_vec_not(1, 1, 0).unwrap() | (1 << 22);

    assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
}

#[test]
fn unsupported_neon_umaxv_arrangement_fails_closed() {
    let word = encoding_neon::encode_umaxv_4s(1, 0).unwrap() & !(1 << 30);

    assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
}

#[test]
fn rejects_unallocated_neon_dup_element_zero_imm5() {
    let word = (0b001110000 << 21) | (1 << 10) | (2 << 5) | 1;

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "NEON copy imm5 field must not be zero",
        })
    );
}

#[test]
fn rejects_unallocated_neon_dup_element_d_q0() {
    let word =
        encoding_neon::encode_dup_element(0, encoding_neon::ElementSize::D, 1, 2, 1).unwrap();

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "NEON DUP element D arrangement requires q=1",
        })
    );
}

#[test]
fn unsupported_neon_dup_element_opcode_fails_closed() {
    let word = encoding_neon::encode_dup_element(1, encoding_neon::ElementSize::S, 2, 1, 0)
        .unwrap()
        | (1 << 12);

    assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
}

#[test]
fn rejects_unallocated_neon_dup_general_zero_imm5() {
    let word = (0b001110000 << 21) | (0b0011 << 11) | (1 << 10) | (2 << 5) | 1;

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "NEON copy imm5 field must not be zero",
        })
    );
}

#[test]
fn rejects_unallocated_neon_dup_general_d_q0() {
    let word = encoding_neon::encode_dup_general(0, encoding_neon::ElementSize::D, 2, 1).unwrap();

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "NEON DUP general D arrangement requires q=1",
        })
    );
}

#[test]
fn rejects_unallocated_neon_ins_general_q0() {
    let word = encoding_neon::encode_ins_general(encoding_neon::ElementSize::S, 1, 2, 1).unwrap()
        & !(1 << 30);

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "NEON INS general requires q=1",
        })
    );
}

#[test]
fn unsupported_neon_movi_cmode_fails_closed() {
    let word = encoding_neon::encode_movi_byte(1, 0xab, 0).unwrap() & !(1 << 13);

    assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
}

#[test]
fn unsupported_neon_movi_op_fails_closed() {
    let word = encoding_neon::encode_movi_byte(0, 0x42, 5).unwrap() | (1 << 29);

    assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
}

#[test]
fn rejects_unallocated_neon_ldst_single_post_imm_arrangement() {
    let word = encoding_neon::encode_ld1_post_imm(encoding_neon::VectorArrangement::D2, 1, 0)
        .unwrap()
        & !(1 << 30);

    assert_eq!(
        decode(word),
        Err(DecodeError::Unallocated {
            word,
            reason: "NEON vector q=0 size=0b11 arrangement is unallocated",
        })
    );
}

#[test]
fn unsupported_neon_ldst_single_post_imm_opcode_fails_closed() {
    let word = encoding_neon::encode_ld1_post_imm(encoding_neon::VectorArrangement::S4, 1, 0)
        .unwrap()
        & !(1 << 12);

    assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
}

#[test]
fn unsupported_words_fail_closed() {
    let word = 0xffff_ffff;

    assert_eq!(decode(word), Err(DecodeError::Unsupported { word }));
}

fn bits(word: u32, offset: u8, width: u8) -> u32 {
    (word >> offset) & ((1u32 << width) - 1)
}
