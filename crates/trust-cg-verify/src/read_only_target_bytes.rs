// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Actual final-word semantics for bounded frameless observation profiles.
//!
//! No encoder, source opcode, MachIR operand, relocation hole or recorded CFG
//! supplies an instruction field. Existing independent scalar/value/select
//! decoders supply the semantics. This adapter neither checks a complete CFG
//! nor grants memory, caller, proof, frame or executable-publication authority.
//! The parent must cover every word and check every complete execution path.

use super::{E, Profile, ReadOnlyTargetError, Step, flags, register};
use crate::aarch64_control_decode::{A64ControlWord, decode_a64_control_word};
use crate::aarch64_csel_semantics::{
    DecodedConditionalSelect, SymbolicRegisterState, condition_holds_flags,
};
use crate::aarch64_instruction_word_proofs::{DecodedWord, decode_word, extend_reg_value};
use crate::aarch64_pair_memory_proofs::{PairMode, decode_pair_memory_word};
use crate::aarch64_scalar_memory_proofs::{
    ScalarAddressing, ScalarBank, ScalarExtension, ScalarTransfer, decode_scalar_memory_word,
};
use crate::aarch64_value_decode_proofs::{
    A64Dest, A64ValueWord, FieldOverrides, decode_a64_value_word, denote_a64_value_flags,
    denote_a64_value_word_compact,
};
use crate::smt::SmtSort;

const MAX_WORDS: usize = 256;
const NOP: u32 = 0xd503_201f;

pub(super) fn adapt(code: &[u8]) -> Result<Vec<Step>, ReadOnlyTargetError> {
    adapt_profile(code, Profile::ReadOnly)
}

pub(super) fn adapt_profile(
    code: &[u8],
    profile: Profile,
) -> Result<Vec<Step>, ReadOnlyTargetError> {
    if code.is_empty() || !code.len().is_multiple_of(4) {
        return Err(ReadOnlyTargetError::Bytes("nonempty complete A64 words"));
    }
    let count = code.len() / 4;
    // Before allocation or construction of any semantic expression.
    if count > MAX_WORDS {
        return Err(ReadOnlyTargetError::Budget("final-word count"));
    }
    code.as_chunks::<4>()
        .0
        .iter()
        .enumerate()
        .map(|(index, bytes)| {
            let word = u32::from_le_bytes(*bytes);
            match profile {
                Profile::ReadOnly => adapt_word(word, index, count),
                Profile::ScalarMemory => adapt_word_profile(word, index, count, profile),
            }
        })
        .collect()
}

fn branch_target(
    index: usize,
    displacement: i64,
    count: usize,
) -> Result<usize, ReadOnlyTargetError> {
    // Signed offsets are relative to the branch word's own PC. Working in
    // complete-word units preserves the ISA's low two zero displacement bits.
    let destination = (index as i64)
        .checked_add(displacement)
        .and_then(|target| usize::try_from(target).ok())
        .filter(|target| *target < count)
        .ok_or(ReadOnlyTargetError::Bytes(
            "branch leaves final-word stream",
        ))?;
    Ok(destination)
}

fn destination(index: u32) -> Result<Option<usize>, ReadOnlyTargetError> {
    match index {
        0..=17 => Ok(Some(index as usize)),
        31 => Ok(None),
        _ => Err(ReadOnlyTargetError::Bytes(
            "non-caller-scratch register write",
        )),
    }
}

fn adapt_word(word: u32, index: usize, count: usize) -> Result<Step, ReadOnlyTargetError> {
    adapt_word_profile(word, index, count, Profile::ReadOnly)
}

fn adapt_word_profile(
    word: u32,
    index: usize,
    count: usize,
    profile: Profile,
) -> Result<Step, ReadOnlyTargetError> {
    if word == NOP {
        return Ok(Step::Inert);
    }
    match decode_a64_control_word(word) {
        Some(A64ControlWord::Branch { displacement }) => {
            return Ok(Step::Jump(branch_target(index, displacement, count)?));
        }
        Some(A64ControlWord::ConditionalBranch {
            condition,
            displacement,
        }) => {
            if condition >= 14 {
                return Err(ReadOnlyTargetError::Bytes(
                    "unsupported conditional branch fields",
                ));
            }
            let condition = condition_holds_flags(condition, &flags())
                .map_err(|_| ReadOnlyTargetError::Bytes("invalid branch condition"))?;
            return Ok(Step::Branch {
                condition,
                taken: branch_target(index, displacement, count)?,
            });
        }
        Some(A64ControlWord::CompareBranch {
            register: rt,
            bits: width,
            nonzero,
            displacement,
        }) => {
            let value = if rt == 31 {
                E::bv_const(0, width)
            } else if width == 32 {
                register(usize::from(rt)).extract(31, 0)
            } else {
                register(usize::from(rt))
            };
            let zero = value.eq_expr(E::bv_const(0, width));
            return Ok(Step::Branch {
                condition: if nonzero { zero.not_expr() } else { zero },
                taken: branch_target(index, displacement, count)?,
            });
        }
        Some(A64ControlWord::Return { register: 30 }) => return Ok(Step::Return),
        Some(A64ControlWord::Return { .. }) => {
            return Err(ReadOnlyTargetError::Bytes("unsupported return register"));
        }
        None => {}
    }
    if matches!(profile, Profile::ScalarMemory)
        && let Some(pair) = decode_pair_memory_word(word)
    {
        if !pair.load
            || pair.mode != PairMode::Offset
            || pair.simd
            || !matches!(pair.element_bytes, 4 | 8)
            || pair.rt == pair.rt2
        {
            return Err(ReadOnlyTargetError::Bytes(
                "unsupported scalar pair memory word",
            ));
        }
        memory_register(u32::from(pair.rn), false)?;
        destination(u32::from(pair.rt))?;
        destination(u32::from(pair.rt2))?;
        // Both lane reads use this PRE-instruction base. The parent observes
        // two demands and two full-X writes without inventing another PC.
        return Ok(Step::LoadPair {
            destinations: [usize::from(pair.rt), usize::from(pair.rt2)],
            address: Box::new(crate::memory_proofs::qf_bv_byte_addr(
                &register(usize::from(pair.rn)),
                pair.offset as u64,
            )),
            byte_width: pair.element_bytes,
            alignment: 1,
        });
    }
    match decode_word(word) {
        Some(DecodedWord::BranchImm { .. }) => {
            return Err(ReadOnlyTargetError::Bytes(
                "calls outside frameless profile",
            ));
        }
        Some(DecodedWord::CondBranch { .. }) => {
            return Err(ReadOnlyTargetError::Bytes(
                "unsupported conditional branch fields",
            ));
        }
        Some(
            DecodedWord::LoadStoreUnsigned { .. }
            | DecodedWord::LoadStoreUnscaled { .. }
            | DecodedWord::LoadStoreIndexed { .. }
            | DecodedWord::LoadStoreRegister { .. },
        ) => {
            return match profile {
                Profile::ReadOnly => load(word),
                Profile::ScalarMemory => scalar_memory(word),
            };
        }
        _ => {}
    }

    if let Ok(decoded) = DecodedConditionalSelect::decode(word) {
        let (rd, _, _) = decoded.registers();
        let destination = destination(u32::from(rd))?;
        let before = SymbolicRegisterState::from_parts(
            std::array::from_fn(register),
            // Conditional-select instructions never read or write SP.
            E::bv_const(0, 64),
            // The explicit Bool flag terms below override this packed slot.
            E::bv_const(0, 4),
        )
        .map_err(|_| ReadOnlyTargetError::Bytes("invalid conditional-select state"))?;
        let after = decoded
            .execute_symbolic_with_flag_terms(&before, &flags())
            .map_err(|_| ReadOnlyTargetError::Bytes("invalid conditional-select flag terms"))?;
        let value = destination
            .and_then(|rd| after.register(rd).cloned())
            .unwrap_or_else(|| E::bv_const(0, 64));
        return Ok(Step::Scalar {
            destination,
            value,
            flags: None,
        });
    }

    scalar(word)
}

fn memory_register(index: u32, zero: bool) -> Result<E, ReadOnlyTargetError> {
    match index {
        0..=17 => Ok(register(index as usize)),
        31 if zero => Ok(E::bv_const(0, 64)),
        _ => Err(ReadOnlyTargetError::Bytes(
            "reserved/SP/non-caller scalar memory register",
        )),
    }
}

fn scalar_memory(word: u32) -> Result<Step, ReadOnlyTargetError> {
    // Independent fixed-field decoding establishes the class before any form
    // binding is used. No indexed/writeback, SIMD, narrow or signed load is
    // silently treated as an ordinary 4/8-byte transfer.
    if !matches!(
        decode_word(word),
        Some(
            DecodedWord::LoadStoreUnsigned {
                size: 2 | 3,
                v: 0,
                opc: 0 | 1,
                ..
            } | DecodedWord::LoadStoreUnscaled {
                size: 2 | 3,
                v: 0,
                opc: 0 | 1,
                ..
            } | DecodedWord::LoadStoreRegister {
                size: 2 | 3,
                v: 0,
                opc: 0 | 1,
                ..
            }
        )
    ) {
        return Err(ReadOnlyTargetError::Bytes("unsupported scalar memory word"));
    }
    let binding = decode_scalar_memory_word(word)
        .ok_or(ReadOnlyTargetError::Bytes("undecoded scalar memory word"))?;
    if binding.form.bank != ScalarBank::Gpr
        || !matches!(binding.form.access_bytes, 4 | 8)
        || binding.form.extension != ScalarExtension::Zero
    {
        return Err(ReadOnlyTargetError::Bytes("unsupported scalar memory form"));
    }
    let base = memory_register(
        binding
            .base_field
            .ok_or(ReadOnlyTargetError::Bytes("missing scalar memory base"))?,
        false,
    )?;
    let address = match binding.form.addressing {
        ScalarAddressing::UnsignedOffset | ScalarAddressing::Unscaled
            if binding.index_field.is_none() =>
        {
            crate::memory_proofs::qf_bv_byte_addr(&base, binding.operand as u64)
        }
        ScalarAddressing::RegisterOffset => {
            let mode = u32::try_from(binding.operand)
                .ok()
                .filter(|mode| matches!(*mode, 4 | 5 | 6 | 7 | 12 | 13 | 14 | 15))
                .ok_or(ReadOnlyTargetError::Bytes(
                    "unallocated scalar memory index mode",
                ))?;
            let index = memory_register(
                binding
                    .index_field
                    .ok_or(ReadOnlyTargetError::Bytes("missing scalar memory index"))?,
                true,
            )?;
            let shift = if mode & 1 == 1 {
                binding.form.access_bytes.trailing_zeros()
            } else {
                0
            };
            let offset = extend_reg_value(index, mode >> 1, shift).ok_or(
                ReadOnlyTargetError::Bytes("invalid scalar memory index extension"),
            )?;
            base.bvadd(offset)
        }
        _ => {
            return Err(ReadOnlyTargetError::Bytes(
                "scalar memory writeback/literal refused",
            ));
        }
    };
    match binding.form.transfer {
        ScalarTransfer::Load => {
            destination(binding.rt_field)?;
            Ok(Step::MemoryLoad {
                destination: binding.rt_field as usize,
                address,
                byte_width: binding.form.access_bytes,
                alignment: 1,
            })
        }
        ScalarTransfer::Store => {
            let full = memory_register(binding.rt_field, true)?;
            let value = if binding.form.access_bytes == 4 {
                full.extract(31, 0)
            } else {
                full
            };
            Ok(Step::MemoryStore {
                address,
                value: Box::new(value),
                byte_width: binding.form.access_bytes,
                alignment: 1,
            })
        }
    }
}

fn load(word: u32) -> Result<Step, ReadOnlyTargetError> {
    // The instruction-word decoder provides the strict class gate; the shared
    // scalar-memory decoder provides the architectural byte offset and form.
    // Operand binding is deliberately NOT used: its old base-frozen theorem
    // does not cover a valid plain LDR whose Rt and Rn overlap.
    if !matches!(
        decode_word(word),
        Some(
            DecodedWord::LoadStoreUnsigned {
                size: 3,
                v: 0,
                opc: 1,
                ..
            } | DecodedWord::LoadStoreUnscaled {
                size: 3,
                v: 0,
                opc: 1,
                ..
            }
        )
    ) {
        return Err(ReadOnlyTargetError::Bytes(
            "unsupported read-only memory word",
        ));
    }
    let binding = decode_scalar_memory_word(word)
        .ok_or(ReadOnlyTargetError::Bytes("undecoded scalar memory word"))?;
    if binding.form.transfer != ScalarTransfer::Load
        || binding.form.bank != ScalarBank::Gpr
        || binding.form.access_bytes != 8
        || binding.form.extension != ScalarExtension::Zero
        || !matches!(
            binding.form.addressing,
            ScalarAddressing::UnsignedOffset | ScalarAddressing::Unscaled
        )
        || binding.index_field.is_some()
    {
        return Err(ReadOnlyTargetError::Bytes(
            "unsupported decoded memory form",
        ));
    }
    let base = binding
        .base_field
        .filter(|base| *base < 31)
        .ok_or(ReadOnlyTargetError::Bytes(
            "SP load outside frameless profile",
        ))?;
    destination(binding.rt_field)?;
    // Snapshot Rn BEFORE the write, including Rt==Rn. Rt=31 must still cause
    // an actual memory demand; the parent discards only the loaded value.
    let address =
        crate::memory_proofs::qf_bv_byte_addr(&register(base as usize), binding.operand as u64);
    Ok(Step::Load {
        destination: binding.rt_field as usize,
        address,
        // Normal-memory base-GPR loads have no implied eight-byte alignment.
        // Source requirements must separately cover this actual address.
        alignment: 1,
    })
}

fn scalar(word: u32) -> Result<Step, ReadOnlyTargetError> {
    let decoded = decode_a64_value_word(word)
        .map_err(|_| ReadOnlyTargetError::Bytes("undecoded scalar value word"))?;
    match decoded {
        // No authenticated entry-SP context belongs to this first profile.
        A64ValueWord::AddSubImm { rn: 31, .. } => {
            return Err(ReadOnlyTargetError::Bytes(
                "SP read outside frameless profile",
            ));
        }
        A64ValueWord::LogicalImmediate { .. }
        | A64ValueWord::MoveWide { .. }
        | A64ValueWord::AddSubShiftedReg { .. }
        | A64ValueWord::LogicalShiftedReg { .. }
        | A64ValueWord::AddSubImm { .. }
        | A64ValueWord::Dp3 { .. }
        | A64ValueWord::Bitfield { .. }
        | A64ValueWord::Dp1 { .. } => {}
        _ => return Err(ReadOnlyTargetError::Bytes("non-integer scalar word")),
    }
    let fields = FieldOverrides::default();
    let effect = denote_a64_value_word_compact(&decoded, &fields)
        .map_err(|_| ReadOnlyTargetError::Bytes("unmodeled scalar value semantics"))?;
    let flags = denote_a64_value_flags(&decoded, &fields)
        .map_err(|_| ReadOnlyTargetError::Bytes("unmodeled scalar flag semantics"))?;
    if effect.writes_nzcv != flags.is_some()
        || effect.value.sort() != SmtSort::BitVec(64)
        || flags.as_ref().is_some_and(|flags| {
            [&flags.n, &flags.z, &flags.c, &flags.v]
                .into_iter()
                .any(|flag| flag.sort() != SmtSort::Bool)
        })
    {
        return Err(ReadOnlyTargetError::Bytes(
            "incomplete scalar architectural effect",
        ));
    }
    let destination = match effect.dest {
        A64Dest::Gpr(rd) => destination(u32::from(rd))?,
        A64Dest::Discarded => None,
        _ => return Err(ReadOnlyTargetError::Bytes("non-GPR scalar destination")),
    };
    Ok(Step::Scalar {
        destination,
        value: effect.value,
        flags: flags.map(Box::new),
    })
}

#[cfg(test)]
#[path = "read_only_target_scalar_bytes_tests.rs"]
mod scalar_memory_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::EvalEnv;
    use std::convert::Infallible;

    const RET_X30: u32 = 0xd65f_03c0;

    fn code(words: &[u32]) -> Vec<u8> {
        words.iter().flat_map(|word| word.to_le_bytes()).collect()
    }

    fn one(word: u32) -> Step {
        adapt_word(word, 0, 2).unwrap()
    }

    fn eval(value: &E, x1: u64, x2: u64, nzcv: u8) -> u64 {
        let value = value
            .try_rewrite_dag::<Infallible>(&mut |node| {
                let E::UF {
                    name,
                    args,
                    ret_sort: SmtSort::Bool,
                } = node
                else {
                    return Ok(None);
                };
                assert!(args.is_empty());
                let bit = match name.as_str() {
                    "flag_n" => 3,
                    "flag_z" => 2,
                    "flag_c" => 1,
                    "flag_v" => 0,
                    _ => panic!("unexpected free flag {name}"),
                };
                Ok(Some(E::bool_const(nzcv & (1 << bit) != 0)))
            })
            .unwrap()
            .unwrap_or_else(|| value.clone());
        let mut env = EvalEnv::default();
        env.insert("x0".into(), x1);
        env.insert("x1".into(), x1);
        env.insert("x2".into(), x2);
        let result = value.try_eval(&env).unwrap();
        if value.sort() == SmtSort::Bool {
            u64::from(result.as_bool())
        } else {
            result.as_u64()
        }
    }

    #[test]
    fn raw_word_preflight_and_exact_inert_return() {
        assert!(adapt(&[]).is_err());
        assert!(adapt(&[0; 3]).is_err());
        assert!(matches!(
            adapt(&code(&[NOP; MAX_WORDS + 1])),
            Err(ReadOnlyTargetError::Budget("final-word count"))
        ));
        let steps = adapt(&code(&[NOP; MAX_WORDS])).unwrap();
        assert_eq!(steps.len(), MAX_WORDS);
        assert!(steps.iter().all(|step| matches!(step, Step::Inert)));
        assert!(matches!(one(RET_X30), Step::Return));
        // Other RET registers, hints, and indirect calls are not inert.
        for word in [0xd65f_0020, NOP ^ (1 << 5), 0xd63f_0020] {
            assert!(adapt_word(word, 0, 2).is_err(), "{word:#010x}");
        }
    }

    #[test]
    fn exact_signed_branch_pc_and_reserved_conditional_fields() {
        let steps = adapt(&code(&[0x1400_0002, 0x17ff_ffff, RET_X30])).unwrap();
        assert!(matches!(steps[0], Step::Jump(2)));
        assert!(matches!(steps[1], Step::Jump(0)));
        let steps = adapt(&code(&[NOP, 0x54ff_ffe0, RET_X30])).unwrap();
        let Step::Branch { condition, taken } = &steps[1] else {
            panic!("B.EQ required")
        };
        assert_eq!(*taken, 0);
        assert_eq!(eval(condition, 0, 0, 4), 1);
        assert_eq!(eval(condition, 0, 0, 0), 0);
        for word in [
            0x9400_0001, // BL
            0x5400_0030, // reserved bit 4
            0x5500_0020, // BC.cond is outside this profile
            0x5400_002e, // AL
            0x5400_002f, // NV
            0x17ff_ffff, // before stream
            0x1400_0002, // beyond stream
            0x1600_0000, // most-negative imm26
            0x5480_0000, // most-negative imm19
        ] {
            assert!(adapt_word(word, 0, 2).is_err(), "{word:#010x}");
        }
    }

    #[test]
    fn compare_branches_read_actual_width_zr_and_not_flags() {
        for width64 in [false, true] {
            for nonzero in [false, true] {
                let word = 0x3400_0021 | (u32::from(width64) << 31) | (u32::from(nonzero) << 24);
                let Step::Branch { condition, taken } = one(word) else {
                    panic!("compare branch required")
                };
                assert_eq!(taken, 1);
                for x1 in [0, 1, 1 << 32, u64::MAX] {
                    let tested = if width64 { x1 } else { x1 & u32::MAX as u64 };
                    let expected = u64::from((tested != 0) == nonzero);
                    for nzcv in [0, 15] {
                        assert_eq!(eval(&condition, x1, 0, nzcv), expected);
                    }
                }
                let Step::Branch { condition, .. } = one((word & !31) | 31) else {
                    panic!("ZR compare branch required")
                };
                assert_eq!(eval(&condition, u64::MAX, 0, 15), u64::from(!nonzero));
            }
        }
    }

    #[test]
    fn loads_keep_snapshot_alias_zr_demand_and_normal_alignment() {
        for (word, offset, rd) in [
            (0xf940_0421, 8_i64, 1), // LDR X1,[X1,#8], reads old X1
            (0xf940_0c3f, 24, 31),   // LDR XZR,[X1,#24], still a read
            (0xf85f_f022, -1, 2),    // LDUR X2,[X1,#-1]
            (0xf850_0022, -256, 2),
            (0xf84f_f022, 255, 2),
        ] {
            let Step::Load {
                destination,
                address,
                alignment,
            } = one(word)
            else {
                panic!("actual load required")
            };
            assert_eq!(destination, rd);
            assert_eq!(alignment, 1);
            for base in [0_u64, 1, u64::MAX] {
                assert_eq!(eval(&address, base, 0, 0), base.wrapping_add(offset as u64));
            }
        }
        for word in [
            0xf900_0020, // store
            0xb940_0020, // four-byte load
            0xfd40_0020, // floating load
            0xf840_0c20, // writeback
            0xf862_6820, // register offset
            0xf940_03e0, // SP base
            0xf940_0032, // writes reserved X18
            0xc85f_7c20, // exclusive load
        ] {
            assert!(adapt_word(word, 0, 2).is_err(), "{word:#010x}");
        }
    }

    #[test]
    fn caller_scratch_and_no_sp_profile_are_fail_closed() {
        for rd in 18..=30 {
            assert!(adapt_word(0xd280_0020 | rd, 0, 2).is_err());
        }
        for word in [
            0x9100_043f, // ADD SP,X1,#1
            0x9100_07e0, // ADD X0,SP,#1
            0xb240_003f, // ORR SP,X1,#1
            0x9e66_0020, // FMOV X0,D1
            0xd53b_4200, // MRS X0,NZCV
            0xd51b_4200, // MSR NZCV,X0
            0x9b60_0020, // reserved data-processing row
            0x0b02_8020, // reserved W shifted add amount 32
            0x0bc2_0020, // reserved shifted add ROR
            0x52c0_0020, // reserved W move-wide hw2
        ] {
            assert!(adapt_word(word, 0, 2).is_err(), "{word:#010x}");
        }
        assert!(matches!(
            one(0xd280_003f),
            Step::Scalar {
                destination: None,
                ..
            }
        ));
    }

    #[test]
    fn scalar_values_reuse_full_x_write_and_prestate_move_keep() {
        let Step::Scalar {
            destination,
            value,
            flags,
        } = one(0x7280_0021)
        // MOVK W1,#1 at halfword0
        else {
            panic!("MOVK required")
        };
        assert_eq!(destination, Some(1));
        assert!(flags.is_none());
        assert_eq!(eval(&value, 0xffff_eeee_dddd_cccc, 0, 0), 0xdddd_0001);
        for (word, expected) in [
            (0x8b02_0020, 13), // ADD X0,X1,X2
            (0xcb02_0020, 5),  // SUB X0,X1,X2
            (0xca02_0020, 13), // EOR X0,X1,X2
            (0x9341_fc20, 4),  // ASR X0,X1,#1
        ] {
            let Step::Scalar { value, flags, .. } = one(word) else {
                panic!("ordinary scalar required")
            };
            assert!(flags.is_none());
            assert_eq!(eval(&value, 9, 4, 0), expected);
        }
    }

    #[test]
    fn conditional_select_reuses_all_variants_widths_aliases_and_conditions() {
        for (variant, base) in [0x1a80_0000, 0x1a80_0400, 0x5a80_0000, 0x5a80_0400]
            .into_iter()
            .enumerate()
        {
            for width64 in [false, true] {
                let mask = if width64 { u64::MAX } else { u32::MAX as u64 };
                for cc in 0..16_u8 {
                    // Destination aliases each source, and ZR discards.
                    for (rd, rn, rm) in [(0, 1, 2), (1, 1, 2), (2, 1, 2), (31, 1, 2), (0, 31, 2)] {
                        let word = base
                            | (u32::from(width64) << 31)
                            | (u32::from(cc) << 12)
                            | (rm << 16)
                            | (rn << 5)
                            | rd;
                        let Step::Scalar {
                            destination,
                            value,
                            flags,
                        } = one(word)
                        else {
                            panic!("CSEL family required")
                        };
                        assert_eq!(destination, (rd != 31).then_some(rd as usize));
                        assert!(flags.is_none());
                        for nzcv in 0..16 {
                            for (raw_a, raw_b) in
                                [(0, 0), (1, u64::MAX), (u64::MAX, 0x8000_0000_0000_0000)]
                            {
                                let holds =
                                    crate::aarch64_csel_semantics::condition_holds(cc, nzcv)
                                        .unwrap();
                                let a = if rn == 31 { 0 } else { raw_a & mask };
                                let b = raw_b & mask;
                                let expected = if rd == 31 {
                                    0
                                } else if holds {
                                    a
                                } else {
                                    (match variant {
                                        0 => b,
                                        1 => b.wrapping_add(1),
                                        2 => !b,
                                        _ => (!b).wrapping_add(1),
                                    }) & mask
                                };
                                assert_eq!(eval(&value, raw_a, raw_b, nzcv), expected);
                            }
                        }
                    }
                }
            }
        }
        // A fixed-bit mutation must not be interpreted as conditional select.
        assert!(adapt_word(0x9a82_0820, 0, 2).is_err());
    }

    #[test]
    fn discarded_flag_producers_still_supply_actual_nzcv() {
        for (word, x1, x2, expected) in [
            (0xf100_003f, 0, 0, [false, true, true, false]), // CMP X1,#0
            (0xeb02_003f, 1, 2, [true, false, false, false]), // CMP X1,X2
            (0xea02_003f, 1, 2, [false, true, false, false]), // TST X1,X2
            (0xab02_003f, u64::MAX, 1, [false, true, true, false]), // ADDS XZR,X1,X2
        ] {
            let Step::Scalar {
                destination,
                flags: Some(flags),
                ..
            } = one(word)
            else {
                panic!("exact flag-writing scalar required")
            };
            assert_eq!(destination, None);
            for (flag, expected) in [&flags.n, &flags.z, &flags.c, &flags.v]
                .into_iter()
                .zip(expected)
            {
                assert_eq!(eval(flag, x1, x2, 0), u64::from(expected));
            }
        }
    }
}
