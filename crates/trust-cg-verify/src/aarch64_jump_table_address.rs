// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0.
//! Independent word/ownership checks for a local ADR-low + ADD-LSL12 pair.
//! This binds a packed address to final layout; it creates no source/proof authority.

use std::collections::BTreeSet;
use trust_cg_ir::regs::{RegClass, preg_class};
use trust_cg_ir::{AArch64Opcode as Op, BlockId, InstId, MachFunction, MachOperand};

/// Validate stable identities, one owner, adjacency, pure flags and exact
/// register/immediate shapes. In particular ADR Rd31 discards to XZR but
/// ADD-immediate Rd31 writes SP: no such expansion is ever admissible.
pub fn validate_expansions(func: &MachFunction) -> Result<(), String> {
    if func.jump_table_address_expansions.is_empty() {
        return Ok(());
    }
    let mut owners: Vec<Option<(BlockId, usize)>> = vec![None; func.insts.len()];
    for &block in &func.block_order {
        let body = func
            .blocks
            .get(block.0 as usize)
            .ok_or("table-address block is absent")?;
        for (position, id) in body.insts.iter().enumerate() {
            let owner = owners
                .get_mut(id.0 as usize)
                .ok_or("table-address instruction is absent")?;
            if owner.replace((block, position)).is_some() {
                return Err("table-address instruction has duplicate owners".into());
            }
        }
    }
    let mut used_adds = BTreeSet::new();
    for (&anchor, row) in &func.jump_table_address_expansions {
        if func.jump_tables.get(row.table as usize).is_none() {
            return Err("expanded table identity is absent".into());
        }
        let adr = func
            .insts
            .get(anchor.0 as usize)
            .ok_or("expanded ADR is absent")?;
        let add = func
            .insts
            .get(row.add.0 as usize)
            .ok_or("expanded ADD is absent")?;
        let Some(&(block, position)) = owners.get(anchor.0 as usize).and_then(Option::as_ref)
        else {
            return Err("expanded ADR is not laid out".into());
        };
        if owners.get(row.add.0 as usize).copied().flatten() != Some((block, position + 1))
            || !used_adds.insert(row.add)
        {
            return Err(
                "expanded ADD is not a unique adjacent instruction in the ADR block".into(),
            );
        }
        let [MachOperand::PReg(rd), MachOperand::Imm(low)] = adr.operands.as_slice() else {
            return Err("expanded ADR is not an exact local literal address".into());
        };
        if adr.opcode != Op::Adr
            || preg_class(*rd) != RegClass::Gpr64
            || trust_cg_ir::aarch64_regs::hw_encoding(*rd) >= 31
            || !(0..4096).contains(low)
        {
            return Err("expanded ADR needs X0..X30 and a nonnegative low12 immediate".into());
        }
        let [
            MachOperand::PReg(dst),
            MachOperand::PReg(src),
            MachOperand::Imm(high),
        ] = add.operands.as_slice()
        else {
            return Err("expanded ADD has an invalid operand layout".into());
        };
        if add.opcode != Op::AddRIShift12 || dst != rd || src != rd || !(1..4096).contains(high) {
            return Err(
                "expanded address needs a same-register ADD LSL12 with positive high12".into(),
            );
        }
        for inst in [adr, add] {
            if inst.flags != inst.opcode.default_flags()
                || inst.proof.is_some()
                || !inst.implicit_uses.is_empty()
                || !inst.implicit_defs.is_empty()
            {
                return Err("expanded address carries effects or noncanonical flags".into());
            }
        }
    }
    Ok(())
}

/// Decode the REAL two words, independently of the producer decomposition,
/// and return the final FUNCTION-RELATIVE address. The caller must compare it
/// with the table's independently recomputed final offset. Negative ADRs,
/// SUB/S/32-bit forms, external relocations and register31 all refuse here.
pub fn decode_expanded_address(
    func: &MachFunction,
    anchor: InstId,
    offset: u32,
    adr_word: u32,
    add_word: u32,
) -> Result<i64, String> {
    let row = func
        .jump_table_address_expansions
        .get(&anchor)
        .ok_or("missing table-address expansion")?;
    let adr = func.insts.get(anchor.0 as usize).ok_or("missing ADR")?;
    let add = func.insts.get(row.add.0 as usize).ok_or("missing ADD")?;
    let [MachOperand::PReg(rd), MachOperand::Imm(expected_low)] = adr.operands.as_slice() else {
        return Err("nonliteral ADR intent".into());
    };
    let [
        MachOperand::PReg(dst),
        MachOperand::PReg(src),
        MachOperand::Imm(expected_high),
    ] = add.operands.as_slice()
    else {
        return Err("nonliteral ADD intent".into());
    };
    let register = trust_cg_ir::aarch64_regs::hw_encoding(*rd) as u32;
    if adr.opcode != Op::Adr
        || add.opcode != Op::AddRIShift12
        || preg_class(*rd) != RegClass::Gpr64
        || register >= 31
        || dst != rd
        || src != rd
        || !(0..4096).contains(expected_low)
        || !(1..4096).contains(expected_high)
    {
        return Err("invalid local table-address pair".into());
    }
    for inst in [adr, add] {
        if inst.flags != inst.opcode.default_flags()
            || inst.proof.is_some()
            || !inst.implicit_uses.is_empty()
            || !inst.implicit_defs.is_empty()
        {
            return Err("address pair cannot carry donated proof or implicit effects".into());
        }
    }
    // ADR: immlo[30:29], signed immhi[23:5], Rd[4:0].
    if adr_word & 0x9F00_0000 != 0x1000_0000 || adr_word & 31 != register {
        return Err("word is not the intended ADR".into());
    }
    let raw = (((adr_word >> 5) & 0x7ffff) << 2) | ((adr_word >> 29) & 3);
    let low = ((raw as i64) << 43) >> 43;
    // 64-bit ADD immediate, no flags, LSL12. No opcode masking to accept SUB.
    if add_word & 0xFFC0_0000 != 0x9140_0000
        || add_word & 31 != register
        || (add_word >> 5) & 31 != register
    {
        return Err("word is not the intended nonflagging same-register ADD LSL12".into());
    }
    let high = i64::from((add_word >> 10) & 4095);
    if low != *expected_low || high != *expected_high {
        return Err("table-address words disagree with literal intent".into());
    }
    Ok(i64::from(offset) + low + high * 4096)
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::function::{JumpTableAddressExpansion, JumpTableData};
    use trust_cg_ir::regs::{PReg, X9};
    use trust_cg_ir::{MachInst, Signature};

    fn pair(low: i64, high: i64) -> (MachFunction, InstId, u32, u32) {
        let mut f = MachFunction::new("local_address".into(), Signature::new(vec![], vec![]));
        let adr = f.push_inst(MachInst::new(
            Op::Adr,
            vec![MachOperand::PReg(X9), MachOperand::Imm(low)],
        ));
        let add = f.push_inst(MachInst::new(
            Op::AddRIShift12,
            vec![
                MachOperand::PReg(X9),
                MachOperand::PReg(X9),
                MachOperand::Imm(high),
            ],
        ));
        f.append_inst(f.entry, adr);
        f.append_inst(f.entry, add);
        f.jump_tables.push(JumpTableData {
            min_val: 0,
            targets: vec![f.entry],
        });
        f.jump_table_address_expansions
            .insert(adr, JumpTableAddressExpansion { table: 0, add });
        // Arm ARM bit fields, deliberately independent of the encoder.
        let raw = low as u32 & 0x1f_ffff;
        let a = 0x1000_0009 | (raw & 3) << 29 | (raw >> 2) << 5;
        let b = 0x9140_0129 | (high as u32) << 10;
        (f, adr, a, b)
    }

    #[test]
    fn actual_words_compose_the_local_address_without_page_or_aslr_assumptions() {
        for delta in [1 << 20, 1_083_624, 0x00ff_ffff] {
            let (f, adr, a, b) = pair(delta & 4095, delta >> 12);
            validate_expansions(&f).unwrap();
            for pc in [0, 4, 4092, 4096, 0x1234_5678] {
                assert_eq!(
                    decode_expanded_address(&f, adr, pc, a, b).unwrap(),
                    i64::from(pc) + delta
                );
            }
        }
    }

    #[test]
    fn sub_flags_width_shift_register_and_literal_word_mutations_refuse() {
        let (f, adr, a, b) = pair(2280, 264);
        for bad in [
            b ^ (1 << 30),
            b ^ (1 << 29),
            b ^ (1 << 31),
            b ^ (1 << 22),
            b ^ (1 << 10),
            (b & !31) | 31,
            (b & !(31 << 5)) | (31 << 5),
        ] {
            assert!(
                decode_expanded_address(&f, adr, 64, a, bad).is_err(),
                "bad ADD {bad:#x}"
            );
        }
        assert!(decode_expanded_address(&f, adr, 64, a ^ (1 << 5), b).is_err());
        // A valid negative ADR is NOT silently treated as this forward expansion.
        let (negative, id, a, b) = pair(-1, 264);
        assert!(validate_expansions(&negative).is_err());
        assert!(decode_expanded_address(&negative, id, 64, a, b).is_err());
    }

    #[test]
    fn register31_external_authority_and_inexact_instruction_custody_refuse() {
        let (base, adr, _, _) = pair(2280, 264);
        for mutation in 0..8 {
            let mut f = base.clone();
            let add = f.jump_table_address_expansions[&adr].add;
            match mutation {
                0 => f.inst_mut(adr).operands[0] = MachOperand::PReg(PReg::new(31)),
                1 => f.inst_mut(adr).operands[1] = MachOperand::Symbol("external".into()),
                2 => f.inst_mut(add).proof = Some(trust_cg_ir::ProofAnnotation::Pure),
                3 => f.jump_table_address_expansions.get_mut(&adr).unwrap().table = 1,
                4 => f.block_mut(f.entry).insts.reverse(),
                5 => f.append_inst(f.entry, add),
                6 => f.jump_table_address_expansions.get_mut(&adr).unwrap().add = InstId(u32::MAX),
                7 => f.inst_mut(add).implicit_defs = &[X9],
                _ => unreachable!(),
            }
            assert!(validate_expansions(&f).is_err(), "mutation {mutation}");
        }
    }
}
