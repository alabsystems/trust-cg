// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0.
//! Scratch-free local address growth, before final branch/layout resolution.
//! External symbols and ordinary literal ADRs do not enter this pass.

use crate::pipeline::PipelineError;
use trust_cg_ir::function::JumpTableAddressExpansion;
use trust_cg_ir::regs::{RegClass, preg_class};
use trust_cg_ir::{AArch64Opcode as Op, BlockId, InstId, MachFunction, MachInst, MachOperand};

fn error(detail: impl std::fmt::Display) -> PipelineError {
    PipelineError::Encoding(format!("[TCG-A64-LOCAL-ADDRESS] {detail}"))
}

#[derive(Clone, Copy)]
struct Site {
    anchor: InstId,
    block: BlockId,
    position: usize,
    table: u32,
    pc: u32,
    target: u32,
}

/// Recompute from actual final one-word instructions and table encounter order,
/// never from an old encoder offset or the previous round's address parts.
fn sites(func: &MachFunction) -> Result<Vec<Site>, PipelineError> {
    let mut result = Vec::new();
    let mut offset = 0u32;
    for &block in &func.block_order {
        for (position, &id) in func.block(block).insts.iter().enumerate() {
            if func.inst(id).is_pseudo() {
                continue;
            }
            if let Some(table) = func.jump_table_at_address(id) {
                result.push(Site {
                    anchor: id,
                    block,
                    position,
                    table,
                    pc: offset,
                    target: 0,
                });
            }
            offset = offset
                .checked_add(4)
                .ok_or_else(|| error("body exceeds u32 layout"))?;
        }
    }
    for site in &mut result {
        let table = func
            .jump_tables
            .get(site.table as usize)
            .ok_or_else(|| error("unknown local table"))?;
        site.target = offset;
        let bytes = u32::try_from(table.targets.len())
            .ok()
            .and_then(|n| n.checked_mul(4))
            .ok_or_else(|| error("table size exceeds u32 layout"))?;
        offset = offset
            .checked_add(bytes)
            .ok_or_else(|| error("tables exceed u32 layout"))?;
    }
    Ok(result)
}

/// Only forward local tables use this pair. There is no implicit SUB opcode
/// or signed-to-unsigned coercion. Literal negative ADRs keep their old route.
fn parts(delta: i64) -> Result<(i64, i64), PipelineError> {
    if !(0..=0x00ff_ffff).contains(&delta) {
        return Err(error(format!(
            "local address delta {delta} is outside the forward two-word range"
        )));
    }
    Ok((delta & 4095, delta >> 12))
}

/// Grow each newly far local ADR once. All original instructions/owners stay
/// in place; the new real ADD has no donated proof or implicit effects.
pub(crate) fn expand(func: &mut MachFunction) -> Result<bool, PipelineError> {
    if func.jump_tables.is_empty() {
        return Ok(false);
    }
    trust_cg_verify::aarch64_jump_table_address::validate_expansions(func).map_err(error)?;
    let pending: Vec<_> = sites(func)?
        .into_iter()
        .filter(|site| {
            !func
                .jump_table_address_expansions
                .contains_key(&site.anchor)
                && i64::from(site.target) - i64::from(site.pc) >= 1 << 20
        })
        .collect();
    for site in pending.iter().rev() {
        let delta = i64::from(site.target) - i64::from(site.pc);
        parts(delta)?;
        let adr = func.inst(site.anchor);
        let [MachOperand::PReg(rd), MachOperand::JumpTableIndex(table)] = adr.operands.as_slice()
        else {
            return Err(error("far ADR is not an exact local-table producer"));
        };
        let rd = *rd;
        if *table != site.table
            || preg_class(rd) != RegClass::Gpr64
            || trust_cg_ir::aarch64_regs::hw_encoding(rd) >= 31
            || adr.flags != Op::Adr.default_flags()
            || adr.proof.is_some()
            || !adr.implicit_defs.is_empty()
            || !adr.implicit_uses.is_empty()
            || func
                .lowering_provenance
                .get(&site.anchor)
                .and_then(trust_cg_ir::LoweringProvenance::source_id)
                .is_some_and(|source| {
                    func.source_fusion_targets.contains_key(&source)
                        || func
                            .source_fusion_targets
                            .values()
                            .any(|&target| target == source)
                })
            || func.call_abi_facts.contains_key(&site.anchor)
            || func
                .trap_expansions
                .iter()
                .any(|row| row.insts.contains(&site.anchor))
        {
            return Err(error(
                "far local ADR has register31, effects or authority that cannot be reassigned",
            ));
        }
        let mut add = MachInst::new(
            Op::AddRIShift12,
            vec![
                MachOperand::PReg(rd),
                MachOperand::PReg(rd),
                MachOperand::Imm(1),
            ],
        );
        add.source_loc = adr.source_loc;
        let add = func
            .try_push_inst(add)
            .ok_or_else(|| error("address ADD instruction arena is full"))?;
        func.block_mut(site.block)
            .insts
            .insert(site.position + 1, add);
        func.inst_mut(site.anchor).operands[1] = MachOperand::Imm(0);
        func.jump_table_address_expansions.insert(
            site.anchor,
            JumpTableAddressExpansion {
                table: site.table,
                add,
            },
        );
        if let Some(provenance) = func.lowering_provenance.get(&site.anchor).copied() {
            func.lowering_provenance.insert(add, provenance);
        }
    }
    Ok(!pending.is_empty())
}

/// Fill actual literal operands only after every instruction-growth round.
/// The independent final-byte consumers still rederive and check the target.
pub(crate) fn refresh(func: &mut MachFunction) -> Result<(), PipelineError> {
    if func.jump_table_address_expansions.is_empty() {
        return Ok(());
    }
    for site in sites(func)? {
        if let Some(row) = func
            .jump_table_address_expansions
            .get(&site.anchor)
            .copied()
        {
            let (low, high) = parts(i64::from(site.target) - i64::from(site.pc))?;
            if high == 0 {
                return Err(error("expanded local address lost its high part"));
            }
            func.inst_mut(site.anchor).operands[1] = MachOperand::Imm(low);
            func.inst_mut(row.add).operands[2] = MachOperand::Imm(high);
        }
    }
    trust_cg_verify::aarch64_jump_table_address::validate_expansions(func).map_err(error)
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::function::JumpTableData;
    use trust_cg_ir::regs::{PReg, X9, X10, X30};
    use trust_cg_ir::{ProofAnnotation, Signature};

    fn append(f: &mut MachFunction, inst: MachInst) -> InstId {
        let id = f.push_inst(inst);
        f.append_inst(f.entry, id);
        id
    }

    fn address_function(words: usize, second: bool) -> (MachFunction, InstId) {
        let mut f = MachFunction::new("address_layout".into(), Signature::new(vec![], vec![]));
        let first = append(
            &mut f,
            MachInst::new(
                Op::Adr,
                vec![MachOperand::PReg(X9), MachOperand::JumpTableIndex(0)],
            ),
        );
        f.jump_tables.push(JumpTableData {
            min_val: 0,
            targets: vec![f.entry; if second { 4 } else { 1 }],
        });
        if second {
            append(
                &mut f,
                MachInst::new(
                    Op::Adr,
                    vec![MachOperand::PReg(X10), MachOperand::JumpTableIndex(1)],
                ),
            );
            f.jump_tables.push(JumpTableData {
                min_val: 0,
                targets: vec![f.entry],
            });
        }
        for _ in (if second { 3 } else { 2 })..words {
            append(&mut f, MachInst::new(Op::AlignNop, vec![]));
        }
        append(&mut f, MachInst::new(Op::Ret, vec![MachOperand::PReg(X30)]));
        (f, first)
    }

    #[test]
    fn address_growth_uses_a_fixedpoint_and_refreshes_moved_pcs_and_tables() {
        // A is just in ADR range; B's later table is not. Growing B moves
        // both tables past A's limit, so A must grow in the next round.
        let (mut f, first) = address_function((1 << 18) - 1, true);
        assert!(expand(&mut f).unwrap());
        assert_eq!(f.jump_table_address_expansions.len(), 1);
        assert!(!f.jump_table_address_expansions.contains_key(&first));
        assert!(expand(&mut f).unwrap());
        assert_eq!(f.jump_table_address_expansions.len(), 2);
        assert!(!expand(&mut f).unwrap());
        refresh(&mut f).unwrap();
        for site in sites(&f).unwrap() {
            let row = f.jump_table_address_expansions[&site.anchor];
            let MachOperand::Imm(low) = f.inst(site.anchor).operands[1] else {
                panic!("literal ADR");
            };
            let MachOperand::Imm(high) = f.inst(row.add).operands[2] else {
                panic!("literal ADD");
            };
            assert_eq!(
                i64::from(site.pc) + low + high * 4096,
                i64::from(site.target)
            );
            assert_eq!(f.inst(row.add).flags, Op::AddRIShift12.default_flags());
            assert!(f.inst(row.add).proof.is_none());
        }
    }

    #[test]
    fn negative_overflow_and_register31_or_authority_cannot_enter_the_local_pair() {
        for delta in [-1, i64::MIN, 1 << 24, i64::MAX] {
            assert!(parts(delta).is_err());
        }
        assert_eq!(parts(0x00ff_ffff).unwrap(), (4095, 4095));
        for mutation in 0..3 {
            let (mut f, adr) = address_function((1 << 18) + 1, false);
            match mutation {
                0 => f.inst_mut(adr).operands[0] = MachOperand::PReg(PReg::new(31)),
                1 => f.inst_mut(adr).proof = Some(ProofAnnotation::Pure),
                2 => f.inst_mut(adr).implicit_uses = &[X9],
                _ => unreachable!(),
            }
            let before = f.insts.len();
            assert!(expand(&mut f).is_err(), "mutation {mutation}");
            assert_eq!(
                f.insts.len(),
                before,
                "refuse before creating a partial pair"
            );
        }
    }

    #[test]
    fn in_range_and_external_symbol_addresses_are_not_rewritten() {
        let (mut near, _) = address_function(100, false);
        let before = format!("{near:?}");
        assert!(!expand(&mut near).unwrap());
        assert_eq!(format!("{near:?}"), before);
        let (mut literal, adr) = address_function(100, false);
        literal.inst_mut(adr).operands[1] = MachOperand::Imm(-(1 << 20));
        let before = format!("{literal:?}");
        assert!(!expand(&mut literal).unwrap());
        assert_eq!(format!("{literal:?}"), before);
        let (mut external, adr) = address_function((1 << 18) + 1, false);
        external.inst_mut(adr).opcode = Op::Adrp;
        external.inst_mut(adr).operands[1] = MachOperand::Symbol("external_symbol".into());
        assert!(!expand(&mut external).unwrap());
        assert!(external.jump_table_address_expansions.is_empty());
        assert!(
            matches!(&external.inst(adr).operands[1], MachOperand::Symbol(name) if name == "external_symbol")
        );
    }
}
