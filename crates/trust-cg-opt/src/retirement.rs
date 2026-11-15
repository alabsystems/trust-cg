// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Representation-only retirement of a pass's ACTUAL consumed instructions.
//! The caller must validate and justify its rewrite before changing links.
//! No semantic deletion proof, ownership certificate or orphan sweep lives
//! here. Stable arena IDs and historical lowering sidecars remain unchanged.

use crate::fast_hash::FxHashSet;
use trust_cg_ir::{AArch64Opcode, InstId, MachFunction, MachInst};

/// Retire only valid supplied IDs that no block still references. Work is one
/// all-block link scan plus the candidate count, not one scan per instruction.
/// Blocks omitted from executable layout still own their references.
pub(crate) fn retire_unlinked(func: &mut MachFunction, consumed: &[InstId]) -> usize {
    retire_unlinked_before(func, consumed, |_| {})
}

/// Let a producer preserve its exact transformation history AFTER links are
/// committed and BEFORE operands/metadata become canonical nonemitting Nops.
/// The callback sees only the now-unlinked valid candidate set, not permission
/// to delete arbitrary arena nodes. It cannot mutate function links through
/// this borrow. In particular, still-live sources must not be marked consumed
/// in provenance merely because a different block used the same arena ID.
pub(crate) fn retire_unlinked_before(
    func: &mut MachFunction,
    consumed: &[InstId],
    before: impl FnOnce(&FxHashSet<InstId>),
) -> usize {
    let mut unlinked: FxHashSet<_> = consumed
        .iter()
        .copied()
        .filter(|id| (id.0 as usize) < func.insts.len())
        .collect();
    if !unlinked.is_empty() {
        for block in &func.blocks {
            for id in &block.insts {
                unlinked.remove(id);
            }
        }
    }
    before(&unlinked);
    let count = unlinked.len();
    for id in unlinked {
        // Deliberately keep inst_lowering_provenance and stable IDs. Those
        // are history, not licenses to execute the retired original again.
        *func.inst_mut(id) = MachInst::new(AArch64Opcode::Nop, vec![]);
    }
    count
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::{LoweringProvenance, MachOperand, Signature, SourceInstDigest, SourceInstId};

    fn instruction() -> MachInst {
        MachInst::new(AArch64Opcode::Movz, vec![MachOperand::Imm(7)])
    }

    fn function() -> MachFunction {
        MachFunction::new("bounded_retirement".into(), Signature::new(vec![], vec![]))
    }

    #[test]
    fn only_actual_unlinked_valid_candidates_retire_once_without_an_orphan_sweep() {
        let mut func = function();
        let consumed = func.push_inst(instruction());
        let unrelated_orphan = func.push_inst(instruction());
        let live = func.push_inst(instruction());
        func.append_inst(func.entry, live);
        let prior_arena_len = func.insts.len();
        let unrelated = format!("{:?}", func.inst(unrelated_orphan));
        let live_before = format!("{:?}", func.inst(live));
        assert_eq!(
            retire_unlinked(&mut func, &[consumed, consumed, live, InstId(u32::MAX)]),
            1
        );
        assert_eq!(func.insts.len(), prior_arena_len);
        assert_eq!(func.inst(consumed).opcode, AArch64Opcode::Nop);
        assert!(func.inst(consumed).operands.is_empty());
        assert_eq!(
            func.inst(consumed).flags,
            AArch64Opcode::Nop.default_flags()
        );
        assert_eq!(format!("{:?}", func.inst(unrelated_orphan)), unrelated);
        assert_eq!(format!("{:?}", func.inst(live)), live_before);
        assert_eq!(func.block(func.entry).insts, [live]);
        assert_eq!(retire_unlinked(&mut func, &[]), 0);
    }

    #[test]
    fn a_block_outside_layout_still_protects_its_instruction_reference() {
        let mut func = function();
        let candidate = func.push_inst(instruction());
        let hidden = func.create_block();
        func.append_inst(hidden, candidate);
        func.block_order.retain(|id| *id != hidden);
        let original = format!("{:?}", func.inst(candidate));
        assert_eq!(retire_unlinked(&mut func, &[candidate]), 0);
        assert_eq!(format!("{:?}", func.inst(candidate)), original);
        assert_eq!(func.block(hidden).insts, [candidate]);
    }

    #[test]
    fn callback_observes_actual_consumption_and_historical_lowering_sidecars_survive() {
        let mut func = function();
        let consumed = func.push_inst(instruction());
        let live = func.push_inst(instruction());
        func.append_inst(func.entry, live);
        let provenance = LoweringProvenance::SourceInst {
            id: SourceInstId {
                block: 8,
                index: 12,
            },
            digest: SourceInstDigest(0x1234),
            trust_ir_inst: None,
        };
        func.set_inst_lowering_provenance(consumed, provenance);
        let mut called = false;
        assert_eq!(
            retire_unlinked_before(&mut func, &[consumed, live], |unlinked| {
                called = true;
                assert_eq!(unlinked.len(), 1);
                assert!(unlinked.contains(&consumed));
                assert!(!unlinked.contains(&live));
            }),
            1
        );
        assert!(called);
        assert_eq!(func.inst_lowering_provenance(consumed), provenance);
        assert_eq!(func.inst(consumed).opcode, AArch64Opcode::Nop);
    }
}
