// trust-cg-regalloc/spill.rs - Spill code generation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Spill code generation: inserts loads/stores for spilled virtual registers.
//!
//! After register allocation determines which VRegs must be spilled, this
//! module rewrites the machine function to insert:
//! - Stores after each definition of a spilled VReg.
//! - Loads before each use of a spilled VReg.
//!
//! Each distinct spilled VReg initially gets a dedicated stack slot. The
//! surrounding pipeline can subsequently rematerialize loads and reuse slots
//! for non-overlapping live intervals. Slot IDs and metadata are planned before
//! any spill instructions are emitted; exhaustion returns an error.
//!
//! Reference: LLVM's `InlineSpiller` and `SpillPlacement`.

use crate::machine_types::{
    InstFlags, InstId, MachFunction, MachInst, MachOperand, PReg, StackSlotAllocationPlan,
    StackSlotId, VReg,
};
use crate::{AllocError, SpillInfo};
use std::collections::{BTreeMap, BTreeSet};

type SpillInsertionPlan = Vec<(InstId, Vec<MachInst>, Vec<MachInst>)>;

/// Pseudo-opcodes for spill instructions.
///
/// These will be lowered to real load/store instructions by the target-specific
/// backend (e.g., `STR Xn, [SP, #offset]` on AArch64).
pub const PSEUDO_SPILL_STORE: u16 = 0xFFF0;
pub const PSEUDO_SPILL_LOAD: u16 = 0xFFF1;

/// Insert spill code for all spilled VRegs in the allocation result.
///
/// For each spill:
/// 1. Allocate a stack slot.
/// 2. After each def of the spilled VReg, insert a store to the stack slot.
/// 3. Before each use of the spilled VReg, insert a load from the stack slot.
///
/// Pseudos retain the original VReg identities; this helper does not create
/// new temporary VRegs or assign physical spill registers. Repeated requests
/// for one VReg share one slot/record, in first-occurrence order. ID exhaustion
/// leaves the function unchanged, including slot metadata.
pub fn insert_spill_code(
    func: &mut MachFunction,
    spilled_vregs: &[VReg],
    _allocation: &BTreeMap<VReg, PReg>,
) -> Result<Vec<SpillInfo>, AllocError> {
    let (slots, spill_infos) = plan_spill_slots(func, spilled_vregs)?;
    let vreg_to_slot: BTreeMap<_, _> = spill_infos
        .iter()
        .map(|spill| (spill.vreg, spill.slot))
        .collect();

    // Phase 1: Scan all blocks and collect the spill insertions needed.
    // We must read func.insts immutably first, then mutate afterward.
    // Each entry: (original_inst_id, loads_before, stores_after).
    let num_blocks = func.blocks.len();
    let mut block_plans: Vec<SpillInsertionPlan> = Vec::with_capacity(num_blocks);

    for block in &func.blocks {
        let mut plan = Vec::new();

        for &inst_id in &block.insts {
            let inst = &func.insts[inst_id.0 as usize];

            // Collect loads needed before this instruction (for spilled uses).
            let mut loads = Vec::new();
            for op in &inst.uses {
                if let Some(vreg) = op.as_vreg()
                    && let Some(&slot) = vreg_to_slot.get(&vreg)
                {
                    loads.push(make_spill_load(vreg, slot));
                }
            }

            // Collect stores needed after this instruction (for spilled defs).
            let mut stores = Vec::new();
            for op in &inst.defs {
                if let Some(vreg) = op.as_vreg()
                    && let Some(&slot) = vreg_to_slot.get(&vreg)
                {
                    stores.push(make_spill_store(vreg, slot));
                }
            }

            plan.push((inst_id, loads, stores));
        }

        block_plans.push(plan);
    }

    // Phase 2: Commit slots and instructions after every allocation succeeded.
    slots.commit(func);
    for (block_idx, plan) in block_plans.into_iter().enumerate() {
        let mut new_insts = Vec::new();

        for (inst_id, loads, stores) in plan {
            // Insert loads before the instruction.
            for load in loads {
                let load_id = InstId(func.insts.len() as u32);
                func.insts.push(load);
                new_insts.push(load_id);
            }

            // Keep the original instruction.
            new_insts.push(inst_id);

            // Insert stores after the instruction.
            for store in stores {
                let store_id = InstId(func.insts.len() as u32);
                func.insts.push(store);
                new_insts.push(store_id);
            }
        }

        func.blocks[block_idx].insts = new_insts;
    }

    Ok(spill_infos)
}

fn plan_spill_slots(
    func: &MachFunction,
    spilled: &[VReg],
) -> Result<(StackSlotAllocationPlan, Vec<SpillInfo>), AllocError> {
    let mut slots = func.stack_slot_allocation_plan();
    let mut seen = BTreeSet::new();
    let mut infos = Vec::new();
    for &vreg in spilled {
        if seen.insert(vreg) {
            let size = vreg.class.size_bytes();
            let slot = slots
                .allocate(size, size)
                .ok_or(AllocError::StackSlotExhausted)?;
            infos.push(SpillInfo { vreg, slot });
        }
    }
    Ok((slots, infos))
}

/// Allocate metadata for the target-owned spill-code lane using the same slot
/// policy as generic pseudo insertion. Refusal does not commit a partial set.
pub(crate) fn allocate_spill_slots(
    func: &mut MachFunction,
    spilled: &[VReg],
) -> Result<Vec<SpillInfo>, AllocError> {
    let (slots, infos) = plan_spill_slots(func, spilled)?;
    slots.commit(func);
    Ok(infos)
}

/// Create a pseudo spill-load instruction: load VReg from stack slot.
fn make_spill_load(vreg: VReg, slot: StackSlotId) -> MachInst {
    MachInst {
        opcode: PSEUDO_SPILL_LOAD,
        defs: vec![MachOperand::VReg(vreg)],
        uses: vec![MachOperand::StackSlot(slot)],
        implicit_defs: Vec::new(),
        implicit_uses: Vec::new(),
        flags: InstFlags::READS_MEMORY,
        tied_operands: vec![],
    }
}

/// Create a pseudo spill-store instruction: store VReg to stack slot.
fn make_spill_store(vreg: VReg, slot: StackSlotId) -> MachInst {
    MachInst {
        opcode: PSEUDO_SPILL_STORE,
        defs: vec![],
        uses: vec![MachOperand::VReg(vreg), MachOperand::StackSlot(slot)],
        implicit_defs: Vec::new(),
        implicit_uses: Vec::new(),
        flags: InstFlags::WRITES_MEMORY,
        tied_operands: vec![],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine_types::RegClass;

    #[test]
    fn test_reg_class_sizes() {
        assert_eq!(RegClass::Gpr32.size_bytes(), 4);
        assert_eq!(RegClass::Gpr64.size_bytes(), 8);
        assert_eq!(RegClass::Fpr32.size_bytes(), 4);
        assert_eq!(RegClass::Fpr64.size_bytes(), 8);
        assert_eq!(RegClass::Fpr128.size_bytes(), 16);
        assert_eq!(RegClass::Fpr16.size_bytes(), 2);
        assert_eq!(RegClass::Fpr8.size_bytes(), 1);
        assert_eq!(RegClass::System.size_bytes(), 4);
    }

    /// Helper: build a simple single-block function where v0 is defined and used.
    fn make_simple_def_use() -> (MachFunction, BTreeMap<VReg, PReg>) {
        use crate::machine_types::*;
        let mut insts = Vec::new();

        // Inst 0: def v0 = imm 42
        let i0 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(VReg {
                id: 0,
                class: RegClass::Gpr64,
            })],
            uses: vec![MachOperand::Imm(42)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });

        // Inst 1: use v0
        let i1 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(VReg {
                id: 0,
                class: RegClass::Gpr64,
            })],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });

        let func = MachFunction {
            name: "simple_spill".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![i0, i1],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: std::collections::BTreeMap::new(),
        };

        let allocation = BTreeMap::new(); // v0 is spilled, not allocated
        (func, allocation)
    }

    #[test]
    fn slot_boundary_spill_exhaustion_preserves_function() {
        let (mut func, allocation) = make_simple_def_use();
        func.next_stack_slot = u32::MAX - 1;
        let before = format!("{func:?}");
        let spilled = [
            VReg::new(0, RegClass::Gpr64),
            VReg::new(1, RegClass::Fpr128),
        ];
        assert!(matches!(
            insert_spill_code(&mut func, &spilled, &allocation),
            Err(AllocError::StackSlotExhausted)
        ));
        assert_eq!(format!("{func:?}"), before);
    }

    #[test]
    fn slot_boundary_spill_does_not_overwrite_existing_slot() {
        let (mut func, allocation) = make_simple_def_use();
        func.stack_slots.insert(
            StackSlotId(0),
            crate::machine_types::RegAllocStackSlot::new(32, 32),
        );
        let original_slot = format!("{:?}", func.stack_slots[&StackSlotId(0)]);
        insert_spill_code(&mut func, &[VReg::new(0, RegClass::Gpr64)], &allocation).unwrap();
        assert_eq!(
            format!("{:?}", func.stack_slots[&StackSlotId(0)]),
            original_slot
        );
        assert_eq!(func.stack_slots.len(), 2);
    }

    #[test]
    fn slot_boundary_repeated_spill_uses_one_slot_and_one_record() {
        let (mut func, allocation) = make_simple_def_use();
        let v0 = VReg::new(0, RegClass::Gpr64);
        let infos = insert_spill_code(&mut func, &[v0, v0], &allocation).unwrap();
        assert_eq!(infos.len(), 1);
        assert_eq!(func.stack_slots.len(), 1);
        assert_eq!(func.next_stack_slot, 1);
    }

    #[test]
    fn slot_boundary_spill_last_slot_emits_matching_store_and_load() {
        let (mut func, allocation) = make_simple_def_use();
        func.next_stack_slot = u32::MAX - 1;
        let v0 = VReg::new(0, RegClass::Gpr64);
        let infos = insert_spill_code(&mut func, &[v0, v0], &allocation).unwrap();
        let slot = StackSlotId(u32::MAX - 1);
        assert_eq!(infos.len(), 1);
        assert_eq!(infos[0].slot, slot);
        assert_eq!(func.next_stack_slot, u32::MAX);
        let insts: Vec<_> = func.blocks[0]
            .insts
            .iter()
            .map(|id| &func.insts[id.0 as usize])
            .collect();
        assert_eq!(
            insts.iter().map(|inst| inst.opcode).collect::<Vec<_>>(),
            [1, PSEUDO_SPILL_STORE, PSEUDO_SPILL_LOAD, 2]
        );
        assert_eq!(
            insts[1].uses,
            [MachOperand::VReg(v0), MachOperand::StackSlot(slot)]
        );
        assert_eq!(insts[2].defs, [MachOperand::VReg(v0)]);
        assert_eq!(insts[2].uses, [MachOperand::StackSlot(slot)]);
    }

    #[test]
    fn slot_boundary_metadata_only_exhaustion_preserves_function() {
        let (mut func, _) = make_simple_def_use();
        func.next_stack_slot = u32::MAX - 1;
        let before = format!("{func:?}");
        let spilled = [
            VReg::new(0, RegClass::Gpr64),
            VReg::new(1, RegClass::Fpr128),
        ];
        assert!(matches!(
            allocate_spill_slots(&mut func, &spilled),
            Err(AllocError::StackSlotExhausted)
        ));
        assert_eq!(format!("{func:?}"), before);
    }

    #[test]
    fn slot_boundary_metadata_only_matches_pseudo_policy_for_all_classes() {
        let (mut metadata, allocation) = make_simple_def_use();
        metadata.stack_slots.insert(
            StackSlotId(4),
            crate::machine_types::RegAllocStackSlot::new(32, 32),
        );
        let mut pseudos = metadata.clone();
        let classes_and_sizes = [
            (RegClass::Gpr32, 4),
            (RegClass::Gpr64, 8),
            (RegClass::Fpr8, 1),
            (RegClass::Fpr16, 2),
            (RegClass::Fpr32, 4),
            (RegClass::Fpr64, 8),
            (RegClass::Fpr128, 16),
            (RegClass::System, 4),
        ];
        // Same numeric ID but distinct register classes remain distinct VRegs.
        let mut spilled: Vec<_> = classes_and_sizes
            .iter()
            .map(|&(class, _)| VReg::new(0, class))
            .collect();
        spilled.push(spilled[0]);
        let before_insts = format!("{:?}", metadata.insts);
        let before_blocks = format!("{:?}", metadata.blocks);
        let infos = allocate_spill_slots(&mut metadata, &spilled).unwrap();
        let pseudo_infos = insert_spill_code(&mut pseudos, &spilled, &allocation).unwrap();
        assert_eq!(infos.len(), 8);
        for (i, (info, &(class, size))) in infos.iter().zip(&classes_and_sizes).enumerate() {
            assert_eq!(info.vreg, VReg::new(0, class));
            assert_eq!(info.slot, StackSlotId(5 + i as u32));
            assert_eq!(info.slot, pseudo_infos[i].slot);
            assert_eq!(metadata.stack_slots[&info.slot].size, size);
            assert_eq!(metadata.stack_slots[&info.slot].align, size);
        }
        assert_eq!(
            format!("{:?}", metadata.stack_slots),
            format!("{:?}", pseudos.stack_slots)
        );
        assert_eq!(format!("{:?}", metadata.insts), before_insts);
        assert_eq!(format!("{:?}", metadata.blocks), before_blocks);
    }

    #[test]
    fn slot_boundary_empty_spill_requests_succeed_at_capacity() {
        let (mut func, allocation) = make_simple_def_use();
        func.next_stack_slot = u32::MAX;
        let before = format!("{func:?}");
        assert!(allocate_spill_slots(&mut func, &[]).unwrap().is_empty());
        assert!(
            insert_spill_code(&mut func, &[], &allocation)
                .unwrap()
                .is_empty()
        );
        assert_eq!(format!("{func:?}"), before);
    }

    #[test]
    fn test_insert_spill_code_allocates_stack_slot() {
        let (mut func, allocation) = make_simple_def_use();
        let v0 = VReg {
            id: 0,
            class: RegClass::Gpr64,
        };

        let spill_infos = insert_spill_code(&mut func, &[v0], &allocation).unwrap();

        assert_eq!(spill_infos.len(), 1);
        assert_eq!(spill_infos[0].vreg, v0);
        // Stack slot should have been allocated.
        assert!(func.stack_slots.contains_key(&spill_infos[0].slot));
        let slot = &func.stack_slots[&spill_infos[0].slot];
        assert_eq!(slot.size, 8); // Gpr64 = 8 bytes
        assert_eq!(slot.align, 8);
    }

    #[test]
    fn test_insert_spill_code_inserts_load_and_store() {
        let (mut func, allocation) = make_simple_def_use();
        let v0 = VReg {
            id: 0,
            class: RegClass::Gpr64,
        };

        insert_spill_code(&mut func, &[v0], &allocation).unwrap();

        // After spill insertion, the block should have more instructions:
        // - Before use of v0: a PSEUDO_SPILL_LOAD
        // - After def of v0: a PSEUDO_SPILL_STORE
        let block = &func.blocks[0];
        assert!(
            block.insts.len() > 2,
            "should have inserted spill load/store, got {} insts",
            block.insts.len()
        );

        // Find load and store pseudo-ops.
        let has_load = block
            .insts
            .iter()
            .any(|&id| func.insts[id.0 as usize].opcode == PSEUDO_SPILL_LOAD);
        let has_store = block
            .insts
            .iter()
            .any(|&id| func.insts[id.0 as usize].opcode == PSEUDO_SPILL_STORE);
        assert!(has_load, "should have inserted a spill load");
        assert!(has_store, "should have inserted a spill store");
    }

    #[test]
    fn test_insert_spill_code_load_before_use() {
        let (mut func, allocation) = make_simple_def_use();
        let v0 = VReg {
            id: 0,
            class: RegClass::Gpr64,
        };

        insert_spill_code(&mut func, &[v0], &allocation).unwrap();

        let block = &func.blocks[0];
        // Find positions of load and the original use instruction.
        let load_pos = block
            .insts
            .iter()
            .position(|&id| func.insts[id.0 as usize].opcode == PSEUDO_SPILL_LOAD);
        let use_pos = block.insts.iter().position(|&id| {
            func.insts[id.0 as usize].opcode == 2 // the original "use v0" instruction
        });

        assert!(load_pos.is_some(), "should have a spill load");
        assert!(use_pos.is_some(), "should have original use instruction");
        assert!(
            load_pos.unwrap() < use_pos.unwrap(),
            "spill load should come before the use"
        );
    }

    #[test]
    fn test_insert_spill_code_store_after_def() {
        let (mut func, allocation) = make_simple_def_use();
        let v0 = VReg {
            id: 0,
            class: RegClass::Gpr64,
        };

        insert_spill_code(&mut func, &[v0], &allocation).unwrap();

        let block = &func.blocks[0];
        // Find positions of the original def and the store.
        let def_pos = block.insts.iter().position(|&id| {
            func.insts[id.0 as usize].opcode == 1 // the original "def v0" instruction
        });
        let store_pos = block
            .insts
            .iter()
            .position(|&id| func.insts[id.0 as usize].opcode == PSEUDO_SPILL_STORE);

        assert!(def_pos.is_some(), "should have original def instruction");
        assert!(store_pos.is_some(), "should have a spill store");
        assert!(
            store_pos.unwrap() > def_pos.unwrap(),
            "spill store should come after the def"
        );
    }

    #[test]
    fn test_insert_spill_code_multiple_vregs() {
        use crate::machine_types::*;
        let mut insts = Vec::new();

        // def v0, def v1, use v0, use v1
        let i0 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(VReg {
                id: 0,
                class: RegClass::Gpr64,
            })],
            uses: vec![MachOperand::Imm(1)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i1 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(VReg {
                id: 1,
                class: RegClass::Fpr64,
            })],
            uses: vec![MachOperand::FImm(2.78)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i2 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![
                MachOperand::VReg(VReg {
                    id: 0,
                    class: RegClass::Gpr64,
                }),
                MachOperand::VReg(VReg {
                    id: 1,
                    class: RegClass::Fpr64,
                }),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });

        let mut func = MachFunction {
            name: "multi_spill".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![i0, i1, i2],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 2,
            next_stack_slot: 0,
            stack_slots: std::collections::BTreeMap::new(),
        };

        let v0 = VReg {
            id: 0,
            class: RegClass::Gpr64,
        };
        let v1 = VReg {
            id: 1,
            class: RegClass::Fpr64,
        };

        let spill_infos = insert_spill_code(&mut func, &[v0, v1], &BTreeMap::new()).unwrap();

        assert_eq!(spill_infos.len(), 2);
        // Different register classes should get slots of different sizes.
        let slot0 = &func.stack_slots[&spill_infos[0].slot];
        let slot1 = &func.stack_slots[&spill_infos[1].slot];
        assert_eq!(slot0.size, 8); // Gpr64
        assert_eq!(slot1.size, 8); // Fpr64

        // Each spilled vreg should get its own unique slot.
        assert_ne!(spill_infos[0].slot, spill_infos[1].slot);
    }

    #[test]
    fn test_insert_spill_code_matches_full_vreg_identity() {
        use crate::machine_types::*;

        let gpr_v0 = VReg {
            id: 0,
            class: RegClass::Gpr64,
        };
        let fpr_v0 = VReg {
            id: 0,
            class: RegClass::Fpr64,
        };

        let mut insts = Vec::new();
        let gpr_def = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(gpr_v0)],
            uses: vec![MachOperand::Imm(1)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });

        let fpr_def = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![MachOperand::VReg(fpr_v0)],
            uses: vec![MachOperand::FImm(2.0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });

        let use_both = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 3,
            defs: vec![],
            uses: vec![MachOperand::VReg(gpr_v0), MachOperand::VReg(fpr_v0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });

        let mut func = MachFunction {
            name: "class_exact_spill".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![gpr_def, fpr_def, use_both],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: std::collections::BTreeMap::new(),
        };

        let spill_infos = insert_spill_code(&mut func, &[gpr_v0], &BTreeMap::new()).unwrap();

        assert_eq!(spill_infos.len(), 1);
        assert_eq!(spill_infos[0].vreg, gpr_v0);

        let gpr_spill_ops = func
            .insts
            .iter()
            .filter(|inst| {
                matches!(inst.opcode, PSEUDO_SPILL_LOAD | PSEUDO_SPILL_STORE)
                    && inst
                        .defs
                        .iter()
                        .chain(inst.uses.iter())
                        .any(|op| op.as_vreg() == Some(gpr_v0))
            })
            .count();
        let fpr_spill_ops = func
            .insts
            .iter()
            .filter(|inst| {
                matches!(inst.opcode, PSEUDO_SPILL_LOAD | PSEUDO_SPILL_STORE)
                    && inst
                        .defs
                        .iter()
                        .chain(inst.uses.iter())
                        .any(|op| op.as_vreg() == Some(fpr_v0))
            })
            .count();

        assert_eq!(gpr_spill_ops, 2);
        assert_eq!(
            fpr_spill_ops, 0,
            "same numeric id in a different class must not be spilled"
        );
    }

    #[test]
    fn test_insert_spill_code_no_spills() {
        let (mut func, allocation) = make_simple_def_use();
        // No spilled vregs — nothing should happen.
        let spill_infos = insert_spill_code(&mut func, &[], &allocation).unwrap();
        assert!(spill_infos.is_empty());
        // Block should be unchanged.
        assert_eq!(func.blocks[0].insts.len(), 2);
    }

    #[test]
    fn test_spill_load_has_correct_flags() {
        let v = VReg {
            id: 0,
            class: RegClass::Gpr64,
        };
        let slot = StackSlotId(0);
        let load = make_spill_load(v, slot);

        assert_eq!(load.opcode, PSEUDO_SPILL_LOAD);
        assert!(load.flags.reads_memory());
        assert_eq!(load.defs.len(), 1);
        assert_eq!(load.defs[0].as_vreg(), Some(v));
        assert_eq!(load.uses.len(), 1);
        assert_eq!(load.uses[0], MachOperand::StackSlot(slot));
    }

    #[test]
    fn test_spill_store_has_correct_flags() {
        let v = VReg {
            id: 0,
            class: RegClass::Gpr64,
        };
        let slot = StackSlotId(0);
        let store = make_spill_store(v, slot);

        assert_eq!(store.opcode, PSEUDO_SPILL_STORE);
        assert!(store.flags.writes_memory());
        assert!(store.defs.is_empty());
        assert_eq!(store.uses.len(), 2);
        assert_eq!(store.uses[0].as_vreg(), Some(v));
        assert_eq!(store.uses[1], MachOperand::StackSlot(slot));
    }

    #[test]
    fn test_insert_spill_code_multi_block() {
        use crate::machine_types::*;
        let mut insts = Vec::new();

        // Block 0: def v0, branch -> block 1
        let i0 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(VReg {
                id: 0,
                class: RegClass::Gpr64,
            })],
            uses: vec![MachOperand::Imm(42)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i1 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(1))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });

        // Block 1: use v0
        let i2 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(VReg {
                id: 0,
                class: RegClass::Gpr64,
            })],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });

        let mut func = MachFunction {
            name: "multi_block_spill".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![i0, i1],
                    preds: Vec::new(),
                    succs: vec![BlockId(1)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i2],
                    preds: vec![BlockId(0)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: std::collections::BTreeMap::new(),
        };

        let v0 = VReg {
            id: 0,
            class: RegClass::Gpr64,
        };
        let spill_infos = insert_spill_code(&mut func, &[v0], &BTreeMap::new()).unwrap();

        assert_eq!(spill_infos.len(), 1);

        // Block 0 should have a store after the def.
        let block0_has_store = func.blocks[0]
            .insts
            .iter()
            .any(|&id| func.insts[id.0 as usize].opcode == PSEUDO_SPILL_STORE);
        assert!(
            block0_has_store,
            "block 0 should have a spill store after def"
        );

        // Block 1 should have a load before the use.
        let block1_has_load = func.blocks[1]
            .insts
            .iter()
            .any(|&id| func.insts[id.0 as usize].opcode == PSEUDO_SPILL_LOAD);
        assert!(
            block1_has_load,
            "block 1 should have a spill load before use"
        );
    }

    // -----------------------------------------------------------------------
    // Additional edge-case and correctness tests (issue #139)
    // -----------------------------------------------------------------------

    #[test]
    fn test_reg_class_size_all_classes() {
        // Exhaustive: every RegClass variant must have a sensible size.
        assert_eq!(RegClass::Gpr32.size_bytes(), 4);
        assert_eq!(RegClass::Gpr64.size_bytes(), 8);
        assert_eq!(RegClass::Fpr8.size_bytes(), 1);
        assert_eq!(RegClass::Fpr16.size_bytes(), 2);
        assert_eq!(RegClass::Fpr32.size_bytes(), 4);
        assert_eq!(RegClass::Fpr64.size_bytes(), 8);
        assert_eq!(RegClass::Fpr128.size_bytes(), 16);
        assert_eq!(RegClass::System.size_bytes(), 4);
    }

    #[test]
    fn test_spill_code_instruction_ordering_invariant() {
        // After spill insertion, for each original instruction:
        // loads come before it, stores come after it.
        // This is a structural correctness invariant.
        let (mut func, allocation) = make_simple_def_use();
        let v0 = VReg {
            id: 0,
            class: RegClass::Gpr64,
        };

        insert_spill_code(&mut func, &[v0], &allocation).unwrap();

        let block = &func.blocks[0];
        let opcodes: Vec<u16> = block
            .insts
            .iter()
            .map(|&id| func.insts[id.0 as usize].opcode)
            .collect();

        // Expected order: [def_v0, STORE, LOAD, use_v0]
        // (store after def, load before use)
        let def_pos = opcodes.iter().position(|&op| op == 1).unwrap();
        let store_pos = opcodes
            .iter()
            .position(|&op| op == PSEUDO_SPILL_STORE)
            .unwrap();
        let load_pos = opcodes
            .iter()
            .position(|&op| op == PSEUDO_SPILL_LOAD)
            .unwrap();
        let use_pos = opcodes.iter().position(|&op| op == 2).unwrap();

        assert!(def_pos < store_pos, "store must come after def");
        assert!(load_pos < use_pos, "load must come before use");
        assert!(
            store_pos < load_pos,
            "store should come before load (def before use)"
        );
    }

    #[test]
    fn test_spill_code_def_and_use_same_instruction() {
        // An instruction that both defines and uses v0 should get both
        // a load (for the use) and a store (for the def).
        use crate::machine_types::*;
        let mut insts = Vec::new();

        // inst 0: v0 = v0 + 1 (both def and use of v0)
        let i0 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(VReg {
                id: 0,
                class: RegClass::Gpr64,
            })],
            uses: vec![
                MachOperand::VReg(VReg {
                    id: 0,
                    class: RegClass::Gpr64,
                }),
                MachOperand::Imm(1),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });

        let mut func = MachFunction {
            name: "def_use_same".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![i0],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: std::collections::BTreeMap::new(),
        };

        let v0 = VReg {
            id: 0,
            class: RegClass::Gpr64,
        };
        insert_spill_code(&mut func, &[v0], &BTreeMap::new()).unwrap();

        let block = &func.blocks[0];
        let has_load = block
            .insts
            .iter()
            .any(|&id| func.insts[id.0 as usize].opcode == PSEUDO_SPILL_LOAD);
        let has_store = block
            .insts
            .iter()
            .any(|&id| func.insts[id.0 as usize].opcode == PSEUDO_SPILL_STORE);

        assert!(has_load, "should insert load for the use of v0");
        assert!(has_store, "should insert store for the def of v0");
    }

    #[test]
    fn test_spill_multiple_uses_in_single_instruction() {
        // An instruction that uses v0 twice should get one load
        // (the scan is per-use, so may get two loads).
        use crate::machine_types::*;
        let mut insts = Vec::new();

        let i0 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(VReg {
                id: 0,
                class: RegClass::Gpr64,
            })],
            uses: vec![MachOperand::Imm(42)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i1 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![
                MachOperand::VReg(VReg {
                    id: 0,
                    class: RegClass::Gpr64,
                }),
                MachOperand::VReg(VReg {
                    id: 0,
                    class: RegClass::Gpr64,
                }),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });

        let mut func = MachFunction {
            name: "multi_use".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![i0, i1],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: std::collections::BTreeMap::new(),
        };

        let v0 = VReg {
            id: 0,
            class: RegClass::Gpr64,
        };
        insert_spill_code(&mut func, &[v0], &BTreeMap::new()).unwrap();

        // Should have at least one load before the double-use instruction.
        let load_count = func.blocks[0]
            .insts
            .iter()
            .filter(|&&id| func.insts[id.0 as usize].opcode == PSEUDO_SPILL_LOAD)
            .count();
        // Two VReg uses of v0 means two loads (one per operand scan).
        assert!(
            load_count >= 2,
            "should have load(s) for double-use: got {load_count}"
        );
    }

    #[test]
    fn test_spill_fpr128_slot_size() {
        // FPR128 should allocate a 16-byte stack slot.
        use crate::machine_types::*;
        let mut insts = Vec::new();

        let i0 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(VReg {
                id: 0,
                class: RegClass::Fpr128,
            })],
            uses: vec![MachOperand::FImm(0.0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i1 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(VReg {
                id: 0,
                class: RegClass::Fpr128,
            })],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });

        let mut func = MachFunction {
            name: "fpr128_spill".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![i0, i1],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: std::collections::BTreeMap::new(),
        };

        let v0 = VReg {
            id: 0,
            class: RegClass::Fpr128,
        };
        let spill_infos = insert_spill_code(&mut func, &[v0], &BTreeMap::new()).unwrap();

        assert_eq!(spill_infos.len(), 1);
        let slot = &func.stack_slots[&spill_infos[0].slot];
        assert_eq!(slot.size, 16, "Fpr128 should use 16-byte slot");
        assert_eq!(slot.align, 16, "Fpr128 should use 16-byte alignment");
    }

    #[test]
    fn test_spill_preserves_non_spilled_instructions() {
        // Instructions that do not use/define spilled VRegs should be
        // unchanged after spill insertion.
        use crate::machine_types::*;
        let mut insts = Vec::new();

        let i0 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(VReg {
                id: 0,
                class: RegClass::Gpr64,
            })],
            uses: vec![MachOperand::Imm(42)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        // Non-spilled instruction.
        let i1 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 99,
            defs: vec![MachOperand::VReg(VReg {
                id: 1,
                class: RegClass::Gpr64,
            })],
            uses: vec![MachOperand::Imm(7)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i2 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(VReg {
                id: 0,
                class: RegClass::Gpr64,
            })],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });

        let mut func = MachFunction {
            name: "preserve_non_spilled".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![i0, i1, i2],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 2,
            next_stack_slot: 0,
            stack_slots: std::collections::BTreeMap::new(),
        };

        let v0 = VReg {
            id: 0,
            class: RegClass::Gpr64,
        };
        insert_spill_code(&mut func, &[v0], &BTreeMap::new()).unwrap();

        // The non-spilled instruction (opcode 99) should still be in the block.
        let has_non_spilled = func.blocks[0]
            .insts
            .iter()
            .any(|&id| func.insts[id.0 as usize].opcode == 99);
        assert!(
            has_non_spilled,
            "non-spilled instruction should be preserved"
        );
    }

    #[test]
    fn test_spill_unique_stack_slots() {
        // Three spilled VRegs should each get their own unique stack slot.
        use crate::machine_types::*;
        let mut insts = Vec::new();

        for id in 0..3u32 {
            let _inst_id = InstId(insts.len() as u32);
            insts.push(MachInst {
                opcode: 1,
                defs: vec![MachOperand::VReg(VReg {
                    id,
                    class: RegClass::Gpr64,
                })],
                uses: vec![MachOperand::Imm(id as i64)],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            });
        }
        for id in 0..3u32 {
            let _inst_id = InstId(insts.len() as u32);
            insts.push(MachInst {
                opcode: 2,
                defs: vec![],
                uses: vec![MachOperand::VReg(VReg {
                    id,
                    class: RegClass::Gpr64,
                })],
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            });
        }

        let inst_ids: Vec<InstId> = (0..6).map(InstId).collect();
        let mut func = MachFunction {
            name: "triple_spill".into(),
            insts,
            blocks: vec![MachBlock {
                insts: inst_ids,
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 3,
            next_stack_slot: 0,
            stack_slots: std::collections::BTreeMap::new(),
        };

        let vregs: Vec<VReg> = (0..3)
            .map(|id| VReg {
                id,
                class: RegClass::Gpr64,
            })
            .collect();
        let spill_infos = insert_spill_code(&mut func, &vregs, &BTreeMap::new()).unwrap();

        assert_eq!(spill_infos.len(), 3);
        let slots: std::collections::BTreeSet<StackSlotId> =
            spill_infos.iter().map(|si| si.slot).collect();
        assert_eq!(
            slots.len(),
            3,
            "each spilled vreg should have a unique slot"
        );
    }

    // -----------------------------------------------------------------------
    // Additional edge-case tests (issue #404 — TL7 coverage expansion)
    // -----------------------------------------------------------------------

    #[test]
    fn test_spill_fpr16_and_fpr8_slot_sizes() {
        // Fpr16 should allocate a 2-byte slot, Fpr8 a 1-byte slot.
        use crate::machine_types::*;
        let mut insts = Vec::new();

        // def v0 (Fpr16), def v1 (Fpr8)
        let i0 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(VReg {
                id: 0,
                class: RegClass::Fpr16,
            })],
            uses: vec![MachOperand::FImm(0.0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i1 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(VReg {
                id: 1,
                class: RegClass::Fpr8,
            })],
            uses: vec![MachOperand::FImm(0.0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        // use v0, use v1
        let i2 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![
                MachOperand::VReg(VReg {
                    id: 0,
                    class: RegClass::Fpr16,
                }),
                MachOperand::VReg(VReg {
                    id: 1,
                    class: RegClass::Fpr8,
                }),
            ],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });

        let mut func = MachFunction {
            name: "fpr_small_spill".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![i0, i1, i2],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 2,
            next_stack_slot: 0,
            stack_slots: std::collections::BTreeMap::new(),
        };

        let v0 = VReg {
            id: 0,
            class: RegClass::Fpr16,
        };
        let v1 = VReg {
            id: 1,
            class: RegClass::Fpr8,
        };
        let spill_infos = insert_spill_code(&mut func, &[v0, v1], &BTreeMap::new()).unwrap();

        assert_eq!(spill_infos.len(), 2);
        let slot0 = &func.stack_slots[&spill_infos[0].slot];
        let slot1 = &func.stack_slots[&spill_infos[1].slot];
        assert_eq!(slot0.size, 2, "Fpr16 should use 2-byte slot");
        assert_eq!(slot0.align, 2, "Fpr16 should use 2-byte alignment");
        assert_eq!(slot1.size, 1, "Fpr8 should use 1-byte slot");
        assert_eq!(slot1.align, 1, "Fpr8 should use 1-byte alignment");
    }

    #[test]
    fn test_spill_three_blocks_def_in_first_use_in_last() {
        // v0 defined in block 0, used in block 2 (block 1 is intermediate).
        // Spill should insert store in block 0 after def, load in block 2 before use.
        use crate::machine_types::*;
        let mut insts = Vec::new();

        // Block 0: def v0
        let i0 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(VReg {
                id: 0,
                class: RegClass::Gpr64,
            })],
            uses: vec![MachOperand::Imm(42)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i1 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(1))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });

        // Block 1: intermediate (nop, branch to block 2)
        let i2 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0x00,
            defs: vec![],
            uses: vec![],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i3 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 0xBA,
            defs: vec![],
            uses: vec![MachOperand::Block(BlockId(2))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        });

        // Block 2: use v0
        let i4 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(VReg {
                id: 0,
                class: RegClass::Gpr64,
            })],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });

        let mut func = MachFunction {
            name: "three_block_spill".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![i0, i1],
                    preds: Vec::new(),
                    succs: vec![BlockId(1)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i2, i3],
                    preds: vec![BlockId(0)],
                    succs: vec![BlockId(2)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![i4],
                    preds: vec![BlockId(1)],
                    succs: Vec::new(),
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: std::collections::BTreeMap::new(),
        };

        let v0 = VReg {
            id: 0,
            class: RegClass::Gpr64,
        };
        insert_spill_code(&mut func, &[v0], &BTreeMap::new()).unwrap();

        // Block 0 should have a store after the def.
        let block0_has_store = func.blocks[0]
            .insts
            .iter()
            .any(|&id| func.insts[id.0 as usize].opcode == PSEUDO_SPILL_STORE);
        assert!(block0_has_store, "block 0 should have spill store");

        // Block 1 should NOT have any spill instructions (no def/use of v0).
        let block1_spill_count = func.blocks[1]
            .insts
            .iter()
            .filter(|&&id| {
                let op = func.insts[id.0 as usize].opcode;
                op == PSEUDO_SPILL_STORE || op == PSEUDO_SPILL_LOAD
            })
            .count();
        assert_eq!(
            block1_spill_count, 0,
            "block 1 should have no spill instructions"
        );

        // Block 2 should have a load before the use.
        let block2_has_load = func.blocks[2]
            .insts
            .iter()
            .any(|&id| func.insts[id.0 as usize].opcode == PSEUDO_SPILL_LOAD);
        assert!(block2_has_load, "block 2 should have spill load");
    }

    #[test]
    fn test_spill_system_reg_class_slot_size() {
        // System register class should get a 4-byte slot.
        use crate::machine_types::*;
        let mut insts = Vec::new();

        let i0 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 1,
            defs: vec![MachOperand::VReg(VReg {
                id: 0,
                class: RegClass::System,
            })],
            uses: vec![MachOperand::Imm(0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });
        let i1 = InstId(insts.len() as u32);
        insts.push(MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(VReg {
                id: 0,
                class: RegClass::System,
            })],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        });

        let mut func = MachFunction {
            name: "system_spill".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![i0, i1],
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 1,
            next_stack_slot: 0,
            stack_slots: std::collections::BTreeMap::new(),
        };

        let v0 = VReg {
            id: 0,
            class: RegClass::System,
        };
        let spill_infos = insert_spill_code(&mut func, &[v0], &BTreeMap::new()).unwrap();

        assert_eq!(spill_infos.len(), 1);
        let slot = &func.stack_slots[&spill_infos[0].slot];
        assert_eq!(slot.size, 4, "System should use 4-byte slot");
    }
}
