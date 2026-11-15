// Exact Invoke custody through the real allocator adapter/rebuild seam.
// Author: Andrew Yates. Copyright 2026 Andrew Yates. Apache-2.0.

use super::*;

#[test]
fn genuine_allocator_spill_staging_keeps_the_original_selected_slot_owner() {
    let mut f = fixture();
    let value = VReg::new(f.func.alloc_vreg(), RegClass::Gpr64);
    f.func.insts[0] = IrMachInst::new(
        IrOpcode::MovI,
        vec![IrOperand::VReg(value), IrOperand::Imm(7)],
    );
    let use_value = f.func.push_inst(IrMachInst::new(
        IrOpcode::MovR,
        vec![IrOperand::PReg(X0), IrOperand::VReg(value)],
    ));
    f.func.block_mut(f.func.entry).insts.insert(1, use_value);
    let mut allocated = ir_to_regalloc(&f.func).unwrap();
    let original_count = allocated.insts.len();
    let spills =
        trust_cg_regalloc::spill::insert_spill_code(&mut allocated, &[value], &BTreeMap::new())
            .unwrap();
    assert_eq!(spills.len(), 1);
    assert_eq!(allocated.insts.len(), original_count + 2);
    assert_eq!(
        allocated.insts[f.selected.0 as usize].opcode,
        IrOpcode::Bl as u16
    );
    let map = rebuild_ir_from_regalloc_with_map(&mut f.func, &allocated).unwrap();
    assert_eq!(map.iter().filter(|id| id.is_none()).count(), 2);
    let actual = bindings(&mut f)[0];
    assert_eq!(actual.call_inst, map[f.selected.0 as usize].unwrap());
    assert_eq!(actual.call_block, f.func.entry);
    assert_eq!(actual.landing_pad_block, f.pad);
    assert!(
        f.func
            .block(actual.call_block)
            .insts
            .contains(&actual.call_inst)
    );
    assert_eq!(
        f.func.insts[actual.call_inst.0 as usize].operands,
        vec![IrOperand::Symbol("same_may_unwind".into())]
    );
    f.offsets = HashMap::from([(f.func.entry, 0), (f.normal, 20), (f.pad, 24)]);
    f.len = 28;
    resolve(&mut f, &EhPropagation::Filler).unwrap();
    assert_eq!(
        sites(&f.func),
        vec![(0, 12, None), (12, 4, Some(f.pad)), (16, 12, None)]
    );
    // This exercises the real generic pseudo/rebuild seam, not physical
    // allocation, materialized native spill semantics, or a proof claim.
}

#[test]
fn allocator_deletion_or_owner_change_cannot_rebind_to_an_identical_helper() {
    let mut attempted = 0;
    for mutation in 0..4 {
        let mut f = fixture();
        let original = format!("{:?}", f.func);
        let mut allocated = ir_to_regalloc(&f.func).unwrap();
        match mutation {
            0 => {
                allocated.blocks[f.func.entry.0 as usize]
                    .insts
                    .retain(|id| *id != f.selected);
                allocated.blocks[f.normal.0 as usize]
                    .insts
                    .insert(0, f.selected);
            }
            1 => allocated.insts[f.selected.0 as usize].opcode = 0xffff,
            2 => {
                let uses = &mut allocated.insts[f.selected.0 as usize].uses;
                let opaque = uses
                    .iter()
                    .position(|operand| {
                        matches!(operand, trust_cg_regalloc::RegAllocOperand::Imm(0))
                    })
                    .expect("real adapter spells the original selected Symbol as Imm(0)");
                uses[opaque] = trust_cg_regalloc::RegAllocOperand::Imm(7);
            }
            3 => {
                let uses = &mut allocated.insts[f.selected.0 as usize].uses;
                assert!(
                    !uses.is_empty(),
                    "real selected call has its opaque callee operand"
                );
                uses.clear();
            }
            _ => unreachable!(),
        }
        let error = rebuild_ir_from_regalloc_with_map(&mut f.func, &allocated).unwrap_err();
        assert!(
            matches!(error, PipelineError::MalformedAarch64Eh { .. }),
            "{error}"
        );
        assert_eq!(
            format!("{:?}", f.func),
            original,
            "failed remap must not publish any partial owner"
        );
        attempted += 1;
    }
    assert_eq!(
        attempted, 4,
        "all authentic allocator-slot corruptions execute"
    );
}
