use super::*;
use trust_cg_ir::function::{EhInvokeBinding, LandingPadEntry, Signature};

fn fixture() -> (MachFunction, EhInvokeBinding, BlockId) {
    let mut func = MachFunction::new("probe_invoke".into(), Signature::new(vec![], vec![]));
    let normal = func.create_block();
    let pad = func.create_block();
    let helper = func.push_inst(MachInst::new(
        AArch64Opcode::Bl,
        vec![MachOperand::Symbol("memmove".into())],
    ));
    let call = func.push_inst(MachInst::new(
        AArch64Opcode::Bl,
        vec![MachOperand::Symbol("invoke".into())],
    ));
    let branch = func.push_inst(MachInst::new(
        AArch64Opcode::B,
        vec![MachOperand::Block(normal)],
    ));
    for id in [helper, call, branch] {
        func.append_inst(func.entry, id);
    }
    for block in [normal, pad] {
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(block, ret);
    }
    func.add_edge(func.entry, normal);
    func.add_edge(func.entry, pad);
    let binding = EhInvokeBinding {
        call_inst: call,
        call_block: func.entry,
        landing_pad_block: pad,
    };
    func.eh_metadata.personality = Some("personality".into());
    func.eh_metadata.call_sites.push(EhCallSiteEntry {
        call_block: func.entry,
        start_offset: 0,
        length: 0,
        landing_pad_block: Some(pad),
    });
    func.eh_metadata.landing_pads.push(LandingPadEntry {
        block: pad,
        offset: 0,
        catch_type_indices: vec![],
        is_cleanup: true,
    });
    func.eh_metadata.call_site_bindings = EhCallSiteBindings::ExactInstructions(vec![binding]);
    (func, binding, normal)
}

#[test]
fn frame_split_tracks_the_exact_call_and_exception_edge_in_either_half() {
    for split in 0..=3 {
        let (mut func, binding, normal) = fixture();
        let original = format!("{func:?}");
        let mut plan = FrameInsertionPlan::new(&func).unwrap();
        let tail = plan.split_block_tail(&func, func.entry, split).unwrap();
        let owner = if split <= 1 { tail } else { func.entry };
        let other = if owner == tail { func.entry } else { tail };
        assert_eq!(plan.eh_call_sites[0].call_block, owner);
        assert_eq!(
            plan.eh_call_site_bindings,
            EhCallSiteBindings::ExactInstructions(vec![EhInvokeBinding {
                call_block: owner,
                ..binding
            },])
        );
        assert!(
            plan.blocks[owner.0 as usize]
                .succs
                .contains(&binding.landing_pad_block)
        );
        assert!(
            !plan.blocks[other.0 as usize]
                .succs
                .contains(&binding.landing_pad_block)
        );
        assert_eq!(
            plan.blocks[binding.landing_pad_block.0 as usize].preds,
            vec![owner]
        );
        assert!(
            plan.blocks[owner.0 as usize]
                .insts
                .contains(&binding.call_inst)
        );
        assert!(
            plan.blocks[func.entry.0 as usize].succs.contains(&normal)
                || plan.blocks[tail.0 as usize].succs.contains(&normal)
        );
        assert_eq!(format!("{func:?}"), original, "planning changed its owner");
        plan.commit(&mut func).unwrap();
        assert_eq!(func.eh_metadata.call_sites[0].call_block, owner);
        assert_eq!(
            func.eh_metadata.call_site_bindings,
            EhCallSiteBindings::ExactInstructions(vec![EhInvokeBinding {
                call_block: owner,
                ..binding
            },])
        );
        crate::pipeline::validate_exact_aarch64_eh_call_identity(&func).unwrap();
    }
}

#[test]
fn legacy_two_call_split_still_refuses_and_keeps_the_source_unchanged() {
    let (mut func, _, _) = fixture();
    func.eh_metadata.call_site_bindings = EhCallSiteBindings::LegacyBlocks;
    let original = format!("{func:?}");
    let mut plan = FrameInsertionPlan::new(&func).unwrap();
    let error = plan.split_block_tail(&func, func.entry, 1).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("separated from its landing-pad edge")
    );
    assert_eq!(format!("{func:?}"), original);
}

#[test]
fn frame_preflight_refuses_missing_orphan_duplicate_wrong_owner_and_noncall() {
    for mutation in 0..6 {
        let (mut func, binding, _) = fixture();
        match mutation {
            0 => {
                func.eh_metadata.call_site_bindings = EhCallSiteBindings::ExactInstructions(vec![])
            }
            1 => func.eh_metadata.call_sites.clear(),
            2 => {
                func.eh_metadata.call_site_bindings =
                    EhCallSiteBindings::ExactInstructions(vec![binding, binding])
            }
            3 => {
                func.eh_metadata.call_site_bindings =
                    EhCallSiteBindings::ExactInstructions(vec![EhInvokeBinding {
                        call_block: binding.landing_pad_block,
                        ..binding
                    }])
            }
            4 => {
                func.insts[binding.call_inst.0 as usize] = MachInst::new(AArch64Opcode::Nop, vec![])
            }
            5 => {
                func.eh_metadata.call_site_bindings =
                    EhCallSiteBindings::ExactInstructions(vec![EhInvokeBinding {
                        call_inst: InstId(u32::MAX),
                        ..binding
                    }])
            }
            _ => unreachable!(),
        }
        let original = format!("{func:?}");
        assert!(
            FrameInsertionPlan::new(&func).is_err(),
            "mutation {mutation}"
        );
        assert_eq!(format!("{func:?}"), original, "mutation {mutation}");
    }
}
