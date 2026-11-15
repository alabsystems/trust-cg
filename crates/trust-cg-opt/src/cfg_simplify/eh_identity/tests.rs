use super::*;
use trust_cg_ir::function::{EhCallSiteEntry, LandingPadEntry, Signature};

fn fixture() -> (MachFunction, EhInvokeBinding) {
    let mut func = MachFunction::new("dead_invoke".into(), Signature::new(vec![], vec![]));
    let dead = func.create_block();
    let pad = func.create_block();
    let call = func.push_inst(MachInst::new(
        AArch64Opcode::Bl,
        vec![MachOperand::Symbol("callee".into())],
    ));
    func.append_inst(dead, call);
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(BlockId(0), ret);
    let pad_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(pad, pad_ret);
    func.add_edge(dead, pad);
    let binding = EhInvokeBinding {
        call_inst: call,
        call_block: dead,
        landing_pad_block: pad,
    };
    func.eh_metadata.personality = Some("personality".into());
    func.eh_metadata.call_sites.push(EhCallSiteEntry {
        call_block: dead,
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
    (func, binding)
}

#[test]
fn fully_dead_handler_prunes_its_exact_binding_and_personality_atomically() {
    let (mut func, _) = fixture();
    assert!(super::super::remove_unreachable_blocks(&mut func, None));
    assert_eq!(func.block_order, vec![BlockId(0)]);
    assert_eq!(
        func.eh_metadata.call_site_bindings,
        EhCallSiteBindings::ExactInstructions(vec![])
    );
    assert!(func.eh_metadata.call_sites.is_empty());
    assert!(func.eh_metadata.landing_pads.is_empty());
    assert!(func.eh_metadata.personality.is_none());
}

#[test]
fn partial_dead_region_keeps_the_live_exact_handler_unchanged() {
    let (mut func, dead) = fixture();
    let live_call = func.push_inst(MachInst::new(
        AArch64Opcode::Bl,
        vec![MachOperand::Symbol("live".into())],
    ));
    func.append_inst(BlockId(0), live_call);
    let live_pad = func.create_block();
    let normal = func.create_block();
    let branch = func.push_inst(MachInst::new(
        AArch64Opcode::B,
        vec![MachOperand::Block(normal)],
    ));
    func.blocks[0].insts = vec![live_call, branch];
    for block in [live_pad, normal] {
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(block, ret);
    }
    func.add_edge(BlockId(0), live_pad);
    func.add_edge(BlockId(0), normal);
    let live = EhInvokeBinding {
        call_inst: live_call,
        call_block: BlockId(0),
        landing_pad_block: live_pad,
    };
    func.eh_metadata.call_sites.push(EhCallSiteEntry {
        call_block: BlockId(0),
        start_offset: 0,
        length: 0,
        landing_pad_block: Some(live_pad),
    });
    func.eh_metadata.landing_pads.push(LandingPadEntry {
        block: live_pad,
        offset: 0,
        catch_type_indices: vec![],
        is_cleanup: true,
    });
    func.eh_metadata.call_site_bindings = EhCallSiteBindings::ExactInstructions(vec![dead, live]);
    assert!(super::super::remove_unreachable_blocks(&mut func, None));
    assert_eq!(func.block_order, vec![BlockId(0), live_pad, normal]);
    assert_eq!(
        func.eh_metadata.call_site_bindings,
        EhCallSiteBindings::ExactInstructions(vec![live])
    );
    assert_eq!(func.eh_metadata.call_sites.len(), 1);
    assert_eq!(func.eh_metadata.landing_pads.len(), 1);
    assert!(func.eh_metadata.personality.is_some());
}

#[test]
fn pruning_preserves_orphan_duplicate_wrong_owner_and_noncall_refusal_evidence() {
    for mutation in 0..11 {
        let (mut func, binding) = fixture();
        match mutation {
            0 => func.eh_metadata.call_sites.clear(),
            1 => {
                let EhCallSiteBindings::ExactInstructions(bindings) =
                    &mut func.eh_metadata.call_site_bindings
                else {
                    unreachable!()
                };
                bindings.push(binding);
            }
            2 => func
                .eh_metadata
                .call_sites
                .push(func.eh_metadata.call_sites[0].clone()),
            3 => func.blocks[binding.call_block.0 as usize].insts.clear(),
            4 => {
                func.insts[binding.call_inst.0 as usize] = MachInst::new(AArch64Opcode::Nop, vec![])
            }
            5 => func.eh_metadata.call_sites[0].landing_pad_block = Some(BlockId(0)),
            6 => func.insts[binding.call_inst.0 as usize]
                .flags
                .insert(trust_cg_ir::InstFlags::IS_PSEUDO),
            7 => func.eh_metadata.landing_pads.clear(),
            8 => {
                func.eh_metadata.call_site_bindings = EhCallSiteBindings::ExactInstructions(vec![])
            }
            9 => {
                let second = func.create_block();
                func.append_inst(second, binding.call_inst);
                func.add_edge(second, binding.landing_pad_block);
                func.eh_metadata.call_sites.push(EhCallSiteEntry {
                    call_block: second,
                    start_offset: 0,
                    length: 0,
                    landing_pad_block: Some(binding.landing_pad_block),
                });
                let EhCallSiteBindings::ExactInstructions(bindings) =
                    &mut func.eh_metadata.call_site_bindings
                else {
                    unreachable!()
                };
                bindings.push(EhInvokeBinding {
                    call_block: second,
                    ..binding
                });
            }
            10 => func.append_inst(BlockId(0), binding.call_inst),
            _ => unreachable!(),
        }
        let before = func.eh_metadata.call_site_bindings.clone();
        let before_sites = func.eh_metadata.call_sites.clone();
        let reachable = HashSet::from_iter([BlockId(0)]);
        super::super::prune_eh_metadata_for_removed_blocks(&mut func, &reachable);
        assert_eq!(
            func.eh_metadata.call_site_bindings, before,
            "mutation {mutation}"
        );
        assert_eq!(
            func.eh_metadata.call_sites, before_sites,
            "mutation {mutation}"
        );
        assert!(func.eh_metadata.has_eh_info(), "mutation {mutation}");
        assert!(
            func.eh_metadata.personality.is_some(),
            "mutation {mutation}"
        );
    }
}
