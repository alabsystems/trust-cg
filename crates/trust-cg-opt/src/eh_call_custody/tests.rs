use super::*;
use trust_cg_ir::function::{EhCallSiteEntry, EhInvokeBinding, LandingPadEntry};
use trust_cg_ir::{AArch64Opcode, BlockId, MachInst, MachOperand, Signature};

pub(crate) fn bind_exact(func: &mut MachFunction, call: InstId, block: BlockId) {
    let pad = add_handler(func, block);
    func.eh_metadata.call_site_bindings =
        EhCallSiteBindings::ExactInstructions(vec![EhInvokeBinding {
            call_inst: call,
            call_block: block,
            landing_pad_block: pad,
        }]);
}

pub(crate) fn bind_legacy(func: &mut MachFunction, block: BlockId) {
    add_handler(func, block);
    func.eh_metadata.call_site_bindings = EhCallSiteBindings::LegacyBlocks;
}

fn add_handler(func: &mut MachFunction, block: BlockId) -> BlockId {
    let pad = func.create_block();
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(pad, ret);
    func.eh_metadata.landing_pads.push(LandingPadEntry {
        block: pad,
        offset: 0,
        catch_type_indices: vec![],
        is_cleanup: true,
    });
    func.eh_metadata.call_sites.push(EhCallSiteEntry {
        call_block: block,
        start_offset: 0,
        length: 0,
        landing_pad_block: Some(pad),
    });
    pad
}

/// Bind `call` in `block` as an invoke whose exception edge leaves for `pad`,
/// as instruction selection lowers `Invoke`: a landing-pad row (one per pad),
/// a call-site row, an exact custody binding added to the function's others,
/// and the CFG edge to the pad.
pub(crate) fn bind_invoke(func: &mut MachFunction, call: InstId, block: BlockId, pad: BlockId) {
    let eh = &mut func.eh_metadata;
    if !eh.landing_pads.iter().any(|entry| entry.block == pad) {
        eh.landing_pads.push(LandingPadEntry {
            block: pad,
            offset: 0,
            catch_type_indices: vec![0],
            is_cleanup: false,
        });
    }
    eh.call_sites.push(EhCallSiteEntry {
        call_block: block,
        start_offset: 0,
        length: 0,
        landing_pad_block: Some(pad),
    });
    let binding = EhInvokeBinding {
        call_inst: call,
        call_block: block,
        landing_pad_block: pad,
    };
    match &mut eh.call_site_bindings {
        EhCallSiteBindings::ExactInstructions(bindings) => bindings.push(binding),
        EhCallSiteBindings::LegacyBlocks => {
            eh.call_site_bindings = EhCallSiteBindings::ExactInstructions(vec![binding]);
        }
    }
    func.add_edge(block, pad);
}

pub(crate) fn snapshot(func: &MachFunction) -> String {
    // Include arena contents, live order, counters, EH rows and all other
    // machine state. A declined transform must not leave a partial mutation.
    format!("{func:?}")
}

fn two_calls() -> (MachFunction, [InstId; 2]) {
    let mut func = MachFunction::new("custody".into(), Signature::new(vec![], vec![]));
    for _ in 0..7 {
        func.push_inst(MachInst::new(AArch64Opcode::Nop, vec![]));
    }
    let calls = std::array::from_fn(|_| {
        let id = func.push_inst(MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("same_callee".into())],
        ));
        func.append_inst(func.entry, id);
        id
    });
    (func, calls)
}

#[test]
fn exact_custody_is_sparse_instruction_identity_not_callee_or_block() {
    let (mut func, [first, second]) = two_calls();
    let entry = func.entry;
    bind_exact(&mut func, second, entry);
    let protected = ProtectedCalls::collect(&func);
    assert!(!protected.contains(first));
    assert!(protected.contains(second));
    assert_eq!(protected.0.len(), 1);
}

#[test]
fn legacy_handler_blocks_protect_all_live_calls_but_not_dead_arena_calls() {
    let (mut func, calls) = two_calls();
    let entry = func.entry;
    bind_legacy(&mut func, entry);
    let duplicate = func.eh_metadata.call_sites[0].clone();
    func.eh_metadata.call_sites.push(duplicate);
    let dead = func.push_inst(MachInst::new(AArch64Opcode::Bl, vec![]));
    let protected = ProtectedCalls::collect(&func);
    assert!(calls.into_iter().all(|id| protected.contains(id)));
    assert!(!protected.contains(dead));
    assert_eq!(protected.0.len(), 2);
}

#[test]
fn legacy_real_call_opcodes_remain_protected_when_the_call_flag_is_malformed() {
    let mut func = MachFunction::new("cleared_call_flags".into(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    let calls: Vec<_> = [
        AArch64Opcode::Bl,
        AArch64Opcode::Blr,
        AArch64Opcode::BL,
        AArch64Opcode::BLR,
    ]
    .into_iter()
    .map(|opcode| {
        let mut inst = MachInst::new(opcode, vec![]);
        inst.flags = trust_cg_ir::InstFlags::EMPTY;
        let id = func.push_inst(inst);
        func.append_inst(entry, id);
        id
    })
    .collect();
    bind_legacy(&mut func, entry);
    let before = snapshot(&func);
    let protected = ProtectedCalls::collect(&func);
    assert_eq!(protected.0.len(), 4);
    assert!(calls.into_iter().all(|id| protected.contains(id)));
    assert_eq!(
        snapshot(&func),
        before,
        "custody does not repair malformed flags"
    );
}

#[test]
fn exact_empty_or_orphan_binding_never_falls_back_to_callee_matching() {
    let (mut func, calls) = two_calls();
    let entry = func.entry;
    bind_exact(&mut func, InstId(999), entry);
    let protected = ProtectedCalls::collect(&func);
    assert!(protected.contains(InstId(999)));
    assert!(calls.into_iter().all(|id| !protected.contains(id)));
    func.eh_metadata.call_site_bindings = EhCallSiteBindings::ExactInstructions(vec![]);
    assert!(ProtectedCalls::collect(&func).0.is_empty());
}

#[test]
fn no_handler_and_invalid_legacy_block_do_not_mint_custody() {
    let (mut func, calls) = two_calls();
    assert!(ProtectedCalls::collect(&func).0.is_empty());
    func.eh_metadata.call_sites.push(EhCallSiteEntry {
        call_block: func.entry,
        start_offset: 0,
        length: 0,
        landing_pad_block: None,
    });
    func.eh_metadata.call_sites.push(EhCallSiteEntry {
        call_block: BlockId(999),
        start_offset: 0,
        length: 0,
        landing_pad_block: Some(func.entry),
    });
    let protected = ProtectedCalls::collect(&func);
    assert!(calls.into_iter().all(|id| !protected.contains(id)));
    assert!(protected.0.is_empty());
}

/// A call in a block of its own, ending in `b next`.
fn call_block(func: &mut MachFunction, block: BlockId, next: BlockId) -> InstId {
    let call = func.push_inst(MachInst::new(
        AArch64Opcode::Bl,
        vec![MachOperand::Symbol("may_throw".into())],
    ));
    func.append_inst(block, call);
    let br = func.push_inst(MachInst::new(
        AArch64Opcode::B,
        vec![MachOperand::Block(next)],
    ));
    func.append_inst(block, br);
    func.add_edge(block, next);
    call
}

#[test]
fn unwind_exits_are_every_call_of_an_invoke_block_and_no_other() {
    let (mut func, [first, second]) = two_calls();
    let entry = func.entry;
    let normal = func.create_block();
    let exit = func.create_block();
    let pad = func.create_block();
    let plain = call_block(&mut func, normal, exit);
    bind_invoke(&mut func, second, entry, pad);
    let exits = UnwindExits::collect(&func);
    assert!(exits.contains(second), "the bound call is an exit");
    assert!(
        exits.contains(first),
        "another call of the invoke block is an exit too (fail-closed)"
    );
    assert!(
        !exits.contains(plain),
        "a call in a block with no exception edge is no exit"
    );
    assert!(exits.leaves_mid_block(entry));
    assert!(!exits.leaves_mid_block(normal));
    assert!(!exits.leaves_mid_block(pad));
}

#[test]
fn unwind_exits_follow_the_landing_pad_edge_when_custody_drifted() {
    // The exact binding names a dead instruction and another block, but the
    // call's block still has the landing pad as a successor: its calls stay
    // exits, as does the drifted row's block.
    let (mut func, calls) = two_calls();
    let entry = func.entry;
    let other = func.create_block();
    let pad = func.create_block();
    bind_invoke(&mut func, InstId(999), other, pad);
    func.add_edge(entry, pad);
    let exits = UnwindExits::collect(&func);
    assert!(calls.into_iter().all(|id| exits.contains(id)));
    assert!(exits.leaves_mid_block(entry));
    assert!(!exits.contains(InstId(999)), "a dead arena id is no exit");
}

#[test]
fn a_function_without_exception_handling_has_no_unwind_exits() {
    let (mut func, calls) = two_calls();
    let entry = func.entry;
    let next = func.create_block();
    func.add_edge(entry, next);
    let exits = UnwindExits::collect(&func);
    assert!(calls.into_iter().all(|id| !exits.contains(id)));
    assert!(!exits.leaves_mid_block(entry));
}
