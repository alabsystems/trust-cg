// Many genuine selected-call records sharing one cleanup-pad graph domain.
// Author: Andrew Yates. Copyright 2026 Andrew Yates. Apache-2.0.

use super::*;

const CALLERS: u32 = 256;

struct SharedPad {
    func: IrMachFunction,
    offsets: HashMap<BlockId, u32>,
    callers: Vec<BlockId>,
    pad: BlockId,
}

fn shared_pad() -> SharedPad {
    let mut func = IrMachFunction::new(
        "many_exact_invokes_one_cleanup".into(),
        IrSignature::new(vec![], vec![]),
    );
    let mut callers = vec![func.entry];
    for _ in 1..CALLERS {
        callers.push(func.create_block());
    }
    let normal = func.create_block();
    let pad = func.create_block();
    let mut exact = Vec::new();
    let mut offsets = HashMap::new();
    for (index, &call_block) in callers.iter().enumerate() {
        let call_inst = func.push_inst(IrMachInst::new(
            IrOpcode::Bl,
            vec![IrOperand::Symbol("same_may_unwind".into())],
        ));
        func.append_inst(call_block, call_inst);
        // Normal execution falls through the next laid-out caller, or the
        // final return. Exceptional execution alone enters the shared pad.
        func.add_edge(
            call_block,
            callers.get(index + 1).copied().unwrap_or(normal),
        );
        func.add_edge(call_block, pad);
        func.eh_metadata.call_sites.push(EhCallSiteEntry {
            call_block,
            start_offset: 0,
            length: 0,
            landing_pad_block: Some(pad),
        });
        exact.push(EhInvokeBinding {
            call_inst,
            call_block,
            landing_pad_block: pad,
        });
        offsets.insert(call_block, 4 * index as u32);
    }
    for (block, offset) in [(normal, 4 * CALLERS), (pad, 4 * (CALLERS + 1))] {
        let ret = func.push_inst(IrMachInst::new(IrOpcode::Ret, vec![]));
        func.append_inst(block, ret);
        offsets.insert(block, offset);
    }
    func.eh_metadata.personality = Some("rust_eh_personality".into());
    func.eh_metadata.landing_pads.push(LandingPadEntry {
        block: pad,
        offset: 0,
        catch_type_indices: vec![],
        is_cleanup: true,
    });
    func.eh_metadata.call_site_bindings = EhCallSiteBindings::ExactInstructions(exact);
    SharedPad {
        func,
        offsets,
        callers,
        pad,
    }
}

#[test]
fn many_invokes_to_one_cleanup_keep_every_independent_four_byte_range_and_pad_filler() {
    let mut f = shared_pad();
    let original = f.func.eh_metadata.call_site_bindings.clone();
    let code_len = 4 * (CALLERS + 2);
    // Expectations come from this fixture's complete independent layout,
    // not the production edge census, offset derivation, or resulting table.
    let mut expected: Vec<_> = (0..CALLERS)
        .map(|index| (4 * index, 4, Some(f.pad)))
        .collect();
    expected.push((4 * CALLERS, 8, None));
    for _ in 0..2 {
        resolve_eh_offsets_with_propagation(
            &mut f.func,
            &f.offsets,
            code_len as usize,
            &EhPropagation::Filler,
        )
        .unwrap();
        assert_eq!(sites(&f.func), expected);
        assert_eq!(f.func.eh_metadata.call_site_bindings, original);
        assert_eq!(f.func.eh_metadata.landing_pads.len(), 1);
        assert_eq!(f.func.eh_metadata.landing_pads[0].offset, 4 * (CALLERS + 1));
        assert_eq!(f.func.block(f.pad).preds.len(), CALLERS as usize);
        assert_eq!(f.func.eh_metadata.call_sites.len(), (CALLERS + 1) as usize);
        for (index, site) in f.func.eh_metadata.call_sites[..CALLERS as usize]
            .iter()
            .enumerate()
        {
            assert_eq!(site.call_block, f.callers[index]);
            assert_eq!((site.start_offset, site.length), (4 * index as u32, 4));
        }
    }
    // This is exact metadata/layout regression evidence. No timing, RSS,
    // native-execution or proof claim follows from the number of records.
}

#[test]
fn one_corrupted_shared_pad_edge_remains_a_typed_refusal_among_many_valid_invokes() {
    let mut attempted = 0;
    for (mutation, expected_counts) in [
        (0, "successors=2, predecessors=1"),
        (1, "successors=0, predecessors=1"),
        (2, "successors=1, predecessors=2"),
        (3, "successors=1, predecessors=0"),
    ] {
        let mut f = shared_pad();
        let caller = f.callers[127];
        match mutation {
            0 => f.func.block_mut(caller).succs.push(f.pad),
            1 => f.func.block_mut(caller).succs.retain(|id| *id != f.pad),
            2 => f.func.block_mut(f.pad).preds.push(caller),
            3 => f.func.block_mut(f.pad).preds.retain(|id| *id != caller),
            _ => unreachable!(),
        }
        let original = f.func.eh_metadata.call_site_bindings.clone();
        let error = resolve_eh_offsets_with_propagation(
            &mut f.func,
            &f.offsets,
            (4 * (CALLERS + 2)) as usize,
            &EhPropagation::Filler,
        )
        .unwrap_err();
        assert!(
            matches!(error, PipelineError::MalformedAarch64Eh { .. }),
            "{error}"
        );
        let detail = error.to_string();
        assert!(
            detail.contains("many_exact_invokes_one_cleanup"),
            "{detail}"
        );
        assert!(detail.contains("not exactly reciprocal"), "{detail}");
        assert!(
            detail.contains(expected_counts),
            "mutation {mutation}: {detail}"
        );
        assert_eq!(f.func.eh_metadata.call_site_bindings, original);
        attempted += 1;
    }
    assert_eq!(
        attempted, 4,
        "all sparse shared-pad edge corruptions execute"
    );
}
