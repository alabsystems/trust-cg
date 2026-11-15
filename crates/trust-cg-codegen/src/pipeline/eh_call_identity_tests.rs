// Exact selected Invoke custody at the final AArch64 EH resolver.
// Author: Andrew Yates. Copyright 2026 Andrew Yates. Apache-2.0.

use super::*;
use trust_cg_ir::function::{
    EhCallSiteBindings, EhCallSiteEntry, EhInvokeBinding, LandingPadEntry, Signature as IrSignature,
};
use trust_cg_ir::regs::X0;

mod regalloc;
mod serialization;
mod shared_pad;

#[derive(Clone)]
struct Fixture {
    func: IrMachFunction,
    offsets: HashMap<BlockId, u32>,
    len: usize,
    before: InstId,
    selected: InstId,
    after: InstId,
    normal: BlockId,
    pad: BlockId,
}

fn fixture() -> Fixture {
    let mut func = IrMachFunction::new(
        "exact_invoke_identity".into(),
        IrSignature::new(vec![], vec![]),
    );
    let entry = func.entry;
    let normal = func.create_block();
    let pad = func.create_block();
    let mov = func.push_inst(IrMachInst::new(
        IrOpcode::MovI,
        vec![IrOperand::PReg(X0), IrOperand::Imm(7)],
    ));
    func.append_inst(entry, mov);
    // Identical callees deliberately defeat first/last/symbol matching.
    let calls: Vec<_> = (0..3)
        .map(|_| {
            let id = func.push_inst(IrMachInst::new(
                IrOpcode::Bl,
                vec![IrOperand::Symbol("same_may_unwind".into())],
            ));
            func.append_inst(entry, id);
            id
        })
        .collect();
    for block in [normal, pad] {
        let ret = func.push_inst(IrMachInst::new(IrOpcode::Ret, vec![]));
        func.append_inst(block, ret);
    }
    func.add_edge(entry, normal);
    func.add_edge(entry, pad);
    func.eh_metadata.personality = Some("rust_eh_personality".into());
    func.eh_metadata.landing_pads.push(LandingPadEntry {
        block: pad,
        offset: 0,
        catch_type_indices: vec![],
        is_cleanup: true,
    });
    func.eh_metadata.call_sites.push(EhCallSiteEntry {
        call_block: entry,
        start_offset: 0,
        length: 0,
        landing_pad_block: Some(pad),
    });
    func.eh_metadata.call_site_bindings =
        EhCallSiteBindings::ExactInstructions(vec![EhInvokeBinding {
            call_inst: calls[1],
            call_block: entry,
            landing_pad_block: pad,
        }]);
    Fixture {
        offsets: HashMap::from([(entry, 0), (normal, 16), (pad, 20)]),
        len: 24,
        before: calls[0],
        selected: calls[1],
        after: calls[2],
        normal,
        pad,
        func,
    }
}

fn bindings(f: &mut Fixture) -> &mut Vec<EhInvokeBinding> {
    let EhCallSiteBindings::ExactInstructions(records) = &mut f.func.eh_metadata.call_site_bindings
    else {
        panic!("fixture must be explicitly modern")
    };
    records
}

fn sites(func: &IrMachFunction) -> Vec<(u32, u32, Option<BlockId>)> {
    func.eh_metadata
        .call_sites
        .iter()
        .map(|s| (s.start_offset, s.length, s.landing_pad_block))
        .collect()
}

fn resolve(f: &mut Fixture, policy: &EhPropagation) -> Result<(), PipelineError> {
    resolve_eh_offsets_with_propagation(&mut f.func, &f.offsets, f.len, policy)
}

#[test]
fn modern_identity_protects_only_the_middle_identical_call_and_replays_exactly() {
    let mut f = fixture();
    let original = f.func.eh_metadata.call_site_bindings.clone();
    resolve(&mut f, &EhPropagation::Filler).unwrap();
    let expected = vec![(0, 8, None), (8, 4, Some(f.pad)), (12, 12, None)];
    assert_eq!(sites(&f.func), expected);
    assert_eq!(f.func.eh_metadata.landing_pads[0].offset, 20);
    assert_eq!(f.func.eh_metadata.call_site_bindings, original);
    for pc in 0..24 {
        let row = f
            .func
            .eh_metadata
            .call_sites
            .iter()
            .find(|s| s.start_offset <= pc && pc < s.start_offset + s.length)
            .expect("filler policy covers every exact encoded byte");
        assert_eq!(
            row.landing_pad_block,
            (8..12).contains(&pc).then_some(f.pad)
        );
    }
    // return-address minus one is 11; neither helper's BL byte is protected.
    resolve(&mut f, &EhPropagation::Filler).unwrap();
    assert_eq!(sites(&f.func), expected);
    assert_eq!(f.func.eh_metadata.call_site_bindings, original);
}

#[test]
fn explicit_legacy_single_call_remains_valid_but_two_unbound_calls_refuse() {
    let mut f = fixture();
    f.func.eh_metadata.call_site_bindings = EhCallSiteBindings::LegacyBlocks;
    let after = f.after;
    f.func
        .block_mut(f.func.entry)
        .insts
        .retain(|id| *id != after);
    f.offsets.insert(f.normal, 12);
    f.offsets.insert(f.pad, 16);
    f.len = 20;
    // Resolution may publish a checked pad offset before a later refusal.
    // Keep the independent one-call positive on its original unresolved input.
    let mut ambiguous = f.clone();
    let error = resolve(&mut ambiguous, &EhPropagation::Filler).unwrap_err();
    assert!(matches!(error, PipelineError::MalformedAarch64Eh { .. }));
    assert!(
        error
            .to_string()
            .contains("contains 2 eligible BL/BLR calls")
    );
    let before = f.before;
    f.func
        .block_mut(f.func.entry)
        .insts
        .retain(|id| *id != before);
    f.offsets.insert(f.normal, 8);
    f.offsets.insert(f.pad, 12);
    f.len = 16;
    resolve(&mut f, &EhPropagation::Filler).unwrap();
    assert_eq!(
        sites(&f.func),
        vec![(0, 4, None), (4, 4, Some(f.pad)), (8, 8, None)]
    );
    assert_eq!(
        f.func.eh_metadata.call_site_bindings,
        EhCallSiteBindings::LegacyBlocks
    );
}

#[test]
fn modern_identity_refuses_missing_or_stale_custody_and_layout_inputs() {
    let cases: &[(&str, fn(&mut Fixture))] = &[
        ("modern empty", |f| bindings(f).clear()),
        ("orphan with no old metadata", |f| {
            f.func.eh_metadata.personality = None;
            f.func.eh_metadata.landing_pads.clear();
            f.func.eh_metadata.call_sites.clear();
            assert!(f.func.eh_metadata.has_eh_info());
        }),
        ("missing semantic row", |f| {
            f.func.eh_metadata.call_sites.clear()
        }),
        ("duplicate exact record", |f| {
            let original = bindings(f)[0];
            bindings(f).push(original);
        }),
        ("conflicting exact record", |f| {
            let mut other = bindings(f)[0];
            other.call_inst = f.before;
            bindings(f).push(other);
        }),
        ("duplicate semantic row", |f| {
            let original = f.func.eh_metadata.call_sites[0].clone();
            f.func.eh_metadata.call_sites.push(original);
        }),
        ("out of arena", |f| {
            bindings(f)[0].call_inst = InstId(u32::MAX)
        }),
        ("wrong claimed block", |f| {
            let normal = f.normal;
            bindings(f)[0].call_block = normal;
        }),
        ("call actually in another block", |f| {
            let before = f.before;
            f.func
                .block_mut(f.func.entry)
                .insts
                .retain(|id| *id != before);
            f.func.block_mut(f.normal).insts.insert(0, before);
            f.offsets.insert(f.normal, 12);
            bindings(f)[0].call_inst = before;
        }),
        ("selected noncall", |f| {
            f.func.insts[f.selected.0 as usize] = IrMachInst::new(IrOpcode::Ret, vec![]);
        }),
        ("selected pseudo", |f| {
            f.func.insts[f.selected.0 as usize] = IrMachInst::new(IrOpcode::Nop, vec![]);
            f.offsets.insert(f.normal, 12);
            f.offsets.insert(f.pad, 16);
            f.len = 20;
        }),
        ("selected unlinked", |f| {
            let selected = f.selected;
            f.func
                .block_mut(f.func.entry)
                .insts
                .retain(|id| *id != selected);
            f.offsets.insert(f.normal, 12);
            f.offsets.insert(f.pad, 16);
            f.len = 20;
        }),
        ("duplicate encoded occurrence", |f| {
            f.func.block_mut(f.normal).insts.insert(0, f.selected);
            f.offsets.insert(f.pad, 24);
            f.len = 28;
        }),
        ("wrong bound pad", |f| {
            let normal = f.normal;
            bindings(f)[0].landing_pad_block = normal;
        }),
        ("missing pad descriptor", |f| {
            f.func.eh_metadata.landing_pads.clear()
        }),
        ("duplicate pad descriptor", |f| {
            let original = f.func.eh_metadata.landing_pads[0].clone();
            f.func.eh_metadata.landing_pads.push(original);
        }),
        ("stale pad offset", |f| {
            f.func.eh_metadata.landing_pads[0].offset = 4
        }),
        ("pad sentinel zero", |f| {
            f.func.block_order = vec![f.pad, f.func.entry, f.normal];
            f.offsets = HashMap::from([(f.pad, 0), (f.func.entry, 4), (f.normal, 20)]);
        }),
        ("missing reciprocal predecessor", |f| {
            f.func.block_mut(f.pad).preds.clear()
        }),
        ("duplicate exceptional successor", |f| {
            f.func.block_mut(f.func.entry).succs.push(f.pad);
        }),
        ("stale authored range", |f| {
            f.func.eh_metadata.call_sites[0].length = 16
        }),
        ("misaligned encoded length", |f| f.len = 25),
        ("short encoded length", |f| f.len = 20),
        ("stale block offset", |f| {
            f.offsets.insert(f.normal, 12);
        }),
        ("missing block offset", |f| {
            f.offsets.remove(&f.normal);
        }),
        ("extra encoder block", |f| {
            f.offsets.insert(BlockId(u32::MAX), 24);
        }),
        ("duplicate layout block", |f| {
            f.func.block_order.push(f.normal)
        }),
        ("missing exceptional successor", |f| {
            let pad = f.pad;
            f.func.block_mut(f.func.entry).succs.retain(|id| *id != pad);
        }),
        ("duplicate exceptional predecessor", |f| {
            let entry = f.func.entry;
            f.func.block_mut(f.pad).preds.push(entry);
        }),
        ("call owner omitted from layout", |f| {
            f.func.block_order = vec![f.normal, f.pad];
            f.offsets = HashMap::from([(f.normal, 0), (f.pad, 4)]);
            f.len = 8;
        }),
        ("pad omitted from layout", |f| {
            f.func.block_order.retain(|id| *id != f.pad);
            f.offsets.remove(&f.pad);
            f.len = 20;
        }),
    ];
    let mut attempted = 0;
    for (name, mutate) in cases {
        let mut f = fixture();
        mutate(&mut f);
        let error = resolve(&mut f, &EhPropagation::Filler).unwrap_err();
        assert!(
            matches!(error, PipelineError::MalformedAarch64Eh { .. }),
            "{name}: {error}"
        );
        assert!(
            error.to_string().contains("exact_invoke_identity"),
            "{name}: {error}"
        );
        attempted += 1;
    }
    assert_eq!(attempted, 31, "every independently corrupted row executes");
}

#[test]
fn modern_identity_accepts_only_the_bound_direct_or_indirect_call_bytes() {
    let mut attempted = 0;
    for opcode in [IrOpcode::Bl, IrOpcode::BL, IrOpcode::Blr, IrOpcode::BLR] {
        let mut f = fixture();
        let operands = match opcode {
            IrOpcode::Blr | IrOpcode::BLR => vec![IrOperand::PReg(X0)],
            _ => vec![IrOperand::Symbol("same_may_unwind".into())],
        };
        f.func.insts[f.selected.0 as usize] = IrMachInst::new(opcode, operands);
        resolve(&mut f, &EhPropagation::Filler).unwrap();
        assert_eq!(
            sites(&f.func),
            vec![(0, 8, None), (8, 4, Some(f.pad)), (12, 12, None)]
        );
        attempted += 1;
    }
    assert_eq!(attempted, 4);
}

#[test]
fn nounwind_frame_classifies_helpers_without_widening_the_exact_protected_call() {
    for (before_unwinds, after_unwinds) in
        [(false, false), (true, false), (false, true), (true, true)]
    {
        let mut f = fixture();
        for (id, unwinds) in [(f.before, before_unwinds), (f.after, after_unwinds)] {
            f.func.insts[id.0 as usize].operands = vec![IrOperand::Symbol(
                if unwinds {
                    "helper_may_unwind"
                } else {
                    "helper_nounwind"
                }
                .into(),
            )];
        }
        let policy = EhPropagation::NounwindFrame {
            nounwind_callees: Arc::new(BTreeSet::from([
                "helper_nounwind".into(),
                "same_may_unwind".into(),
            ])),
        };
        resolve(&mut f, &policy).unwrap();
        let mut expected = vec![];
        if before_unwinds {
            expected.push((0, 8, None));
        }
        expected.push((8, 4, Some(f.pad)));
        if after_unwinds {
            expected.push((12, 12, None));
        }
        assert_eq!(
            sites(&f.func),
            expected,
            "before={before_unwinds}, after={after_unwinds}"
        );
    }
}

#[test]
fn modern_identity_does_not_admit_unmodeled_nounwind_frames() {
    let policy = EhPropagation::NounwindFrame {
        nounwind_callees: Arc::new(BTreeSet::new()),
    };
    for resume in [false, true] {
        let mut f = fixture();
        if resume {
            let id = f.func.push_inst(IrMachInst::new(
                IrOpcode::Bl,
                vec![IrOperand::Symbol("_Unwind_Resume".into())],
            ));
            f.func.block_mut(f.pad).insts.insert(0, id);
            f.len += 4;
        } else {
            f.func.eh_metadata.personality = Some("__gxx_personality_v0".into());
        }
        let error = resolve(&mut f, &policy).unwrap_err();
        assert!(matches!(error, PipelineError::MalformedAarch64Eh { .. }));
        assert!(
            error.to_string().contains("[TCG-EH-NOUNWIND-FRAME]"),
            "{error}"
        );
    }
}

#[test]
fn production_frame_insertion_preserves_selected_identity_and_rederives_its_bytes() {
    for slot_bytes in [0, 1 << 20] {
        let mut f = fixture();
        let original_entry = f.func.entry;
        if slot_bytes != 0 {
            f.func
                .alloc_stack_slot(trust_cg_ir::function::StackSlot::new(slot_bytes, 16));
        }
        let layout = crate::frame::try_compute_frame_layout(&f.func, 0, false).unwrap();
        crate::frame::insert_prologue_epilogue(&mut f.func, &layout).unwrap();
        let actual = bindings(&mut f)[0];
        assert_eq!(actual.call_inst, f.selected);
        assert_eq!(actual.landing_pad_block, f.pad);
        assert_eq!(actual.call_block == original_entry, slot_bytes == 0);
        assert!(f.func.block(actual.call_block).insts.contains(&f.selected));
        assert_eq!(
            f.func.eh_metadata.call_sites[0].call_block,
            actual.call_block
        );
        let mut cursor = 0;
        let mut selected_offset = None;
        f.offsets.clear();
        for &block in &f.func.block_order {
            f.offsets.insert(block, cursor);
            for &id in &f.func.block(block).insts {
                if !f.func.insts[id.0 as usize].is_pseudo() {
                    if id == f.selected {
                        selected_offset = Some(cursor);
                    }
                    cursor += 4;
                }
            }
        }
        f.len = cursor as usize;
        resolve(&mut f, &EhPropagation::Filler).unwrap();
        let protected: Vec<_> = sites(&f.func)
            .into_iter()
            .filter(|s| s.2.is_some())
            .collect();
        assert_eq!(protected, vec![(selected_offset.unwrap(), 4, Some(f.pad))]);
        assert_eq!(bindings(&mut f).as_slice(), &[actual]);
    }
}
