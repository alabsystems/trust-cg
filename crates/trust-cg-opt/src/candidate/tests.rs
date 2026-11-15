use super::*;
use trust_cg_ir::{Signature, StackSlot};

pub(crate) mod support;

fn fixture() -> (MachFunction, InstId, BlockId) {
    let mut func = MachFunction::new("candidate".into(), Signature::new(vec![], vec![]));
    let exit = func.create_block();
    let entry = func.entry;
    let term = emit(
        &mut func,
        entry,
        AArch64Opcode::B,
        vec![MachOperand::Block(exit)],
    )
    .unwrap();
    func.add_edge(entry, exit);
    (func, term, exit)
}

#[test]
fn invalid_block_emission_is_read_only() {
    let (mut func, _, _) = fixture();
    let before = format!("{func:?}");
    assert_eq!(
        emit(&mut func, BlockId(u32::MAX), AArch64Opcode::Nop, vec![]),
        None
    );
    assert_eq!(format!("{func:?}"), before);
}

#[test]
fn setup_anchor_must_be_resident_and_unique() {
    for case in 0..4 {
        let (mut func, term, exit) = fixture();
        let anchor = match case {
            0 => InstId(u32::MAX),
            1 => {
                func.block_mut(func.entry).insts.clear();
                term
            }
            2 => {
                func.block_mut(exit).insts.push(term);
                term
            }
            _ => {
                func.block_mut(func.entry).insts.push(term);
                term
            }
        };
        let before = format!("{func:?}");
        assert_eq!(
            emit_before(&mut func, anchor, AArch64Opcode::Nop, vec![]),
            None
        );
        assert_eq!(format!("{func:?}"), before);
    }
}

#[test]
fn layout_requires_unique_existing_and_fresh_anchors() {
    for case in 0..7 {
        let (mut func, _, exit) = fixture();
        let fresh = func.create_block();
        let mut added = vec![fresh];
        match case {
            0 => func.block_order.retain(|id| *id != exit),
            1 => func.block_order.push(exit),
            2 => func.block_order.retain(|id| *id != fresh),
            3 => func.block_order.push(fresh),
            4 => added.push(fresh),
            5 => added = vec![exit],
            _ => added = vec![BlockId(u32::MAX)],
        }
        let before = format!("{func:?}");
        assert_eq!(insert_new_blocks_before(&mut func, exit, &added), None);
        assert_eq!(format!("{func:?}"), before);
    }
}

#[test]
fn splice_checks_instruction_ownership_and_original_edge() {
    for case in 0..5 {
        let (mut func, term, exit) = fixture();
        let entry = func.entry;
        let fresh = func.create_block();
        match case {
            0 => func.inst_mut(term).operands.clear(),
            1 => func.block_mut(entry).succs.clear(),
            2 => func.block_mut(exit).preds.clear(),
            3 => func.block_mut(entry).insts.clear(),
            _ => func.block_mut(fresh).insts.push(term),
        }
        let before = format!("{func:?}");
        assert_eq!(splice_edge(&mut func, entry, term, exit, fresh), None);
        assert_eq!(format!("{func:?}"), before);
    }
}

#[test]
fn successful_insertion_preserves_layout_order_and_edge_metadata() {
    let (mut func, term, exit) = fixture();
    let entry = func.entry;
    let first = func.create_block();
    let second = func.create_block();
    insert_new_blocks_before(&mut func, exit, &[second, first]).unwrap();
    let setup = emit_before(&mut func, term, AArch64Opcode::Nop, vec![]).unwrap();
    splice_edge(&mut func, entry, term, exit, second).unwrap();
    assert_eq!(func.block_order, [entry, second, first, exit]);
    assert_eq!(func.block(entry).insts, [setup, term]);
    assert_eq!(func.block(entry).succs, [second]);
    assert_eq!(func.block(second).preds, [entry]);
    assert!(func.block(exit).preds.is_empty());
    assert_eq!(func.inst(term).operands, [MachOperand::Block(second)]);
}

#[test]
fn transaction_synchronizes_sparse_and_metadata_identities() {
    let (mut func, _, _) = fixture();
    func.noalias_params.push(1_000_000_000);
    assert!(commit(&mut func, |candidate| {
        let reg = alloc(candidate, RegClass::Gpr64)?;
        assert_eq!(reg.id, 1_000_000_001);
        emit(
            candidate,
            candidate.entry,
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(reg), MachOperand::Imm(1)],
        )?;
        Some(())
    }));
    assert_eq!(func.next_vreg, 1_000_000_002);
}

#[test]
fn failed_synchronization_does_not_start_rewrite() {
    let (mut func, _, _) = fixture();
    func.noalias_params.push(u32::MAX);
    let before = format!("{func:?}");
    assert!(!commit(&mut func, |_| panic!(
        "exhausted metadata must prevent candidate execution"
    )));
    assert_eq!(format!("{func:?}"), before);
}

#[test]
fn late_refusal_discards_every_candidate_field() {
    let (mut func, _, _) = fixture();
    let before = format!("{func:?}");
    assert!(!commit(&mut func, |candidate| {
        let block = candidate.try_create_block()?;
        candidate.try_alloc_stack_slot(StackSlot::new(8, 16))?;
        alloc(candidate, RegClass::Gpr64)?;
        emit(candidate, block, AArch64Opcode::Nop, vec![])?;
        candidate.name.push_str("-unpublished");
        candidate.noalias_params.push(17);
        None
    }));
    assert_eq!(format!("{func:?}"), before);
}

#[test]
fn a_counter_left_stale_before_the_pass_is_refused_not_repaired() {
    // L10-P5: at a pass boundary the commit admits the function itself, so
    // the candidate's synchronization cannot launder a stale counter.
    let (mut func, _, _) = fixture();
    func.noalias_params.push(5);
    func.require_id_admission_before_allocation();
    let before = format!("{func:?}");
    assert!(!commit(&mut func, |_| panic!(
        "a refused admission must prevent candidate execution"
    )));
    assert_eq!(format!("{func:?}"), before);
    assert_eq!(func.next_vreg, 0, "the counter is not repaired");
    assert_eq!(
        func.id_admission_refusal(),
        Some(trust_cg_ir::MachIdAdmissionError::StaleCounter {
            domain: trust_cg_ir::MachIdDomain::VReg,
            counter: 0,
            live_id: 5,
            site: trust_cg_ir::MachIdSite::NoaliasParam { index: 0 },
        })
    );

    // An admitted boundary commits as before, from the admitted counter.
    let (mut clean, _, _) = fixture();
    clean.require_id_admission_before_allocation();
    assert!(commit(&mut clean, |candidate| {
        assert_eq!(alloc(candidate, RegClass::Gpr64)?.id, 0);
        Some(())
    }));
    assert_eq!(clean.next_vreg, 1);
    assert_eq!(clean.id_admission_refusal(), None);
}
