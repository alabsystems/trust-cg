// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use trust_cg_ir::BlockId;
use trust_cg_ir::function::{MachBlock, Signature, StackSlot, Type};
use trust_cg_ir::regs::{D0, S0, X0};
use trust_cg_lower::instructions::{Block, Opcode as L, Value};

fn fixture(width: usize) -> (Function, MachFunction) {
    let mut sources: Vec<Function> =
        serde_json::from_str(include_str!("source_bound_cell_fixture.json")).unwrap();
    let mut source = sources.remove(0);
    let lir_ty = if width == 4 {
        trust_cg_lower::Type::F32
    } else {
        trust_cg_lower::Type::F64
    };
    source.signature.params = vec![lir_ty.clone(); 2];
    source.signature.returns = vec![lir_ty.clone()];
    source.stack_slots[0].size = width as u32;
    source.stack_slots[0].align = width as u32;
    for block in source.blocks.values_mut() {
        for (_, ty) in &mut block.params {
            *ty = lir_ty.clone();
        }
        for inst in &mut block.instructions {
            match &mut inst.opcode {
                L::Load { ty, .. } | L::Store { ty, .. } => *ty = lir_ty.clone(),
                _ => {}
            }
        }
    }
    let ty = if width == 4 { Type::F32 } else { Type::F64 };
    let mut machine = MachFunction::new(
        source.name.clone(),
        Signature::new(vec![ty.clone(); 2], vec![ty]),
    );
    machine.stack_slots = vec![StackSlot::new(width as u32, width as u32)];
    machine.next_vreg = 5;
    let p = |n| O::PReg(PReg::new(n));
    let i = O::Imm;
    let sp = O::Special(SpecialReg::SP);
    let f = if width == 4 { 128 } else { 96 };
    let ins = |op, args| MachInst::new(op, args);
    machine.insts = vec![
        ins(M::Nop, vec![p(f), p(f)]),
        ins(M::Nop, vec![p(f + 1), p(f + 1)]),
        ins(M::SubRI, vec![p(19), p(29), i(16 + width as i64)]),
        ins(M::StrRI, vec![p(f), p(19), i(0)]),
        ins(M::MOVXrr, vec![p(0), p(19)]),
        ins(M::Nop, vec![p(0), p(0)]),
        ins(M::NeonOrrV, vec![p(f), p(f + 1), p(f + 1), i(1)]),
        ins(M::Bl, vec![O::Symbol("c_change".into())]),
        ins(M::B, vec![i(1)]),
        ins(M::LdrRI, vec![p(f), p(19), i(0)]),
        ins(M::Nop, vec![p(f), p(f)]),
        ins(M::Ret, vec![p(30)]),
        ins(M::StpPreIndex, vec![p(20), p(19), sp.clone(), i(-32)]),
        ins(M::StpRI, vec![p(29), p(30), sp.clone(), i(16)]),
        ins(M::AddRI, vec![p(29), sp.clone(), i(16)]),
        ins(M::SubRI, vec![sp.clone(), sp.clone(), i(16)]),
        ins(M::AddRI, vec![sp.clone(), sp.clone(), i(16)]),
        ins(M::LdpRI, vec![p(29), p(30), sp.clone(), i(16)]),
        ins(M::LdpPostIndex, vec![p(20), p(19), sp, i(32)]),
    ];
    for id in [0, 1, 5, 10] {
        machine.insts[id].flags = InstFlags::IS_PSEUDO;
    }
    machine.insts[5].flags |= InstFlags::IS_CALL_ARG_SETUP;
    machine.insts[6].flags |= InstFlags::IS_CALL_ARG_SETUP;
    machine.insts[7].implicit_uses = if width == 4 { &[X0, S0] } else { &[X0, D0] };
    machine.insts[11].implicit_uses = if width == 4 { &[S0] } else { &[D0] };
    let block = |insts: Vec<u32>, preds: Vec<u32>, succs: Vec<u32>| MachBlock {
        insts: insts.into_iter().map(InstId).collect(),
        preds: preds.into_iter().map(BlockId).collect(),
        succs: succs.into_iter().map(BlockId).collect(),
        loop_depth: 0,
    };
    machine.blocks = vec![
        block(
            vec![12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 8],
            vec![],
            vec![1],
        ),
        block(vec![9, 10, 16, 17, 18, 11], vec![0], vec![]),
    ];
    machine.block_order = vec![BlockId(0), BlockId(1)];
    (source, machine)
}

fn checked(source: &Function, machine: &MachFunction) -> Option<CheckedCellFrame> {
    let view = super::super::linear::source_view(source)?;
    let chain = super::super::linear::machine_chain(machine)?;
    super::super::check_owned_instructions(machine, &chain.live, false)?;
    check(&view, machine, &chain.instructions)
}

#[test]
fn scalar_callback_byte_transport_matches_captured_frame() {
    for width in [4, 8] {
        let (source, machine) = fixture(width);
        let result = checked(&source, &machine).expect("captured callback frame");
        assert_eq!(result.envelope, [12, 13, 14, 15, 16, 17, 18].map(InstId));
        assert_eq!(result.cell_width, width);
        assert_eq!(result.calls, 1);
        // Diagnostic recognition must not silently become frame proof authority.
        assert!(super::super::source_bound_frame(&source, &machine).is_none());
    }
}

#[test]
fn emit_scalar_cell_stack_algebra_for_independent_replay() {
    for width in [4, 8] {
        let query = crate::ay_bridge::generate_smt2_query_raw(
            &super::obligation(width),
            &crate::ay_bridge::AYConfig::default(),
        );
        assert!(query.contains("entry_memory"));
        assert!(query.contains("cell_after"));
        println!(
            "SCALAR_CELL_STACK_QUERY={}",
            serde_json::json!({"width":width,"query":query})
        );
    }
}

#[test]
fn scalar_callback_rejects_frame_argument_memory_and_source_mutations() {
    for width in [4, 8] {
        let (source, machine) = fixture(width);
        for index in [2, 3, 4, 6, 7, 9, 11, 12, 13, 14, 15, 16, 17, 18] {
            let mut wrong = machine.clone();
            wrong.insts[index].opcode = M::Nop;
            assert!(
                checked(&source, &wrong).is_none(),
                "opcode mutant {width}/{index}"
            );
        }
        for (index, operand, value) in [
            (12, 3, -16),
            (13, 3, 0),
            (14, 2, 0),
            (15, 2, 32),
            (16, 2, 32),
            (17, 3, 0),
            (18, 3, 16),
            (2, 2, 0),
            (2, 2, 8),
            (2, 2, 64),
            (3, 2, 1),
            (9, 2, 1),
        ] {
            let mut wrong = machine.clone();
            wrong.insts[index].operands[operand] = O::Imm(value);
            assert!(
                checked(&source, &wrong).is_none(),
                "address mutant {width}/{index}/{value}"
            );
        }
        for index in [4, 6, 9] {
            let mut wrong = machine.clone();
            wrong.insts[index].operands[0] = O::PReg(PReg::new(1));
            assert!(
                checked(&source, &wrong).is_none(),
                "wiring mutant {width}/{index}"
            );
        }
        let mut wrong = machine.clone();
        wrong.insts[7].operands[0] = O::Symbol("other_callback".into());
        assert!(checked(&source, &wrong).is_none());
        let mut wrong = machine.clone();
        wrong.insts[7].implicit_defs = &[X19];
        assert!(checked(&source, &wrong).is_none());
        let mut wrong = source.clone();
        wrong.blocks.get_mut(&Block(0)).unwrap().instructions[3].args[1] = Value(0);
        assert!(checked(&wrong, &machine).is_none());
        let mut wrong = source.clone();
        wrong.blocks.get_mut(&Block(0)).unwrap().instructions[1].args[0] = Value(1);
        assert!(checked(&wrong, &machine).is_none());
        let mut wrong = source.clone();
        wrong.stack_slots[0].size += 1;
        assert!(checked(&wrong, &machine).is_none());
        let mut wrong = source.clone();
        wrong.blocks.get_mut(&Block(1)).unwrap().instructions[1].args[0] = Value(0);
        assert!(checked(&wrong, &machine).is_none());
    }
}
