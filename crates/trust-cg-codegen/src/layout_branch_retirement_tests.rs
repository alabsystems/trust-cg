// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Branch elision must retire only its exact removed, pure arena instructions.
//! Stable source attribution is history, never a tombstone's proof credit.

use super::*;
use trust_cg_ir::function::{LandingPadEntry, Signature, Type};
use trust_cg_ir::inst::{InstFlags, ProofAnnotation, SourceLoc};
use trust_cg_ir::provenance::{LoweringProvenance, SourceInstDigest, SourceInstId, TrustIrInstId};
use trust_cg_ir::regs::{X0, X1, X9, X30};

fn function(name: &str, blocks: usize) -> MachFunction {
    let mut func = MachFunction::new(
        name.into(),
        Signature::new(vec![Type::I64; 2], vec![Type::I64]),
    );
    for _ in 1..blocks {
        func.create_block();
    }
    func
}

fn add(func: &mut MachFunction, block: u32, inst: MachInst) -> InstId {
    let id = func.push_inst(inst);
    func.append_inst(BlockId(block), id);
    id
}

fn branch(target: u32) -> MachInst {
    MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(target))])
}

fn arithmetic(opcode: AArch64Opcode) -> MachInst {
    MachInst::new(
        opcode,
        vec![
            MachOperand::PReg(X0),
            MachOperand::PReg(X0),
            MachOperand::Imm(1),
        ],
    )
}

fn ret() -> MachInst {
    MachInst::new(AArch64Opcode::Ret, vec![MachOperand::PReg(X30)]).with_implicit_uses(&[X0])
}

fn attribution(block: u32) -> LoweringProvenance {
    LoweringProvenance::SourceInst {
        id: SourceInstId { block, index: 3 },
        digest: SourceInstDigest::compute("Jump", 0, 0),
        trust_ir_inst: Some(TrustIrInstId(17)),
    }
}

fn assert_retired(func: &MachFunction, id: InstId) {
    let inst = func.inst(id);
    assert_eq!(inst.opcode, AArch64Opcode::Nop);
    assert_eq!(inst.flags, InstFlags::IS_PSEUDO);
    assert!(inst.operands.is_empty());
    assert!(inst.implicit_defs.is_empty());
    assert!(inst.implicit_uses.is_empty());
    assert!(inst.proof.is_none());
    assert!(inst.source_loc.is_none());
    assert!(func.blocks.iter().all(|block| !block.insts.contains(&id)));
}

fn assert_same_instruction(after: &MachInst, before: &MachInst) {
    assert_eq!(after.opcode, before.opcode);
    assert_eq!(after.operands, before.operands);
    assert_eq!(after.implicit_defs, before.implicit_defs);
    assert_eq!(after.implicit_uses, before.implicit_uses);
    assert_eq!(after.flags, before.flags);
    assert_eq!(after.proof, before.proof);
    assert_eq!(after.source_loc, before.source_loc);
}

#[test]
fn pure_elision_retires_exact_ids_preserves_source_history_and_is_idempotent() {
    let mut func = function("retirement", 3);
    let first = add(
        &mut func,
        0,
        branch(1)
            .with_proof(ProofAnnotation::Pure)
            .with_source_loc(SourceLoc {
                file: 2,
                line: 19,
                col: 4,
            }),
    );
    let body = add(
        &mut func,
        1,
        arithmetic(AArch64Opcode::AddRI)
            .with_proof(ProofAnnotation::NoSignedOverflow)
            .with_source_loc(SourceLoc {
                file: 2,
                line: 20,
                col: 4,
            }),
    );
    let second = add(&mut func, 1, branch(2));
    let exit = add(&mut func, 2, ret());
    func.add_edge(BlockId(0), BlockId(1));
    func.add_edge(BlockId(1), BlockId(2));
    for (id, block) in [(first, 0), (second, 1), (body, 1)] {
        func.set_inst_lowering_provenance(id, attribution(block));
    }
    let before = func.clone();
    assert!(aarch64_elide_branch_to_next(&mut func));
    for id in [first, second] {
        assert_retired(&func, id);
        assert_eq!(
            func.inst_lowering_provenance(id),
            before.inst_lowering_provenance(id)
        );
    }
    assert_eq!(func.insts.len(), before.insts.len());
    assert_eq!(func.block_order, before.block_order);
    assert_same_instruction(func.inst(body), before.inst(body));
    assert_same_instruction(func.inst(exit), before.inst(exit));
    assert_eq!(func.inst_lowering_provenance(body), attribution(1));
    for (after, before) in func.blocks.iter().zip(&before.blocks) {
        assert_eq!(after.preds, before.preds);
        assert_eq!(after.succs, before.succs);
    }
    let once = format!("{func:?}");
    assert!(!aarch64_elide_branch_to_next(&mut func));
    assert_eq!(format!("{func:?}"), once);
}

#[test]
fn trailing_pseudos_survive_while_only_the_last_real_branch_is_retired() {
    let mut func = function("trailing_pseudos", 2);
    let body = add(&mut func, 0, arithmetic(AArch64Opcode::AddRI));
    let removed = add(&mut func, 0, branch(1));
    let copy = add(
        &mut func,
        0,
        MachInst::new(
            AArch64Opcode::Copy,
            vec![MachOperand::PReg(X0), MachOperand::PReg(X0)],
        ),
    );
    let nop = add(&mut func, 0, MachInst::new(AArch64Opcode::Nop, vec![]));
    add(&mut func, 1, ret());
    func.add_edge(BlockId(0), BlockId(1));
    let before = func.clone();
    assert!(aarch64_elide_branch_to_next(&mut func));
    assert_retired(&func, removed);
    assert_eq!(func.block(BlockId(0)).insts, [body, copy, nop]);
    for id in [body, copy, nop] {
        assert_same_instruction(func.inst(id), before.inst(id));
    }
    assert!(!aarch64_elide_branch_to_next(&mut func));
}

#[test]
fn malformed_or_effectful_branches_and_other_control_are_not_retired() {
    for mutation in 0..15 {
        let mut func = function("must_keep", 3);
        let mut inst = branch(1);
        match mutation {
            0 => inst.operands.push(MachOperand::Imm(0)),
            1 => inst.operands.push(MachOperand::Block(BlockId(1))),
            2 => inst.operands = vec![MachOperand::Symbol("callee".into())],
            3 => inst.operands = vec![MachOperand::Imm(1)],
            4 => inst.operands = vec![MachOperand::Block(BlockId(2))],
            5 => inst.operands.clear(),
            6 => inst.flags |= InstFlags::HAS_SIDE_EFFECTS,
            7 => inst.flags |= InstFlags::IS_CALL,
            8 => inst.flags = InstFlags::EMPTY,
            9 => inst.flags |= InstFlags::IS_PSEUDO,
            10 => inst.implicit_defs = &[X9],
            11 => inst.implicit_uses = &[X0],
            12 => {
                inst = MachInst::new(
                    AArch64Opcode::BCond,
                    vec![MachOperand::Imm(0), MachOperand::Block(BlockId(1))],
                )
            }
            13 => {
                inst = MachInst::new(
                    AArch64Opcode::Cbz,
                    vec![MachOperand::PReg(X0), MachOperand::Block(BlockId(1))],
                )
            }
            _ => inst = MachInst::new(AArch64Opcode::Br, vec![MachOperand::PReg(X9)]),
        }
        let id = add(&mut func, 0, inst.with_proof(ProofAnnotation::Pure));
        add(&mut func, 1, ret());
        add(&mut func, 2, ret());
        func.set_inst_lowering_provenance(id, attribution(0));
        let before = format!("{func:?}");
        assert!(
            !aarch64_elide_branch_to_next(&mut func),
            "mutation {mutation}"
        );
        assert_eq!(format!("{func:?}"), before, "mutation {mutation}");
        assert!(func.block(BlockId(0)).insts.contains(&id));
        assert_eq!(func.inst_lowering_provenance(id), attribution(0));
    }
    let mut func = function("nonterminal_branch", 2);
    let id = add(&mut func, 0, branch(1));
    add(&mut func, 0, arithmetic(AArch64Opcode::AddRI));
    add(&mut func, 1, ret());
    let before = format!("{func:?}");
    assert!(!aarch64_elide_branch_to_next(&mut func));
    assert_eq!(format!("{func:?}"), before);
    assert_eq!(func.inst(id).opcode, AArch64Opcode::B);
}

#[test]
fn landing_pad_keeps_its_only_real_branch_and_all_eh_metadata() {
    for has_real_body in [false, true] {
        let mut func = function("landing_pad", 2);
        if has_real_body {
            add(&mut func, 0, arithmetic(AArch64Opcode::AddRI));
        }
        let removed = add(&mut func, 0, branch(1));
        add(&mut func, 0, MachInst::new(AArch64Opcode::Nop, vec![]));
        add(&mut func, 1, ret());
        func.add_edge(BlockId(0), BlockId(1));
        func.eh_metadata.add_landing_pad(LandingPadEntry {
            block: BlockId(0),
            offset: 44,
            catch_type_indices: vec![0, 3],
            is_cleanup: true,
        });
        let before = func.clone();
        assert_eq!(aarch64_elide_branch_to_next(&mut func), has_real_body);
        assert_eq!(func.eh_metadata.personality, before.eh_metadata.personality);
        assert_eq!(
            func.eh_metadata.landing_pads,
            before.eh_metadata.landing_pads
        );
        assert_eq!(func.eh_metadata.call_sites, before.eh_metadata.call_sites);
        assert_eq!(
            func.eh_metadata.eh_type_table,
            before.eh_metadata.eh_type_table
        );
        if has_real_body {
            assert_retired(&func, removed);
        } else {
            assert_same_instruction(func.inst(removed), before.inst(removed));
            assert_eq!(func.block(BlockId(0)).insts, before.block(BlockId(0)).insts);
        }
    }
}

fn diamond() -> (MachFunction, [InstId; 2]) {
    let mut func = function("encoded_diamond", 4);
    add(
        &mut func,
        0,
        MachInst::new(
            AArch64Opcode::CmpRR,
            vec![MachOperand::PReg(X0), MachOperand::PReg(X1)],
        ),
    );
    add(
        &mut func,
        0,
        MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Imm(0), MachOperand::Block(BlockId(1))],
        ),
    );
    let first = add(&mut func, 0, branch(2));
    add(&mut func, 1, arithmetic(AArch64Opcode::AddRI));
    add(&mut func, 1, branch(3));
    add(
        &mut func,
        2,
        MachInst::new(
            AArch64Opcode::SubRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(1),
            ],
        ),
    );
    let second = add(&mut func, 2, branch(3));
    add(&mut func, 3, ret());
    for (from, to) in [(0, 1), (0, 2), (1, 3), (2, 3)] {
        func.add_edge(BlockId(from), BlockId(to));
    }
    func.block_order = vec![BlockId(0), BlockId(2), BlockId(3), BlockId(1)];
    (func, [first, second])
}

#[test]
fn retirement_preserves_the_historical_elided_diamonds_actual_encoded_words() {
    for trailing_nop in [false, true] {
        let (mut func, removed) = diamond();
        if trailing_nop {
            add(&mut func, 0, MachInst::new(AArch64Opcode::Nop, vec![]));
            add(&mut func, 2, MachInst::new(AArch64Opcode::Nop, vec![]));
        }
        // Independent historical-elision oracle: remove the two known
        // layout-next edges from executable blocks but retain their arena B.
        let mut historical = func.clone();
        for block in &mut historical.blocks {
            block.insts.retain(|id| !removed.contains(id));
        }
        assert!(aarch64_elide_branch_to_next(&mut func));
        for id in removed {
            assert_retired(&func, id);
        }
        crate::pipeline::resolve_branches(&mut func).unwrap();
        crate::pipeline::resolve_branches(&mut historical).unwrap();
        let code = crate::pipeline::encode_function(&func).unwrap();
        assert_eq!(code, crate::pipeline::encode_function(&historical).unwrap());
        assert_eq!(
            code,
            crate::pipeline::encode_function_with_fixups(&func)
                .unwrap()
                .0
        );
        let words: Vec<_> = code
            .as_chunks::<4>()
            .0
            .iter()
            .map(|word| u32::from_le_bytes(*word))
            .collect();
        assert_eq!(
            words,
            [
                0xeb01_001f,
                0x5400_0060,
                0xd100_0420,
                0xd65f_03c0,
                0x9100_0400,
                0x17ff_fffe
            ]
        );
    }
}
