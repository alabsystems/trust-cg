// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Regression controls for the shared NZCV read/may-write/definite-kill boundary.
//! These are concrete classification and graph-walk tests, not independent proof.

use crate::effects::{
    definitely_writes_flags, kills_nzcv, may_clobber_nzcv, nzcv_dead_after_branch,
    nzcv_dead_at_block_entry, nzcv_unknown, reads_nzcv, writes_flags,
};
use trust_cg_ir::aarch64_regs::{D0, D1, NZCV, V0, W0, W1, W2, W4, X0, X1, X2, X3, X4};
use trust_cg_ir::llsc::{LlscOrdering, LlscPseudo, LlscRmwOp, LlscWidth};
use trust_cg_ir::{
    AArch64Opcode as Op, BlockId, InstFlags, MachFunction, MachInst, MachOperand, PReg,
};

fn reg(value: PReg) -> MachOperand {
    MachOperand::PReg(value)
}

fn architectural_writer(opcode: Op) -> MachInst {
    let operands = match opcode {
        Op::CmpRR | Op::CMPXrr | Op::Tst => vec![reg(X0), reg(X1)],
        Op::CMPWrr => vec![reg(W0), reg(W1)],
        Op::CmpRI | Op::CMPXri => vec![reg(X0), MachOperand::Imm(1)],
        Op::CMPWri => vec![reg(W0), MachOperand::Imm(1)],
        Op::Fcmp => vec![reg(D0), reg(D1)],
        Op::AddsRR | Op::SubsRR | Op::Adcs | Op::Sbcs => vec![reg(X2), reg(X0), reg(X1)],
        Op::AddsRI | Op::SubsRI => vec![reg(X2), reg(X0), MachOperand::Imm(1)],
        other => panic!("not a fixture architectural flag writer: {other:?}"),
    };
    MachInst::new(opcode, operands)
}

fn reader(opcode: Op) -> MachInst {
    let operands = match opcode {
        Op::CSet => vec![reg(W2), MachOperand::Imm(0)],
        Op::Csel | Op::Csinc | Op::Csinv | Op::Csneg => {
            vec![reg(X2), reg(X0), reg(X1), MachOperand::Imm(0)]
        }
        Op::Adc | Op::Sbc | Op::Adcs | Op::Sbcs => vec![reg(X2), reg(X0), reg(X1)],
        Op::BCond | Op::Bcc => vec![MachOperand::Imm(0), MachOperand::Block(BlockId(0))],
        other => panic!("not a fixture flag reader: {other:?}"),
    };
    MachInst::new(opcode, operands)
}

fn call(opcode: Op) -> MachInst {
    let target = match opcode {
        Op::Bl | Op::BL => MachOperand::Symbol("ordinary_abi_callee".into()),
        Op::Blr | Op::BLR => reg(X4),
        other => panic!("not a fixture ordinary ABI call: {other:?}"),
    };
    MachInst::new(opcode, vec![target])
}

fn llsc(pseudo: LlscPseudo) -> MachInst {
    let ordering = MachOperand::Imm(LlscOrdering::ACQ_REL.to_imm());
    let operation = MachOperand::Imm(LlscRmwOp::Add.to_imm());
    let operands = match pseudo {
        LlscPseudo::Rmw(LlscWidth::B128) => vec![
            reg(X0),
            reg(X1),
            reg(X2),
            reg(X3),
            reg(W4),
            reg(trust_cg_ir::aarch64_regs::X5),
            reg(trust_cg_ir::aarch64_regs::X6),
            reg(trust_cg_ir::aarch64_regs::X7),
            operation,
            ordering,
        ],
        LlscPseudo::Rmw(width) => {
            let (old, new, value) = if width == LlscWidth::B64 {
                (X0, X1, X3)
            } else {
                (W0, W1, trust_cg_ir::aarch64_regs::W3)
            };
            vec![
                reg(old),
                reg(new),
                reg(W2),
                reg(value),
                reg(X4),
                operation,
                ordering,
            ]
        }
        LlscPseudo::CmpSwap(LlscWidth::B128) => vec![
            reg(X0),
            reg(X1),
            reg(W2),
            reg(X3),
            reg(X4),
            reg(trust_cg_ir::aarch64_regs::X5),
            reg(trust_cg_ir::aarch64_regs::X6),
            reg(trust_cg_ir::aarch64_regs::X7),
            ordering,
        ],
        LlscPseudo::CmpSwap(width) => {
            let (old, expected, desired) = if width == LlscWidth::B64 {
                (X0, X2, X3)
            } else {
                (W0, W2, trust_cg_ir::aarch64_regs::W3)
            };
            vec![
                reg(old),
                reg(W1),
                reg(expected),
                reg(desired),
                reg(X4),
                ordering,
            ]
        }
        LlscPseudo::Load128 => vec![reg(X0), reg(X1), reg(W2), reg(X3), ordering],
        LlscPseudo::Store128 => {
            vec![
                reg(X0),
                reg(X1),
                reg(W2),
                reg(X3),
                reg(X4),
                reg(trust_cg_ir::aarch64_regs::X5),
                ordering,
            ]
        }
    };
    assert_eq!(operands.len(), pseudo.operand_count(), "{pseudo:?}");
    MachInst::new(pseudo.opcode(), operands)
}

fn successor_function(barrier: MachInst) -> MachFunction {
    let mut function = MachFunction::new(
        "nzcv_helper_control".into(),
        trust_cg_ir::Signature::new(vec![], vec![]),
    );
    let successor = function.create_block();
    for instruction in [
        MachInst::new(Op::Cbz, vec![reg(X4), MachOperand::Block(successor)]),
        MachInst::new(Op::B, vec![MachOperand::Block(successor)]),
    ] {
        let id = function.push_inst(instruction);
        function.append_inst(function.entry, id);
    }
    function.add_edge(function.entry, successor);
    for instruction in [barrier, reader(Op::CSet), MachInst::new(Op::Ret, vec![])] {
        let id = function.push_inst(instruction);
        function.append_inst(successor, id);
    }
    function
}

#[test]
fn every_llsc_pseudo_is_a_may_writer_but_never_a_definite_kill() {
    assert_eq!(LlscPseudo::ALL.len(), 12);
    for pseudo in LlscPseudo::ALL {
        let mut instruction = llsc(pseudo);
        // Real LL/SC carriers do not carry IS_PSEUDO. Opcode ownership, not
        // that metadata bit, must preserve the opaque-expansion boundary.
        assert!(
            !instruction.flags.contains(InstFlags::IS_PSEUDO),
            "{pseudo:?}"
        );
        for flags in [instruction.flags, InstFlags::EMPTY, InstFlags::IS_PSEUDO] {
            instruction.flags = flags;
            assert!(writes_flags(instruction.opcode), "{pseudo:?}, {flags:?}");
            assert!(!definitely_writes_flags(instruction.opcode), "{pseudo:?}");
            assert!(!reads_nzcv(&instruction), "{pseudo:?}, {flags:?}");
            assert!(nzcv_unknown(&instruction), "{pseudo:?}, {flags:?}");
            assert!(!kills_nzcv(&instruction), "{pseudo:?}, {flags:?}");
            assert!(may_clobber_nzcv(&instruction), "{pseudo:?}, {flags:?}");
        }
    }
}

#[test]
fn architectural_writes_kill_only_when_the_instruction_does_not_read_flags() {
    for opcode in [
        Op::CmpRR,
        Op::CmpRI,
        Op::CMPWrr,
        Op::CMPXrr,
        Op::CMPWri,
        Op::CMPXri,
        Op::Tst,
        Op::Fcmp,
        Op::AddsRR,
        Op::AddsRI,
        Op::SubsRR,
        Op::SubsRI,
        Op::Adcs,
        Op::Sbcs,
    ] {
        let instruction = architectural_writer(opcode);
        let reads_carry = matches!(opcode, Op::Adcs | Op::Sbcs);
        assert!(writes_flags(opcode), "{opcode:?}");
        assert!(definitely_writes_flags(opcode), "{opcode:?}");
        assert_eq!(reads_nzcv(&instruction), reads_carry, "{opcode:?}");
        assert!(!nzcv_unknown(&instruction), "{opcode:?}");
        assert_eq!(kills_nzcv(&instruction), !reads_carry, "{opcode:?}");
    }
}

#[test]
fn explicit_nzcv_uses_take_precedence_over_writer_and_call_kills() {
    for mut instruction in [
        architectural_writer(Op::CmpRR),
        architectural_writer(Op::AddsRI),
        call(Op::Bl),
        call(Op::Blr),
        MachInst::new(Op::MovR, vec![reg(X2), reg(X0)]),
        llsc(LlscPseudo::Rmw(LlscWidth::B32)),
    ] {
        instruction.implicit_uses = &[X0, NZCV];
        assert!(reads_nzcv(&instruction), "{:?}", instruction.opcode);
        assert!(!kills_nzcv(&instruction), "{:?}", instruction.opcode);
    }
}

#[test]
fn implicit_nzcv_definitions_are_opaque_even_on_writers_calls_and_nops() {
    for mut instruction in [
        architectural_writer(Op::CmpRI),
        call(Op::Bl),
        call(Op::Blr),
        MachInst::new(Op::Copy, vec![reg(X2), reg(X0)]),
        MachInst::new(Op::Nop, vec![]),
    ] {
        instruction.implicit_defs = &[X0, NZCV];
        assert!(!reads_nzcv(&instruction), "{:?}", instruction.opcode);
        assert!(nzcv_unknown(&instruction), "{:?}", instruction.opcode);
        assert!(!kills_nzcv(&instruction), "{:?}", instruction.opcode);
        instruction.implicit_uses = &[NZCV];
        assert!(reads_nzcv(&instruction), "{:?}", instruction.opcode);
        assert!(nzcv_unknown(&instruction), "{:?}", instruction.opcode);
        assert!(!kills_nzcv(&instruction), "{:?}", instruction.opcode);
    }
}

#[test]
fn ordinary_abi_register_arguments_and_clobbers_do_not_become_nzcv_effects() {
    for opcode in [Op::Bl, Op::Blr, Op::BL, Op::BLR] {
        let instruction = call(opcode)
            .with_implicit_uses(&[X0, X1, V0])
            .with_implicit_defs(&[X0, X1, X2, V0]);
        assert!(!reads_nzcv(&instruction), "{opcode:?}");
        assert!(!nzcv_unknown(&instruction), "{opcode:?}");
        assert!(kills_nzcv(&instruction), "{opcode:?}");
        assert!(may_clobber_nzcv(&instruction), "{opcode:?}");
        assert!(!definitely_writes_flags(opcode), "{opcode:?}");
    }
}

#[test]
fn reader_transparent_and_opaque_pseudo_controls_remain_distinct() {
    for opcode in [
        Op::CSet,
        Op::Csel,
        Op::Csinc,
        Op::Csinv,
        Op::Csneg,
        Op::Adc,
        Op::Sbc,
        Op::Adcs,
        Op::Sbcs,
        Op::BCond,
        Op::Bcc,
    ] {
        let instruction = reader(opcode);
        assert!(reads_nzcv(&instruction), "{opcode:?}");
        assert!(!kills_nzcv(&instruction), "{opcode:?}");
    }
    for instruction in [
        MachInst::new(Op::Copy, vec![reg(X2), reg(X0)]),
        MachInst::new(Op::Nop, vec![]),
        MachInst::new(Op::AddRR, vec![reg(X2), reg(X0), reg(X1)]),
        MachInst::new(Op::Ret, vec![]),
    ] {
        assert!(!reads_nzcv(&instruction), "{:?}", instruction.opcode);
        assert!(!nzcv_unknown(&instruction), "{:?}", instruction.opcode);
        assert!(!kills_nzcv(&instruction), "{:?}", instruction.opcode);
    }
    let instruction = MachInst::with_flags(Op::MovR, vec![reg(X2), reg(X0)], InstFlags::IS_PSEUDO);
    assert!(nzcv_unknown(&instruction));
    assert!(!kills_nzcv(&instruction));
}

#[test]
fn generic_system_register_reads_remain_opaque_for_every_metadata_view() {
    for operands in [
        vec![reg(X0), MachOperand::Imm(0xDA10)], // NZCV, not a TLS read.
        vec![reg(X0), MachOperand::Imm(0xDE82)], // No per-key exemption.
        vec![reg(X0), MachOperand::Imm(-1)],
        vec![],
    ] {
        let mut instruction = MachInst::new(Op::Mrs, operands);
        for flags in [instruction.flags, InstFlags::EMPTY, InstFlags::IS_PSEUDO] {
            instruction.flags = flags;
            assert!(nzcv_unknown(&instruction), "{instruction:?}");
            assert!(may_clobber_nzcv(&instruction), "{instruction:?}");
            assert!(!kills_nzcv(&instruction), "{instruction:?}");
        }
        instruction.implicit_uses = &[NZCV];
        instruction.implicit_defs = &[NZCV];
        assert!(reads_nzcv(&instruction));
        assert!(nzcv_unknown(&instruction));
        assert!(may_clobber_nzcv(&instruction));
        assert!(!kills_nzcv(&instruction));
    }
}

#[test]
fn shared_successor_walks_do_not_skip_generic_system_register_observers() {
    for key in [0xDA10, 0xDE82] {
        let observer = MachInst::new(Op::Mrs, vec![reg(X0), MachOperand::Imm(key)]);
        let mut function = successor_function(observer.clone());
        let successor = function.block(function.entry).succs[0];
        // A later guaranteed overwrite does not hide the preceding opaque
        // observer; exercise both shared entry and post-branch APIs.
        let after_observer = function.block(successor).insts[1];
        *function.inst_mut(after_observer) = architectural_writer(Op::CmpRI);
        let deleted = crate::fast_hash::FxHashSet::default();
        assert!(!nzcv_dead_at_block_entry(&function, function.entry));
        assert!(!nzcv_dead_after_branch(
            &function,
            function.entry,
            0,
            &deleted
        ));

        // This is not a blanket kill switch: the same opaque access after an
        // actual overwrite cannot observe flags that preceded that writer.
        let first = function.block(successor).insts[0];
        *function.inst_mut(first) = architectural_writer(Op::CmpRI);
        *function.inst_mut(after_observer) = observer;
        assert!(nzcv_dead_at_block_entry(&function, function.entry));
        assert!(nzcv_dead_after_branch(
            &function,
            function.entry,
            0,
            &deleted
        ));
    }
}

#[test]
fn shared_successor_walks_never_use_llsc_may_writes_as_kills() {
    for pseudo in LlscPseudo::ALL {
        let function = successor_function(llsc(pseudo));
        let deleted = crate::fast_hash::FxHashSet::default();
        assert!(
            !nzcv_dead_at_block_entry(&function, function.entry),
            "{pseudo:?}"
        );
        assert!(
            !nzcv_dead_after_branch(&function, function.entry, 0, &deleted),
            "{pseudo:?}"
        );
    }
    for barrier in [architectural_writer(Op::CmpRI), call(Op::Bl)] {
        let function = successor_function(barrier);
        let deleted = crate::fast_hash::FxHashSet::default();
        assert!(nzcv_dead_at_block_entry(&function, function.entry));
        assert!(nzcv_dead_after_branch(
            &function,
            function.entry,
            0,
            &deleted
        ));
    }
}
