use super::*;
use crate::eh_call_custody::tests::{bind_exact, bind_legacy, snapshot};
use trust_cg_ir::regs::{SP, X0, X1, X2, X3};

fn memcpy_fill() -> (MachFunction, InstId) {
    let mut func = new_func();
    let entry = func.entry;
    let slot = with_slot(&mut func, 16, 4);
    func.next_vreg = 40;
    for inst in [
        MachInst::new(AArch64Opcode::Copy, vec![g64(1), MachOperand::PReg(X1)]),
        MachInst::new(
            AArch64Opcode::AddPCRel,
            vec![g64(10), MachOperand::PReg(SP), MachOperand::StackSlot(slot)],
        ),
        MachInst::new(AArch64Opcode::Movz, vec![g64(2), imm(16)]),
        MachInst::new(AArch64Opcode::Movz, vec![g64(3), imm(0)]),
        MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X0), g64(10)]),
        MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X1), g64(1)]),
        MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X2), g64(2)]),
        MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(X3), g64(3)]),
    ] {
        push(&mut func, entry, inst);
    }
    // The `bl memcpy` instruction selection makes for a LIR `Memcpy`, the
    // only one the fill reads; the EH custody below is what keeps it.
    let call = push(&mut func, entry, library_memcpy_call());
    for inst in [
        MachInst::new(AArch64Opcode::AddRI, vec![g64(11), g64(10), imm(4)]),
        MachInst::new(AArch64Opcode::LdrRI, vec![g32(20), g64(10), imm(0)]),
        MachInst::new(AArch64Opcode::LdrRI, vec![g32(21), g64(11), imm(0)]),
        MachInst::new(AArch64Opcode::Ret, vec![]),
    ] {
        push(&mut func, entry, inst);
    }
    (func, call)
}

#[test]
fn protected_memcpy_fill_is_not_deleted_even_for_a_private_promotable_slot() {
    for legacy in [false, true] {
        let (mut func, call) = memcpy_fill();
        let entry = func.entry;
        if legacy {
            bind_legacy(&mut func, entry);
        } else {
            bind_exact(&mut func, call, entry);
        }
        let before = snapshot(&func);
        assert!(!ScalarReplacementOfAggregates.run(&mut func));
        assert_eq!(snapshot(&func), before);
    }
    let (mut ordinary, call) = memcpy_fill();
    assert!(ScalarReplacementOfAggregates.run(&mut ordinary));
    assert!(!ordinary.block(ordinary.entry).insts.contains(&call));
}
