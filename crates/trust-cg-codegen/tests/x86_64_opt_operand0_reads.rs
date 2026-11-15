// trust-cg-codegen/tests/x86_64_opt_operand0_reads.rs - x86 machine passes keep the defs that operand-0 reads need
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The production x86 pass order (`X86Pipeline::run_x86_optimization_passes`
//! at O1, O2 and O3) must not delete the definition of a register that an
//! instruction reads through its operand 0.
//!
//! `trust_cg_opt::effects::x86_produces_value` was a blacklist, so opcodes
//! appended after it was written answered "operand 0 is a def" by default. For
//! the volatile stores and the narrow compare-exchanges operand 0 is a READ —
//! the destination address and the desired value — so x86 DCE never counted
//! the read, found the defining `Lea` / `MovRR32` unused, and deleted it. The
//! object still compiled. Measured on the unfixed tree, compiling trust IR
//! through the production `Compiler` at O2: a volatile store to an `Alloca`
//! became `mov qword ptr [rcx], rdi` with `rcx` never written, and an `i8`
//! `CmpXchg` became `lock cmpxchg byte ptr [rdx], r8b` with `r8b` never
//! written — run under Rosetta, compare-exchange(slot = 1, expected 1,
//! desired 5) returned 107.
//!
//! The shapes below are the ones instruction selection emits
//! (`select_memory_store` after a `StackAddr` `Lea`, and `select_cmpxchg`).
//! A register can only be defined by an instruction that names it in operand
//! 0, so each check asks for such an instruction before the read — a
//! necessary condition that does not depend on the def/use model under test.
//! Host-neutral: nothing here executes x86 code.

use trust_cg_codegen::x86_64::{X86Pipeline, X86PipelineConfig};
use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_ir::x86_64_regs::{EAX, EDX, ESI, RAX, RDI};
use trust_cg_lower::function::{Signature, StackSlotInfo};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::types::Type;
use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst, X86ISelOperand};
use trust_cg_opt::OptLevel;

const OPT_LEVELS: [OptLevel; 3] = [OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn vreg(id: u32, class: RegClass) -> VReg {
    VReg::new(id, class)
}

fn op(v: VReg) -> X86ISelOperand {
    X86ISelOperand::VReg(v)
}

fn mem(base: X86ISelOperand) -> X86ISelOperand {
    X86ISelOperand::MemAddr {
        base: Box::new(base),
        disp: 0,
    }
}

fn function(name: &str, params: Vec<Type>, returns: Vec<Type>) -> X86ISelFunction {
    let mut func = X86ISelFunction::new(name.to_string(), Signature { params, returns });
    func.ensure_block(Block(0));
    func.next_vreg = 16;
    func
}

fn optimize(mut func: X86ISelFunction, opt_level: OptLevel) -> X86ISelFunction {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level,
        ..X86PipelineConfig::default()
    });
    let _ = pipeline.run_x86_optimization_passes(&mut func);
    func
}

fn entry(func: &X86ISelFunction) -> &[X86ISelInst] {
    &func.blocks[&Block(0)].insts
}

/// The index of the first `opcode` in the entry block.
fn position(insts: &[X86ISelInst], opcode: X86Opcode) -> usize {
    insts
        .iter()
        .position(|inst| inst.opcode == opcode)
        .unwrap_or_else(|| panic!("{opcode:?} must survive: {insts:#?}"))
}

/// Some instruction before `index` names `v` in operand 0.
fn written_before(insts: &[X86ISelInst], index: usize, v: VReg) -> bool {
    insts[..index]
        .iter()
        .any(|inst| inst.operands.first() == Some(&op(v)))
}

/// `let mut x = 0; ptr::write_volatile(&mut x, 5);` — the address is a `Lea`
/// of the stack slot, and the store's operand 0 is `[address + 0]`.
fn volatile_store_to_local(store: X86Opcode, value_class: RegClass) -> X86ISelFunction {
    let mut func = function("volatile_store_to_local", vec![], vec![Type::I64]);
    func.stack_slots.push(StackSlotInfo::new(8, 8));
    let address = vreg(1, RegClass::Gpr64);
    let value = vreg(2, value_class);
    let zero = vreg(3, RegClass::Gpr64);
    for inst in [
        X86ISelInst::new(
            X86Opcode::Lea,
            vec![op(address), mem(X86ISelOperand::StackSlot(0))],
        ),
        X86ISelInst::new(X86Opcode::MovRI, vec![op(value), X86ISelOperand::Imm(5)]),
        X86ISelInst::new(store, vec![mem(op(address)), op(value)]),
        X86ISelInst::new(X86Opcode::MovRI, vec![op(zero), X86ISelOperand::Imm(0)]),
        X86ISelInst::new(X86Opcode::MovRR, vec![X86ISelOperand::PReg(RAX), op(zero)]),
        X86ISelInst::new(X86Opcode::Ret, vec![]),
    ] {
        func.push_inst(Block(0), inst);
    }
    func
}

#[test]
fn a_volatile_store_keeps_the_def_of_its_address() {
    for (store, value_class) in [
        (X86Opcode::VolatileMovMR, RegClass::Gpr64),
        (X86Opcode::VolatileMovMR32, RegClass::Gpr32),
        (X86Opcode::VolatileMovMR16, RegClass::Gpr32),
        (X86Opcode::VolatileMovMR8, RegClass::Gpr32),
    ] {
        for opt_level in OPT_LEVELS {
            let func = optimize(volatile_store_to_local(store, value_class), opt_level);
            let insts = entry(&func);
            let at = position(insts, store);
            let Some(X86ISelOperand::MemAddr { base, .. }) = insts[at].operands.first() else {
                panic!("{store:?} at {opt_level:?} lost its address operand: {insts:#?}");
            };
            match base.as_ref() {
                // Folding the slot straight into the store is a legal outcome.
                X86ISelOperand::StackSlot(0) => {}
                X86ISelOperand::VReg(address) => assert!(
                    written_before(insts, at, *address),
                    "{store:?} at {opt_level:?} stores through {address:?}, which nothing \
                     writes: {insts:#?}"
                ),
                other => panic!("{store:?} at {opt_level:?}: unexpected base {other:?}"),
            }
        }
    }
}

/// `select_cmpxchg`: `desired' := desired; EAX := expected;
/// CMPXCHG [desired', MemAddr]; result := EAX`.
fn compare_exchange(cmpxchg: X86Opcode) -> X86ISelFunction {
    let mut func = function(
        "compare_exchange",
        vec![Type::I64, Type::I32, Type::I32],
        vec![Type::I32],
    );
    let pointer = vreg(1, RegClass::Gpr64);
    let expected = vreg(2, RegClass::Gpr32);
    let desired = vreg(3, RegClass::Gpr32);
    let desired_copy = vreg(4, RegClass::Gpr32);
    let result = vreg(5, RegClass::Gpr32);
    for inst in [
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![op(pointer), X86ISelOperand::PReg(RDI)],
        ),
        X86ISelInst::new(
            X86Opcode::MovRR32,
            vec![op(expected), X86ISelOperand::PReg(ESI)],
        ),
        X86ISelInst::new(
            X86Opcode::MovRR32,
            vec![op(desired), X86ISelOperand::PReg(EDX)],
        ),
        X86ISelInst::new(X86Opcode::MovRR32, vec![op(desired_copy), op(desired)]),
        X86ISelInst::new(
            X86Opcode::MovRR32,
            vec![X86ISelOperand::PReg(EAX), op(expected)],
        ),
        X86ISelInst::new(cmpxchg, vec![op(desired_copy), mem(op(pointer))]),
        X86ISelInst::new(
            X86Opcode::MovRR32,
            vec![op(result), X86ISelOperand::PReg(EAX)],
        ),
        X86ISelInst::new(
            X86Opcode::MovRR32,
            vec![X86ISelOperand::PReg(EAX), op(result)],
        ),
        X86ISelInst::new(X86Opcode::Ret, vec![]),
    ] {
        func.push_inst(Block(0), inst);
    }
    func
}

#[test]
fn a_compare_exchange_keeps_the_def_of_its_desired_value() {
    for cmpxchg in [
        X86Opcode::Cmpxchg,
        X86Opcode::Cmpxchg16,
        X86Opcode::Cmpxchg8,
    ] {
        for opt_level in OPT_LEVELS {
            let func = optimize(compare_exchange(cmpxchg), opt_level);
            let insts = entry(&func);
            let at = position(insts, cmpxchg);
            let Some(X86ISelOperand::VReg(desired)) = insts[at].operands.first() else {
                panic!("{cmpxchg:?} at {opt_level:?} lost its desired value: {insts:#?}");
            };
            assert!(
                written_before(insts, at, *desired),
                "{cmpxchg:?} at {opt_level:?} exchanges in {desired:?}, which nothing writes: \
                 {insts:#?}"
            );
        }
    }
}
