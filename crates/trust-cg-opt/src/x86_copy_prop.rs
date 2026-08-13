// trust-cg-opt - x86-64 Copy Propagation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Conservative copy propagation for x86-64 ISel-output functions.
//!
//! This pass is intentionally scoped to the x86 pass-manager surface. It is not
//! part of the default x86 codegen pipeline.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::regs::RegClass;
use trust_cg_ir::{VReg, X86Opcode};
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::effects::{x86_inst_effect, x86_produces_value, x86_reads_flags, x86_writes_flags};
use crate::x86_pass_manager::X86MachinePass;

const MAX_COPY_CHAIN: usize = 16;

/// Copy propagation for x86-64 ISel-output machine functions.
pub struct X86CopyPropagation;

impl X86CopyPropagation {
    /// Run x86 copy propagation directly on an ISel function.
    pub fn run_on_function(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func)
    }
}

impl X86MachinePass for X86CopyPropagation {
    fn name(&self) -> &str {
        "x86-copy-prop"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func)
    }
}

fn run_impl(func: &mut X86ISelFunction) -> bool {
    let mut changed = false;

    for block_id in func.block_order.clone() {
        let Some(block) = func.blocks.get_mut(&block_id) else {
            continue;
        };

        let mut copies = HashMap::new();

        for inst in &mut block.insts {
            if is_copy_prop_barrier(inst) {
                if can_rewrite_uses_before_clearing_barrier(inst)
                    && rewrite_use_operands(inst, &copies)
                {
                    changed = true;
                }
                copies.clear();
                continue;
            }

            if rewrite_use_operands(inst, &copies) {
                changed = true;
            }

            if let Some(def) = defined_vreg(inst) {
                invalidate_copies_with_vreg(&mut copies, def);
            }

            if let Some((dst, src)) = copy_vregs(inst) {
                copies.insert(dst, src);
            }
        }
    }

    changed
}

fn rewrite_use_operands(inst: &mut X86ISelInst, copies: &HashMap<VReg, VReg>) -> bool {
    let mut changed = false;
    let use_start = use_operand_start(inst);

    for operand in inst.operands.iter_mut().skip(use_start) {
        changed |= rewrite_operand(operand, copies);
    }

    changed
}

fn rewrite_operand(operand: &mut X86ISelOperand, copies: &HashMap<VReg, VReg>) -> bool {
    match operand {
        X86ISelOperand::VReg(vreg) => {
            let Some(replacement) = resolve_copy(*vreg, copies) else {
                return false;
            };
            *vreg = replacement;
            true
        }
        X86ISelOperand::MemAddr { base, .. } => rewrite_operand(base, copies),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            let base_changed = rewrite_operand(base, copies);
            let index_changed = rewrite_operand(index, copies);
            base_changed || index_changed
        }
        _ => false,
    }
}

fn resolve_copy(vreg: VReg, copies: &HashMap<VReg, VReg>) -> Option<VReg> {
    let mut current = vreg;
    let mut seen = HashSet::new();

    for _ in 0..MAX_COPY_CHAIN {
        if !seen.insert(current) {
            break;
        }

        let Some(next) = copies.get(&current).copied() else {
            break;
        };
        if next.class != vreg.class {
            break;
        }

        current = next;
    }

    (current != vreg).then_some(current)
}

fn copy_vregs(inst: &X86ISelInst) -> Option<(VReg, VReg)> {
    let expected_class = copy_opcode_class(inst.opcode)?;
    if inst.operands.len() != 2 {
        return None;
    }

    let dst = match inst.operands[0] {
        X86ISelOperand::VReg(vreg) => vreg,
        _ => return None,
    };
    let src = match inst.operands[1] {
        X86ISelOperand::VReg(vreg) => vreg,
        _ => return None,
    };

    (dst != src && dst.class == src.class && dst.class == expected_class).then_some((dst, src))
}

fn copy_opcode_class(opcode: X86Opcode) -> Option<RegClass> {
    match opcode {
        X86Opcode::MovRR => Some(RegClass::Gpr64),
        X86Opcode::MovRR32 => Some(RegClass::Gpr32),
        X86Opcode::MovssRR => Some(RegClass::Fpr32),
        X86Opcode::MovsdRR => Some(RegClass::Fpr64),
        X86Opcode::MovdqaRR => Some(RegClass::Fpr128),
        _ => None,
    }
}

fn defined_vreg(inst: &X86ISelInst) -> Option<VReg> {
    if !x86_produces_value(inst.opcode) {
        return None;
    }

    match inst.operands.first() {
        Some(X86ISelOperand::VReg(vreg)) => Some(*vreg),
        _ => None,
    }
}

fn invalidate_copies_with_vreg(copies: &mut HashMap<VReg, VReg>, def: VReg) {
    copies.retain(|dst, src| *dst != def && *src != def);
}

fn use_operand_start(inst: &X86ISelInst) -> usize {
    if x86_produces_value(inst.opcode) && !first_operand_is_def_and_use(inst) {
        1
    } else {
        0
    }
}

fn is_copy_prop_barrier(inst: &X86ISelInst) -> bool {
    let flags = inst.flags;

    !x86_inst_effect(inst).is_pure()
        || inst_touches_fixed_register(inst)
        || flags.is_call()
        || flags.is_branch()
        || flags.is_terminator()
        || flags.is_return()
        || flags.has_side_effects()
        || flags.reads_memory()
        || flags.writes_memory()
        || x86_reads_flags(inst.opcode)
        || x86_writes_flags(inst.opcode)
        || matches!(inst.opcode, X86Opcode::Phi | X86Opcode::StackAlloc)
}

fn can_rewrite_uses_before_clearing_barrier(inst: &X86ISelInst) -> bool {
    can_rewrite_flag_barrier_uses(inst)
        || can_rewrite_memory_barrier_uses(inst)
        || can_rewrite_return_barrier_uses(inst)
}

fn can_rewrite_flag_barrier_uses(inst: &X86ISelInst) -> bool {
    let flags = inst.flags;

    x86_inst_effect(inst).is_pure()
        && !x86_produces_value(inst.opcode)
        && !inst_touches_fixed_register(inst)
        && !flags.is_call()
        && !flags.is_branch()
        && !flags.is_terminator()
        && !flags.is_return()
        && !flags.reads_memory()
        && !flags.writes_memory()
        && !x86_reads_flags(inst.opcode)
        && x86_writes_flags(inst.opcode)
        && is_rewritable_flag_barrier_opcode(inst.opcode)
        && !matches!(inst.opcode, X86Opcode::Phi | X86Opcode::StackAlloc)
}

fn can_rewrite_memory_barrier_uses(inst: &X86ISelInst) -> bool {
    let flags = inst.flags;

    is_rewritable_memory_barrier_opcode(inst.opcode)
        && has_rewritable_memory_operand(inst)
        && !inst_touches_fixed_register(inst)
        && !flags.is_call()
        && !flags.is_branch()
        && !flags.is_terminator()
        && !flags.is_return()
        && !x86_reads_flags(inst.opcode)
        && !x86_writes_flags(inst.opcode)
}

fn can_rewrite_return_barrier_uses(inst: &X86ISelInst) -> bool {
    inst.opcode == X86Opcode::Ret
        && inst.flags.is_return()
        && !inst_touches_fixed_register(inst)
        && inst
            .operands
            .iter()
            .all(|operand| matches!(operand, X86ISelOperand::VReg(_)))
}

fn is_rewritable_flag_barrier_opcode(opcode: X86Opcode) -> bool {
    matches!(
        opcode,
        X86Opcode::CmpRR
            | X86Opcode::CmpRI
            | X86Opcode::CmpRI8
            | X86Opcode::TestRR
            | X86Opcode::TestRI
            | X86Opcode::Ucomisd
            | X86Opcode::Ucomiss
            | X86Opcode::Ptest
    )
}

fn is_rewritable_memory_barrier_opcode(opcode: X86Opcode) -> bool {
    matches!(
        opcode,
        X86Opcode::MovRM8
            | X86Opcode::MovRM16
            | X86Opcode::MovRM32
            | X86Opcode::MovRM
            | X86Opcode::MovMR8
            | X86Opcode::MovMR16
            | X86Opcode::MovMR32
            | X86Opcode::MovMR
            | X86Opcode::MovsdRM
            | X86Opcode::MovsdMR
            | X86Opcode::MovssRM
            | X86Opcode::MovssMR
            | X86Opcode::MovdquRM
            | X86Opcode::MovdquMR
            | X86Opcode::MovdqaRM
            | X86Opcode::MovdqaMR
            | X86Opcode::MovRMSib
            | X86Opcode::MovMRSib
    )
}

fn has_rewritable_memory_operand(inst: &X86ISelInst) -> bool {
    inst.operands.iter().any(|operand| {
        matches!(
            operand,
            X86ISelOperand::MemAddr { .. } | X86ISelOperand::SibMemAddr { .. }
        )
    })
}

fn inst_touches_fixed_register(inst: &X86ISelInst) -> bool {
    inst.operands.iter().any(operand_touches_fixed_register)
}

fn operand_touches_fixed_register(operand: &X86ISelOperand) -> bool {
    match operand {
        X86ISelOperand::PReg(_) => true,
        X86ISelOperand::MemAddr { base, .. } => operand_touches_fixed_register(base),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            operand_touches_fixed_register(base) || operand_touches_fixed_register(index)
        }
        _ => false,
    }
}

fn first_operand_is_def_and_use(inst: &X86ISelInst) -> bool {
    use X86Opcode::*;

    matches!(
        inst.opcode,
        Neg | Not
            | Inc
            | Dec
            | AddRI
            | SubRI
            | AndRI
            | OrRI
            | XorRI
            | AddRM
            | SubRM
            | ImulRM
            | ImulRMSib
            | ShlRI
            | ShrRI
            | SarRI
            | ShlRR
            | ShrRR
            | SarRR
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    use trust_cg_ir::regs::{RegClass, VReg};
    use trust_cg_ir::x86_64_regs::{RAX, RDI};
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::instructions::Block;
    use trust_cg_lower::types::Type;

    use crate::X86PassManager;

    fn vreg(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn vreg32(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr32))
    }

    fn vreg_class(id: u32, class: RegClass) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, class))
    }

    fn xmm(id: u32) -> X86ISelOperand {
        vreg_class(id, RegClass::Fpr128)
    }

    fn mem_addr(base: X86ISelOperand, disp: i32) -> X86ISelOperand {
        X86ISelOperand::MemAddr {
            base: Box::new(base),
            disp,
        }
    }

    fn sib_addr(
        base: X86ISelOperand,
        index: X86ISelOperand,
        scale: u8,
        disp: i32,
    ) -> X86ISelOperand {
        X86ISelOperand::SibMemAddr {
            base: Box::new(base),
            index: Box::new(index),
            scale,
            disp,
        }
    }

    fn make_func(insts: Vec<X86ISelInst>) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("x86_copy_prop_test".to_string(), sig);
        let entry = Block(0);
        func.ensure_block(entry);
        func.next_vreg = 8;
        for inst in insts {
            func.push_inst(entry, inst);
        }
        func
    }

    fn entry_insts(func: &X86ISelFunction) -> &[X86ISelInst] {
        &func.blocks.get(&Block(0)).unwrap().insts
    }

    #[test]
    fn x86_copy_prop_rewrites_movrr_use_through_pass_manager() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut pm = X86PassManager::new().with_pass(Box::new(X86CopyPropagation));

        assert!(pm.run_once(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[1].operands, vec![vreg(2), vreg(0)]);
    }

    #[test]
    fn x86_copy_prop_chases_local_movrr_chain() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(
                X86Opcode::Lea,
                vec![vreg(3), vreg(2), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(copy_prop.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[1].operands, vec![vreg(2), vreg(0)]);
        assert_eq!(
            insts[2].operands,
            vec![vreg(3), vreg(0), X86ISelOperand::Imm(8)]
        );
    }

    #[test]
    fn x86_copy_prop_rewrites_sib_base_and_index_uses() {
        let sib_addr = X86ISelOperand::SibMemAddr {
            base: Box::new(vreg(1)),
            index: Box::new(vreg(3)),
            scale: 4,
            disp: 16,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(3), vreg(2)]),
            X86ISelInst::new(X86Opcode::LeaSib, vec![vreg(4), sib_addr]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(copy_prop.run_on_function(&mut func));

        assert_eq!(
            entry_insts(&func)[2].operands,
            vec![
                vreg(4),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(vreg(0)),
                    index: Box::new(vreg(2)),
                    scale: 4,
                    disp: 16,
                },
            ]
        );
    }

    #[test]
    fn x86_copy_prop_chases_local_movrr32_chain() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR32, vec![vreg32(1), vreg32(0)]),
            X86ISelInst::new(X86Opcode::MovRR32, vec![vreg32(2), vreg32(1)]),
            X86ISelInst::new(X86Opcode::MovRR32, vec![vreg32(3), vreg32(2)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(copy_prop.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[1].operands, vec![vreg32(2), vreg32(0)]);
        assert_eq!(insts[2].operands, vec![vreg32(3), vreg32(0)]);
    }

    #[test]
    fn x86_copy_prop_chases_local_xmm_copy_chains() {
        for (opcode, class) in [
            (X86Opcode::MovssRR, RegClass::Fpr32),
            (X86Opcode::MovsdRR, RegClass::Fpr64),
            (X86Opcode::MovdqaRR, RegClass::Fpr128),
        ] {
            let reg = |id| vreg_class(id, class);
            let mut func = make_func(vec![
                X86ISelInst::new(opcode, vec![reg(1), reg(0)]),
                X86ISelInst::new(opcode, vec![reg(2), reg(1)]),
                X86ISelInst::new(X86Opcode::Ret, vec![]),
            ]);
            let mut copy_prop = X86CopyPropagation;

            assert!(
                copy_prop.run_on_function(&mut func),
                "{opcode:?} copy chain should propagate"
            );

            assert_eq!(entry_insts(&func)[1].operands, vec![reg(2), reg(0)]);
        }
    }

    #[test]
    fn x86_copy_prop_and_dce_remove_dead_vector_copy_before_store() {
        let store_addr = X86ISelOperand::MemAddr {
            base: Box::new(vreg(3)),
            disp: 16,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovdqaRR, vec![xmm(1), xmm(0)]),
            X86ISelInst::new(
                X86Opcode::Pshufd,
                vec![xmm(2), xmm(1), X86ISelOperand::Imm(0b11_10_01_00)],
            ),
            X86ISelInst::new(X86Opcode::MovdquMR, vec![store_addr, xmm(2)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut pm = X86PassManager::new()
            .with_pass(Box::new(X86CopyPropagation))
            .with_pass(Box::new(crate::X86DeadCodeElimination));

        assert!(pm.run_once(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            insts.iter().map(|inst| inst.opcode).collect::<Vec<_>>(),
            vec![X86Opcode::Pshufd, X86Opcode::MovdquMR, X86Opcode::Ret]
        );
        assert_eq!(
            insts[0].operands,
            vec![xmm(2), xmm(0), X86ISelOperand::Imm(0b11_10_01_00)]
        );
    }

    #[test]
    fn x86_copy_prop_stops_when_source_is_redefined() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(!copy_prop.run_on_function(&mut func));

        assert_eq!(entry_insts(&func)[2].operands, vec![vreg(2), vreg(1)]);
    }

    #[test]
    fn x86_copy_prop_preserves_memory_barriers() {
        let store_addr = X86ISelOperand::MemAddr {
            base: Box::new(vreg(3)),
            disp: 16,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![store_addr, vreg(4)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(!copy_prop.run_on_function(&mut func));

        assert_eq!(entry_insts(&func)[2].operands, vec![vreg(2), vreg(1)]);
    }

    #[test]
    fn x86_copy_prop_rewrites_store_memory_barrier_operands_before_clearing() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(3), vreg(2)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(3), 16), vreg(1)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(4), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(copy_prop.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            insts[2].operands,
            vec![mem_addr(vreg(2), 16), vreg(0)],
            "store address and stored value should be rewritten at the barrier"
        );
        assert_eq!(
            insts[3].operands,
            vec![vreg(4), vreg(1)],
            "memory barrier must still clear copy state for later instructions"
        );
    }

    #[test]
    fn x86_copy_prop_rewrites_load_address_before_clearing_memory_barrier() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(2), mem_addr(vreg(1), 8)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(3), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(copy_prop.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[1].operands, vec![vreg(2), mem_addr(vreg(0), 8)]);
        assert_eq!(
            insts[2].operands,
            vec![vreg(3), vreg(1)],
            "load barrier must still clear copy state for later instructions"
        );
    }

    #[test]
    fn x86_copy_prop_rewrites_sib_store_memory_barrier_operands() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(3), vreg(2)]),
            X86ISelInst::new(X86Opcode::MovdqaRR, vec![xmm(5), xmm(4)]),
            X86ISelInst::new(
                X86Opcode::MovdquMR,
                vec![sib_addr(vreg(1), vreg(3), 4, 32), xmm(5)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(copy_prop.run_on_function(&mut func));

        assert_eq!(
            entry_insts(&func)[3].operands,
            vec![sib_addr(vreg(0), vreg(2), 4, 32), xmm(4)]
        );
    }

    #[test]
    fn x86_copy_prop_rejects_fixed_register_memory_barrier_operands() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(
                X86Opcode::MovMR,
                vec![mem_addr(X86ISelOperand::PReg(RAX), 16), vreg(1)],
            ),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(!copy_prop.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            insts[1].operands,
            vec![mem_addr(X86ISelOperand::PReg(RAX), 16), vreg(1)]
        );
        assert_eq!(insts[2].operands, vec![vreg(2), vreg(1)]);
    }

    #[test]
    fn x86_copy_prop_preserves_call_barriers() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(
                X86Opcode::Call,
                vec![X86ISelOperand::Symbol("callee".to_string())],
            ),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(!copy_prop.run_on_function(&mut func));

        assert_eq!(entry_insts(&func)[2].operands, vec![vreg(2), vreg(1)]);
    }

    #[test]
    fn x86_copy_prop_rewrites_return_operand_before_clearing_barrier() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![vreg(1)]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(copy_prop.run_on_function(&mut func));

        assert_eq!(entry_insts(&func)[1].operands, vec![vreg(0)]);
    }

    #[test]
    fn x86_copy_prop_return_still_clears_copy_state() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![vreg(1)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(copy_prop.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[1].operands, vec![vreg(0)]);
        assert_eq!(
            insts[2].operands,
            vec![vreg(2), vreg(1)],
            "return barrier must clear copy state for later instructions"
        );
    }

    #[test]
    fn x86_copy_prop_preserves_fixed_register_return_barrier() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![X86ISelOperand::PReg(RAX)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(!copy_prop.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[1].operands, vec![X86ISelOperand::PReg(RAX)]);
        assert_eq!(insts[2].operands, vec![vreg(2), vreg(1)]);
    }

    #[test]
    fn x86_copy_prop_does_not_cross_control_flow_edges() {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("x86_copy_prop_blocks".to_string(), sig);
        let entry = Block(0);
        let exit = Block(1);
        func.ensure_block(entry);
        func.ensure_block(exit);
        func.blocks.get_mut(&entry).unwrap().successors.push(exit);
        func.next_vreg = 8;
        func.push_inst(
            entry,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
        );
        func.push_inst(
            entry,
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(exit)]),
        );
        func.push_inst(
            exit,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
        );
        func.push_inst(exit, X86ISelInst::new(X86Opcode::Ret, vec![]));
        let mut copy_prop = X86CopyPropagation;

        assert!(!copy_prop.run_on_function(&mut func));

        let exit_insts = &func.blocks.get(&exit).unwrap().insts;
        assert_eq!(exit_insts[0].operands, vec![vreg(2), vreg(1)]);
    }

    #[test]
    fn x86_copy_prop_preserves_fixed_physical_register_glue() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![X86ISelOperand::PReg(RAX), vreg(1)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(3), X86ISelOperand::PReg(RDI)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(!copy_prop.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[1].operands, vec![X86ISelOperand::PReg(RAX), vreg(1)]);
        assert_eq!(insts[2].operands, vec![vreg(2), vreg(1)]);
        assert_eq!(insts[3].operands, vec![vreg(3), X86ISelOperand::PReg(RDI)]);
    }

    #[test]
    fn x86_copy_prop_preserves_sib_fixed_physical_register_barrier() {
        let sib_addr = X86ISelOperand::SibMemAddr {
            base: Box::new(X86ISelOperand::PReg(RAX)),
            index: Box::new(vreg(2)),
            scale: 4,
            disp: 0,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::LeaSib, vec![vreg(4), sib_addr]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(3), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(!copy_prop.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            insts[1].operands,
            vec![
                vreg(4),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(X86ISelOperand::PReg(RAX)),
                    index: Box::new(vreg(2)),
                    scale: 4,
                    disp: 0,
                },
            ]
        );
        assert_eq!(insts[2].operands, vec![vreg(3), vreg(1)]);
    }

    #[test]
    fn x86_copy_prop_rewrites_cmp_before_clearing_flag_barrier() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![
                    vreg(2),
                    X86ISelOperand::CondCode(trust_cg_ir::X86CondCode::E),
                ],
            ),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(3), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(copy_prop.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[1].operands, vec![vreg(0), X86ISelOperand::Imm(0)]);
        assert_eq!(insts[3].operands, vec![vreg(3), vreg(1)]);
    }

    #[test]
    fn x86_copy_prop_rewrites_test_rr_before_clearing_flag_barrier() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::TestRR, vec![vreg(1), vreg(1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![
                    vreg(2),
                    X86ISelOperand::CondCode(trust_cg_ir::X86CondCode::E),
                ],
            ),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(3), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(copy_prop.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[1].operands, vec![vreg(0), vreg(0)]);
        assert_eq!(
            insts[3].operands,
            vec![vreg(3), vreg(1)],
            "copy map must still be cleared at the flag barrier"
        );
    }

    #[test]
    fn x86_copy_prop_does_not_rewrite_def_use_flag_writer_destination() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(1), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(!copy_prop.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[1].operands, vec![vreg(1), X86ISelOperand::Imm(1)]);
        assert_eq!(insts[2].operands, vec![vreg(2), vreg(1)]);
    }

    #[test]
    fn x86_copy_prop_requires_matching_virtual_register_classes() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::MovRR,
                vec![
                    vreg_class(1, RegClass::Gpr64),
                    vreg_class(0, RegClass::Gpr32),
                ],
            ),
            X86ISelInst::new(
                X86Opcode::MovRR,
                vec![
                    vreg_class(2, RegClass::Gpr64),
                    vreg_class(1, RegClass::Gpr64),
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(!copy_prop.run_on_function(&mut func));

        assert_eq!(
            entry_insts(&func)[1].operands,
            vec![
                vreg_class(2, RegClass::Gpr64),
                vreg_class(1, RegClass::Gpr64),
            ]
        );
    }
}
