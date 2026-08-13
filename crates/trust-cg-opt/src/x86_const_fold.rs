// trust-cg-opt - x86-64 Constant Folding
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Conservative constant folding for x86-64 ISel-output functions.
//!
//! This pass is intentionally scoped to the x86 pass-manager surface. It is not
//! part of the default x86 codegen pipeline.

use std::collections::HashMap;

use trust_cg_ir::regs::RegClass;
use trust_cg_ir::{OpcodeCategory, VReg, X86Opcode};
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::effects::{x86_inst_effect, x86_produces_value, x86_reads_flags, x86_writes_flags};
use crate::x86_pass_manager::X86MachinePass;

/// Constant folding for x86-64 ISel-output machine functions.
pub struct X86ConstantFolding;

impl X86ConstantFolding {
    /// Run x86 constant folding directly on an ISel function.
    pub fn run_on_function(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func)
    }
}

impl X86MachinePass for X86ConstantFolding {
    fn name(&self) -> &str {
        "x86-const-fold"
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

        let mut constants = HashMap::new();

        for index in 0..block.insts.len() {
            if let Some((dst, result)) = try_fold_const_ri(&block.insts[index], &constants)
                .or_else(|| try_fold_const_rr(&block.insts[index], &constants))
                && has_no_observable_effects_except_flags(&block.insts[index])
            {
                if flags_written_here_are_dead(&block.insts, index)
                    || fold_replacement_preserves_flags(&block.insts[index])
                {
                    block.insts[index] = X86ISelInst::new(
                        X86Opcode::MovRI,
                        vec![X86ISelOperand::VReg(dst), X86ISelOperand::Imm(result)],
                    );
                    changed = true;
                }

                constants.insert(dst, result);
                continue;
            }

            // RR -> RI narrowing: a two-source ALU op with exactly ONE
            // tracked-constant source rewrites to its reg-imm form. The
            // value is identical and so are the flags (the RI forms of
            // Add/Sub/Imul define flags exactly as their RR forms for the
            // same operand values), so no flag-deadness condition is
            // needed; the freed constant vreg becomes DCE-able.
            if let Some(replacement) = try_narrow_rr_to_ri(&block.insts[index], &constants) {
                block.insts[index] = replacement;
                changed = true;
                // Fall through to the tracker below: the rewritten inst may
                // itself now be fully foldable on a later fixpoint pass.
            }

            if update_const_tracker(&block.insts[index], &mut constants) {
                continue;
            }

            invalidate_defined_vreg(&block.insts[index], &mut constants);
        }
    }

    changed
}

/// Rewrite `Op d, s1, s2` (or tied `Op d, s`) with exactly one
/// tracked-constant register source into the corresponding reg-imm form:
/// `AddRR/SubRR -> AddRI/SubRI`, `ImulRR -> ImulRRI`. Only when the
/// constant is the SECOND source (Add is commutative so either side works;
/// Sub only the subtrahend) and fits an encodable i32 immediate.
fn try_narrow_rr_to_ri(inst: &X86ISelInst, constants: &HashMap<VReg, i64>) -> Option<X86ISelInst> {
    let (ri_opcode, commutative) = match inst.opcode {
        X86Opcode::AddRR => (X86Opcode::AddRI, true),
        X86Opcode::SubRR => (X86Opcode::SubRI, false),
        X86Opcode::ImulRR => (X86Opcode::ImulRRI, true),
        _ => return None,
    };
    let (d, s1, s2) = match inst.operands.as_slice() {
        [
            X86ISelOperand::VReg(d),
            X86ISelOperand::VReg(s1),
            X86ISelOperand::VReg(s2),
        ] => (*d, *s1, *s2),
        // Tied form: `Op d, s` == `Op d, d, s`.
        [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)] => (*d, *d, *s),
        _ => return None,
    };
    let imm_ok = |c: i64| i32::try_from(c).is_ok();
    let (reg, imm) = match (constants.get(&s1).copied(), constants.get(&s2).copied()) {
        // Exactly-one-constant cases only: both-constant is the full
        // fold's job (try_fold_const_rr), none-constant is not ours.
        (None, Some(c2)) if imm_ok(c2) => (s1, c2),
        (Some(c1), None) if commutative && imm_ok(c1) => (s2, c1),
        _ => return None,
    };
    let mut out = X86ISelInst::new(
        ri_opcode,
        vec![
            X86ISelOperand::VReg(d),
            X86ISelOperand::VReg(reg),
            X86ISelOperand::Imm(imm),
        ],
    );
    out.lowering_provenance = inst.lowering_provenance;
    Some(out)
}

fn try_fold_const_ri(inst: &X86ISelInst, constants: &HashMap<VReg, i64>) -> Option<(VReg, i64)> {
    let category = inst.opcode.categorize();
    match category {
        OpcodeCategory::AddRI
        | OpcodeCategory::SubRI
        | OpcodeCategory::AndRI
        | OpcodeCategory::OrRI
        | OpcodeCategory::XorRI
        | OpcodeCategory::ShlRI
        | OpcodeCategory::ShrRI
        | OpcodeCategory::SarRI => {}
        _ if inst.opcode == X86Opcode::ImulRRI => {}
        _ => return None,
    }

    let dst = match inst.operands.first()? {
        X86ISelOperand::VReg(vreg) => *vreg,
        _ => return None,
    };

    let (src, imm) = match inst.operands.as_slice() {
        [X86ISelOperand::VReg(_), X86ISelOperand::Imm(imm)] => (*constants.get(&dst)?, *imm),
        [_, src, X86ISelOperand::Imm(imm)] => (lookup_const(src, constants)?, *imm),
        _ => return None,
    };

    let result = fold_ri_value(dst.class, category, inst.opcode, src, imm)?;

    Some((dst, result))
}

/// Register-register ALU fold: when every source of a pure two-source ALU
/// instruction is a tracked block-local constant, compute the result.
/// Handles both the tied 2-operand form (`Op d, s` — d is def AND use) and
/// the 3-operand form (`Op d, s1, s2`). The value semantics per class
/// mirror `fold_ri_value` (wrap at the carrier width).
fn try_fold_const_rr(inst: &X86ISelInst, constants: &HashMap<VReg, i64>) -> Option<(VReg, i64)> {
    let category = inst.opcode.categorize();
    match category {
        OpcodeCategory::AddRR
        | OpcodeCategory::SubRR
        | OpcodeCategory::MulRR
        | OpcodeCategory::AndRR
        | OpcodeCategory::OrRR
        | OpcodeCategory::XorRR => {}
        _ => return None,
    }

    let dst = match inst.operands.first()? {
        X86ISelOperand::VReg(vreg) => *vreg,
        _ => return None,
    };

    let (lhs, rhs) = match inst.operands.as_slice() {
        // Tied: `Op d, s` computes d := d OP s.
        [X86ISelOperand::VReg(_), s @ X86ISelOperand::VReg(_)] => {
            (*constants.get(&dst)?, lookup_const(s, constants)?)
        }
        // Three-operand: `Op d, s1, s2` computes d := s1 OP s2.
        [X86ISelOperand::VReg(_), s1, s2] => {
            (lookup_const(s1, constants)?, lookup_const(s2, constants)?)
        }
        _ => return None,
    };

    let result = fold_rr_value(dst.class, category, lhs, rhs)?;
    Some((dst, result))
}

fn fold_rr_value(class: RegClass, category: OpcodeCategory, lhs: i64, rhs: i64) -> Option<i64> {
    match class {
        RegClass::Gpr32 => {
            let l = lhs as u32;
            let r = rhs as u32;
            let result = match category {
                OpcodeCategory::AddRR => l.wrapping_add(r),
                OpcodeCategory::SubRR => l.wrapping_sub(r),
                OpcodeCategory::MulRR => l.wrapping_mul(r),
                OpcodeCategory::AndRR => l & r,
                OpcodeCategory::OrRR => l | r,
                OpcodeCategory::XorRR => l ^ r,
                _ => return None,
            };
            Some(result as i64)
        }
        RegClass::Gpr64 => {
            let result = match category {
                OpcodeCategory::AddRR => lhs.wrapping_add(rhs),
                OpcodeCategory::SubRR => lhs.wrapping_sub(rhs),
                OpcodeCategory::MulRR => lhs.wrapping_mul(rhs),
                OpcodeCategory::AndRR => lhs & rhs,
                OpcodeCategory::OrRR => lhs | rhs,
                OpcodeCategory::XorRR => lhs ^ rhs,
                _ => return None,
            };
            Some(result)
        }
        _ => None,
    }
}

fn fold_ri_value(
    class: RegClass,
    category: OpcodeCategory,
    opcode: X86Opcode,
    src: i64,
    imm: i64,
) -> Option<i64> {
    match class {
        RegClass::Gpr32 => fold_ri_value_gpr32(category, opcode, src, imm),
        RegClass::Gpr64 => fold_ri_value_gpr64(category, opcode, src, imm),
        _ => None,
    }
}

fn fold_ri_value_gpr32(
    category: OpcodeCategory,
    opcode: X86Opcode,
    src: i64,
    imm: i64,
) -> Option<i64> {
    let src = src as u32;
    let imm = imm as u32;
    let result = match category {
        OpcodeCategory::AddRI => src.wrapping_add(imm),
        OpcodeCategory::SubRI => src.wrapping_sub(imm),
        OpcodeCategory::AndRI => src & imm,
        OpcodeCategory::OrRI => src | imm,
        OpcodeCategory::XorRI => src ^ imm,
        OpcodeCategory::ShlRI => {
            let shift = shift_amount(imm as i64, 31)?;
            src.wrapping_shl(shift)
        }
        OpcodeCategory::ShrRI => {
            let shift = shift_amount(imm as i64, 31)?;
            src.wrapping_shr(shift)
        }
        OpcodeCategory::SarRI => {
            let shift = shift_amount(imm as i64, 31)?;
            ((src as i32).wrapping_shr(shift)) as u32
        }
        _ if opcode == X86Opcode::ImulRRI => src.wrapping_mul(imm),
        _ => unreachable!("category filtered above"),
    };
    Some(result as i64)
}

fn fold_ri_value_gpr64(
    category: OpcodeCategory,
    opcode: X86Opcode,
    src: i64,
    imm: i64,
) -> Option<i64> {
    let result = match category {
        OpcodeCategory::AddRI => src.wrapping_add(imm),
        OpcodeCategory::SubRI => src.wrapping_sub(imm),
        OpcodeCategory::AndRI => src & imm,
        OpcodeCategory::OrRI => src | imm,
        OpcodeCategory::XorRI => src ^ imm,
        OpcodeCategory::ShlRI => {
            let shift = shift_amount(imm, 63)?;
            src.wrapping_shl(shift)
        }
        OpcodeCategory::ShrRI => {
            let shift = shift_amount(imm, 63)?;
            ((src as u64).wrapping_shr(shift)) as i64
        }
        OpcodeCategory::SarRI => {
            let shift = shift_amount(imm, 63)?;
            src.wrapping_shr(shift)
        }
        _ if opcode == X86Opcode::ImulRRI => src.wrapping_mul(imm),
        _ => unreachable!("category filtered above"),
    };
    Some(result)
}

fn shift_amount(imm: i64, max: i64) -> Option<u32> {
    if (0..=max).contains(&imm) {
        Some(imm as u32)
    } else {
        None
    }
}

fn normalize_const_for_vreg(vreg: VReg, value: i64) -> i64 {
    match vreg.class {
        RegClass::Gpr32 => (value as u32) as i64,
        _ => value,
    }
}

fn lookup_const(operand: &X86ISelOperand, constants: &HashMap<VReg, i64>) -> Option<i64> {
    match operand {
        X86ISelOperand::Imm(value) => Some(*value),
        X86ISelOperand::VReg(vreg) => constants.get(vreg).copied(),
        _ => None,
    }
}

fn update_const_tracker(inst: &X86ISelInst, constants: &mut HashMap<VReg, i64>) -> bool {
    let Some(X86ISelOperand::VReg(dst)) = inst.operands.first() else {
        return false;
    };

    match inst.opcode {
        X86Opcode::MovRI => {
            if let Some(X86ISelOperand::Imm(value)) = inst.operands.get(1) {
                constants.insert(*dst, normalize_const_for_vreg(*dst, *value));
            } else {
                constants.remove(dst);
            }
            true
        }
        X86Opcode::MovRR | X86Opcode::MovRR32
            if Some(dst.class) == copy_opcode_class(inst.opcode) =>
        {
            if let Some(X86ISelOperand::VReg(src)) = inst.operands.get(1)
                && src.class == dst.class
                && let Some(value) = constants.get(src).copied()
            {
                constants.insert(*dst, normalize_const_for_vreg(*dst, value));
            } else {
                constants.remove(dst);
            }
            true
        }
        // `MOV r64, r32` (the ISel zero-extend idiom for `Uextend i32 -> i64`)
        // writes a 32-bit register, which on x86-64 ZERO-EXTENDS the value into
        // the full 64-bit destination. Model the tracked constant accordingly:
        // the Gpr64 def equals the Gpr32 source value with the upper 32 bits
        // forced to zero.
        //
        // SOUNDNESS / LATENT-BUG GUARD: we mask the source to `u32` and then
        // widen via `as i64` (an unsigned widening that leaves bits [63:32]
        // clear). We deliberately do NOT sign-extend here. A sign-extending
        // model (e.g. `value as i32 as i64`) would record
        // 0xffff_ffff_8000_0000 for a high-bit value like 0x8000_0000 and
        // miscompile every downstream 64-bit read of this register. The Gpr32
        // source constant is already normalized to its zero-extended form by
        // `normalize_const_for_vreg`, but we re-mask defensively so this arm is
        // correct regardless of how the source was tracked.
        X86Opcode::MovRR32 if dst.class == RegClass::Gpr64 => {
            if let Some(X86ISelOperand::VReg(src)) = inst.operands.get(1)
                && src.class == RegClass::Gpr32
                && let Some(value) = constants.get(src).copied()
            {
                constants.insert(*dst, (value as u32) as i64);
            } else {
                constants.remove(dst);
            }
            true
        }
        X86Opcode::MovRR | X86Opcode::MovRR32 => {
            constants.remove(dst);
            true
        }
        X86Opcode::Inc | X86Opcode::Dec => {
            if inst.operands.len() == 1
                && matches!(dst.class, RegClass::Gpr32 | RegClass::Gpr64)
                && let Some(value) = constants.get(dst).copied()
            {
                let value = match inst.opcode {
                    X86Opcode::Inc => value.wrapping_add(1),
                    X86Opcode::Dec => value.wrapping_sub(1),
                    _ => unreachable!("opcode filtered above"),
                };
                constants.insert(*dst, normalize_const_for_vreg(*dst, value));
            } else {
                constants.remove(dst);
            }
            true
        }
        _ => false,
    }
}

fn copy_opcode_class(opcode: X86Opcode) -> Option<RegClass> {
    match opcode {
        X86Opcode::MovRR => Some(RegClass::Gpr64),
        X86Opcode::MovRR32 => Some(RegClass::Gpr32),
        _ => None,
    }
}

fn invalidate_defined_vreg(inst: &X86ISelInst, constants: &mut HashMap<VReg, i64>) {
    if !x86_produces_value(inst.opcode) {
        return;
    }

    if let Some(X86ISelOperand::VReg(dst)) = inst.operands.first() {
        constants.remove(dst);
    }
}

fn has_no_observable_effects_except_flags(inst: &X86ISelInst) -> bool {
    let flags = inst.flags;

    x86_inst_effect(inst).is_pure()
        && !inst_touches_fixed_register(inst)
        && !flags.is_call()
        && !flags.is_branch()
        && !flags.is_terminator()
        && !flags.is_return()
        && !flags.has_side_effects()
        && !flags.reads_memory()
        && !flags.writes_memory()
}

fn flags_written_here_are_dead(insts: &[X86ISelInst], index: usize) -> bool {
    if !x86_writes_flags(insts[index].opcode) {
        return true;
    }

    for inst in &insts[index + 1..] {
        if x86_reads_flags(inst.opcode) {
            return false;
        }
        if x86_writes_flags(inst.opcode) {
            return true;
        }
        if instruction_may_export_flags(inst) {
            return false;
        }
    }

    false
}

fn fold_replacement_preserves_flags(inst: &X86ISelInst) -> bool {
    matches!(
        inst.opcode,
        X86Opcode::ShlRI | X86Opcode::ShrRI | X86Opcode::SarRI
    ) && matches!(inst.operands.last(), Some(X86ISelOperand::Imm(0)))
}

fn instruction_may_export_flags(inst: &X86ISelInst) -> bool {
    // Proof-carrier trap pseudos (Sentinel S5) are flag-TRANSPARENT for
    // this scan, in both of their possible futures: if EXPANDED, the
    // expansion begins with its own CMP/TEST (a full flag re-definition —
    // any later reader sees the expansion's flags, never the folded
    // instruction's); if proof-DELETED, the pseudo contributes nothing at
    // all. In neither world can a reader observe the candidate's flags
    // THROUGH the pseudo, and treating it as an export barrier would block
    // folding across every bounds-checked body (the unrolled-matmul shape).
    if is_trap_carrier_pseudo(inst.opcode) {
        return false;
    }
    let flags = inst.flags;

    flags.is_call()
        || flags.is_branch()
        || flags.is_terminator()
        || flags.is_return()
        || flags.has_side_effects()
}

/// The Sentinel S5 proof-carrier pseudos: single-instruction bounds/null/
/// div-zero/shift-range guards, expanded (or proof-deleted) later in the
/// codegen pipeline.
fn is_trap_carrier_pseudo(opcode: X86Opcode) -> bool {
    matches!(
        opcode,
        X86Opcode::TrapBoundsCheckExact
            | X86Opcode::TrapNullIfZeroExact
            | X86Opcode::TrapDivZeroExact
            | X86Opcode::TrapShiftRangeExact
    )
}

fn inst_touches_fixed_register(inst: &X86ISelInst) -> bool {
    inst.operands.iter().any(operand_touches_fixed_register)
}

fn operand_touches_fixed_register(operand: &X86ISelOperand) -> bool {
    match operand {
        X86ISelOperand::PReg(_) => true,
        X86ISelOperand::MemAddr { base, .. } => operand_touches_fixed_register(base),
        // Keep in lockstep with the sibling helpers (x86_dce/x86_peephole):
        // recurse into BOTH SIB address registers (adversarial-review NIT —
        // currently unreachable from this pass's matchers, but divergence
        // here is how future reachability becomes a hole).
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            operand_touches_fixed_register(base) || operand_touches_fixed_register(index)
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use trust_cg_ir::regs::{RegClass, VReg};
    use trust_cg_ir::{InstFlags, X86CondCode};
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

    fn make_func(insts: Vec<X86ISelInst>) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("x86_const_fold_test".to_string(), sig);
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

    fn entry_opcodes(func: &X86ISelFunction) -> Vec<X86Opcode> {
        entry_insts(func).iter().map(|inst| inst.opcode).collect()
    }

    #[test]
    fn x86_const_fold_folds_rr_forms_with_tracked_sources() {
        // 3-operand AddRR with both sources tracked constants folds; the
        // trailing CmpRI kills the folded instruction's flags.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(192)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(2), vreg(0), vreg(1)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut pm = X86PassManager::new().with_pass(Box::new(X86ConstantFolding));
        assert!(pm.run_once(&mut func));
        let insts = entry_insts(&func);
        assert_eq!(insts[2].opcode, X86Opcode::MovRI);
        assert_eq!(insts[2].operands[1], X86ISelOperand::Imm(960));
    }

    #[test]
    fn x86_const_fold_scans_through_trap_carrier_pseudos() {
        // A proof-carrier pseudo between the foldable AddRR and the flag
        // killer is flag-transparent (expanded: its own CMP re-defines
        // flags; deleted: contributes nothing) — the fold must fire.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(3)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(4)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]),
            X86ISelInst::new(
                X86Opcode::TrapBoundsCheckExact,
                vec![vreg(5), vreg(2), X86ISelOperand::Imm(24)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut pm = X86PassManager::new().with_pass(Box::new(X86ConstantFolding));
        assert!(pm.run_once(&mut func));
        let insts = entry_insts(&func);
        assert_eq!(insts[2].opcode, X86Opcode::MovRI);
        assert_eq!(insts[2].operands[1], X86ISelOperand::Imm(7));
        // The carrier itself is untouched.
        assert_eq!(insts[3].opcode, X86Opcode::TrapBoundsCheckExact);
    }

    #[test]
    fn x86_const_fold_rr_respects_live_flags() {
        // AddRR whose flags feed a Setcc must NOT be rewritten (value is
        // still tracked, but the instruction stays).
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(3)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(4)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(3), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut pm = X86PassManager::new().with_pass(Box::new(X86ConstantFolding));
        pm.run_once(&mut func);
        assert_eq!(entry_insts(&func)[2].opcode, X86Opcode::AddRR);
    }

    #[test]
    fn x86_const_fold_folds_add_ri_when_flags_are_killed() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(10)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(20)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(30)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut pm = X86PassManager::new().with_pass(Box::new(X86ConstantFolding));

        assert!(pm.run_once(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRI,
                X86Opcode::MovRI,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[1].operands, vec![vreg(1), X86ISelOperand::Imm(30)]);
        assert_eq!(insts[1].flags, X86Opcode::MovRI.default_flags());
    }

    #[test]
    fn x86_const_fold_tracks_folded_value_for_later_safe_folds() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(2)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(3)],
            ),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(4)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(9)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(fold.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[1].opcode, X86Opcode::MovRI);
        assert_eq!(insts[1].operands, vec![vreg(1), X86ISelOperand::Imm(5)]);
        assert_eq!(insts[2].opcode, X86Opcode::MovRI);
        assert_eq!(insts[2].operands, vec![vreg(2), X86ISelOperand::Imm(9)]);
    }

    #[test]
    fn x86_const_fold_folds_sub_ri_when_flags_are_killed() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(42)]),
            X86ISelInst::new(
                X86Opcode::SubRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(17)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(25)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(fold.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRI,
                X86Opcode::MovRI,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[1].operands, vec![vreg(1), X86ISelOperand::Imm(25)]);
        assert_eq!(insts[1].flags, X86Opcode::MovRI.default_flags());
    }

    #[test]
    fn x86_const_fold_folds_imul_rri_when_flags_are_killed() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![vreg(0), X86ISelOperand::Imm(i64::MAX)],
            ),
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(2)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(-2)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(fold.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRI,
                X86Opcode::MovRI,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[1].operands, vec![vreg(1), X86ISelOperand::Imm(-2)]);
        assert_eq!(insts[1].flags, X86Opcode::MovRI.default_flags());
    }

    #[test]
    fn x86_const_fold_folds_bitwise_ri_when_flags_are_killed() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(0b1010)]),
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(0b1100)],
            ),
            X86ISelInst::new(
                X86Opcode::OrRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(0b0011)],
            ),
            X86ISelInst::new(
                X86Opcode::XorRI,
                vec![vreg(3), vreg(2), X86ISelOperand::Imm(0b0110)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(3), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(fold.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRI,
                X86Opcode::MovRI,
                X86Opcode::MovRI,
                X86Opcode::MovRI,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(
            insts[1].operands,
            vec![vreg(1), X86ISelOperand::Imm(0b1000)]
        );
        assert_eq!(
            insts[2].operands,
            vec![vreg(2), X86ISelOperand::Imm(0b1011)]
        );
        assert_eq!(
            insts[3].operands,
            vec![vreg(3), X86ISelOperand::Imm(0b1101)]
        );
    }

    #[test]
    fn x86_const_fold_tracks_const_through_inc_for_later_safe_fold() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(41)]),
            X86ISelInst::new(X86Opcode::Inc, vec![vreg(0)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(43)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(fold.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRI,
                X86Opcode::Inc,
                X86Opcode::MovRI,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[1].operands, vec![vreg(0)]);
        assert_eq!(insts[2].operands, vec![vreg(1), X86ISelOperand::Imm(43)]);
    }

    #[test]
    fn x86_const_fold_tracks_const_through_dec_for_later_safe_fold() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(10)]),
            X86ISelInst::new(X86Opcode::Dec, vec![vreg(0)]),
            X86ISelInst::new(
                X86Opcode::SubRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(4)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(fold.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRI,
                X86Opcode::Dec,
                X86Opcode::MovRI,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[1].operands, vec![vreg(0)]);
        assert_eq!(insts[2].operands, vec![vreg(1), X86ISelOperand::Imm(5)]);
    }

    #[test]
    fn x86_const_fold_masks_gpr32_inc_dec_wrapping() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![vreg32(0), X86ISelOperand::Imm(0xffff_ffff)],
            ),
            X86ISelInst::new(X86Opcode::Inc, vec![vreg32(0)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg32(1), vreg32(0), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg32(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Dec, vec![vreg32(2)]),
            X86ISelInst::new(
                X86Opcode::XorRI,
                vec![vreg32(3), vreg32(2), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::CmpRI,
                vec![vreg32(3), X86ISelOperand::Imm(0xffff_ffff)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(fold.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[2].opcode, X86Opcode::MovRI);
        assert_eq!(insts[2].operands, vec![vreg32(1), X86ISelOperand::Imm(1)]);
        assert_eq!(insts[5].opcode, X86Opcode::MovRI);
        assert_eq!(
            insts[5].operands,
            vec![vreg32(3), X86ISelOperand::Imm(0xffff_ffff)]
        );
    }

    #[test]
    fn x86_const_fold_inc_dec_malformed_and_unsupported_invalidate() {
        let tracked = VReg::new(0, RegClass::Gpr64);
        let unsupported = VReg::new(1, RegClass::Fpr64);
        let mut constants = HashMap::from([(tracked, 7), (unsupported, 11)]);

        assert!(update_const_tracker(
            &X86ISelInst::new(
                X86Opcode::Inc,
                vec![X86ISelOperand::VReg(tracked), X86ISelOperand::Imm(1),],
            ),
            &mut constants
        ));
        assert!(!constants.contains_key(&tracked));

        assert!(update_const_tracker(
            &X86ISelInst::new(X86Opcode::Dec, vec![X86ISelOperand::VReg(unsupported)]),
            &mut constants
        ));
        assert!(!constants.contains_key(&unsupported));
    }

    #[test]
    fn x86_const_fold_preserves_sub_ri_when_flags_are_read() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(42)]),
            X86ISelInst::new(
                X86Opcode::SubRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(17)],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(2), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(!fold.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRI,
                X86Opcode::SubRI,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_const_fold_preserves_bitwise_ri_when_flags_are_read() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(0b1010)]),
            X86ISelInst::new(
                X86Opcode::XorRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(0b0110)],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(2), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(!fold.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRI,
                X86Opcode::XorRI,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_const_fold_preserves_imul_rri_when_flags_are_read() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(-3)],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(2), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(!fold.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRI,
                X86Opcode::ImulRRI,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_const_fold_tracks_const_through_movrr32() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg32(0), X86ISelOperand::Imm(2)]),
            X86ISelInst::new(X86Opcode::MovRR32, vec![vreg32(1), vreg32(0)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg32(2), vreg32(1), X86ISelOperand::Imm(3)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(2), X86ISelOperand::Imm(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(fold.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[2].opcode, X86Opcode::MovRI);
        assert_eq!(insts[2].operands, vec![vreg32(2), X86ISelOperand::Imm(5)]);
    }

    #[test]
    fn x86_const_fold_masks_gpr32_arithmetic_overflow() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![vreg32(0), X86ISelOperand::Imm(0xffff_ffff)],
            ),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg32(1), vreg32(0), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(fold.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[1].opcode, X86Opcode::MovRI);
        assert_eq!(insts[1].operands, vec![vreg32(1), X86ISelOperand::Imm(0)]);
    }

    #[test]
    fn x86_const_fold_masks_gpr32_arithmetic_shift() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![vreg32(0), X86ISelOperand::Imm(0x8000_0000)],
            ),
            X86ISelInst::new(
                X86Opcode::SarRI,
                vec![vreg32(1), vreg32(0), X86ISelOperand::Imm(31)],
            ),
            X86ISelInst::new(
                X86Opcode::CmpRI,
                vec![vreg32(1), X86ISelOperand::Imm(0xffff_ffff)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(fold.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[1].opcode, X86Opcode::MovRI);
        assert_eq!(
            insts[1].operands,
            vec![vreg32(1), X86ISelOperand::Imm(0xffff_ffff)]
        );
    }

    #[test]
    fn x86_const_fold_preserves_gpr32_shift_above_lane_width() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg32(0), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(
                X86Opcode::ShlRI,
                vec![vreg32(1), vreg32(0), X86ISelOperand::Imm(40)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(!fold.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRI,
                X86Opcode::ShlRI,
                X86Opcode::CmpRI,
                X86Opcode::Ret
            ]
        );
    }

    #[test]
    fn x86_const_fold_keeps_same_numeric_id_classes_distinct() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(10)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg32(0), X86ISelOperand::Imm(3)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(20)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(30)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(fold.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[2].opcode, X86Opcode::MovRI);
        assert_eq!(insts[2].operands, vec![vreg(1), X86ISelOperand::Imm(30)]);
    }

    #[test]
    fn x86_const_fold_invalidation_is_class_exact() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(10)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg32(0), X86ISelOperand::Imm(3)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg32(0), vreg32(2)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(20)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(30)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(fold.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[3].opcode, X86Opcode::MovRI);
        assert_eq!(insts[3].operands, vec![vreg(1), X86ISelOperand::Imm(30)]);
    }

    #[test]
    fn x86_const_fold_folds_shift_ri_chain_when_flags_are_killed() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(3)]),
            X86ISelInst::new(
                X86Opcode::ShlRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(4)],
            ),
            X86ISelInst::new(
                X86Opcode::ShrRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(
                X86Opcode::SarRI,
                vec![vreg(3), vreg(2), X86ISelOperand::Imm(3)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(3), X86ISelOperand::Imm(3)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(fold.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRI,
                X86Opcode::MovRI,
                X86Opcode::MovRI,
                X86Opcode::MovRI,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[1].operands, vec![vreg(1), X86ISelOperand::Imm(48)]);
        assert_eq!(insts[2].operands, vec![vreg(2), X86ISelOperand::Imm(24)]);
        assert_eq!(insts[3].operands, vec![vreg(3), X86ISelOperand::Imm(3)]);
    }

    #[test]
    fn x86_const_fold_preserves_shift_ri_when_flags_are_read() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(8)]),
            X86ISelInst::new(
                X86Opcode::ShlRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(2), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(!fold.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRI,
                X86Opcode::ShlRI,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_const_fold_folds_zero_count_shifts_when_flags_are_read() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(-8)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(0), X86ISelOperand::Imm(-8)]),
            X86ISelInst::new(
                X86Opcode::ShlRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::ShrRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::SarRI,
                vec![vreg(3), vreg(2), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(4), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(fold.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRI,
                X86Opcode::CmpRI,
                X86Opcode::MovRI,
                X86Opcode::MovRI,
                X86Opcode::MovRI,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[2].operands, vec![vreg(1), X86ISelOperand::Imm(-8)]);
        assert_eq!(insts[3].operands, vec![vreg(2), X86ISelOperand::Imm(-8)]);
        assert_eq!(insts[4].operands, vec![vreg(3), X86ISelOperand::Imm(-8)]);
    }

    #[test]
    fn x86_const_fold_preserves_shift_ri_when_flags_escape_block() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(8)]),
            X86ISelInst::new(
                X86Opcode::ShrRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(!fold.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::MovRI, X86Opcode::ShrRI, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_const_fold_preserves_add_ri_when_flags_are_read() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(10)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(20)],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(2), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(!fold.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRI,
                X86Opcode::AddRI,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_const_fold_preserves_add_ri_when_flags_escape_block() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(10)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(20)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(!fold.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::MovRI, X86Opcode::AddRI, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_const_fold_preserves_side_effectful_fold_candidate() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(10)]),
            X86ISelInst::with_flags(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(20)],
                InstFlags::HAS_SIDE_EFFECTS,
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(30)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(!fold.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRI,
                X86Opcode::AddRI,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(entry_insts(&func)[1].flags, InstFlags::HAS_SIDE_EFFECTS);
    }

    #[test]
    fn x86_const_fold_preserves_memory_and_call_effects() {
        let store_addr = X86ISelOperand::MemAddr {
            base: Box::new(vreg(0)),
            disp: 16,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(10)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![store_addr, vreg(0)]),
            X86ISelInst::new(
                X86Opcode::Call,
                vec![X86ISelOperand::Symbol("callee".to_string())],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let before = entry_opcodes(&func);
        let mut fold = X86ConstantFolding;

        assert!(!fold.run_on_function(&mut func));

        assert_eq!(entry_opcodes(&func), before);
        assert!(entry_insts(&func)[1].flags.writes_memory());
        assert!(entry_insts(&func)[2].flags.is_call());
    }

    #[test]
    fn x86_const_fold_zero_extends_gpr32_through_movrr32_into_gpr64_fold() {
        // Regression for the Gpr32 implicit zero-extension miscompile.
        //
        //   MovRI  %r32a, 0x40000000
        //   AddRI  %r32b, %r32a, 0x40000000   ; folds to 0x80000000 (high bit set)
        //   MovRR32 %r64,  %r32b              ; x86 `mov r64, r32` ZERO-extends
        //   OrRI   %r64r, %r64, 1             ; downstream 64-bit fold
        //
        // x86-64 writes to a 32-bit register zero-extend into the full 64-bit
        // register, so %r64 == 0x0000_0000_8000_0000 and the OrRI must fold to
        // 0x0000_0000_8000_0001 (2147483649). A sign-extending const model would
        // (wrongly) produce 0xffff_ffff_8000_0001.
        let r32a = X86ISelOperand::VReg(VReg::new(0, RegClass::Gpr32));
        let r32b = X86ISelOperand::VReg(VReg::new(1, RegClass::Gpr32));
        let r64 = X86ISelOperand::VReg(VReg::new(2, RegClass::Gpr64));
        let r64r = X86ISelOperand::VReg(VReg::new(3, RegClass::Gpr64));
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![r32a.clone(), X86ISelOperand::Imm(0x4000_0000)],
            ),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![r32b.clone(), r32a, X86ISelOperand::Imm(0x4000_0000)],
            ),
            X86ISelInst::new(X86Opcode::MovRR32, vec![r64.clone(), r32b]),
            X86ISelInst::new(
                X86Opcode::OrRI,
                vec![r64r.clone(), r64, X86ISelOperand::Imm(1)],
            ),
            // Kill the OrRI's flags so the fold replaces it with a MovRI.
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(7), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut fold = X86ConstantFolding;

        assert!(fold.run_on_function(&mut func));

        let insts = entry_insts(&func);
        // The downstream OrRI was folded to a MovRI carrying the ZERO-extended
        // constant. 0x80000001 == 2147483649, NOT the sign-extended
        // 0xffff_ffff_8000_0001 (-2147483647).
        assert_eq!(insts[3].opcode, X86Opcode::MovRI);
        assert_eq!(
            insts[3].operands,
            vec![r64r, X86ISelOperand::Imm(0x8000_0001)]
        );
    }

    #[test]
    fn x86_const_fold_movrr32_zext_drops_const_when_source_unknown() {
        // The zero-extend idiom only tracks a constant when the Gpr32 source has
        // a known constant; otherwise the Gpr64 def's constant must be dropped
        // (no fold for a downstream consumer).
        let r32 = VReg::new(0, RegClass::Gpr32);
        let r64 = VReg::new(1, RegClass::Gpr64);
        let mut constants = HashMap::new();
        assert!(update_const_tracker(
            &X86ISelInst::new(
                X86Opcode::MovRR32,
                vec![X86ISelOperand::VReg(r64), X86ISelOperand::VReg(r32)],
            ),
            &mut constants
        ));
        assert!(!constants.contains_key(&r64));
    }

    #[test]
    fn x86_const_fold_movrr32_zext_masks_negative_gpr32_constant() {
        // A Gpr32 source holding a value whose high bit is set must zero-extend:
        // tracked Gpr64 constant has its upper 32 bits cleared.
        let r32 = VReg::new(0, RegClass::Gpr32);
        let r64 = VReg::new(1, RegClass::Gpr64);
        // Even if the source were (defensively) recorded with sign bits, the
        // zext arm re-masks to u32. Seed with a sign-extended-looking value.
        let mut constants = HashMap::from([(r32, -1i64)]);
        assert!(update_const_tracker(
            &X86ISelInst::new(
                X86Opcode::MovRR32,
                vec![X86ISelOperand::VReg(r64), X86ISelOperand::VReg(r32)],
            ),
            &mut constants
        ));
        assert_eq!(constants.get(&r64).copied(), Some(0x0000_0000_ffff_ffff));
    }
}
