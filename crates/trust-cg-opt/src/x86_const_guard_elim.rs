// trust-cg-opt - x86-64 Const-Index Guard Elimination
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Deletion of proof-carrier guard pseudos whose condition is STATICALLY
//! TRUE by block-local reaching constants (X9 slice 1 companion pass).
//!
//! After `X86LoopUnroll` + `X86ConstantFolding`, a fully-unrolled
//! bounds-checked body carries one `TrapBoundsCheckExact [base, idx, #b]`
//! per clone whose `idx` is a block-local `MovRI` constant — ~150 such
//! statically-true checks on the matmul benchmark alone (each later
//! expands to a live `CMP`+`Jcc`). This pass deletes a guard pseudo when
//! the same per-block constant-tracking authority `x86_const_fold` uses
//! proves its assertion:
//!
//! * `TrapBoundsCheckExact [base, idx, Imm(b)]` — semantics: trap unless
//!   `idx <u b` (the expansion emits `CMP idx,b ; Jcc AE -> UD2`). Deleted
//!   iff the tracked constant `c` of `idx` satisfies `(c as u64) < (b as
//!   u64)`: the assertion is statically true, so removal is EXACT — the
//!   rolled program's check also never fired.
//! * `TrapDivZeroExact [d]` — trap iff `d == 0`. Deleted iff the tracked
//!   constant of `d` is nonzero. (Gpr32 constants are stored
//!   zero-extended by the tracker, so the low-32 zero test is exact.)
//!
//! Anything unproven is KEPT — the pass only ever removes a check whose
//! trap condition provably cannot fire, which is the same authority under
//! which `x86_const_fold` rewrites value computations. Constant tracking
//! is deliberately minimal and fail-closed: `MovRI` defines, exact
//! same-class copies propagate, any other def (or a hidden-def
//! `Xchg`/`Cmpxchg*`-class instruction) invalidates.
//!
//! Registered in the pipeline ONLY under the `TCG_X86_UNROLL` opt-in and
//! respecting the `TCG_NO_X86_BCE` kill switch (it IS a bounds-check
//! elimination); a default-ON flip owes its own differential evidence.

use std::collections::HashMap;

use trust_cg_ir::regs::RegClass;
use trust_cg_ir::{VReg, X86Opcode};
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::effects::x86_produces_value;
use crate::x86_pass_manager::X86MachinePass;

/// Const-index guard elimination for x86-64 ISel-output functions.
pub struct X86ConstGuardElim;

impl X86MachinePass for X86ConstGuardElim {
    fn name(&self) -> &str {
        "x86-const-guard-elim"
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
        let mut constants: HashMap<VReg, i64> = HashMap::new();
        // Guard pseudos already EXECUTED on this straight-line path, keyed
        // by their exact operand list. If control reaches a second
        // identical pseudo with none of its vregs redefined since, the
        // earlier one has already proven the values safe (it would have
        // trapped otherwise) — the later can never fire and is deleted.
        let mut seen_guards: Vec<(X86Opcode, Vec<X86ISelOperand>)> = Vec::new();
        let mut keep: Vec<bool> = Vec::with_capacity(block.insts.len());
        for inst in &block.insts {
            let mut retain = true;
            match inst.opcode {
                X86Opcode::TrapBoundsCheckExact => {
                    if let [_, X86ISelOperand::VReg(idx), X86ISelOperand::Imm(bound)] =
                        inst.operands.as_slice()
                        && let Some(c) = constants.get(idx)
                        && (*c as u64) < (*bound as u64)
                    {
                        retain = false;
                    }
                    if retain && guard_already_executed(&seen_guards, inst) {
                        retain = false;
                    }
                    if retain {
                        seen_guards.push((inst.opcode, inst.operands.clone()));
                    }
                }
                X86Opcode::TrapDivZeroExact => {
                    if let [X86ISelOperand::VReg(d)] = inst.operands.as_slice()
                        && let Some(c) = constants.get(d)
                        && *c != 0
                    {
                        retain = false;
                    }
                    if retain && guard_already_executed(&seen_guards, inst) {
                        retain = false;
                    }
                    if retain {
                        seen_guards.push((inst.opcode, inst.operands.clone()));
                    }
                }
                // A re-statement of a constant the vreg PROVABLY already
                // holds is a no-op — delete it (the unroller's per-clone
                // stride re-materializations).
                X86Opcode::MovRI => {
                    if let [X86ISelOperand::VReg(d), X86ISelOperand::Imm(v)] =
                        inst.operands.as_slice()
                    {
                        let stored = match d.class {
                            RegClass::Gpr32 => (*v as u32) as i64,
                            _ => *v,
                        };
                        if constants.get(d) == Some(&stored) {
                            retain = false;
                        }
                    }
                }
                _ => {}
            }
            if !retain {
                changed = true;
            }
            keep.push(retain);
            if retain {
                // Any def invalidates guards mentioning the defined vreg
                // (hidden-def opcodes clear everything via the tracker's
                // conservative arm below plus this sweep).
                invalidate_seen_guards(inst, &mut seen_guards);
                update_tracker(inst, &mut constants);
            }
        }
        if keep.iter().any(|k| !k) {
            let mut it = keep.iter();
            block.insts.retain(|_| *it.next().unwrap());
        }
    }
    changed
}

fn guard_already_executed(seen: &[(X86Opcode, Vec<X86ISelOperand>)], inst: &X86ISelInst) -> bool {
    seen.iter()
        .any(|(op, operands)| *op == inst.opcode && operands == &inst.operands)
}

/// Drop remembered guards whose operand vregs `inst` (re)defines; a
/// hidden-def opcode drops them all.
fn invalidate_seen_guards(inst: &X86ISelInst, seen: &mut Vec<(X86Opcode, Vec<X86ISelOperand>)>) {
    if matches!(
        inst.opcode,
        X86Opcode::Xchg | X86Opcode::Cmpxchg | X86Opcode::Cmpxchg8 | X86Opcode::Cmpxchg16
    ) {
        seen.clear();
        return;
    }
    if !x86_produces_value(inst.opcode) {
        return;
    }
    let Some(X86ISelOperand::VReg(d)) = inst.operands.first() else {
        return;
    };
    seen.retain(|(_, operands)| {
        !operands
            .iter()
            .any(|op| matches!(op, X86ISelOperand::VReg(v) if v == d))
    });
}

/// Minimal fail-closed constant tracking: `MovRI` defines, exact
/// same-class `MovRR`/`MovRR32` copies propagate, everything else that
/// defines a vreg invalidates it; hidden-def opcodes clear the whole map.
fn update_tracker(inst: &X86ISelInst, constants: &mut HashMap<VReg, i64>) {
    match inst.opcode {
        X86Opcode::Xchg | X86Opcode::Cmpxchg | X86Opcode::Cmpxchg8 | X86Opcode::Cmpxchg16 => {
            constants.clear();
            return;
        }
        X86Opcode::MovRI => {
            if let [X86ISelOperand::VReg(d), X86ISelOperand::Imm(v)] = inst.operands.as_slice() {
                let stored = match d.class {
                    RegClass::Gpr32 => (*v as u32) as i64,
                    _ => *v,
                };
                constants.insert(*d, stored);
                return;
            }
        }
        X86Opcode::MovRR | X86Opcode::MovRR32 => {
            let want = if inst.opcode == X86Opcode::MovRR {
                RegClass::Gpr64
            } else {
                RegClass::Gpr32
            };
            if let [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)] = inst.operands.as_slice()
                && d.class == want
                && s.class == want
            {
                match constants.get(s).copied() {
                    Some(v) => {
                        constants.insert(*d, v);
                    }
                    None => {
                        constants.remove(d);
                    }
                }
                return;
            }
        }
        _ => {}
    }
    if x86_produces_value(inst.opcode)
        && let Some(X86ISelOperand::VReg(d)) = inst.operands.first()
    {
        constants.remove(d);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::instructions::Block;

    fn vr(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg {
            id,
            class: RegClass::Gpr64,
        })
    }

    fn imm(v: i64) -> X86ISelOperand {
        X86ISelOperand::Imm(v)
    }

    fn make_func(insts: Vec<X86ISelInst>) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![],
        };
        let mut func = X86ISelFunction::new("guard_elim_test".to_string(), sig);
        func.ensure_block(Block(0));
        for inst in insts {
            func.push_inst(Block(0), inst);
        }
        func
    }

    fn opcodes(func: &X86ISelFunction) -> Vec<X86Opcode> {
        func.blocks[&Block(0)]
            .insts
            .iter()
            .map(|i| i.opcode)
            .collect()
    }

    #[test]
    fn deletes_statically_true_bounds_check() {
        let mut f = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vr(1), imm(5)]),
            X86ISelInst::new(X86Opcode::TrapBoundsCheckExact, vec![vr(0), vr(1), imm(24)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(X86ConstGuardElim.run(&mut f));
        assert_eq!(opcodes(&f), vec![X86Opcode::MovRI, X86Opcode::Ret]);
    }

    #[test]
    fn keeps_out_of_bounds_and_unknown_checks() {
        // c == bound (25 <u 24 false) and unknown index both KEEP.
        let mut f = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vr(1), imm(24)]),
            X86ISelInst::new(X86Opcode::TrapBoundsCheckExact, vec![vr(0), vr(1), imm(24)]),
            X86ISelInst::new(X86Opcode::TrapBoundsCheckExact, vec![vr(0), vr(9), imm(24)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!X86ConstGuardElim.run(&mut f));
        assert_eq!(opcodes(&f).len(), 4);
    }

    #[test]
    fn redefinition_invalidates_tracking() {
        // idx redefined by an untracked op between MovRI and the check.
        let mut f = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vr(1), imm(5)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vr(1), vr(1), vr(2)]),
            X86ISelInst::new(X86Opcode::TrapBoundsCheckExact, vec![vr(0), vr(1), imm(24)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!X86ConstGuardElim.run(&mut f));
        assert_eq!(opcodes(&f).len(), 4);
    }

    #[test]
    fn deletes_nonzero_divisor_check_and_keeps_zero() {
        let mut f = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vr(1), imm(17)]),
            X86ISelInst::new(X86Opcode::TrapDivZeroExact, vec![vr(1)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vr(2), imm(0)]),
            X86ISelInst::new(X86Opcode::TrapDivZeroExact, vec![vr(2)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(X86ConstGuardElim.run(&mut f));
        let ops = opcodes(&f);
        assert_eq!(
            ops,
            vec![
                X86Opcode::MovRI,
                X86Opcode::MovRI,
                X86Opcode::TrapDivZeroExact,
                X86Opcode::Ret
            ]
        );
    }

    #[test]
    fn dedups_identical_guard_without_redef() {
        let mut f = make_func(vec![
            X86ISelInst::new(X86Opcode::TrapBoundsCheckExact, vec![vr(0), vr(8), imm(24)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vr(3), imm(7)]),
            X86ISelInst::new(X86Opcode::TrapBoundsCheckExact, vec![vr(0), vr(8), imm(24)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(X86ConstGuardElim.run(&mut f));
        let ops = opcodes(&f);
        assert_eq!(
            ops,
            vec![
                X86Opcode::TrapBoundsCheckExact,
                X86Opcode::MovRI,
                X86Opcode::Ret
            ]
        );
    }

    #[test]
    fn keeps_identical_guard_after_index_redef() {
        let mut f = make_func(vec![
            X86ISelInst::new(X86Opcode::TrapBoundsCheckExact, vec![vr(0), vr(8), imm(24)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vr(8), vr(8), vr(3)]),
            X86ISelInst::new(X86Opcode::TrapBoundsCheckExact, vec![vr(0), vr(8), imm(24)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!X86ConstGuardElim.run(&mut f));
        assert_eq!(opcodes(&f).len(), 4);
    }

    #[test]
    fn deletes_redundant_movri_restatement() {
        let mut f = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vr(1), imm(192)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vr(1), imm(192)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vr(1), imm(8)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(X86ConstGuardElim.run(&mut f));
        // Second 192 deleted; the 8 (different value) kept.
        let insts = &f.blocks[&Block(0)].insts;
        assert_eq!(insts.len(), 3);
        assert_eq!(insts[1].operands[1], imm(8));
    }

    #[test]
    fn copy_propagates_and_hidden_def_clears() {
        let mut f = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vr(1), imm(3)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vr(2), vr(1)]),
            X86ISelInst::new(X86Opcode::Xchg, vec![vr(3), vr(4)]),
            X86ISelInst::new(X86Opcode::TrapBoundsCheckExact, vec![vr(0), vr(2), imm(24)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        // Xchg clears tracking -> the check survives despite the copy.
        assert!(!X86ConstGuardElim.run(&mut f));
        assert_eq!(opcodes(&f).len(), 5);
    }
}
