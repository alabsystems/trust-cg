// trust-cg-opt - x86-64 Copy Propagation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Conservative copy propagation for x86-64 ISel-output functions.
//!
//! This pass is intentionally scoped to the x86 pass-manager surface. The x86
//! codegen pipeline runs it in its production O1 and O2/O3 pass orders.

use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use trust_cg_ir::regs::RegClass;
use trust_cg_ir::{VReg, X86Opcode};
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::effects::{
    x86_inst_effect, x86_operand0_may_be_read, x86_produces_value, x86_reads_flags,
    x86_writes_flags,
};
use crate::x86_pass_manager::X86MachinePass;

const MAX_COPY_CHAIN: usize = 16;

/// Copy propagation for x86-64 ISel-output machine functions.
pub struct X86CopyPropagation;

impl X86CopyPropagation {
    /// Run x86 copy propagation directly on an ISel function.
    pub fn run_on_function(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func, alu_barrier_rewrite_enabled())
    }
}

impl X86MachinePass for X86CopyPropagation {
    fn name(&self) -> &str {
        "x86-copy-prop"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func, alu_barrier_rewrite_enabled())
    }
}

/// `allow_alu` is passed explicitly rather than read from the `OnceLock` inside, so
/// both answers are unit-testable in one process — a `OnceLock` gate cannot be
/// flipped twice in a test binary, and an untestable enabled path is not worth
/// shipping.
fn run_impl(func: &mut X86ISelFunction, allow_alu: bool) -> bool {
    let mut changed = false;

    for block_id in func.block_order.clone() {
        let Some(block) = func.blocks.get_mut(&block_id) else {
            continue;
        };

        let mut copies = HashMap::default();

        for inst in &mut block.insts {
            if is_copy_prop_barrier(inst) {
                // ⚑ INVALIDATION GRANULARITY. This used to rewrite a rewritable
                // barrier's uses and then `clear()` the WHOLE map. Every
                // value-producing x86 ALU op is a barrier here because it writes
                // flags, so the FIRST user of a copy was rewritten and every
                // LATER user of the same copy was not — a partial,
                // order-dependent rewrite.
                //
                // ⚑ AND FIXING IT DID NOT FIX THE PASS. The hypothesis was that
                // this granularity bug was the mechanism behind the pass being a
                // net loss: on `p5_struct_acc` it splits a `rotate_left(9)` pair
                // (the `ShlRI` source rewritten v29 -> v28 while the `ShrRI`
                // source stays v29, so the peephole's rotate matcher fails its
                // `shl_src != shr_src` guard and a one-uop `ROL` becomes four
                // instructions). MEASURED after this fix, with the knob on:
                //
                //   m1_call_chain  0.9996 -> 1.0811   (was 1.0804 before the fix)
                //   b1_mispredict  1.0946 -> 1.1316   (was 1.1309)
                //   h2_vec_grow    0.9979 -> 1.0078   (was 1.0102)
                //   p2_collatz     1.0083 -> 1.0216   (was 1.0227)
                //
                // i.e. unchanged, and p5's `rol` count still goes 1 -> 0. So the
                // granularity bug is REAL and this is the right shape, but it is
                // not the operative defect. The pass stays DEFAULT OFF and the
                // remaining mechanism is unidentified; diagnosing it needs the
                // `trace-peephole-entry` IR dump, not another guess.
                //
                // LLVM clobbers only the registers the instruction DEFINES
                // (`MachineCopyPropagation.cpp`, `invalidateRegister` on each
                // def), never the whole table. The non-barrier path below
                // already does exactly that; only this arm threw the map away.
                // A barrier the pass DECLINES to rewrite — a call, a memory op,
                // a terminator — still clears everything, because those can
                // invalidate arbitrary registers.
                if can_rewrite_uses_before_clearing_barrier(inst, allow_alu)
                    && rewrite_use_operands(inst, &copies)
                {
                    changed = true;
                }
                // Only the PURE, VALUE-PRODUCING ALU category may keep the map:
                // such an instruction clobbers nothing but its own destination,
                // exactly like the non-barrier path below. A memory barrier, a
                // return, or a flag-only barrier still clears everything —
                // those can invalidate registers this pass does not track, and
                // four tests pin that (`..._preserves_memory_barriers`,
                // `..._return_still_clears_copy_state` and the two
                // rewrite-before-clearing ones).
                if allow_alu && can_rewrite_alu_barrier_uses(inst) {
                    if let Some(def) = defined_vreg(inst) {
                        invalidate_copies_with_vreg(&mut copies, def);
                    }
                } else {
                    copies.clear();
                }
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
    let mut seen = HashSet::default();

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

/// Index of the first operand this pass may rewrite as a use.
///
/// Operand 0 of a value-producing instruction is its destination and is never
/// renamed, even when the form also reads it (`Not [v]`, `AddRR [d, s]`,
/// `Cmovcc`, see [`crate::effects::x86_operand0_may_be_read`]): renaming a
/// tied operand 0 through a copy `d := s` renames the WRITE too, so `NOT d`
/// became `NOT s` and `d` kept the un-inverted copy. An opcode that defines no
/// register reads operand 0, which may follow a copy.
fn use_operand_start(inst: &X86ISelInst) -> usize {
    usize::from(x86_produces_value(inst.opcode))
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

static ALU_BARRIER_REWRITE_ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the value-producing-ALU copy-rewrite from a TRACKED compiler option,
/// once (`-Ztrust-ir-cg-args=x86-copyprop-alu`). **DEFAULT OFF.**
///
/// It is off because it was MEASURED and does not pay, not because it is unsound.
/// One bridge, 15 interleaved samples per arm on a pinned core:
///
/// ```text
///   b1_mispredict  218.74ms -> 221.05ms   1.0106x   P(on<off) = 0.200
///   p1_xorshift    448.42ms -> 448.52ms   1.0002x   P = 0.600
///   p2_collatz     167.10ms -> 167.12ms   1.0001x   P = 0.427
///   p3_gcd         259.86ms -> 259.66ms   0.9993x   P = 0.693
/// ```
///
/// It FIRES — `b1_mispredict`'s `main` goes 137 -> 126 instructions, exit code
/// unchanged — and the only non-neutral timing is b1 itself, in the WRONG
/// direction. That is consistent with everything else measured on this host this
/// round: removing instructions from a hot loop was cancelled or reversed by
/// alignment four separate times, and b1 in particular is misprediction-bound, so
/// eleven fewer instructions buy nothing.
///
/// Kept, opt-in, because the ANALYSIS gap it closes is real and general (see
/// `can_rewrite_alu_barrier_uses`) and a future change — better alignment, or a
/// program that is actually issue-bound — could make it pay. The number above is
/// what it has to beat.
pub fn set_alu_barrier_rewrite_enabled(enabled: bool) -> bool {
    match ALU_BARRIER_REWRITE_ENABLED.set(enabled) {
        Ok(()) => true,
        Err(requested) => ALU_BARRIER_REWRITE_ENABLED.get() == Some(&requested),
    }
}

fn alu_barrier_rewrite_enabled() -> bool {
    if let Some(enabled) = ALU_BARRIER_REWRITE_ENABLED.get() {
        return *enabled;
    }
    crate::tcg_env_flag("TCG_X86_COPYPROP_ALU")
}

fn can_rewrite_uses_before_clearing_barrier(inst: &X86ISelInst, allow_alu: bool) -> bool {
    can_rewrite_flag_barrier_uses(inst)
        || (allow_alu && can_rewrite_alu_barrier_uses(inst))
        || can_rewrite_memory_barrier_uses(inst)
        || can_rewrite_return_barrier_uses(inst)
}

/// A pure, VALUE-PRODUCING, flag-writing ALU instruction whose USE operands may be
/// rewritten before the barrier clears the copy map.
///
/// # Why this category was missing, and what it costs
///
/// [`is_copy_prop_barrier`] treats every flag writer as a barrier, and
/// [`can_rewrite_flag_barrier_uses`] rescues only the flag writers that produce NO
/// value (`Cmp`/`Test`/`Ucomis*`/`Ptest`). But on x86 essentially every ALU
/// instruction writes flags, so the effect was that **copy propagation never
/// rewrote the operands of any value-producing arithmetic**.
///
/// Measured cost, from a dump taken at the position this pass actually runs:
/// `b1_mispredict`'s xorshift block arrives as
///
/// ```text
///   MovRR v15, v11 ; ShlRI v18, v15, 13 ; XorRR v19, v11, v18
///   MovRR v20, v19 ; ShrRI v23, v20, 7  ; XorRR v24, v19, v23
///   MovRR v25, v24 ; ShlRI v28, v25, 17 ; XorRR v29, v24, v28
/// ```
///
/// Each `MovRR` exists only to feed the following shift, and the shift is
/// THREE-address so it does not destroy its input — the shift could read the
/// original register and the copy is pure waste. Three instructions per iteration,
/// in the one corpus program that trails clang, gcc AND LLVM.
///
/// # Soundness
///
/// A copy establishes that two registers hold the SAME VALUE. A pure ALU
/// instruction's result and its flags are both functions of its operand VALUES, so
/// substituting a copy-equal register for a use changes neither. Class safety comes
/// from the pass itself: [`copy_vregs`] only records same-class copies and
/// [`resolve_copy`] refuses to cross a class boundary, so no aliased width view can
/// be substituted.
///
/// `alu_operand0_is_pure_def` is the load-bearing extra condition: it restricts
/// this to the non-tied form, so operand 0 is a PURE definition and
/// [`use_operand_start`] therefore skips exactly the def and nothing else. A tied
/// two-address form reads its destination, and is left alone.
fn can_rewrite_alu_barrier_uses(inst: &X86ISelInst) -> bool {
    let flags = inst.flags;

    x86_inst_effect(inst).is_pure()
        && x86_produces_value(inst.opcode)
        && alu_operand0_is_pure_def(inst)
        && !inst_touches_fixed_register(inst)
        && !flags.is_call()
        && !flags.is_branch()
        && !flags.is_terminator()
        && !flags.is_return()
        && !flags.has_side_effects()
        && !flags.reads_memory()
        && !flags.writes_memory()
        && !x86_reads_flags(inst.opcode)
        && x86_writes_flags(inst.opcode)
        && is_rewritable_alu_barrier_opcode(inst.opcode)
}

/// Three-address ALU opcodes whose operands this pass may rewrite. Each writes its
/// result to operand 0, reads only operands 1.., and has no implicit register
/// result (so no `Mul`/`Div`, whose `rdx:rax` pair is invisible in the operand
/// list).
/// Operand 0 of an allowlisted ALU form is a PURE definition, so
/// [`use_operand_start`] skips exactly the def and every remaining operand is a
/// read.
///
/// [`x86_operand0_may_be_read`] deliberately OVER-APPROXIMATES for the
/// register-immediate ALU and shift opcodes. Its own comment says so: "The
/// three-operand `[d, s, imm]` forms do not read `d`, but the passes' tied list has
/// always counted them; keep the over-approximation." That predicate is shared with
/// other passes and is NOT changed here; this local test instead encodes the arity
/// convention for exactly the opcodes this pass allowlists.
///
/// For those opcodes the TIED form is `[d, imm]` and the three-address form is
/// `[d, s, imm]`, so an operand count of three identifies the non-tied shape. Every
/// other allowlisted opcode defers to the shared predicate, which is exact for
/// them (`ImulRRI` is documented there as writing operand 0 only, and the RR forms
/// distinguish tied by arity already).
fn alu_operand0_is_pure_def(inst: &X86ISelInst) -> bool {
    match inst.opcode {
        X86Opcode::AddRI
        | X86Opcode::SubRI
        | X86Opcode::AndRI
        | X86Opcode::OrRI
        | X86Opcode::XorRI
        | X86Opcode::ShlRI
        | X86Opcode::ShrRI
        | X86Opcode::SarRI => inst.operands.len() == 3,
        _ => !x86_operand0_may_be_read(inst),
    }
}

/// Three-address ALU opcodes whose operands this pass may rewrite. Each writes its
/// result to operand 0, reads only operands 1.., and has no implicit register
/// result (so no `Mul`/`Div`, whose `rdx:rax` pair is invisible in the operand
/// list).
fn is_rewritable_alu_barrier_opcode(opcode: X86Opcode) -> bool {
    matches!(
        opcode,
        X86Opcode::AddRR
            | X86Opcode::SubRR
            | X86Opcode::XorRR
            | X86Opcode::AndRR
            | X86Opcode::OrRR
            | X86Opcode::ImulRR
            | X86Opcode::AddRI
            | X86Opcode::SubRI
            | X86Opcode::XorRI
            | X86Opcode::AndRI
            | X86Opcode::OrRI
            | X86Opcode::ImulRRI
            | X86Opcode::ShlRI
            | X86Opcode::ShrRI
            | X86Opcode::SarRI
    )
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
            // `BT reg, imm` — a bit test. OMITTED until 2026-10-01 although it
            // is in the SAME category as every opcode above, by this repo's own
            // three classification tables: `x86_64_ops.rs` groups it with
            // `CmpRR | ... | Ucomiss` as flags-only `HAS_SIDE_EFFECTS`,
            // `effects.rs` gives it `MemoryEffect::Pure`, and
            // `x86_produces_value` returns FALSE for it in that same arm. So it
            // satisfies every other condition in
            // `can_rewrite_flag_barrier_uses` and was excluded by this list
            // alone.
            //
            // The cost was measured on `p2_collatz`, the only program above
            // parity among those that currently compile (1.0113x LLVM). Its
            // inner loop arrives as `MovRR v21, v12 ; BtRI v21, 0` — a copy of
            // the loop-carried value made ONLY to test its bit 0, where the
            // test could read `v12` directly and the copy is pure waste.
            //
            // Soundness is the module doc's existing argument verbatim: a copy
            // establishes that two registers hold the same VALUE, and `BT`'s
            // only output is RFLAGS, a function of its operand value and the
            // immediate bit index. Substituting a copy-equal register changes
            // neither. Class safety comes from the pass: `copy_vregs` records
            // only same-class copies and `resolve_copy` refuses to cross a
            // class boundary.
            | X86Opcode::BtRI
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
            | X86Opcode::MovzxRM8
            | X86Opcode::MovzxRM16
            | X86Opcode::MovzxRM8Sib
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

    /// `Not [v1]` is `v1 := !v1`: operand 0 is read AND written. Renaming it
    /// through the copy `v1 := v0` would invert `v0` instead and leave `v1`
    /// holding the un-inverted value that the return reads.
    #[test]
    fn x86_copy_prop_never_renames_a_tied_not_destination() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(5)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::Not, vec![vreg(1)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![X86ISelOperand::PReg(RAX), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(!copy_prop.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[2].operands, vec![vreg(1)], "NOT must still invert v1");
        assert_eq!(insts[3].operands, vec![X86ISelOperand::PReg(RAX), vreg(1)]);
    }

    /// In the two-operand form `Not [d, s]` operand 0 is only the
    /// destination: the source may follow the copy, the destination may not.
    #[test]
    fn x86_copy_prop_rewrites_only_the_source_of_a_two_operand_not() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(5)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::Not, vec![vreg(1), vreg(1)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![X86ISelOperand::PReg(RAX), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(copy_prop.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            insts[2].operands,
            vec![vreg(1), vreg(0)],
            "only the source follows the copy; v1 is still the destination"
        );
        assert_eq!(insts[3].operands, vec![X86ISelOperand::PReg(RAX), vreg(1)]);
    }

    /// No value-producing opcode may have its destination renamed, whatever
    /// its operand-0 read: a rename changes which register is written.
    #[test]
    fn x86_copy_prop_use_start_skips_every_defined_operand0() {
        use crate::effects::x86_operand0_may_be_read;

        for opcode in [
            X86Opcode::Not,
            X86Opcode::Neg,
            X86Opcode::Inc,
            X86Opcode::Bswap,
            X86Opcode::AddRR,
            X86Opcode::Addsd,
            X86Opcode::Cmovcc,
            X86Opcode::MovRR,
            X86Opcode::Lea,
        ] {
            for operand_count in 1..=3 {
                let inst = X86ISelInst::new(opcode, (0..operand_count).map(vreg).collect());
                assert_eq!(
                    use_operand_start(&inst),
                    1,
                    "{opcode:?} with {operand_count} operands (operand 0 may be read: {})",
                    x86_operand0_may_be_read(&inst)
                );
            }
        }
        for opcode in [X86Opcode::CmpRR, X86Opcode::JmpR, X86Opcode::MovMR] {
            let inst = X86ISelInst::new(opcode, vec![vreg(0), vreg(1)]);
            assert_eq!(use_operand_start(&inst), 0, "{opcode:?} reads operand 0");
        }
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

    // ---- value-producing ALU flag writers ----

    /// `b1_mispredict`'s xorshift shape: a copy whose ONLY use is the source of a
    /// three-address shift. The shift does not destroy its input, so it can read
    /// the original and the copy becomes dead (DCE removes it).
    #[test]
    fn rewrites_a_copy_feeding_a_three_address_shift() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(15), vreg(11)]),
            X86ISelInst::new(
                X86Opcode::ShlRI,
                vec![vreg(18), vreg(15), X86ISelOperand::Imm(13)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(run_impl(&mut func, true));
        let shl = entry_insts(&func)
            .iter()
            .find(|i| i.opcode == X86Opcode::ShlRI)
            .expect("the shift survives")
            .clone();
        assert_eq!(
            shl.operands,
            vec![vreg(18), vreg(11), X86ISelOperand::Imm(13)],
            "the shift now reads the copy's SOURCE"
        );
    }

    #[test]
    fn rewrites_a_copy_feeding_a_three_address_xor() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(20), vreg(19)]),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(24), vreg(20), vreg(23)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(run_impl(&mut func, true));
        let x = entry_insts(&func)
            .iter()
            .find(|i| i.opcode == X86Opcode::XorRR)
            .expect("the xor survives")
            .clone();
        assert_eq!(x.operands, vec![vreg(24), vreg(19), vreg(23)]);
    }

    /// THE load-bearing restriction: a TIED two-address form reads its destination,
    /// so operand 0 is not a pure def and `use_operand_start` cannot be trusted to
    /// skip exactly the def. Left alone.
    #[test]
    fn declines_a_tied_two_address_alu_form() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(15), vreg(11)]),
            // Two operands: the tied form, `v15 := v15 ^ v3`.
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(15), vreg(3)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        run_impl(&mut func, true);
        let x = entry_insts(&func)
            .iter()
            .find(|i| i.opcode == X86Opcode::XorRR)
            .expect("the xor survives")
            .clone();
        assert_eq!(
            x.operands,
            vec![vreg(15), vreg(3)],
            "a tied form must not be rewritten"
        );
    }

    /// A flag READER still bars rewriting: its flags come from an earlier producer
    /// and this pass reasons about registers, not flag provenance.
    #[test]
    fn declines_a_flag_reading_alu_form() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(15), vreg(11)]),
            X86ISelInst::new(
                X86Opcode::Cmovcc,
                vec![
                    vreg(18),
                    vreg(15),
                    X86ISelOperand::CondCode(trust_cg_ir::X86CondCode::B),
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        run_impl(&mut func, true);
        let c = entry_insts(&func)
            .iter()
            .find(|i| i.opcode == X86Opcode::Cmovcc)
            .expect("the cmov survives")
            .clone();
        assert_eq!(c.operands[1], vreg(15), "a flag reader is not rewritten");
    }

    /// Cross-class copies are never recorded, so no aliased width view can be
    /// substituted into an ALU use.
    #[test]
    fn declines_a_cross_class_copy_into_an_alu_use() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR32, vec![vreg32(15), vreg32(11)]),
            X86ISelInst::new(
                X86Opcode::ShlRI,
                vec![vreg(18), vreg(15), X86ISelOperand::Imm(13)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        run_impl(&mut func, true);
        let shl = entry_insts(&func)
            .iter()
            .find(|i| i.opcode == X86Opcode::ShlRI)
            .expect("the shift survives")
            .clone();
        assert_eq!(
            shl.operands[1],
            vreg(15),
            "a 64-bit use must not be rewritten from a 32-bit copy"
        );
    }

    /// DEFAULT-OFF pin: with the widening disabled, a value-producing ALU flag
    /// writer is a plain barrier and its uses are not rewritten.
    #[test]
    fn default_leaves_a_value_producing_alu_use_alone() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(15), vreg(11)]),
            X86ISelInst::new(
                X86Opcode::ShlRI,
                vec![vreg(18), vreg(15), X86ISelOperand::Imm(13)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        run_impl(&mut func, false);
        let shl = entry_insts(&func)
            .iter()
            .find(|i| i.opcode == X86Opcode::ShlRI)
            .expect("the shift survives")
            .clone();
        assert_eq!(shl.operands[1], vreg(15), "default keeps the copy's use");
    }

    /// `BtRI` is the shape `p2_collatz`'s inner loop arrives in: a copy of the
    /// loop-carried value made ONLY so its bit 0 can be tested. `BT` reads its
    /// operand and writes nothing but RFLAGS, so the test can read the original.
    #[test]
    fn x86_copy_prop_rewrites_bt_ri_before_clearing_flag_barrier() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::BtRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut copy_prop = X86CopyPropagation;

        assert!(copy_prop.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            insts[1].operands,
            vec![vreg(0), X86ISelOperand::Imm(0)],
            "BtRI must read the ORIGINAL register, leaving the copy dead for DCE"
        );
    }

    /// The class guard, which is what keeps a width view from being substituted:
    /// a 32-bit copy must not be forwarded into a 64-bit `BtRI` use.
    #[test]
    fn x86_copy_prop_refuses_a_cross_class_copy_into_bt_ri() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR32, vec![vreg32(1), vreg32(0)]),
            X86ISelInst::new(X86Opcode::BtRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut copy_prop = X86CopyPropagation;
        let _ = copy_prop.run_on_function(&mut func);

        let insts = entry_insts(&func);
        assert_eq!(
            insts[1].operands,
            vec![vreg(1), X86ISelOperand::Imm(0)],
            "a Gpr32 copy must not be forwarded into a Gpr64 use"
        );
    }
}
