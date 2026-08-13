// trust-cg-opt - x86-64 two-address pre-expansion (coalescer-driven)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Pre-regalloc two-address EXPANSION for x86-64 ISel-output functions.
//!
//! A three-address integer ALU op `Op d, a, b` must become the x86 two-address
//! form (d == lhs). Today ISel emits the three-address form and a POST-regalloc
//! `fixup_two_address` inserts `MovRR d, a` whenever the allocator gave d != a —
//! and it almost always does, since the tie is never expressed to the allocator.
//! Those redundant copies dominate tight ALU loops (b17_xorshift emits two per
//! `x ^= x<<k` step; the sort/hash hot loops likewise).
//!
//! This pass makes the allocator eliminate them, WITHOUT any hand-rolled liveness
//! (four such attempts miscompiled b16). For each coalesceable three-address op
//! it performs the purely MECHANICAL, semantics-preserving rewrite
//!
//! ```text
//!   Op [d, a, b]   ==>   MovRR [d, a] ;  Op [d, d, b]
//! ```
//!
//! * `MovRR [d, a]` is a class-exact register copy → normalizes to a
//!   `PSEUDO_COPY` at the isel→regalloc bridge, which the PROVEN regalloc
//!   coalescer folds (`d ← a`) iff `d` and `a` do not interfere — using the
//!   allocator's own liveness/interference (`coalesce.rs`), never ours. When they
//!   DO interfere (loop-carried `a` still live), the copy survives — correct, and
//!   no worse than today's post-RA fixup.
//! * `Op [d, d, b]` stays THREE-ADDRESS with dst == lhs, so the encoder / post-RA
//!   dataflow validator / replay see the shape they already fully cover, and the
//!   post-RA `fixup_two_address` no-ops (dst == lhs). The coalesced-away
//!   `PSEUDO_COPY` is accepted by `x86_validate_removed_original_copy`.
//!
//! Semantics: `MovRR d,a` sets `d = a`, then `Op d,d,b` computes `d = a op b` —
//! byte-identical to the original `Op d,a,b`. GUARDS (both required for
//! correctness): skip when `d == a` (already in-place, nothing to do) and when
//! `d == b` (the rewrite would read `d` after clobbering it — e.g. `d = a; d =
//! d op d = a op a` — a miscompile). Gated `TCG_X86_TWOADDR_EXPAND` (opt-in).

use trust_cg_ir::regs::RegClass;
use trust_cg_ir::{VReg, X86Opcode};
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::x86_pass_manager::X86MachinePass;

fn enabled() -> bool {
    crate::env_lock::var_os("TCG_X86_TWOADDR_EXPAND").is_some()
}

/// GPR three-operand two-address integer ALU ops (def = operand 0, tied lhs =
/// operand 1, second source = operand 2). Only the RR forms whose second source
/// is a register (so the `d == b` aliasing guard is meaningful).
fn is_expandable_gpr_two_address(op: X86Opcode) -> bool {
    matches!(
        op,
        X86Opcode::AddRR
            | X86Opcode::SubRR
            | X86Opcode::AndRR
            | X86Opcode::OrRR
            | X86Opcode::XorRR
            | X86Opcode::ImulRR
            | X86Opcode::AdcRR
            | X86Opcode::SbbRR
    )
}

/// The class-exact register-copy opcode for a GPR class, matching the
/// `x86_isel_copy_like_vregs` combos so the inserted copy normalizes to
/// `PSEUDO_COPY` (the form the coalescer folds). `None` for classes outside the
/// coalescer's recognized set (the expansion is then skipped — a perf no-op).
fn copy_opcode_for_class(class: RegClass) -> Option<X86Opcode> {
    match class {
        RegClass::Gpr64 | RegClass::System => Some(X86Opcode::MovRR),
        RegClass::Gpr32 => Some(X86Opcode::MovRR32),
        _ => None,
    }
}

/// x86-64 pre-regalloc two-address expansion pass.
pub struct X86TwoAddressExpand;

impl X86TwoAddressExpand {
    pub fn run_on_function(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func)
    }
}

impl X86MachinePass for X86TwoAddressExpand {
    fn name(&self) -> &str {
        "x86-two-addr-expand"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func)
    }
}

fn run_impl(func: &mut X86ISelFunction) -> bool {
    if !enabled() {
        return false;
    }
    // PROFITABILITY gate (NOT a correctness gate — correctness is entirely the
    // regalloc coalescer's interference test). Count how many times each vreg is
    // READ across the function. We only expand `Op d,a,b` when `a` is read
    // EXACTLY ONCE (here, as this op's lhs): then `a`'s live range ends at this
    // op, so `d` (which begins here) cannot interfere with it, and the coalescer
    // is GUARANTEED to fold the inserted copy — a clean win with zero added
    // register pressure. When `a` is read more than once the copy might not fold
    // (a stays live), so inserting it would only raise pressure and can REGRESS
    // spill-heavy loops (b06/b18); we skip those. A wrong count only changes
    // whether we expand, never the result.
    let read_counts = count_reads(func);
    let mut changed = false;
    for block_id in func.block_order.clone() {
        let Some(block) = func.blocks.get_mut(&block_id) else {
            continue;
        };
        let mut new_insts: Vec<X86ISelInst> = Vec::with_capacity(block.insts.len());
        for inst in std::mem::take(&mut block.insts) {
            if let Some((copy, rewritten)) = try_expand(&inst, &read_counts) {
                new_insts.push(copy);
                new_insts.push(rewritten);
                changed = true;
            } else {
                new_insts.push(inst);
            }
        }
        block.insts = new_insts;
    }
    changed
}

/// Count how many times each vreg is READ (appears as a non-def-slot operand, or
/// inside a memory operand's base/index) across the whole function.
fn count_reads(func: &X86ISelFunction) -> std::collections::HashMap<VReg, u32> {
    use crate::effects::x86_produces_value;
    let mut counts: std::collections::HashMap<VReg, u32> = std::collections::HashMap::new();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            let has_def = x86_produces_value(inst.opcode);
            for (i, op) in inst.operands.iter().enumerate() {
                if has_def && i == 0 {
                    continue; // operand-0 def slot is not a read
                }
                count_operand_reads(op, &mut counts);
            }
        }
    }
    counts
}

fn count_operand_reads(op: &X86ISelOperand, counts: &mut std::collections::HashMap<VReg, u32>) {
    match op {
        X86ISelOperand::VReg(v) => {
            *counts.entry(*v).or_insert(0) += 1;
        }
        X86ISelOperand::MemAddr { base, .. } => count_operand_reads(base, counts),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            count_operand_reads(base, counts);
            count_operand_reads(index, counts);
        }
        _ => {}
    }
}

/// If `inst` is a coalesceable three-address GPR ALU op `[d, a, b]` with the
/// guards satisfied AND expanding it is profitable (`a` dead after the op),
/// return `(MovRR [d, a], Op [d, d, b])`; else `None`.
fn try_expand(
    inst: &X86ISelInst,
    read_counts: &std::collections::HashMap<VReg, u32>,
) -> Option<(X86ISelInst, X86ISelInst)> {
    if !is_expandable_gpr_two_address(inst.opcode) {
        return None;
    }
    // Exactly three register operands [d, a, b].
    let [
        X86ISelOperand::VReg(d),
        X86ISelOperand::VReg(a),
        X86ISelOperand::VReg(b),
    ] = inst.operands.as_slice()
    else {
        return None;
    };
    let (d, a, b) = (*d, *a, *b);
    // GUARD 1: already in-place — nothing to coalesce.
    if d == a {
        return None;
    }
    // GUARD 2: def aliases the second source — the rewrite `d=a; d=d op b` would
    // read `d` (== b) AFTER clobbering it, computing `a op a` instead of `a op b`.
    if d == b {
        return None;
    }
    // Class-exact copy so it normalizes to PSEUDO_COPY; skip other classes.
    if d.class != a.class {
        return None;
    }
    // PROFITABILITY: only expand when `a` is read exactly once (here) — then `a`
    // is dead after the op and the coalescer is guaranteed to fold the copy with
    // no added pressure. (Profitability only; correctness is the coalescer's.)
    if read_counts.get(&a).copied() != Some(1) {
        return None;
    }
    let copy_op = copy_opcode_for_class(d.class)?;

    // Preserve the original op's flags / proof origin on the rewritten op (it is
    // the same operation, just with dst reused as lhs). The copy is a plain move.
    let copy = X86ISelInst::new(
        copy_op,
        vec![X86ISelOperand::VReg(d), X86ISelOperand::VReg(a)],
    );
    let mut rewritten = inst.clone();
    rewritten.operands = vec![
        X86ISelOperand::VReg(d),
        X86ISelOperand::VReg(d),
        X86ISelOperand::VReg(b),
    ];
    Some((copy, rewritten))
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::regs::VReg;
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::instructions::Block;
    use trust_cg_lower::types::Type;

    fn g64(id: u32) -> VReg {
        VReg::new(id, RegClass::Gpr64)
    }
    fn vr(v: VReg) -> X86ISelOperand {
        X86ISelOperand::VReg(v)
    }

    /// A function with a single block of `insts` and one Ret.
    fn func_with(insts: Vec<X86ISelInst>) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut f = X86ISelFunction::new("expand_test".to_string(), sig);
        f.ensure_block(Block(0));
        let blk = f.blocks.get_mut(&Block(0)).unwrap();
        blk.insts = insts;
        blk.insts.push(X86ISelInst::new(X86Opcode::Ret, vec![]));
        f
    }

    fn count(f: &X86ISelFunction, op: X86Opcode) -> usize {
        f.blocks
            .get(&Block(0))
            .unwrap()
            .insts
            .iter()
            .filter(|i| i.opcode == op)
            .count()
    }

    // Both modes use thread-local overrides, so parallel tests remain isolated.
    #[test]
    fn two_addr_expand_behavior() {
        let env_scope = crate::env_lock::override_scope();
        let _default_off =
            crate::env_lock::ScopedEnvVar::unset(&env_scope, "TCG_X86_TWOADDR_EXPAND");
        let (d, a, b) = (g64(10), g64(11), g64(12));
        let mk_simple = || {
            vec![
                X86ISelInst::new(X86Opcode::XorRR, vec![vr(d), vr(a), vr(b)]),
                // downstream use of d and b so neither is dead-stripped; a is
                // read ONLY in the XorRR (exactly once).
                X86ISelInst::new(X86Opcode::AddRR, vec![vr(d), vr(d), vr(b)]),
            ]
        };

        // (1) Off by default (env unset): no expansion.
        let mut off = func_with(mk_simple());
        assert!(
            !X86TwoAddressExpand.run_on_function(&mut off),
            "off by default"
        );
        assert_eq!(count(&off, X86Opcode::MovRR), 0);

        let _enabled =
            crate::env_lock::ScopedEnvVar::set(&env_scope, "TCG_X86_TWOADDR_EXPAND", "1");

        // (2) Opt-in: `a` used once -> expands to MovRR d,a ; XorRR d,d,b.
        let mut on = func_with(mk_simple());
        assert!(
            X86TwoAddressExpand.run_on_function(&mut on),
            "should expand"
        );
        assert_eq!(count(&on, X86Opcode::MovRR), 1, "one copy inserted");
        let xor = on
            .blocks
            .get(&Block(0))
            .unwrap()
            .insts
            .iter()
            .find(|i| i.opcode == X86Opcode::XorRR)
            .unwrap();
        assert_eq!(xor.operands, vec![vr(d), vr(d), vr(b)], "XorRR -> [d,d,b]");

        // (3) d == b guard: `d = a ^ d` would compute a^a -> MUST skip.
        let (d2, a2) = (g64(20), g64(21));
        let mut alias = func_with(vec![
            X86ISelInst::new(X86Opcode::XorRR, vec![vr(d2), vr(a2), vr(d2)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vr(d2), vr(d2), vr(a2)]),
        ]);
        assert!(
            !X86TwoAddressExpand.run_on_function(&mut alias),
            "must NOT expand when d == b"
        );

        // (4) Profitability: `a` read twice -> skip (no guaranteed fold).
        let (d3, a3, b3, e3) = (g64(30), g64(31), g64(32), g64(33));
        let mut busy = func_with(vec![
            X86ISelInst::new(X86Opcode::XorRR, vec![vr(d3), vr(a3), vr(b3)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vr(e3), vr(a3), vr(b3)]), // 2nd read of a
            X86ISelInst::new(X86Opcode::AddRR, vec![vr(d3), vr(d3), vr(e3)]),
        ]);
        assert!(
            !X86TwoAddressExpand.run_on_function(&mut busy),
            "skip when lhs used more than once"
        );
    }
}
