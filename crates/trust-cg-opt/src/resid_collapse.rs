// trust-cg-opt - SOUND single-trip residual-loop collapse (aarch64)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! # Single-trip residual-loop collapse (`resid-collapse`)
//!
//! Decides an always-taken counted-loop EXIT branch at compile time and
//! replaces the `BCond exit; B latch` terminator pair with an unconditional
//! `B exit`, unlinking the (then statically unreachable) latch.
//!
//! ## Why this exists
//!
//! `scalar-unroll`'s FULL-UNROLL mode deliberately emits `trip-1` straight-line
//! copies and re-enters the ORIGINAL loop header for the FINAL iteration (so
//! every loop live-out is produced by the original code — its soundness
//! contract). The leftover header is a genuine loop in the CFG that always runs
//! EXACTLY ONCE: the iv enters as the compile-time constant `init + (trip-1)`
//! and the exit compare `iv + step == bound` is decidable. Left alone, the hot
//! path pays the loop control (`cmp`/`b.eq`/`b` plus the latch writeback block)
//! on every outer iteration, and — worse — the backedge makes the iv MULTI-DEF,
//! so every downstream invariance-driven pass (`alias-hoist`'s versioned load
//! hoisting in particular) must treat the residual body's addresses as variant
//! and cannot hoist its loads. On Shootout `matrix` this single residual
//! iteration is worth ~9% of whole-program time, and the un-hoistable lane-9
//! loads block another chunk (measured by the V0..V5 asm-ladder experiment,
//! 2026-08; see the session notes).
//!
//! ## The proof obligation (first-execution induction; fail-closed)
//!
//! For a block `H` ending `..., Cmp(a, b), BCond(cc, EXIT), B(T)`:
//!
//! 1. `H` contains no other branch/terminator; the `Cmp` is IMMEDIATELY before
//!    the `BCond` (no instruction between them can clobber flags).
//! 2. The backedge target `T` is `H` itself, or a latch block `L` whose ONLY
//!    predecessor is `H` (so `L` — and through it the backedge — can execute
//!    only if the `BCond` falls through).
//! 3. Every OTHER predecessor `P` of `H` (the entries) delivers the same
//!    compile-time constant `c` for the iv: `reaching-const` (the audited
//!    reaching-definitions engine, extended here through `MovR`/`Copy`/
//!    `AddRI #0` copies) resolves the iv at `P`'s terminator to `c`.
//! 4. Inside `H`, `a`'s LAST definition before the `Cmp` is `AddRI(a, iv, #s)`
//!    (by the audited def-role table), the iv has NO definition in `H` before
//!    that `AddRI` (its value there is the entry value `c`), and `a` is not
//!    redefined between the `AddRI` and the `Cmp`.
//! 5. The compare RHS is an immediate (`CmpRI #k`) or resolves to a unique
//!    reaching constant (`CmpRR` vs a `Movz`/`Movk` chain).
//! 6. Evaluating the compare at the compare's register width with two's-
//!    complement wrap-around — `lhs = (c + s) mod 2^w` vs `k` under
//!    `cc ∈ {EQ, GE (signed), HS (unsigned)}` — yields TAKEN.
//!
//! Then on the FIRST execution of `H` the exit branch is taken, so the backedge
//! never runs, so `H` never re-executes with any other iv value — by induction
//! the `BCond` is always taken and rewriting it to `B(EXIT)` is bit-exact.
//! The latch `L` (unreachable: its only predecessor edge is the deleted
//! fall-through) is unlinked from the CFG and the block order. Nothing that
//! ever executed is skipped, so NO liveness argument about `L`'s writebacks is
//! needed. Every gate above fails closed.
//!
//! After the rewrite the residual body is straight-line and its iv is
//! effectively single-def, so `alias-hoist` (which runs later) can prove the
//! residual loads' addresses invariant and hoist them with the other lanes.
//!
//! Emits only `B` (already ubiquitous); deletes a `BCond` + `B`. No new
//! opcode, no proof-DB entry. Runs at O2/O3 right after `scalar-unroll`.
//! Compile-time kill switch: `TCG_NO_RESID_COLLAPSE` (run() becomes a no-op,
//! byte-identical output). Per-pass bisect: `TRUST_CG_DISABLE_PASSES=residcollapse`.

use trust_cg_ir::{AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, VReg};

use crate::effects::aarch64_def_operand_positions;
use crate::pass_manager::MachinePass;
use crate::reaching_const::{unique_reaching_const, unique_reaching_def};

/// AArch64 condition codes (numeric encodings, matching the encoder contract
/// and the other loop passes).
const CC_EQ: i64 = 0;
const CC_HS: i64 = 2;
const CC_GE: i64 = 10;

/// Copy-following depth for the entry-constant resolution: `MovR iv, t` on top
/// of the `Movz`/`Movk` chain (scalar-unroll's tail writeback) plus slack.
const MAX_COPY_DEPTH: u32 = 4;

/// Dev trace hook (`TRUST_CG_TRACE_RESIDCOLLAPSE`).
fn trace(msg: &str) {
    if std::env::var_os("TRUST_CG_TRACE_RESIDCOLLAPSE").is_some() {
        eprintln!("[residcollapse] {msg}");
    }
}

/// Single-trip residual-loop collapse pass.
pub struct ResidTripCollapse;

impl MachinePass for ResidTripCollapse {
    fn name(&self) -> &str {
        "resid-collapse"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        if std::env::var_os("TCG_NO_RESID_COLLAPSE").is_some() {
            return false;
        }
        let mut changed = false;
        // Re-scan after each committed collapse: a rewrite changes the CFG the
        // recognition (preds/succs) depends on. Each collapse deletes one
        // conditional branch, so the loop terminates.
        while let Some(plan) = find_candidate(func) {
            commit(func, &plan);
            changed = true;
        }
        changed
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        _provenance: &mut trust_cg_ir::ProvenanceMap,
    ) -> bool {
        self.run(func)
    }
}

/// A proven always-taken exit branch ready to commit.
struct Plan {
    /// The block whose terminator pair is rewritten.
    header: BlockId,
    /// The always-taken exit target.
    exit: BlockId,
    /// The never-taken backedge target (`header` itself or the latch).
    back_target: BlockId,
    /// The latch to unlink (`None` when the backedge is a self-loop).
    latch: Option<BlockId>,
    /// The `Cmp` feeding the decided `BCond` (deleted post-rewrite when the
    /// flags are provably dead) and the step `AddRI` / its dst (deleted when
    /// the value has no remaining linked use).
    cmp: InstId,
    step_add: InstId,
    step: VReg,
    /// The `CmpRR` bound register, for Movz-chain cleanup (`None` for CmpRI).
    bound_reg: Option<VReg>,
}

fn find_candidate(func: &MachFunction) -> Option<Plan> {
    for &header in &func.block_order {
        if let Some(plan) = try_block(func, header) {
            return Some(plan);
        }
    }
    None
}

fn try_block(func: &MachFunction, header: BlockId) -> Option<Plan> {
    let insts = &func.block(header).insts;
    if insts.len() < 3 {
        return None;
    }

    // --- Terminator shape: exactly `..., Cmp, BCond(cc, EXIT), B(T)` with no
    // other branch/terminator anywhere in the block (gate 1).
    let b_id = *insts.last()?;
    let bc_id = insts[insts.len() - 2];
    let cmp_id = insts[insts.len() - 3];
    let b_inst = func.inst(b_id);
    let bc_inst = func.inst(bc_id);
    if b_inst.opcode != AArch64Opcode::B || bc_inst.opcode != AArch64Opcode::BCond {
        return None;
    }
    for &id in &insts[..insts.len() - 2] {
        let inst = func.inst(id);
        if inst.is_branch() || inst.is_terminator() {
            return None;
        }
    }
    let cc = bc_inst.operands.first()?.as_imm()?;
    if !matches!(cc, CC_EQ | CC_HS | CC_GE) {
        return None;
    }
    let exit = match bc_inst.operands.get(1)? {
        MachOperand::Block(t) => *t,
        _ => return None,
    };
    let back_target = match b_inst.operands.first()? {
        MachOperand::Block(t) => *t,
        _ => return None,
    };
    if exit == header || exit == back_target {
        return None;
    }

    // --- Backedge structure (gate 2): self-loop, or a latch whose ONLY
    // predecessor is `header` (so it runs only via the fall-through edge).
    // The latch is UNLINKED on commit, so its content must be the pure
    // scalar-unroll writeback shape (copies + `B`): a call or any
    // fixed-register/memory-operand instruction could be referenced by
    // structural metadata (EH call sites) that unlinking would dangle.
    let latch = if back_target == header {
        None
    } else {
        let lp = &func.block(back_target).preds;
        if lp.len() != 1 || lp[0] != header {
            return None;
        }
        // The latch must not be the function entry (entered without any pred).
        if back_target == func.entry {
            return None;
        }
        let latch_insts = &func.block(back_target).insts;
        let (&latch_term, latch_body) = latch_insts.split_last()?;
        let term = func.inst(latch_term);
        if term.opcode != AArch64Opcode::B {
            return None;
        }
        for &id in latch_body {
            let inst = func.inst(id);
            if copy_source(inst).is_none()
                || !inst.implicit_defs.is_empty()
                || !inst.implicit_uses.is_empty()
                || inst
                    .operands
                    .iter()
                    .any(|op| !matches!(op, MachOperand::VReg(_) | MachOperand::Imm(_)))
            {
                return None;
            }
        }
        Some(back_target)
    };
    // A header that is the function entry has an implicit entry with unknown
    // state — fail closed.
    if header == func.entry {
        return None;
    }

    // --- Compare shape (gate 5): `CmpRR(a, b)` / `CmpRI(a, #k)`.
    let cmp_inst = func.inst(cmp_id);
    let (a, rhs_const, bound_reg) = match cmp_inst.opcode {
        AArch64Opcode::CmpRI => {
            let a = cmp_inst.operands.first()?.as_vreg()?;
            let k = cmp_inst.operands.get(1)?.as_imm()?;
            (a, k, None)
        }
        AArch64Opcode::CmpRR => {
            let a = cmp_inst.operands.first()?.as_vreg()?;
            let b = cmp_inst.operands.get(1)?.as_vreg()?;
            let k = const_through_copies(func, cmp_id, b, MAX_COPY_DEPTH)?;
            (a, k, Some(b))
        }
        _ => return None,
    };

    // --- In-block dataflow (gate 4): a's LAST def before the Cmp is
    // `AddRI(a, iv, #s)`; the iv has no def in the block before that AddRI.
    let cmp_pos = insts.len() - 3;
    let mut a_def: Option<(usize, InstId)> = None;
    for (pos, &id) in insts[..cmp_pos].iter().enumerate() {
        if defines_id(func, id, a.id) {
            a_def = Some((pos, id));
        }
    }
    let (add_pos, add_id) = a_def?;
    let add_inst = func.inst(add_id);
    if add_inst.opcode != AArch64Opcode::AddRI || add_inst.operands.len() != 3 {
        return None;
    }
    if add_inst.operands.first()?.as_vreg()? != a {
        return None;
    }
    let iv = add_inst.operands.get(1)?.as_vreg()?;
    let step = add_inst.operands.get(2)?.as_imm()?;
    // The compare width is the compared register's class; require the AddRI to
    // produce at that same width (a == dst already checked; iv feeds it).
    if iv.class != a.class {
        return None;
    }
    for &id in &insts[..add_pos] {
        if defines_id(func, id, iv.id) {
            return None; // iv redefined before the AddRI — entry value lost
        }
    }

    // --- Entry constants (gate 3): every predecessor except the backedge
    // source resolves the iv to the same constant at its terminator.
    let back_src = latch.unwrap_or(header);
    let mut entry_const: Option<i64> = None;
    let mut entries = 0usize;
    for &p in &func.block(header).preds {
        if p == back_src {
            continue;
        }
        let &p_term = func.block(p).insts.last()?;
        let c = const_through_copies(func, p_term, iv, MAX_COPY_DEPTH)?;
        match entry_const {
            None => entry_const = Some(c),
            Some(prev) if prev == c => {}
            Some(_) => return None,
        }
        entries += 1;
    }
    if entries == 0 {
        return None;
    }
    let c = entry_const?;

    // --- Decide the branch (gate 6) at the compare's width with wrap-around.
    let taken = branch_taken(a.class.size_bits(), c, step, rhs_const, cc)?;
    if !taken {
        return None;
    }

    trace(&format!(
        "hdr {header:?}: collapse (iv const {c}, step {step}, rhs {rhs_const}, cc {cc}) -> {exit:?}"
    ));
    Some(Plan {
        header,
        exit,
        back_target,
        latch,
        cmp: cmp_id,
        step_add: add_id,
        step: a,
        bound_reg,
    })
}

/// Evaluate `BCond(cc)` after `Cmp((c + s) mod 2^w, k)`. Returns `None` for an
/// unsupported width (fail closed).
fn branch_taken(width_bits: u32, c: i64, s: i64, k: i64, cc: i64) -> Option<bool> {
    let mask: u64 = match width_bits {
        32 => 0xFFFF_FFFF,
        64 => u64::MAX,
        _ => return None,
    };
    let lhs = (c as u64).wrapping_add(s as u64) & mask;
    let rhs = (k as u64) & mask;
    let sext = |v: u64| -> i64 {
        if width_bits == 32 {
            v as u32 as i32 as i64
        } else {
            v as i64
        }
    };
    Some(match cc {
        CC_EQ => lhs == rhs,
        CC_HS => lhs >= rhs,
        CC_GE => sext(lhs) >= sext(rhs),
        _ => return None,
    })
}

/// True iff `inst` writes vreg-id `id` per the audited operand-role table.
fn defines_id(func: &MachFunction, inst_id: InstId, id: u32) -> bool {
    let inst = func.inst(inst_id);
    aarch64_def_operand_positions(inst.opcode, inst.operands.len())
        .into_iter()
        .any(|pos| matches!(inst.operands.get(pos), Some(MachOperand::VReg(v)) if v.id == id))
}

/// [`unique_reaching_const`] extended through register copies: when the unique
/// reaching def of `v` at `use_inst` is a plain copy (`MovR`/`Copy` of two
/// operands, or `AddRI .., #0`), resolve the SOURCE at the copy instruction
/// recursively. Each hop masks to the copy destination's register-class width
/// (a W-form write zeroes the upper half), and the final value is truncated to
/// the queried vreg's width — the same bit-exact model `reaching_const` uses.
fn const_through_copies(func: &MachFunction, use_inst: InstId, v: VReg, depth: u32) -> Option<i64> {
    if depth == 0 {
        return None;
    }
    if let Some(k) = unique_reaching_const(func, use_inst, v) {
        return Some(k);
    }
    let def_id = unique_reaching_def(func, use_inst, v.id)?;
    let def = func.inst(def_id);
    let src = copy_source(def)?;
    let dst = def.operands.first()?.as_vreg()?;
    let mut val = const_through_copies(func, def_id, src, depth - 1)?;
    if dst.class.size_bits() <= 32 {
        val = (val as u64 & 0xFFFF_FFFF) as i64;
    }
    if v.class.size_bits() <= 32 {
        val = (val as u64 & 0xFFFF_FFFF) as i64;
    }
    Some(val)
}

/// `MovR(d, s)` / `Copy(d, s)` / `AddRI(d, s, #0)` copy source.
fn copy_source(inst: &MachInst) -> Option<VReg> {
    match inst.opcode {
        AArch64Opcode::MovR | AArch64Opcode::Copy if inst.operands.len() == 2 => {
            inst.operands[1].as_vreg()
        }
        AArch64Opcode::AddRI
            if inst.operands.len() == 3 && inst.operands[2].as_imm() == Some(0) =>
        {
            inst.operands[1].as_vreg()
        }
        _ => None,
    }
}

/// Commit a proven plan: replace the `BCond + B` pair with `B(exit)`, remove
/// the backedge, unlink the (now unreachable) latch, and clean up the newly
/// dead loop-control instructions (no DCE instance runs after this pipeline
/// slot, and each dead `mov`/`cmp` would otherwise execute on every outer
/// iteration of the surrounding hot loop).
fn commit(func: &mut MachFunction, plan: &Plan) {
    // Replace the terminator pair.
    let nb = func.push_inst(MachInst::new(
        AArch64Opcode::B,
        vec![MachOperand::Block(plan.exit)],
    ));
    {
        let block = func.block_mut(plan.header);
        block.insts.truncate(block.insts.len() - 2);
        block.insts.push(nb);
    }
    // Drop the never-taken backedge (header -> back_target).
    remove_cfg_edge(func, plan.header, plan.back_target);
    // Unlink the latch: with its only predecessor edge gone it is unreachable.
    if let Some(latch) = plan.latch {
        let succs: Vec<BlockId> = func.block(latch).succs.clone();
        for s in succs {
            remove_cfg_edge(func, latch, s);
        }
        func.block_order.retain(|&b| b != latch);
    }

    // --- Dead loop-control cleanup (each step individually fail-closed). ---
    // The Cmp's only consumer was the deleted BCond; delete it when the flags
    // are PROVABLY dead at the rewrite point (every path from the exit reaches
    // a flags WRITER before any flags READER).
    let mut cmp_deleted = false;
    if flags_dead_from(func, plan.exit) {
        unlink_inst(func, plan.header, plan.cmp);
        cmp_deleted = true;
    }
    // The step AddRI fed only the Cmp (and the unlinked latch writeback);
    // delete it when its dst has no remaining use in any linked block.
    if cmp_deleted && !has_linked_use(func, plan.step.id) {
        unlink_inst(func, plan.header, plan.step_add);
    }
    // A CmpRR bound materialized by an otherwise-unused Movz chain: delete the
    // chain when the register has no remaining linked use.
    if cmp_deleted
        && let Some(bound) = plan.bound_reg
        && !has_linked_use(func, bound.id)
    {
        let defs: Vec<(BlockId, InstId)> = linked_defs_of(func, bound.id);
        // Only a pure Movz/Movk materialization chain is deletable — anything
        // else (a copy of a live value, arithmetic) stays.
        if defs.iter().all(|&(_, id)| {
            matches!(
                func.inst(id).opcode,
                AArch64Opcode::Movz | AArch64Opcode::Movk
            )
        }) {
            for (b, id) in defs {
                unlink_inst(func, b, id);
            }
        }
    }
}

/// True iff the NZCV flags are dead on entry to `start`: every path from
/// `start` hits a flags-writing instruction before any flags-reading one.
/// Conservative: an unknown opcode neither reads nor writes per the audited
/// tables, so a path that ends (Ret/no succs) without a reader is dead.
fn flags_dead_from(func: &MachFunction, start: BlockId) -> bool {
    let mut visited: std::collections::HashSet<BlockId> = std::collections::HashSet::new();
    let mut work = vec![start];
    while let Some(b) = work.pop() {
        if !visited.insert(b) {
            continue;
        }
        let mut killed = false;
        for &id in &func.block(b).insts {
            let op = func.inst(id).opcode;
            if crate::effects::reads_flags(op) {
                return false; // a live reader — keep the compare
            }
            if crate::effects::writes_flags(op) {
                killed = true;
                break;
            }
        }
        if !killed {
            for &s in &func.block(b).succs {
                work.push(s);
            }
        }
    }
    true
}

/// True iff any instruction in a LINKED block uses vreg-id `id` (an operand at
/// a non-def position, or a `Movk`'s tied def-use read of its own dst).
fn has_linked_use(func: &MachFunction, id: u32) -> bool {
    for &b in &func.block_order {
        for &inst_id in &func.block(b).insts {
            let inst = func.inst(inst_id);
            let def_positions = aarch64_def_operand_positions(inst.opcode, inst.operands.len());
            // Movk reads the previous value of its (tied) destination.
            if inst.opcode == AArch64Opcode::Movk
                && matches!(inst.operands.first(), Some(MachOperand::VReg(v)) if v.id == id)
            {
                return true;
            }
            for (pos, op) in inst.operands.iter().enumerate() {
                if def_positions.contains(&pos) {
                    continue;
                }
                if matches!(op, MachOperand::VReg(v) if v.id == id) {
                    return true;
                }
            }
        }
    }
    false
}

/// Every linked instruction defining vreg-id `id`, with its block.
fn linked_defs_of(func: &MachFunction, id: u32) -> Vec<(BlockId, InstId)> {
    let mut defs = Vec::new();
    for &b in &func.block_order {
        for &inst_id in &func.block(b).insts {
            if defines_id(func, inst_id, id) {
                defs.push((b, inst_id));
            }
        }
    }
    defs
}

/// Remove `inst` from `block`'s instruction list (the arena entry is orphaned,
/// matching the other passes' deletion pattern).
fn unlink_inst(func: &mut MachFunction, block: BlockId, inst: InstId) {
    func.block_mut(block).insts.retain(|&i| i != inst);
}

fn remove_cfg_edge(func: &mut MachFunction, from: BlockId, to: BlockId) {
    func.block_mut(from).succs.retain(|&s| s != to);
    func.block_mut(to).preds.retain(|&p| p != from);
}

#[cfg(test)]
mod tests;
