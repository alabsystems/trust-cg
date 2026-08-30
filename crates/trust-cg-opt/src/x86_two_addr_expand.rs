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
//! Those redundant copies dominate tight ALU loops (b17/p1 xorshift emits one
//! per `x ^= x<<k` step; the sort/hash hot loops likewise).
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
//! d op d = a op a` — a miscompile).
//!
//! # Profitability predicate (2026-08-28 revision)
//!
//! The original gate expanded only when the lhs `a` was read EXACTLY ONCE in the
//! whole function. That declined every loop-carried xorshift-style kernel: in
//! `MovRR [t, a]; ShlRI [k, t, 13]; XorRR [d, a, k]; ...; MovRR [a, d']` the
//! shift-temp copy is a second read of `a` — but it is strictly BEFORE the XOR,
//! so `a` still dies at the XOR and the expansion is exactly what regalloc needs
//! to merge the chain. The gate is now the UNION of two sound deadness proofs
//! (either suffices, both are profitability-only — correctness stays with the
//! coalescer):
//!
//! 1. GLOBAL single-read: `a` is read exactly once function-wide (necessarily
//!    here) — retained from the original gate so straight-line shapes whose
//!    block ends without a redefinition keep expanding.
//! 2. BLOCK-LOCAL kill: scanning forward from the candidate within its block,
//!    `a` is REDEFINED before any read. Reads decline; conditional/partial/RMW
//!    "defs" (`Cmovcc*`, `Setcc`, `Inc`/`Dec`) count as reads, never kills; if
//!    the block ends without a read or a kill the scan fails CLOSED (`a` may be
//!    live-out and this pass has no global liveness).
//!
//! # Direction — load-bearing, do not commute
//!
//! The inserted copy ties dst to the LHS `a`, NEVER to the rhs `b` — even when
//! `b` is the dying operand. The commuted variant (tie dst to a dying rhs) was
//! REFUTED at +24% on p1: it rotates the loop-carried value into a fresh
//! register every stage and breaks backedge coalescing. Tying the dying lhs
//! merges the chain's non-overlapping ranges (p1: {v4,v14,v18,v22}) into ONE
//! register and turns the backedge copy into a deletable self-move. This pass
//! deliberately has NO commute logic; keep it that way.
//!
//! # Loop-scope call gate (2026-08-29)
//!
//! A suite A/B with the pass unconditionally on measured wins ONLY on
//! call-heavy or mixed programs — m2_call_heavy −18%, m1 −4%, p6 −4%, h4 −3%,
//! h3 −3% — and losses on tight call-free inner loops — p7_sieve +43%, p8
//! +15%. A loop that already pays >= 20-cycle call overhead per iteration
//! absorbs whatever expansion copies the coalescer fails to fold; a call-free
//! tight loop does not — there the unfolded copies cost more than the post-RA
//! fixup MOVs they replace. Straight-line/non-loop code is always cheap: its
//! copies execute once and coalescing normally folds them.
//!
//! A follow-up A/B showed BLOCK granularity is too fine: m2's profitable
//! expansions sit in call-FREE blocks of its call-heavy loop (block-gated ==
//! pass-off at 0.11, while expand-everywhere reproduced the win at
//! 0.09–0.10). Eligibility is therefore keyed to the INNERMOST ENCLOSING
//! NATURAL LOOP:
//!
//!   * a block in no natural-loop body is ELIGIBLE (straight-line code);
//!   * otherwise the block is eligible iff the BODY of its innermost
//!     (deepest; ties broken arbitrarily) enclosing loop contains at least
//!     one call instruction — direct `Call`, register-indirect `CallR`,
//!     memory-indirect `CallM`, i.e. everything carrying
//!     `InstFlags::IS_CALL` (`is_call_inst`).
//!
//! Loop info comes from [`crate::mach_view::CfgAnalysis::compute`] (the same
//! analysis `X86BranchLayout` runs over `X86ISelFunction`), computed ONCE per
//! function and folded into a per-block eligibility set before the block walk
//! — never per candidate. Nesting consequence, deliberate: a call-free inner
//! loop nested inside a call-heavy outer loop stays protected (innermost
//! wins — it is exactly the p7-shaped tight loop the gate exists to shield).
//! Ineligible blocks are left byte-identical to the pass being off.
//!
//! # Gating
//!
//! DEFAULT-ON, scoped by the loop-scope call gate (above).
//! `TCG_NO_X86_TWOADDR_EXPAND` is the kill switch and always wins — over the
//! legacy opt-in and over `TCG_X86_TWOADDR_EXPAND_ALL`. The legacy opt-in
//! `TCG_X86_TWOADDR_EXPAND` is still accepted for compat but is subsumed by
//! the default: it adds nothing when set, never overrides the kill switch, and
//! does NOT lift the call gate. `TCG_X86_TWOADDR_EXPAND_ALL` (opt-in) lifts
//! the loop-scope call gate and restores the expand-everywhere behavior —
//! kept for future suite A/Bs.

use trust_cg_ir::regs::RegClass;
use trust_cg_ir::{VReg, X86Opcode};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::x86_pass_manager::X86MachinePass;

fn enabled() -> bool {
    // DEFAULT-ON. `TCG_NO_X86_TWOADDR_EXPAND` kills the pass and ALWAYS wins;
    // the legacy `TCG_X86_TWOADDR_EXPAND` opt-in is subsumed by the default
    // (harmless if set, never overrides the kill switch).
    crate::env_lock::var_os("TCG_NO_X86_TWOADDR_EXPAND").is_none()
}

fn expand_all() -> bool {
    // Opt-in `TCG_X86_TWOADDR_EXPAND_ALL`: lift the block-scope call gate and
    // expand in EVERY eligible block (the pre-2026-08-29 unconditional
    // behavior), kept for future suite A/Bs. It never overrides the kill
    // switch — `enabled()` is checked first and returns early.
    crate::env_lock::var_os("TCG_X86_TWOADDR_EXPAND_ALL").is_some()
}

/// Is `inst` a call? Covers every x86 call form the IR has — direct `Call`,
/// register-indirect `CallR`, memory-indirect `CallM` — via the `IS_CALL`
/// instruction flag (derived from the opcode at construction), with an
/// explicit opcode match as a safety net for instructions built through
/// `with_flags` with non-default flags.
fn is_call_inst(inst: &X86ISelInst) -> bool {
    inst.flags.is_call()
        || matches!(
            inst.opcode,
            X86Opcode::Call | X86Opcode::CallR | X86Opcode::CallM
        )
}

/// The set of blocks the LOOP-SCOPE CALL GATE admits (see the module doc):
/// every block outside all natural-loop bodies, plus every block whose
/// innermost (deepest) enclosing loop's body contains at least one call.
/// Computed ONCE per function — the block walk only tests membership.
fn eligible_blocks(func: &X86ISelFunction) -> std::collections::HashSet<Block> {
    use crate::mach_view::CfgAnalysis;
    // One pass over the function: which blocks contain a call?
    let call_blocks: std::collections::HashSet<Block> = func
        .block_order
        .iter()
        .copied()
        .filter(|bid| {
            func.blocks
                .get(bid)
                .is_some_and(|b| b.insts.iter().any(is_call_inst))
        })
        .collect();
    let cfg = CfgAnalysis::compute(func);
    // Per-loop: does the BODY (header and latches included) contain a call?
    let loop_has_call: Vec<bool> = cfg
        .loops
        .iter()
        .map(|l| l.body.iter().any(|b| call_blocks.contains(b)))
        .collect();
    func.block_order
        .iter()
        .copied()
        .filter(|bid| {
            // Innermost enclosing loop = the containing loop with the
            // greatest nesting depth (ties: any deepest).
            match cfg
                .loops
                .iter()
                .enumerate()
                .filter(|(_, l)| l.body.contains(bid))
                .max_by_key(|(_, l)| l.depth)
            {
                None => true, // in no natural loop: straight-line, eligible
                Some((idx, _)) => loop_has_call[idx],
            }
        })
        .collect()
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

/// x86 value-producing opcodes whose operand-0 "def" ALSO consumes the
/// register's previous value: conditional writes (`Cmovcc*` leave dst intact on
/// a false condition), partial writes (`Setcc` writes only the low byte), and
/// one-operand read-modify-write ops (`Inc [v]` / `Dec [v]`). For deadness
/// these are READS of the old value, never kills.
fn operand_zero_also_reads(op: X86Opcode) -> bool {
    matches!(
        op,
        X86Opcode::Cmovcc
            | X86Opcode::Cmovcc32
            | X86Opcode::Setcc
            | X86Opcode::Inc
            | X86Opcode::Dec
    )
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
    if func.block_order.is_empty() {
        return false; // no entry block — nothing to do (CfgAnalysis needs one)
    }
    // LOOP-SCOPE CALL GATE (computed ONCE per function, membership-tested per
    // block, never per candidate): a loop already paying call overhead per
    // iteration absorbs unfolded expansion copies (m2_call_heavy −18%
    // measured); a call-free tight loop does not (p7_sieve +43% measured);
    // non-loop straight-line code is always cheap. `None` when
    // TCG_X86_TWOADDR_EXPAND_ALL lifts the gate for A/Bs. See the module doc.
    let eligible = if expand_all() {
        None
    } else {
        Some(eligible_blocks(func))
    };
    // Function-wide read counts feed profitability proof (1); the block-local
    // scan in `lhs_dead_after` is proof (2). See the module doc.
    let read_counts = count_reads(func);
    let mut changed = false;
    for block_id in func.block_order.clone() {
        if let Some(eligible) = &eligible {
            if !eligible.contains(&block_id) {
                // Ineligible: left byte-identical to the pass being off.
                continue;
            }
        }
        let Some(block) = func.blocks.get_mut(&block_id) else {
            continue;
        };
        let insts = std::mem::take(&mut block.insts);
        let mut new_insts: Vec<X86ISelInst> = Vec::with_capacity(insts.len());
        for (idx, inst) in insts.iter().enumerate() {
            // The deadness scan runs over the ORIGINAL tail `insts[idx+1..]`.
            // Sound even though earlier iterations already expanded into
            // `new_insts`: the rewrite preserves every instruction's per-vreg
            // first-touch kind at its position (`a` and `b` stay first-touched
            // as READS, `d` as a WRITE — `d ∉ {a, b}` by the guards), which is
            // all the scan observes.
            if let Some((copy, rewritten)) = try_expand(inst, &insts[idx + 1..], &read_counts) {
                new_insts.push(copy);
                new_insts.push(rewritten);
                changed = true;
            } else {
                new_insts.push(inst.clone());
            }
        }
        block.insts = new_insts;
    }
    changed
}

/// Count how many times each vreg is READ (appears as a non-def-slot operand, or
/// inside a memory operand's base/index) across the whole function. Def-use
/// opcodes (`operand_zero_also_reads`) count their operand-0 as a read too —
/// `Inc [a]` genuinely consumes `a`'s old value, and missing that read would
/// overstate deadness in profitability proof (1).
fn count_reads(func: &X86ISelFunction) -> std::collections::HashMap<VReg, u32> {
    use crate::effects::x86_produces_value;
    let mut counts: std::collections::HashMap<VReg, u32> = std::collections::HashMap::new();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            let pure_def = x86_produces_value(inst.opcode) && !operand_zero_also_reads(inst.opcode);
            for (i, op) in inst.operands.iter().enumerate() {
                if pure_def && i == 0 {
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

/// Block-local forward deadness test for the candidate's lhs `a`: scan the
/// instructions strictly AFTER the candidate within its block.
///
///   * a READ of `a` first → `a` is live past the op → decline;
///   * a full, unconditional WRITE of `a` first (redefinition) → the value the
///     candidate consumed is dead → accept;
///   * block ends without either → DECLINE: `a` may be live-out into a
///     successor and this pass has no global liveness (and must not grow one —
///     four hand-rolled liveness attempts miscompiled b16) → fail closed.
///
/// Within one instruction reads are classified BEFORE the write: an instruction
/// that both reads and redefines `a` (`AddRR [a, a, x]`, `Inc [a]`) consumes
/// the old value. Conditional (`Cmovcc*`) and partial (`Setcc`) writes are
/// routed through the read check via `operand_zero_also_reads` — never kills.
///
/// Purely a PROFITABILITY test: a wrong answer changes whether we expand, never
/// the result (correctness is the regalloc coalescer's interference test).
fn lhs_dead_after(a: VReg, tail: &[X86ISelInst]) -> bool {
    use crate::effects::x86_produces_value;
    for inst in tail {
        let pure_def = x86_produces_value(inst.opcode) && !operand_zero_also_reads(inst.opcode);
        for (i, op) in inst.operands.iter().enumerate() {
            if pure_def && i == 0 {
                if matches!(op, X86ISelOperand::VReg(_)) {
                    continue; // pure def slot: a write, not a read
                }
                // A memory operand in the def slot would still READ its
                // base/index — fall through to the read check (conservative).
            }
            if operand_reads_vreg(op, a) {
                return false; // read before any redefinition -> live
            }
        }
        if pure_def && inst.operands.first() == Some(&X86ISelOperand::VReg(a)) {
            return true; // redefined before any read -> dead
        }
    }
    false // block ended with `a` neither read nor redefined -> fail closed
}

/// Does `op` (in a read position) mention `a`, directly or via a memory
/// operand's base/index?
fn operand_reads_vreg(op: &X86ISelOperand, a: VReg) -> bool {
    match op {
        X86ISelOperand::VReg(v) => *v == a,
        X86ISelOperand::MemAddr { base, .. } => operand_reads_vreg(base, a),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            operand_reads_vreg(base, a) || operand_reads_vreg(index, a)
        }
        _ => false,
    }
}

/// If `inst` is a coalesceable three-address GPR ALU op `[d, a, b]` with the
/// guards satisfied AND expanding it is profitable (`a` dead after the op by
/// either deadness proof), return `(MovRR [d, a], Op [d, d, b])`; else `None`.
/// `tail_after` is the rest of the candidate's block, used by proof (2).
fn try_expand(
    inst: &X86ISelInst,
    tail_after: &[X86ISelInst],
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
    let copy_op = copy_opcode_for_class(d.class)?;
    // PROFITABILITY (two independent sound deadness proofs; either suffices):
    //  (1) GLOBAL single-read: `a` is read exactly once function-wide
    //      (necessarily here, as this op's lhs) -> dead after this op
    //      everywhere. Retained so straight-line shapes whose block ends
    //      without a redefinition keep expanding.
    //  (2) BLOCK-LOCAL kill: forward in this block, `a` is redefined before
    //      any read -> dead after this op even though it has OTHER, strictly
    //      EARLIER reads. This is the loop-carried xorshift shape
    //      (`MovRR t,a; ShlRI k,t,13; XorRR d,a,k; ...; MovRR a,d'`): the old
    //      (1)-only gate declined every such kernel because the shift-temp
    //      copy is a second read — even though it precedes the op. The
    //      backedge copy redefines `a`, so (2) accepts. If the block ends
    //      without a read or a kill, (2) fails CLOSED (`a` may be live-out).
    // Either proof guarantees the coalescer folds the inserted copy (`a`'s
    // range ends at this op, `d`'s begins here -> no interference) with zero
    // added pressure. When neither holds the copy might survive and only raise
    // pressure — that can REGRESS spill-heavy loops (b06/b18) — so we skip.
    if read_counts.get(&a).copied() != Some(1) && !lhs_dead_after(a, tail_after) {
        return None;
    }

    // DIRECTION (load-bearing): tie dst to the LHS `a` — never commute to tie
    // the rhs `b`, even when `b` is the dying operand. The commuted form was
    // REFUTED (+24% on p1): it rotates the loop-carried value into a fresh
    // register every stage and breaks backedge coalescing. See the module doc.
    //
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

    /// Count occurrences of `op` across ALL blocks of `f`.
    fn count(f: &X86ISelFunction, op: X86Opcode) -> usize {
        f.block_order
            .iter()
            .filter_map(|bid| f.blocks.get(bid))
            .flat_map(|b| b.insts.iter())
            .filter(|i| i.opcode == op)
            .count()
    }

    /// Multi-block function: `(block, insts, successors)` triples; the FIRST
    /// triple is the CFG entry (the ISel layout convention `block_order[0]`).
    /// Successor EDGES (not terminators) are what `CfgAnalysis` walks, so the
    /// fixtures carry edges and only the exit block bothers with a `Ret`.
    fn func_with_blocks(blocks: Vec<(u32, Vec<X86ISelInst>, Vec<u32>)>) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut f = X86ISelFunction::new("expand_test".to_string(), sig);
        for (bid, insts, succs) in blocks {
            f.ensure_block(Block(bid));
            for s in succs {
                f.add_successor(Block(bid), Block(s));
            }
            f.blocks.get_mut(&Block(bid)).unwrap().insts = insts;
        }
        f
    }

    /// A direct `Call` (Symbol operand — reads and writes no vregs, so it is
    /// invisible to both deadness proofs) used to make a fixture LOOP
    /// call-dense: the loop-scope call gate only expands inside loops whose
    /// body contains at least one call (m2 −18% vs p7 +43%, see module doc).
    fn call_inst() -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::Call,
            vec![X86ISelOperand::Symbol("callee".into())],
        )
    }

    /// Simple accept shape: `a` read exactly once (deadness proof (1)). No
    /// call anywhere — in a straight-line (non-loop) block the loop-scope
    /// call gate admits it regardless.
    fn simple_read_once() -> Vec<X86ISelInst> {
        let (d, a, b) = (g64(10), g64(11), g64(12));
        vec![
            X86ISelInst::new(X86Opcode::XorRR, vec![vr(d), vr(a), vr(b)]),
            // downstream use of d and b so neither is dead-stripped; `a` is
            // read ONLY by the XorRR (exactly once).
            X86ISelInst::new(X86Opcode::AddRR, vec![vr(d), vr(d), vr(b)]),
        ]
    }

    /// A two-block natural loop `{B1 (header), B2 (latch)}` with the accept
    /// shape in B1: entry B0 -> B1 -> B2 -> {B1 back edge, B3 exit}. When
    /// `latch_insts` is empty the loop is call-FREE (the p7_sieve shape); the
    /// m2 shape puts a call in the latch.
    fn loop_with_candidate(latch_insts: Vec<X86ISelInst>) -> X86ISelFunction {
        func_with_blocks(vec![
            (0, vec![], vec![1]),
            (1, simple_read_once(), vec![2]),
            (2, latch_insts, vec![1, 3]),
            (3, vec![X86ISelInst::new(X86Opcode::Ret, vec![])], vec![]),
        ])
    }

    // Env-var tests use the crate's thread-local override scopes exclusively
    // (`env_lock::override_scope` + `ScopedEnvVar`), so parallel tests never
    // race: each test shadows ALL of the pass's variables in its own scope
    // first (`var_os` falls back to the real process env for any name left
    // unshadowed).

    /// Shadow (unset) every env var this pass reads, making the test hermetic
    /// against the invoking shell. Tests that need a var SET layer a
    /// `ScopedEnvVar::set` on top inside their own scope.
    fn unset_pass_env(
        scope: &crate::env_lock::EnvOverrideScope,
    ) -> [crate::env_lock::ScopedEnvVar<'_>; 3] {
        [
            crate::env_lock::ScopedEnvVar::unset(scope, "TCG_NO_X86_TWOADDR_EXPAND"),
            crate::env_lock::ScopedEnvVar::unset(scope, "TCG_X86_TWOADDR_EXPAND"),
            crate::env_lock::ScopedEnvVar::unset(scope, "TCG_X86_TWOADDR_EXPAND_ALL"),
        ]
    }

    #[test]
    fn x86_two_addr_default_on_kill_switch_and_legacy_env() {
        let scope = crate::env_lock::override_scope();
        let _env = unset_pass_env(&scope);

        // (1) DEFAULT-ON: no env var at all -> the pass runs and expands
        // (the fixture block is straight-line non-loop code, which the
        // loop-scope call gate always admits).
        let mut on = func_with(simple_read_once());
        assert!(
            X86TwoAddressExpand.run_on_function(&mut on),
            "pass must be ON by default (no env var set)"
        );
        assert_eq!(count(&on, X86Opcode::MovRR), 1, "one copy inserted");

        // (2) Kill switch wins — even when the legacy force-on is ALSO set.
        {
            let _no = crate::env_lock::ScopedEnvVar::set(&scope, "TCG_NO_X86_TWOADDR_EXPAND", "1");
            let _legacy = crate::env_lock::ScopedEnvVar::set(&scope, "TCG_X86_TWOADDR_EXPAND", "1");
            let mut off = func_with(simple_read_once());
            assert!(
                !X86TwoAddressExpand.run_on_function(&mut off),
                "TCG_NO_X86_TWOADDR_EXPAND must disable the pass (and beat the legacy opt-in)"
            );
            assert_eq!(count(&off, X86Opcode::MovRR), 0);
        }

        // (3) Legacy opt-in alone still works (subsumed by the default).
        {
            let _legacy = crate::env_lock::ScopedEnvVar::set(&scope, "TCG_X86_TWOADDR_EXPAND", "1");
            let mut legacy_on = func_with(simple_read_once());
            assert!(
                X86TwoAddressExpand.run_on_function(&mut legacy_on),
                "legacy TCG_X86_TWOADDR_EXPAND still enables the pass"
            );
        }
    }

    /// The p1_xorshift hot-loop shape. `v4` has TWO reads (the shift-temp copy
    /// and the XOR), so the old read-count==1 gate declined it — but the extra
    /// read is strictly BEFORE the XOR and the backedge copy `MovRR [v4, v14]`
    /// REDEFINES `v4` afterwards, so the block-local scan (proof (2)) accepts.
    #[test]
    fn x86_two_addr_p1_xorshift_shape_expands_via_block_local_kill() {
        let scope = crate::env_lock::override_scope();
        let _env = unset_pass_env(&scope);

        let (v4, v11, v13, v14) = (g64(4), g64(11), g64(13), g64(14));
        // Single straight-line block (no CFG back edge), so the loop-scope
        // call gate admits it without a call — this test pins the block-local
        // kill proof, not the gate.
        let mut f = func_with(vec![
            // shift-temp copy: the 2nd read of v4, BEFORE the candidate
            X86ISelInst::new(X86Opcode::MovRR, vec![vr(v11), vr(v4)]),
            X86ISelInst::new(
                X86Opcode::ShlRI,
                vec![vr(v13), vr(v11), X86ISelOperand::Imm(13)],
            ),
            // candidate: v4 dead after (its remaining touch below is a WRITE)
            X86ISelInst::new(X86Opcode::XorRR, vec![vr(v14), vr(v4), vr(v13)]),
            // backedge copy REDEFINES v4 -> the forward scan accepts
            X86ISelInst::new(X86Opcode::MovRR, vec![vr(v4), vr(v14)]),
        ]);
        assert!(
            X86TwoAddressExpand.run_on_function(&mut f),
            "xorshift step must expand under the block-local kill proof"
        );
        let insts = &f.blocks.get(&Block(0)).unwrap().insts;
        let xor_idx = insts
            .iter()
            .position(|i| i.opcode == X86Opcode::XorRR)
            .expect("XorRR still present");
        assert_eq!(
            insts[xor_idx].operands,
            vec![vr(v14), vr(v14), vr(v13)],
            "XorRR rewritten to dst==lhs form [d, d, b]"
        );
        // DIRECTION pin: the copy ties dst to the LHS `v4` (`MovRR v14, v4`),
        // never a commuted tie to the rhs `v13` — the commuted variant was
        // REFUTED (+24% p1, breaks backedge coalescing).
        assert_eq!(
            insts[xor_idx - 1].opcode,
            X86Opcode::MovRR,
            "copy inserted immediately before the rewritten op"
        );
        assert_eq!(
            insts[xor_idx - 1].operands,
            vec![vr(v14), vr(v4)],
            "copy is MovRR [d, a] (dst <- LHS)"
        );
        // 2 original MovRRs + 1 inserted copy.
        assert_eq!(count(&f, X86Opcode::MovRR), 3);
    }

    /// Decline: lhs is READ after the candidate; the later redefinition comes
    /// too late (read-before-redef).
    #[test]
    fn x86_two_addr_decline_lhs_read_after_candidate() {
        let scope = crate::env_lock::override_scope();
        let _env = unset_pass_env(&scope);

        let (d, a, b) = (g64(40), g64(41), g64(42));
        // Straight-line non-loop block: always eligible under the loop-scope
        // call gate, so the decline is attributable to the read-after.
        let mut f = func_with(vec![
            X86ISelInst::new(X86Opcode::XorRR, vec![vr(d), vr(a), vr(b)]),
            // read of `a` AFTER the candidate -> `a` is live past it. (CmpRR
            // produces no value and is not itself an expansion candidate.)
            X86ISelInst::new(X86Opcode::CmpRR, vec![vr(a), vr(b)]),
            // redefinition AFTER the read: must NOT rescue the candidate.
            X86ISelInst::new(X86Opcode::MovRR, vec![vr(a), vr(b)]),
        ]);
        assert!(
            !X86TwoAddressExpand.run_on_function(&mut f),
            "read of lhs after the candidate (before its redef) must decline"
        );
        assert_eq!(count(&f, X86Opcode::MovRR), 1, "no copy inserted");
    }

    /// Decline: block ends with lhs neither read nor redefined -> the scan
    /// fails CLOSED (`a` may be live-out; no global liveness available). The
    /// extra read of `a` sits BEFORE the candidate so the global single-read
    /// proof (1) declines too — this pins the scan's block-end behavior.
    #[test]
    fn x86_two_addr_decline_block_end_without_redef_fails_closed() {
        let scope = crate::env_lock::override_scope();
        let _env = unset_pass_env(&scope);

        let (t, d, a, b) = (g64(50), g64(51), g64(52), g64(53));
        // Straight-line non-loop block: always eligible under the loop-scope
        // call gate, so the decline is attributable to the fail-closed scan.
        let mut f = func_with(vec![
            // earlier read of `a` (kills proof (1): read count == 2)
            X86ISelInst::new(X86Opcode::MovRR, vec![vr(t), vr(a)]),
            X86ISelInst::new(X86Opcode::XorRR, vec![vr(d), vr(a), vr(b)]),
            // no further touch of `a`; block ends -> fail closed
            X86ISelInst::new(X86Opcode::AddRR, vec![vr(d), vr(d), vr(b)]),
        ]);
        assert!(
            !X86TwoAddressExpand.run_on_function(&mut f),
            "block end without a redefinition of lhs must fail closed"
        );
        assert_eq!(count(&f, X86Opcode::MovRR), 1, "no copy inserted");
    }

    /// The retained proof (1): lhs read exactly once function-wide expands even
    /// though its block ends without a redefinition. This pins the UNION — the
    /// block-local scan alone would fail closed here, but the global
    /// single-read proof is sound (the only read IS the candidate) and was the
    /// original gate's acceptance class; going default-on must not lose it.
    #[test]
    fn x86_two_addr_global_single_read_still_accepted() {
        let scope = crate::env_lock::override_scope();
        let _env = unset_pass_env(&scope);

        // straight-line fixture: the loop-scope gate admits, proof (1) accepts
        let mut f = func_with(simple_read_once());
        assert!(
            X86TwoAddressExpand.run_on_function(&mut f),
            "single-read lhs must still expand (proof (1) retained)"
        );
        assert_eq!(count(&f, X86Opcode::MovRR), 1, "one copy inserted");
    }

    /// Def-use "redefinitions" are NOT kills: `Inc [a]` reads `a`'s old value,
    /// so the scan must classify it as a read and decline (likewise `Dec`,
    /// `Cmovcc*` conditional writes, and `Setcc` partial writes — pinned on the
    /// predicate directly below).
    #[test]
    fn x86_two_addr_def_use_redefinition_is_not_a_kill() {
        let scope = crate::env_lock::override_scope();
        let _env = unset_pass_env(&scope);

        let (d, a, b) = (g64(60), g64(61), g64(62));
        // Straight-line non-loop block: always eligible under the loop-scope
        // call gate, so the decline is attributable to the Inc-is-a-read rule.
        let mut f = func_with(vec![
            X86ISelInst::new(X86Opcode::XorRR, vec![vr(d), vr(a), vr(b)]),
            // one-operand RMW: reads a's old value -> `a` is live -> decline
            X86ISelInst::new(X86Opcode::Inc, vec![vr(a)]),
            // real redefinition, but only after the Inc's read
            X86ISelInst::new(X86Opcode::MovRR, vec![vr(a), vr(d)]),
        ]);
        assert!(
            !X86TwoAddressExpand.run_on_function(&mut f),
            "Inc of lhs after the candidate is a READ, not a kill"
        );
        assert_eq!(count(&f, X86Opcode::MovRR), 1, "no copy inserted");

        // The full def-use set the scan must never treat as a kill.
        for op in [
            X86Opcode::Cmovcc,
            X86Opcode::Cmovcc32,
            X86Opcode::Setcc,
            X86Opcode::Inc,
            X86Opcode::Dec,
        ] {
            assert!(operand_zero_also_reads(op), "{op:?} operand-0 is def-USE");
        }
        assert!(!operand_zero_also_reads(X86Opcode::MovRR));
        assert!(!operand_zero_also_reads(X86Opcode::AddRR));
    }

    /// GUARD 2: `d == b` would compute `a op a` after the rewrite -> MUST skip
    /// regardless of profitability.
    #[test]
    fn x86_two_addr_decline_when_dst_aliases_rhs() {
        let scope = crate::env_lock::override_scope();
        let _env = unset_pass_env(&scope);

        let (d2, a2) = (g64(20), g64(21));
        // Straight-line non-loop block: always eligible under the loop-scope
        // call gate, so the decline is attributable to the aliasing guard.
        let mut alias = func_with(vec![
            X86ISelInst::new(X86Opcode::XorRR, vec![vr(d2), vr(a2), vr(d2)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vr(d2), vr(d2), vr(a2)]),
        ]);
        assert!(
            !X86TwoAddressExpand.run_on_function(&mut alias),
            "must NOT expand when d == b"
        );
    }

    /// P7-PROTECTION PIN: the accept shape (proof (1) satisfied) inside a
    /// natural loop whose body has NO call DECLINES under the loop-scope call
    /// gate. Measured rationale: with the pass unconditional, tight call-free
    /// inner loops regressed (p7_sieve +43%, p8 +15%) because the coalescer
    /// does not fold the expansion copies there — call-free loops must stay
    /// byte-identical to the pass being off.
    #[test]
    fn x86_two_addr_declines_call_free_loop() {
        let scope = crate::env_lock::override_scope();
        let _env = unset_pass_env(&scope);

        let mut f = loop_with_candidate(vec![]); // empty latch: call-free loop
        assert!(
            !X86TwoAddressExpand.run_on_function(&mut f),
            "candidate in a call-free loop must decline under the loop-scope call gate"
        );
        assert_eq!(count(&f, X86Opcode::MovRR), 0, "no copy inserted");
    }

    /// The m2_call_heavy shape: the candidate block itself is call-FREE, but
    /// the body of its innermost enclosing loop has a call in ANOTHER block
    /// (the latch) -> eligible, expands. This is exactly what the earlier
    /// BLOCK-scope gate missed (m2 gated == off at 0.11; expand-everywhere
    /// reproduced the −18% win at 0.09-0.10), forcing loop granularity.
    #[test]
    fn x86_two_addr_expands_call_free_block_in_call_containing_loop() {
        let scope = crate::env_lock::override_scope();
        let _env = unset_pass_env(&scope);

        let mut f = loop_with_candidate(vec![call_inst()]); // call in the latch
        assert!(
            X86TwoAddressExpand.run_on_function(&mut f),
            "call-free block inside a call-containing loop must expand"
        );
        let (d, a, b) = (g64(10), g64(11), g64(12));
        let insts = &f.blocks.get(&Block(1)).unwrap().insts;
        assert_eq!(
            insts[0].opcode,
            X86Opcode::MovRR,
            "copy inserted in the candidate's own (call-free) block"
        );
        assert_eq!(insts[0].operands, vec![vr(d), vr(a)], "MovRR [d, a]");
        assert_eq!(
            insts[1].operands,
            vec![vr(d), vr(d), vr(b)],
            "XorRR rewritten to [d, d, b]"
        );
        assert_eq!(count(&f, X86Opcode::MovRR), 1, "exactly one copy inserted");
    }

    /// INNERMOST-WINS PIN: a call-free inner loop nested inside a
    /// call-containing outer loop stays protected — eligibility is decided by
    /// the DEEPEST enclosing loop, and the inner loop is precisely the
    /// p7-shaped tight loop the gate exists to shield.
    #[test]
    fn x86_two_addr_call_free_inner_loop_protected_despite_outer_call() {
        let scope = crate::env_lock::override_scope();
        let _env = unset_pass_env(&scope);

        // Outer loop {B1..B4} (back edge B4->B1) contains a call in its
        // header B1; inner loop {B2, B3} (back edge B3->B2) is call-free and
        // holds the candidate in B2.
        let mut f = func_with_blocks(vec![
            (0, vec![], vec![1]),
            (1, vec![call_inst()], vec![2]),
            (2, simple_read_once(), vec![3]),
            (3, vec![], vec![2, 4]),
            (4, vec![], vec![1, 5]),
            (5, vec![X86ISelInst::new(X86Opcode::Ret, vec![])], vec![]),
        ]);
        assert!(
            !X86TwoAddressExpand.run_on_function(&mut f),
            "call-free INNER loop must decline even inside a call-heavy outer loop"
        );
        assert_eq!(count(&f, X86Opcode::MovRR), 0, "no copy inserted");
    }

    /// NON-LOOP PIN: a straight-line block outside every natural loop is
    /// eligible with no call anywhere in the function — its copies execute
    /// once and coalescing normally folds them.
    #[test]
    fn x86_two_addr_expands_non_loop_straight_line_without_call() {
        let scope = crate::env_lock::override_scope();
        let _env = unset_pass_env(&scope);

        let mut f = func_with(simple_read_once()); // no call, no loop
        assert!(
            X86TwoAddressExpand.run_on_function(&mut f),
            "non-loop straight-line code must expand without any call"
        );
        assert_eq!(count(&f, X86Opcode::MovRR), 1, "one copy inserted");
    }

    /// `TCG_X86_TWOADDR_EXPAND_ALL` (opt-in) lifts the loop-scope call gate:
    /// the very shape `x86_two_addr_declines_call_free_loop` pins as declined
    /// expands again — the everywhere behavior, kept for suite A/Bs. The kill
    /// switch still beats it.
    #[test]
    fn x86_two_addr_expand_all_env_lifts_call_gate() {
        let scope = crate::env_lock::override_scope();
        let _env = unset_pass_env(&scope);
        let _all = crate::env_lock::ScopedEnvVar::set(&scope, "TCG_X86_TWOADDR_EXPAND_ALL", "1");

        let mut f = loop_with_candidate(vec![]); // the call-free loop shape
        assert!(
            X86TwoAddressExpand.run_on_function(&mut f),
            "TCG_X86_TWOADDR_EXPAND_ALL=1 must expand in a call-free loop"
        );
        assert_eq!(count(&f, X86Opcode::MovRR), 1, "one copy inserted");

        // Kill switch wins over EXPAND_ALL (and everything else).
        {
            let _no = crate::env_lock::ScopedEnvVar::set(&scope, "TCG_NO_X86_TWOADDR_EXPAND", "1");
            let mut off = loop_with_candidate(vec![]);
            assert!(
                !X86TwoAddressExpand.run_on_function(&mut off),
                "TCG_NO_X86_TWOADDR_EXPAND must beat TCG_X86_TWOADDR_EXPAND_ALL"
            );
            assert_eq!(count(&off, X86Opcode::MovRR), 0);
        }
    }

    /// The opcode set the loop-scope gate treats as calls: every x86 call
    /// form the IR has (`Call`, `CallR`, `CallM` — all carrying
    /// `InstFlags::IS_CALL`), and none of the nearby non-call control flow.
    #[test]
    fn x86_two_addr_call_gate_opcode_set() {
        assert!(is_call_inst(&call_inst()), "direct Call");
        assert!(
            is_call_inst(&X86ISelInst::new(X86Opcode::CallR, vec![vr(g64(1))])),
            "register-indirect CallR"
        );
        assert!(
            is_call_inst(&X86ISelInst::new(
                X86Opcode::CallM,
                vec![X86ISelOperand::MemAddr {
                    base: Box::new(vr(g64(1))),
                    disp: 0,
                }],
            )),
            "memory-indirect CallM"
        );
        for op in [X86Opcode::Ret, X86Opcode::Jmp] {
            assert!(!is_call_inst(&X86ISelInst::new(op, vec![])), "{op:?}");
        }
        assert!(!is_call_inst(&X86ISelInst::new(
            X86Opcode::MovRR,
            vec![vr(g64(1)), vr(g64(2))],
        )));
    }
}
