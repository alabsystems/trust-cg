// trust-cg-opt - AArch64 loop latch/layout combine
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Late scalar AArch64 loop latch/layout combine.
//!
//! This pass recognizes the conservative counted-loop shape emitted for simple
//! trust_ir block-parameter loops:
//!
//! ```text
//! preheader:
//!   ...
//!   b header
//! header:
//!   cmp iv, limit
//!   cset p, cond
//!   cbnz p, body
//!   b exit
//! body/latch:
//!   ...
//!   iv = iv.next
//!   b header
//! exit:
//!   ...
//! ```
//!
//! When the exit already follows the latch in layout order, it rewrites the
//! steady-state path to test in the latch and fall through to the exit:
//!
//! ```text
//! header:
//!   cmp iv, limit
//!   b.cond body
//!   b exit
//! body:
//!   ...
//!   iv = iv.next
//!   b split_latch
//! split_latch:
//!   cmp iv, limit
//!   b.cond body
//! exit:
//!   ...
//! ```
//!
//! The original header guard remains in place, preserving zero-trip behavior.
//!
//! A second tier handles already-ROTATED loops (the importer's do-while shape,
//! e.g. Bubblesort's inner compare-swap loop): when the loop's latch chain is
//! PURE (only `CmpRR`/`CmpRI` + `BCond` + `MovR`/`Copy` + `B` — no memory ops,
//! no calls) and an in-loop predecessor reaches it only through an
//! unconditional `B`, the chain's instructions are CLONED into that
//! predecessor, replacing its terminating branch:
//!
//! ```text
//! swap:                          swap:
//!   str ...                        str ...
//!   b latch          ==>           cmp iv.next, limit
//! latch:                           b.cond exit
//!   cmp iv.next, limit             mov iv, iv.next
//!   b.cond exit                    b header
//!   mov iv, iv.next
//!   b header
//! ```
//!
//! This removes one taken branch per swap-arm iteration. It is
//! semantics-preserving by construction: the predecessor jumped straight into
//! the chain, so appending the exact instruction sequence the chain would have
//! executed (branch targets kept identical, flags produced by the chain's own
//! compares) changes no value, no memory state, and no exit target on any
//! path. The `MovR` writebacks intentionally re-define the SAME carrier dsts —
//! they are the same block-param writebacks the latch performed.

use std::collections::HashSet;

use trust_cg_ir::{
    AArch64Opcode, BlockId, CondCode, InstId, MachFunction, MachInst, MachOperand, PassId,
    ProvenanceMap, VReg,
};

use crate::dom::DomTree;
use crate::effects::{aarch64_for_each_use_position, for_each_inst_def};
use crate::loops::{LoopAnalysis, NaturalLoop};
use crate::pass_manager::{AnalysisCache, MachinePass};

/// Conservative scalar counted-loop latch/layout combine for AArch64.
pub struct LoopLatchLayoutCombine;

impl MachinePass for LoopLatchLayoutCombine {
    fn name(&self) -> &str {
        "loop-latch-layout"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        // In-pipeline instance: LEGACY tiers only. The extended tier-3b
        // rotation runs as a POST-CONVERGENCE single shot (see
        // `run_extended_loop_rotation`) so no loop-shape recognizer in the
        // iterative pipeline ever observes an extension-rotated loop.
        run_loop_latch_layout_combine(func, None, false)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_loop_latch_layout_combine(func, Some(provenance), false)
    }

    fn run_with_analyses(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut AnalysisCache,
    ) -> bool {
        self.run(func)
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        self.run_with_provenance(func, provenance)
    }
}

#[derive(Debug, Clone)]
struct HeaderCondition {
    compare_id: InstId,
    compare_inst: MachInst,
    cond: CondCode,
    body: BlockId,
    exit: BlockId,
    branch_id: InstId,
    removed_ids: Vec<InstId>,
}

fn loop_latch_layout_pass_id() -> PassId {
    PassId::new("loop-latch-layout")
}

/// Post-convergence entry for the EXTENDED tier-3b rotation (inverted
/// orientations, carrier-copy prefixes, cmp headers). Called by the pipeline
/// AFTER `run_to_fixpoint` so the vectorizers' NATIVE loop classifiers never
/// see an extension-rotated loop (2026-08-13 v2_memfill wrong-abort class);
/// their own canonical-backedge hardening (neon-fill) remains as defense in
/// depth for importer-emitted do-whiles. Honors both kill switches.
pub fn run_extended_loop_rotation(
    func: &mut MachFunction,
    provenance: Option<&mut ProvenanceMap>,
) -> bool {
    if !loop_rotate_enabled() || !loop_rotate_extended_enabled() {
        return false;
    }
    run_loop_latch_layout_combine(func, provenance, true)
}

fn run_loop_latch_layout_combine(
    func: &mut MachFunction,
    mut provenance: Option<&mut ProvenanceMap>,
    extended: bool,
) -> bool {
    let mut changed = false;

    // Recompute analyses after every successful rewrite. The loop shape changes
    // by adding a dedicated latch block, so stale loop info is deliberately
    // avoided even for O2's single pipeline iteration.
    for _ in 0..func.blocks.len() {
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        // The EXTENDED tier rotates INNERMOST loops only: rotating a loop
        // that contains other loops buys one taken branch per OUTER
        // iteration — amortized over the whole inner execution, nothing —
        // while reshaping the layout of every contained loop (measured
        // +5% on p7_sieve when its 60k-iteration outer loop rotated).
        // Innermost bodies are where the per-iteration savings live
        // (b1_mispredict -11%); the legacy tiers keep their own admission.
        let candidates: Vec<(NaturalLoop, bool)> = loops
            .all_loops()
            .map(|lp| {
                let innermost = loops
                    .all_loops()
                    .all(|o| o.header == lp.header || !lp.body.contains(&o.header));
                (lp.clone(), innermost)
            })
            .collect();

        let mut rewrote_one = false;
        for (lp, innermost) in candidates {
            if rewrite_loop(func, &lp, provenance.as_deref_mut(), extended && innermost) {
                changed = true;
                rewrote_one = true;
                break;
            }
        }

        if !rewrote_one {
            break;
        }
    }

    changed
}

fn rewrite_loop(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    mut provenance: Option<&mut ProvenanceMap>,
    extended: bool,
) -> bool {
    if rewrite_counted_two_block_loop(func, lp, provenance.as_deref_mut()) {
        return true;
    }
    if loop_rotate_enabled() {
        // Tier 3a: rotate a top-tested two-block counted loop whose header exits
        // on the CONDITION (`b.cond exit; b body`) — the inverse orientation of
        // tier 1's `b.cond body; b exit`. The header is already a valid zero-trip
        // guard, so it is left untouched; the loop test is duplicated into a
        // split latch (fib2's tail-recursion-elim accumulator loop).
        if rewrite_rotated_two_block_case_b(func, lp, provenance.as_deref_mut()) {
            return true;
        }
        // Tier 3b: rotate a loop whose header is a PURE TEST-ONLY guard by
        // duplicating that test into each in-loop backedge predecessor, so the
        // steady state skips the header round-trip (ackermann's countdown loop
        // with two backedges, header `cbz M, exit`).
        if duplicate_header_test_into_latches(func, lp, provenance.as_deref_mut(), extended) {
            return true;
        }
    }
    latch_taildup_enabled() && tail_duplicate_pure_latch_chain(func, lp, provenance)
}

/// Compile-time kill switch: set `TCG_NO_LOOP_ROTATE` (any value) to disable the
/// two loop-ROTATION tiers (case-B two-block rotation and test-only-header
/// duplication). The whole pass is additionally governed by
/// `TRUST_CG_DISABLE_PASSES=looplatch`.
fn loop_rotate_enabled() -> bool {
    std::env::var_os("TCG_NO_LOOP_ROTATE").is_none()
}

/// Gate for the EXTENDED tier-3b rotation (inverted-orientation headers,
/// carrier-copy prefixes, CmpRR/CmpRI headers). Default ON since 2026-08-14:
/// the miscompile that originally forced this behind an opt-in flag —
/// neon-fill's NATIVE classifier routing its vector residual into a rotated
/// loop's abort-armed header check (v2_memfill/v3_popcount wrong-abort) —
/// is fixed at the source: neon-fill's NATIVE arm now requires the canonical
/// unconditional latch backedge and classifies rotated loops through its
/// ROTATED arm's `rotated_exit` guard instead. `TCG_NO_LOOP_ROTATE_EXT`
/// remains as a bisection kill switch for the extension alone
/// (`TCG_NO_LOOP_ROTATE` still disables all rotation tiers).
/// Measured upside: b1_mispredict -11% (1.140x -> 1.016x vs LLVM).
/// Consulted only by [`run_extended_loop_rotation`]; the in-pipeline pass
/// instance always runs legacy-only.
fn loop_rotate_extended_enabled() -> bool {
    std::env::var_os("TCG_NO_LOOP_ROTATE_EXT").is_none()
}

fn rewrite_counted_two_block_loop(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    provenance: Option<&mut ProvenanceMap>,
) -> bool {
    if !is_simple_two_block_loop(func, lp) {
        return false;
    }
    if block_contains_phi(func, lp.header) || block_contains_phi(func, lp.latch) {
        return false;
    }

    let Some(header_cond) = parse_header_condition(func, lp) else {
        return false;
    };
    if block_contains_phi(func, header_cond.exit) {
        return false;
    }
    if next_block(func, lp.latch) != Some(header_cond.exit) {
        return false;
    }
    if func.block(header_cond.exit).preds != [lp.header] {
        return false;
    }
    let carrier_copies = trailing_carrier_copies(func, lp.latch);
    if !is_counted_like_latch_update(&carrier_copies, func, &header_cond.compare_inst) {
        return false;
    }
    if !carrier_copies
        .iter()
        .all(|&id| can_harden_carrier_copy(func.inst(id)))
    {
        return false;
    }

    apply_rewrite(func, lp, header_cond, carrier_copies, provenance);
    true
}

fn is_simple_two_block_loop(func: &MachFunction, lp: &NaturalLoop) -> bool {
    let Some(preheader) = lp.preheader else {
        return false;
    };
    if lp.header == lp.latch || lp.body.len() != 2 {
        return false;
    }
    if !lp.body.contains(&lp.header) || !lp.body.contains(&lp.latch) {
        return false;
    }

    let header = func.block(lp.header);
    let loop_preds: Vec<BlockId> = header
        .preds
        .iter()
        .copied()
        .filter(|pred| lp.body.contains(pred))
        .collect();
    let non_loop_preds: Vec<BlockId> = header
        .preds
        .iter()
        .copied()
        .filter(|pred| !lp.body.contains(pred))
        .collect();
    if loop_preds != [lp.latch] || non_loop_preds != [preheader] {
        return false;
    }

    if !func.block(preheader).succs.contains(&lp.header) {
        return false;
    }

    let latch = func.block(lp.latch);
    if latch.succs != [lp.header] {
        return false;
    }
    let Some(&last_id) = latch.insts.last() else {
        return false;
    };
    let last = func.inst(last_id);
    last.opcode == AArch64Opcode::B && branch_target(last) == Some(lp.header)
}

fn block_contains_phi(func: &MachFunction, block: BlockId) -> bool {
    func.block(block)
        .insts
        .iter()
        .any(|&id| func.inst(id).opcode == AArch64Opcode::Phi)
}

fn parse_header_condition(func: &MachFunction, lp: &NaturalLoop) -> Option<HeaderCondition> {
    let header = func.block(lp.header);
    if header.succs.len() != 2 || !header.succs.contains(&lp.latch) {
        return None;
    }

    let exit = header
        .succs
        .iter()
        .copied()
        .find(|succ| !lp.body.contains(succ))?;

    let insts = &header.insts;
    if insts.len() < 3 {
        return None;
    }

    let exit_branch_id = *insts.last()?;
    let exit_branch = func.inst(exit_branch_id);
    if exit_branch.opcode != AArch64Opcode::B || branch_target(exit_branch) != Some(exit) {
        return None;
    }

    let cond_pos = insts.len().checked_sub(2)?;
    let cond_branch_id = insts[cond_pos];
    let cond_branch = func.inst(cond_branch_id);
    let cond_target = branch_target(cond_branch)?;
    if cond_target != lp.latch && cond_target != exit {
        return None;
    }
    let branch_to_body = cond_target == lp.latch;

    let mut parsed = match cond_branch.opcode {
        AArch64Opcode::BCond => parse_bcond_header(func, insts, cond_pos, branch_to_body)?,
        AArch64Opcode::Cbz | AArch64Opcode::Cbnz => {
            parse_cbnz_header(func, insts, cond_pos, branch_to_body)?
        }
        _ => return None,
    };

    parsed.body = lp.latch;
    parsed.exit = exit;
    parsed.branch_id = cond_branch_id;

    if !deleted_value_uses_are_limited_to_condition_sequence(func, &parsed) {
        return None;
    }
    if !header_has_only_condition_insts(insts, &parsed, exit_branch_id) {
        return None;
    }
    if !matches!(
        parsed.compare_inst.opcode,
        AArch64Opcode::CmpRR | AArch64Opcode::CmpRI
    ) {
        return None;
    }

    Some(parsed)
}

fn parse_bcond_header(
    func: &MachFunction,
    insts: &[InstId],
    cond_pos: usize,
    branch_to_body: bool,
) -> Option<HeaderCondition> {
    let bcond = func.inst(insts[cond_pos]);
    let raw_cond = bcond.operands.first()?.as_imm()? as u8;
    let branch_cond = decode_cond(raw_cond)?;

    // Materialized bool form before cmp-branch-fusion:
    //   cmp iv, limit
    //   cset p, cond
    //   cmp p, #0
    //   b.ne body
    if let Some(parsed) =
        parse_materialized_bool_before_bcond(func, insts, cond_pos, branch_cond, branch_to_body)
    {
        return Some(parsed);
    }

    let compare_pos = cond_pos.checked_sub(1)?;
    let compare_id = insts[compare_pos];
    let compare = func.inst(compare_id);
    if !matches!(compare.opcode, AArch64Opcode::CmpRR | AArch64Opcode::CmpRI) {
        return None;
    }

    Some(HeaderCondition {
        compare_id,
        compare_inst: compare.clone(),
        cond: if branch_to_body {
            branch_cond
        } else {
            branch_cond.invert()
        },
        body: BlockId(0),
        exit: BlockId(0),
        branch_id: insts[cond_pos],
        removed_ids: Vec::new(),
    })
}

fn parse_materialized_bool_before_bcond(
    func: &MachFunction,
    insts: &[InstId],
    cond_pos: usize,
    branch_cond: CondCode,
    branch_to_body: bool,
) -> Option<HeaderCondition> {
    if !matches!(branch_cond, CondCode::EQ | CondCode::NE) {
        return None;
    }

    let bool_cmp_pos = cond_pos.checked_sub(1)?;
    let bool_cmp_id = insts[bool_cmp_pos];
    let bool_cmp = func.inst(bool_cmp_id);
    if bool_cmp.opcode != AArch64Opcode::CmpRI || bool_cmp.operands.get(1)?.as_imm()? != 0 {
        return None;
    }
    let pred = bool_cmp.operands.first()?;

    let cset_pos = bool_cmp_pos.checked_sub(1)?;
    let cset_id = insts[cset_pos];
    let cset = func.inst(cset_id);
    if cset.opcode != AArch64Opcode::CSet || cset.operands.first()? != pred {
        return None;
    }
    let cset_cond = decode_cond(cset.operands.get(1)?.as_imm()? as u8)?;

    let compare_pos = cset_pos.checked_sub(1)?;
    let compare_id = insts[compare_pos];
    let compare = func.inst(compare_id);
    if !matches!(compare.opcode, AArch64Opcode::CmpRR | AArch64Opcode::CmpRI) {
        return None;
    }

    let branch_takes_when_cset_true = branch_cond == CondCode::NE;
    Some(HeaderCondition {
        compare_id,
        compare_inst: compare.clone(),
        cond: cond_for_body(branch_to_body, branch_takes_when_cset_true, cset_cond),
        body: BlockId(0),
        exit: BlockId(0),
        branch_id: insts[cond_pos],
        removed_ids: vec![cset_id, bool_cmp_id],
    })
}

fn parse_cbnz_header(
    func: &MachFunction,
    insts: &[InstId],
    cond_pos: usize,
    branch_to_body: bool,
) -> Option<HeaderCondition> {
    let branch = func.inst(insts[cond_pos]);
    let pred = branch.operands.first()?;
    let branch_takes_when_cset_true = branch.opcode == AArch64Opcode::Cbnz;

    let cset_pos = cond_pos.checked_sub(1)?;
    let cset_id = insts[cset_pos];
    let cset = func.inst(cset_id);
    if cset.opcode != AArch64Opcode::CSet || cset.operands.first()? != pred {
        return None;
    }
    let cset_cond = decode_cond(cset.operands.get(1)?.as_imm()? as u8)?;

    let compare_pos = cset_pos.checked_sub(1)?;
    let compare_id = insts[compare_pos];
    let compare = func.inst(compare_id);
    if !matches!(compare.opcode, AArch64Opcode::CmpRR | AArch64Opcode::CmpRI) {
        return None;
    }

    Some(HeaderCondition {
        compare_id,
        compare_inst: compare.clone(),
        cond: cond_for_body(branch_to_body, branch_takes_when_cset_true, cset_cond),
        body: BlockId(0),
        exit: BlockId(0),
        branch_id: insts[cond_pos],
        removed_ids: vec![cset_id],
    })
}

fn cond_for_body(
    branch_to_body: bool,
    branch_takes_when_cset_true: bool,
    cset_cond: CondCode,
) -> CondCode {
    if branch_to_body == branch_takes_when_cset_true {
        cset_cond
    } else {
        cset_cond.invert()
    }
}

fn header_has_only_condition_insts(
    insts: &[InstId],
    parsed: &HeaderCondition,
    exit_branch_id: InstId,
) -> bool {
    let mut allowed: HashSet<InstId> = HashSet::new();
    allowed.insert(parsed.compare_id);
    allowed.insert(parsed.branch_id);
    allowed.insert(exit_branch_id);
    allowed.extend(parsed.removed_ids.iter().copied());
    insts.iter().all(|id| allowed.contains(id))
}

fn deleted_value_uses_are_limited_to_condition_sequence(
    func: &MachFunction,
    parsed: &HeaderCondition,
) -> bool {
    let mut accepted_users: HashSet<InstId> = parsed.removed_ids.iter().copied().collect();
    accepted_users.insert(parsed.branch_id);

    parsed.removed_ids.iter().copied().all(|removed_id| {
        let removed = func.inst(removed_id);
        let mut safe = true;
        for_each_inst_def(removed, |def| {
            if !all_vreg_uses_are_by(func, def, &accepted_users) {
                safe = false;
            }
        });
        safe
    })
}

fn all_vreg_uses_are_by(func: &MachFunction, vreg: VReg, accepted_users: &HashSet<InstId>) -> bool {
    for &block_id in &func.block_order {
        let block = func.block(block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            let mut uses_vreg = false;
            aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |pos| {
                if matches!(inst.operands.get(pos), Some(MachOperand::VReg(candidate)) if *candidate == vreg)
                {
                    uses_vreg = true;
                }
            });
            if uses_vreg && !accepted_users.contains(&inst_id) {
                return false;
            }
        }
    }
    true
}

fn trailing_carrier_copies(func: &MachFunction, block: BlockId) -> Vec<InstId> {
    let insts = &func.block(block).insts;
    if insts.len() < 2 {
        return Vec::new();
    }

    let mut copies = Vec::new();
    let mut pos = insts.len() - 1;
    while pos > 0 {
        let id = insts[pos - 1];
        if !matches!(
            func.inst(id).opcode,
            AArch64Opcode::MovR | AArch64Opcode::Copy
        ) {
            break;
        }
        copies.push(id);
        pos -= 1;
    }
    copies.reverse();
    copies
}

fn is_counted_like_latch_update(
    carrier_copies: &[InstId],
    func: &MachFunction,
    compare: &MachInst,
) -> bool {
    if carrier_copies.is_empty() {
        return false;
    }

    let compared_regs: Vec<&MachOperand> = compare
        .operands
        .iter()
        .filter(|op| op.is_vreg() || op.is_preg())
        .collect();
    if compared_regs.is_empty() {
        return false;
    }

    let defs = compared_regs
        .iter()
        .filter(|op| carrier_copies_define_operand(func, carrier_copies, op))
        .count();
    defs == 1
}

fn carrier_copies_define_operand(
    func: &MachFunction,
    carrier_copies: &[InstId],
    operand: &MachOperand,
) -> bool {
    carrier_copies.iter().any(|&id| {
        let inst = func.inst(id);
        inst.opcode.produces_value() && inst.operands.first() == Some(operand)
    })
}

fn can_harden_carrier_copy(inst: &MachInst) -> bool {
    if !matches!(inst.opcode, AArch64Opcode::MovR | AArch64Opcode::Copy) {
        return false;
    }
    let Some(dst) = inst.operands.first() else {
        return false;
    };
    let Some(src) = inst.operands.get(1) else {
        return false;
    };
    is_gpr_operand(dst) && is_gpr_operand(src)
}

fn is_gpr_operand(op: &MachOperand) -> bool {
    match op {
        MachOperand::VReg(vreg) => matches!(
            vreg.class,
            trust_cg_ir::RegClass::Gpr64 | trust_cg_ir::RegClass::Gpr32
        ),
        MachOperand::PReg(preg) => preg.is_gpr(),
        _ => false,
    }
}

fn apply_rewrite(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    header_cond: HeaderCondition,
    carrier_copies: Vec<InstId>,
    mut provenance: Option<&mut ProvenanceMap>,
) {
    let pass = loop_latch_layout_pass_id();
    let body = lp.latch;

    let latch_branch_id = *func
        .block(body)
        .insts
        .last()
        .expect("validated latch branch");
    let latch_branch_source_loc = func.inst(latch_branch_id).source_loc;
    let body_loop_depth = func.block(body).loop_depth;

    // Header guard: keep the zero-trip check, but collapse materialized bool
    // control flow to a direct B.cond where this pass can prove the pattern.
    {
        let branch = func.inst_mut(header_cond.branch_id);
        branch.opcode = AArch64Opcode::BCond;
        branch.operands = vec![
            MachOperand::Imm(header_cond.cond.encoding() as i64),
            MachOperand::Block(header_cond.body),
        ];
    }
    if let Some(provenance) = provenance.as_deref_mut() {
        provenance.record_in_place_transform(header_cond.branch_id, pass.clone());
        for &removed_id in &header_cond.removed_ids {
            provenance.record_deletion(
                removed_id,
                pass.clone(),
                "loop-latch-layout replaced materialized loop predicate with direct branch",
            );
        }
    }

    if !header_cond.removed_ids.is_empty() {
        let removed: HashSet<InstId> = header_cond.removed_ids.iter().copied().collect();
        func.block_mut(lp.header)
            .insts
            .retain(|id| !removed.contains(id));
    }

    // Split a dedicated latch block. Keeping the loop-carried copies in a
    // separate predecessor avoids self-loop copy coalescing: the body sees the
    // copied values as live-ins from the latch edge, just as it did through the
    // original header backedge.
    let new_latch = func.create_block();
    func.block_mut(new_latch).loop_depth = body_loop_depth;
    move_block_after(func, new_latch, body);

    let moved: HashSet<InstId> = carrier_copies.iter().copied().collect();
    func.block_mut(body).insts.retain(|id| !moved.contains(id));

    {
        let branch = func.inst_mut(latch_branch_id);
        branch.opcode = AArch64Opcode::B;
        branch.operands = vec![MachOperand::Block(new_latch)];
        branch.source_loc = latch_branch_source_loc;
    }

    func.block_mut(new_latch).insts.extend(carrier_copies);
    harden_carrier_copies(func, new_latch, provenance.as_deref_mut(), pass.clone());

    let mut latch_cmp = header_cond.compare_inst.clone();
    latch_cmp.source_loc = header_cond.compare_inst.source_loc;
    let latch_cmp_id = func.push_inst(latch_cmp);
    func.append_inst(new_latch, latch_cmp_id);

    let mut new_latch_branch = MachInst::new(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(header_cond.cond.encoding() as i64),
            MachOperand::Block(body),
        ],
    );
    new_latch_branch.source_loc = latch_branch_source_loc;
    let new_latch_branch_id = func.push_inst(new_latch_branch);
    func.append_inst(new_latch, new_latch_branch_id);

    if let Some(provenance) = provenance {
        provenance.record_in_place_transform(latch_branch_id, pass.clone());
        provenance.record_clone(header_cond.compare_id, latch_cmp_id, pass.clone());
        provenance.record_clone(latch_branch_id, new_latch_branch_id, pass);
    }

    // CFG maintenance. The old body->header backedge becomes body->new_latch,
    // and the new latch owns the conditional backedge plus exit fallthrough.
    func.block_mut(body).succs.retain(|&succ| succ != lp.header);
    func.block_mut(lp.header).preds.retain(|&pred| pred != body);
    add_edge_unique(func, body, new_latch);
    add_edge_unique(func, new_latch, body);
    add_edge_unique(func, new_latch, header_cond.exit);
}

fn harden_carrier_copies(
    func: &mut MachFunction,
    block: BlockId,
    mut provenance: Option<&mut ProvenanceMap>,
    pass: PassId,
) {
    let carrier_ids = func.block(block).insts.clone();
    for id in carrier_ids {
        let inst = func.inst(id);
        if !can_harden_carrier_copy(inst) {
            continue;
        }
        let source_loc = inst.source_loc;
        let dst = inst.operands[0].clone();
        let src = inst.operands[1].clone();
        let mut hardened = MachInst::new(AArch64Opcode::AddRI, vec![dst, src, MachOperand::Imm(0)]);
        hardened.source_loc = source_loc;
        *func.inst_mut(id) = hardened;
        if let Some(provenance) = provenance.as_deref_mut() {
            provenance.record_in_place_transform(id, pass.clone());
        }
    }
}

// ---------------------------------------------------------------------------
// Tier 3a: rotate an inverted-guard two-block counted loop (fib2)
// ---------------------------------------------------------------------------

/// A two-block loop whose header is ALREADY a valid zero-trip guard of the
/// INVERTED orientation `cmp; b.cond EXIT; b BODY` — the conditional branch
/// leaves the loop and the unconditional branch falls into the body. This is
/// the shape clang -O1 emits for a tail-recursion-eliminated accumulator loop
/// (fib2's `fib`), which tier 1 does not recognize because it expects the
/// opposite `b.cond BODY; b EXIT`.
struct CaseBHeader {
    compare_id: InstId,
    compare_inst: MachInst,
    /// Condition under which the loop CONTINUES (branches to the body): the
    /// logical inverse of the header's exit condition.
    continue_cond: CondCode,
    exit: BlockId,
}

/// Recognize the inverted top-tested guard `[cmp, b.cond EXIT, b BODY]`.
/// Fail-closed: the header must be EXACTLY those three instructions (a pure
/// guard doing no other work), the compare a `CmpRR`/`CmpRI`, and the exit a
/// block outside the loop.
fn parse_case_b_header(func: &MachFunction, lp: &NaturalLoop) -> Option<CaseBHeader> {
    let header = func.block(lp.header);
    if header.succs.len() != 2 || !header.succs.contains(&lp.latch) {
        return None;
    }
    let exit = header
        .succs
        .iter()
        .copied()
        .find(|succ| !lp.body.contains(succ))?;

    // A pure guard is exactly compare + conditional-exit + unconditional-body.
    if header.insts.len() != 3 {
        return None;
    }
    let compare_id = header.insts[0];
    let cond_branch = func.inst(header.insts[1]);
    let uncond_branch = func.inst(header.insts[2]);

    // Inverted orientation: the unconditional branch continues to the body, the
    // conditional branch leaves to the exit.
    if uncond_branch.opcode != AArch64Opcode::B || branch_target(uncond_branch) != Some(lp.latch) {
        return None;
    }
    if cond_branch.opcode != AArch64Opcode::BCond || branch_target(cond_branch) != Some(exit) {
        return None;
    }
    let exit_cond = decode_cond(cond_branch.operands.first()?.as_imm()? as u8)?;

    let compare = func.inst(compare_id);
    if !matches!(compare.opcode, AArch64Opcode::CmpRR | AArch64Opcode::CmpRI) {
        return None;
    }

    Some(CaseBHeader {
        compare_id,
        compare_inst: compare.clone(),
        continue_cond: exit_cond.invert(),
        exit,
    })
}

/// Tier 3a: rotate the inverted-guard two-block loop by splitting a dedicated
/// latch (reusing tier 1's carrier-copy machinery) that re-tests on the updated
/// induction value and back-edges into the body, leaving the header as the
/// one-time zero-trip guard.
fn rewrite_rotated_two_block_case_b(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    provenance: Option<&mut ProvenanceMap>,
) -> bool {
    if !is_simple_two_block_loop(func, lp) {
        return false;
    }
    if block_contains_phi(func, lp.header) || block_contains_phi(func, lp.latch) {
        return false;
    }
    let Some(header) = parse_case_b_header(func, lp) else {
        return false;
    };
    if block_contains_phi(func, header.exit) {
        return false;
    }
    // The exit must currently be reached only from the header (it will gain the
    // split latch as a second predecessor). A shared exit would need phi-aware
    // edge splitting we do not attempt.
    if func.block(header.exit).preds != [lp.header] {
        return false;
    }
    let carrier_copies = trailing_carrier_copies(func, lp.latch);
    if !is_counted_like_latch_update(&carrier_copies, func, &header.compare_inst) {
        return false;
    }
    if !carrier_copies
        .iter()
        .all(|&id| can_harden_carrier_copy(func.inst(id)))
    {
        return false;
    }

    apply_rotate_case_b(func, lp, header, carrier_copies, provenance);
    true
}

fn apply_rotate_case_b(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    header: CaseBHeader,
    carrier_copies: Vec<InstId>,
    mut provenance: Option<&mut ProvenanceMap>,
) {
    let pass = loop_latch_layout_pass_id();
    let body = lp.latch;

    let latch_branch_id = *func
        .block(body)
        .insts
        .last()
        .expect("validated latch branch");
    let latch_branch_source_loc = func.inst(latch_branch_id).source_loc;
    let body_loop_depth = func.block(body).loop_depth;

    // Split a dedicated latch after the body — same rationale as tier 1: keeping
    // the loop-carried copies in their own predecessor avoids self-loop copy
    // coalescing. Lay out header, body, new_latch, exit contiguously so the new
    // latch's exit edge and the body's backedge both become fall-throughs.
    let new_latch = func.create_block();
    func.block_mut(new_latch).loop_depth = body_loop_depth;
    move_block_after(func, body, lp.header);
    move_block_after(func, new_latch, body);
    move_block_after(func, header.exit, new_latch);

    let moved: HashSet<InstId> = carrier_copies.iter().copied().collect();
    func.block_mut(body).insts.retain(|id| !moved.contains(id));

    {
        let branch = func.inst_mut(latch_branch_id);
        branch.opcode = AArch64Opcode::B;
        branch.operands = vec![MachOperand::Block(new_latch)];
        branch.source_loc = latch_branch_source_loc;
    }

    func.block_mut(new_latch).insts.extend(carrier_copies);
    harden_carrier_copies(func, new_latch, provenance.as_deref_mut(), pass.clone());

    let mut latch_cmp = header.compare_inst.clone();
    latch_cmp.source_loc = header.compare_inst.source_loc;
    let latch_cmp_id = func.push_inst(latch_cmp);
    func.append_inst(new_latch, latch_cmp_id);

    // The rotated backedge: continue into the body while the loop condition
    // holds on the freshly updated induction value.
    let mut latch_bcond = MachInst::new(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(header.continue_cond.encoding() as i64),
            MachOperand::Block(body),
        ],
    );
    latch_bcond.source_loc = latch_branch_source_loc;
    let latch_bcond_id = func.push_inst(latch_bcond);
    func.append_inst(new_latch, latch_bcond_id);

    // Explicit exit branch keeps the rotation correct independent of final block
    // layout; codegen's fall-through elision drops it when the exit is the
    // physical successor (which the reorder above arranges).
    let mut latch_exit = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(header.exit)]);
    latch_exit.source_loc = latch_branch_source_loc;
    let latch_exit_id = func.push_inst(latch_exit);
    func.append_inst(new_latch, latch_exit_id);

    if let Some(provenance) = provenance {
        provenance.record_in_place_transform(latch_branch_id, pass.clone());
        provenance.record_clone(header.compare_id, latch_cmp_id, pass);
    }

    // CFG maintenance: body->header becomes body->new_latch; the new latch owns
    // the conditional backedge and the exit fall-through. The header keeps its
    // own guard edges (header->body, header->exit) and loses the backedge pred.
    func.block_mut(body).succs.retain(|&succ| succ != lp.header);
    func.block_mut(lp.header).preds.retain(|&pred| pred != body);
    add_edge_unique(func, body, new_latch);
    add_edge_unique(func, new_latch, body);
    add_edge_unique(func, new_latch, header.exit);
}

// ---------------------------------------------------------------------------
// Tier 3b: rotate a pure test-only header by duplicating it into the latches
// ---------------------------------------------------------------------------

/// A loop header consisting ONLY of a test that branches two ways — to an exit
/// outside the loop and to a body-entry inside it — with NO value-producing or
/// side-effecting instructions, and whose LAST instruction is the unconditional
/// `b BODY` fall-through. Duplicating this test into a backedge predecessor is
/// sound because the registers it reads are exactly the values live out of that
/// predecessor (the header is the predecessor's successor and consumes them at
/// entry, so cloning changes no value on any path).
struct TestOnlyHeader {
    /// Header instructions preceding the final unconditional `b` — the
    /// flag-only compare(s) and the conditional branch; cloned into each latch.
    clone_insts: Vec<InstId>,
    /// Body-entry successor (inside the loop).
    body: BlockId,
    /// Exit successor (outside the loop).
    exit: BlockId,
    /// Where each latch's terminating `b` is retargeted after the clone: the
    /// header's own unconditional-branch target. `body` when the header is
    /// `b.cond exit; b body` (the conditional EXITS), `exit` when it is
    /// `b.cond body; b exit` (the conditional CONTINUES — b1_mispredict's
    /// while-loop orientation, where the cloned `b.cond body` becomes the
    /// rotated backedge and the fallthrough exits).
    terminal_target: BlockId,
}

/// Recognize a pure test-only header ending in `b BODY`. Fail-closed: every
/// instruction must be a flag-only compare (`CmpRR`/`CmpRI`) or a branch
/// (`B`/`BCond`/`Cbz`/`Cbnz`); none may define a virtual register or touch
/// memory. The header must have exactly two successors — one in the loop body,
/// one outside — and its branch targets must be exactly those two.
fn parse_test_only_header(
    func: &MachFunction,
    lp: &NaturalLoop,
    extended: bool,
) -> Option<TestOnlyHeader> {
    let header = func.block(lp.header);
    if header.succs.len() != 2 {
        return None;
    }
    let body = header.succs.iter().copied().find(|s| lp.body.contains(s))?;
    let exit = header
        .succs
        .iter()
        .copied()
        .find(|s| !lp.body.contains(s))?;
    if body == exit {
        return None;
    }

    let mut carrier_dsts: Vec<u32> = Vec::new();
    let mut seen_non_copy = false;
    for &id in &header.insts {
        let inst = func.inst(id);
        match inst.opcode {
            // A leading run of GPR carrier copies feeding the test (the
            // importer's block-param protocol keeps the IV compare reading a
            // header-local temp, e.g. `MovR t, iv; CmpRR t, n`). Each clone
            // renames the dest to a FRESH vreg per latch — no second
            // definition is ever created — so these are safe to duplicate.
            // The dest must be header-local (checked below).
            AArch64Opcode::MovR | AArch64Opcode::Copy
                if extended && !seen_non_copy && can_harden_carrier_copy(inst) =>
            {
                // Per-INSTANCE flag vetting (review hardening): the arm's
                // `continue` bypasses the blanket check below, and flags are
                // stamped per instance — a MovR carrying memory/call flags
                // must not be cloned uninspected.
                if inst.reads_memory() || inst.writes_memory() || inst.is_call() {
                    return None;
                }
                let Some(MachOperand::VReg(dst)) = inst.operands.first() else {
                    return None;
                };
                carrier_dsts.push(dst.id);
                continue;
            }
            // The compares' only "side effect" is the NZCV write — which is
            // precisely what the clone exists to reproduce at the latch. The
            // clones are spliced immediately before the latch terminal, after
            // every existing flag consumer in the latch, and the rotated
            // latch->body edge carries the same flag values the header's own
            // compare produced (same opcode, same operand values). Exempting
            // them here revives arms that were dead since the tier landed:
            // `has_side_effects()` is true for CmpRR/CmpRI, so only
            // cbz/cbnz-style headers ever passed the blanket check below.
            AArch64Opcode::CmpRR | AArch64Opcode::CmpRI if extended => {
                // Exempt ONLY the NZCV write (`has_side_effects`); every other
                // per-instance screen still applies (review hardening — a
                // compare instance stamped with memory flags must decline).
                if inst.produces_value()
                    || inst.reads_memory()
                    || inst.writes_memory()
                    || inst.is_call()
                {
                    return None;
                }
                seen_non_copy = true;
                continue;
            }
            AArch64Opcode::B | AArch64Opcode::BCond | AArch64Opcode::Cbz | AArch64Opcode::Cbnz => {
                seen_non_copy = true;
            }
            _ => return None,
        }
        // No other value-producing instruction may appear: cloning it would
        // create a second definition of its destination in every latch.
        if inst.produces_value()
            || inst.has_side_effects()
            || inst.reads_memory()
            || inst.writes_memory()
            || inst.is_call()
        {
            return None;
        }
    }
    // Every carrier dest must be consumed ONLY inside this header: a use
    // anywhere else would read the original vreg while the rotated latches
    // define fresh renames, changing the value it sees.
    if !carrier_dsts.is_empty() {
        let header_ids: HashSet<InstId> = header.insts.iter().copied().collect();
        for block in func.blocks.iter() {
            for &iid in &block.insts {
                if header_ids.contains(&iid) {
                    continue;
                }
                for op in &func.inst(iid).operands {
                    if let MachOperand::VReg(v) = op
                        && carrier_dsts.contains(&v.id)
                    {
                        return None;
                    }
                }
            }
        }
    }

    // The header's last instruction is its unconditional branch; each latch
    // reuses its own terminating branch as that edge, so only the prefix
    // (compare + conditional branch) needs cloning. Both orientations are
    // accepted: `b.cond exit; b body` (terminal -> body) and
    // `b.cond body; b exit` (terminal -> exit). The exact-{body, exit}
    // targets check below guarantees the prefix conditional(s) point at the
    // OTHER successor in each case.
    let (&last_id, prefix) = header.insts.split_last()?;
    let last = func.inst(last_id);
    if last.opcode != AArch64Opcode::B {
        return None;
    }
    let terminal_target = match branch_target(last) {
        Some(t) if t == body => t,
        // Inverted orientation (`b.cond body; b exit`) is part of the
        // extended rotation.
        Some(t) if t == exit && extended => t,
        _ => return None,
    };

    // The branch targets across the whole header must be exactly {body, exit}.
    let mut targets: Vec<BlockId> = header
        .insts
        .iter()
        .filter(|&&id| func.inst(id).is_branch())
        .filter_map(|&id| branch_target(func.inst(id)))
        .collect();
    targets.sort_by_key(|b| b.0);
    targets.dedup();
    let mut expected = [body, exit];
    expected.sort_by_key(|b| b.0);
    if targets != expected {
        return None;
    }

    Some(TestOnlyHeader {
        clone_insts: prefix.to_vec(),
        body,
        exit,
        terminal_target,
    })
}

/// Tier 3b: rotate a loop whose header is a pure test-only guard by duplicating
/// that test into every in-loop backedge predecessor. The header then survives
/// only as the one-time entry guard, so steady-state iterations back-edge
/// straight into the body without the header round-trip (ackermann's countdown
/// loop with two backedges into a `cbz M, exit` header).
/// Extended-rotation profitability floor: total in-loop instruction count.
/// Rotating a TINY loop (a vectorizer residual, a 3-inst byte loop) buys at
/// most one taken branch per iteration of a loop that barely runs, while the
/// cloned test and the changed loop shape perturb downstream block layout —
/// measured on p7_sieve as a net +4.6% runtime when tiny residual loops were
/// rotated (their neighbors' headers lost body-fallthrough orientation). The
/// win case (b1_mispredict, -11%) is a ~33-inst multi-block body; 16 cleanly
/// separates the populations on the corpus.
const MIN_EXTENDED_ROTATE_LOOP_INSTS: usize = 8;

fn duplicate_header_test_into_latches(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    provenance: Option<&mut ProvenanceMap>,
    extended: bool,
) -> bool {
    if block_contains_phi(func, lp.header) {
        return false;
    }
    if extended {
        let loop_insts: usize = lp.body.iter().map(|&b| func.block(b).insts.len()).sum();
        if loop_insts < MIN_EXTENDED_ROTATE_LOOP_INSTS {
            return false;
        }
    }
    let Some(header) = parse_test_only_header(func, lp, extended) else {
        return false;
    };
    if block_contains_phi(func, header.body) || block_contains_phi(func, header.exit) {
        return false;
    }

    // Every in-loop predecessor of the header must reach it via a terminating
    // unconditional `b header` and must NOT be the body-entry itself (that is a
    // self-loop, handled by the case-B split). There must also be at least one
    // out-of-loop predecessor so the header survives as the entry guard.
    let header_preds = func.block(lp.header).preds.clone();
    let mut latches: Vec<BlockId> = Vec::new();
    let mut has_outside_pred = false;
    for pred in header_preds {
        if !lp.body.contains(&pred) {
            has_outside_pred = true;
            continue;
        }
        if pred == lp.header {
            return false;
        }
        // A latch that IS the body-entry means a two-block loop; the legacy
        // tier defers those to tiers 1/3a. The EXTENDED tier takes them:
        // tier 1's `header_has_only_condition_insts` declines carrier-copy
        // headers (p5_struct_acc's `MovR t, iv; cmp t, n` shape), and the
        // clone-into-latch transform is orientation- and shape-sound here —
        // the cloned conditional simply becomes a self-backedge on the body
        // block, with the header surviving as the entry guard.
        if pred == header.body && !extended {
            return false;
        }
        let pred_block = func.block(pred);
        let Some((&term_id, rest)) = pred_block.insts.split_last() else {
            return false;
        };
        let term = func.inst(term_id);
        if term.opcode != AArch64Opcode::B || branch_target(term) != Some(lp.header) {
            return false;
        }
        if rest
            .iter()
            .any(|&id| func.inst(id).is_branch() || func.inst(id).is_terminator())
        {
            return false;
        }
        latches.push(pred);
    }
    if latches.is_empty() || !has_outside_pred {
        return false;
    }

    apply_duplicate_header_test(func, lp, header, latches, provenance);
    true
}

fn apply_duplicate_header_test(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    header: TestOnlyHeader,
    latches: Vec<BlockId>,
    mut provenance: Option<&mut ProvenanceMap>,
) {
    let pass = loop_latch_layout_pass_id();

    for latch in latches {
        // Clone the header's test prefix (carrier copies + compare +
        // conditional branch). Carrier-copy dests are renamed to fresh vregs
        // (one per latch) and every later cloned instruction reads the
        // renamed temp, so no vreg ever gains a second definition.
        // Keyed on the FULL VReg (id, class): same-id different-class vregs
        // are distinct values in this IR (see `all_vreg_uses_are_by`), and an
        // id-only key would conflate two carrier dests sharing an id across
        // classes — renaming a use to a never-defined fresh vreg
        // (review-confirmed PLAUSIBLE miscompile shape).
        let mut rename: std::collections::HashMap<VReg, u32> = std::collections::HashMap::new();
        let mut cloned_ids: Vec<(InstId, InstId)> = Vec::with_capacity(header.clone_insts.len());
        for &src_id in &header.clone_insts {
            let mut cloned_inst = func.inst(src_id).clone();
            let is_copy = matches!(
                cloned_inst.opcode,
                AArch64Opcode::MovR | AArch64Opcode::Copy
            ) && can_harden_carrier_copy(&cloned_inst);
            if is_copy {
                // Rename src via the map first, then allocate the fresh dest.
                if let Some(MachOperand::VReg(srcv)) = cloned_inst.operands.get(1).cloned()
                    && let Some(&fresh) = rename.get(&srcv)
                {
                    cloned_inst.operands[1] = MachOperand::VReg(VReg { id: fresh, ..srcv });
                }
                if let Some(MachOperand::VReg(dstv)) = cloned_inst.operands.first().cloned() {
                    let fresh = func.alloc_vreg();
                    rename.insert(dstv, fresh);
                    cloned_inst.operands[0] = MachOperand::VReg(VReg { id: fresh, ..dstv });
                }
            } else {
                for op in cloned_inst.operands.iter_mut() {
                    if let MachOperand::VReg(v) = op
                        && let Some(&fresh) = rename.get(v)
                    {
                        *op = MachOperand::VReg(VReg { id: fresh, ..*v });
                    }
                }
            }
            let new_id = func.push_inst(cloned_inst);
            cloned_ids.push((src_id, new_id));
        }

        // Splice the clones in front of the latch's terminating `b header`, then
        // retarget that branch to the header's own unconditional-branch target
        // (`terminal_target`: body in the classic orientation, exit in the
        // inverted one); the cloned conditional supplies the other edge.
        let term_id = *func
            .block(latch)
            .insts
            .last()
            .expect("validated backedge branch");
        {
            let insts = &mut func.block_mut(latch).insts;
            let pos = insts.len() - 1;
            insts.splice(pos..pos, cloned_ids.iter().map(|&(_, id)| id));
        }
        func.inst_mut(term_id).operands = vec![MachOperand::Block(header.terminal_target)];

        if let Some(provenance) = provenance.as_deref_mut() {
            for &(src_id, new_id) in &cloned_ids {
                provenance.record_clone(src_id, new_id, pass.clone());
            }
            provenance.record_in_place_transform(term_id, pass.clone());
        }

        // CFG: the latch no longer feeds the header; it exits and back-edges
        // into the body exactly as the header did.
        func.block_mut(latch).succs.retain(|&s| s != lp.header);
        func.block_mut(lp.header).preds.retain(|&p| p != latch);
        add_edge_unique(func, latch, header.body);
        add_edge_unique(func, latch, header.exit);
    }
}

// ---------------------------------------------------------------------------
// Tier 2: rotated-loop pure-latch tail duplication
// ---------------------------------------------------------------------------

/// Total instructions cloned per duplication (including the retargeted branch).
const MAX_TAILDUP_CHAIN_INSTS: usize = 8;
/// Blocks the latch chain may span.
const MAX_TAILDUP_CHAIN_BLOCKS: usize = 4;

/// Compile-time kill switch: set `TCG_NO_LATCH_TAILDUP` (any value) to disable
/// the rotated-loop tail-duplication tier. The whole pass (both tiers) is
/// additionally governed by `TRUST_CG_DISABLE_PASSES=looplatch`.
fn latch_taildup_enabled() -> bool {
    std::env::var_os("TCG_NO_LATCH_TAILDUP").is_none()
}

/// The exact pure instruction sequence executed from the head of a latch chain
/// through the terminating backedge `B header` (exclusive).
struct PureLatchChain {
    /// Head block of the chain (the target of the predecessor's branch).
    head: BlockId,
    /// Every instruction executed along the chain in execution order,
    /// EXCLUDING intermediate `B` links between chain blocks and the final
    /// backedge branch (the predecessor's own `B` is retargeted instead).
    cloned: Vec<InstId>,
    /// Targets of the chain's conditional exits, in order.
    bcond_targets: Vec<BlockId>,
}

/// Walk the latch chain starting at `head`: a linear run of in-loop blocks
/// containing only `CmpRR`/`CmpRI`/`MovR`/`Copy`/`BCond`, each linked by a
/// terminating unconditional `B`, ending with the backedge `B lp.header`.
/// Fail-closed: any other opcode (memory op, call, cbz/tbz, ...), a cycle, or
/// a chain that leaves the loop or exceeds the size caps returns `None`.
fn parse_pure_latch_chain(
    func: &MachFunction,
    lp: &NaturalLoop,
    head: BlockId,
) -> Option<PureLatchChain> {
    let mut cloned = Vec::new();
    let mut bcond_targets = Vec::new();
    let mut visited: HashSet<BlockId> = HashSet::new();
    let mut cur = head;

    for _ in 0..MAX_TAILDUP_CHAIN_BLOCKS {
        if !visited.insert(cur) || !lp.body.contains(&cur) || cur == lp.header {
            return None;
        }
        let (&term_id, body_ids) = func.block(cur).insts.split_last()?;
        let term = func.inst(term_id);
        if term.opcode != AArch64Opcode::B {
            return None;
        }
        let next = branch_target(term)?;
        for &id in body_ids {
            let inst = func.inst(id);
            match inst.opcode {
                AArch64Opcode::CmpRR
                | AArch64Opcode::CmpRI
                | AArch64Opcode::MovR
                | AArch64Opcode::Copy => {}
                AArch64Opcode::BCond => bcond_targets.push(branch_target(inst)?),
                _ => return None,
            }
            cloned.push(id);
        }
        // +1 accounts for the retargeted terminating branch.
        if cloned.len() + 1 > MAX_TAILDUP_CHAIN_INSTS {
            return None;
        }
        if next == lp.header {
            return Some(PureLatchChain {
                head,
                cloned,
                bcond_targets,
            });
        }
        cur = next;
    }
    None
}

/// Tier 2: clone a rotated loop's pure latch chain into an in-loop predecessor
/// that reaches it only via an unconditional `B` (see the module docs). The
/// predecessor then owns its own conditional exit + backedge, saving one taken
/// branch every iteration that goes through it (Bubblesort's swap arm).
fn tail_duplicate_pure_latch_chain(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    // Deterministic candidate order: current layout order.
    let order = func.block_order.clone();
    for &pred in &order {
        if !lp.body.contains(&pred) || pred == lp.header {
            continue;
        }
        let pred_block = func.block(pred);
        if pred_block.succs.len() != 1 {
            continue;
        }
        let head = pred_block.succs[0];
        if head == pred || head == lp.header || !lp.body.contains(&head) {
            continue;
        }
        // The predecessor's ONLY control flow must be its terminating `B head`.
        let Some((&pred_branch_id, pred_body)) = pred_block.insts.split_last() else {
            continue;
        };
        let pred_branch = func.inst(pred_branch_id);
        if pred_branch.opcode != AArch64Opcode::B
            || branch_target(pred_branch) != Some(head)
            || pred_body
                .iter()
                .any(|&id| func.inst(id).is_branch() || func.inst(id).is_terminator())
        {
            continue;
        }
        // The chain must stay reachable for its remaining (fallthrough) preds;
        // a single-pred chain would just be moved, not deduplicated.
        if func.block(head).preds.len() < 2 {
            continue;
        }
        let Some(chain) = parse_pure_latch_chain(func, lp, head) else {
            continue;
        };
        // The header and every conditional-exit target gain `pred` as a new
        // predecessor; cloning next to a Phi would corrupt its operand pairs.
        if block_contains_phi(func, lp.header)
            || chain
                .bcond_targets
                .iter()
                .any(|&target| block_contains_phi(func, target))
        {
            continue;
        }

        apply_tail_duplicate(
            func,
            lp,
            pred,
            pred_branch_id,
            chain,
            provenance.as_deref_mut(),
        );
        return true;
    }
    false
}

fn apply_tail_duplicate(
    func: &mut MachFunction,
    lp: &NaturalLoop,
    pred: BlockId,
    pred_branch_id: InstId,
    chain: PureLatchChain,
    provenance: Option<&mut ProvenanceMap>,
) {
    let pass = loop_latch_layout_pass_id();

    // Clone the chain's executed sequence verbatim (operands, and thus branch
    // targets, identical) and splice it in front of the predecessor's branch.
    let mut clone_ids: Vec<(InstId, InstId)> = Vec::with_capacity(chain.cloned.len());
    for &src_id in &chain.cloned {
        let cloned_inst = func.inst(src_id).clone();
        let new_id = func.push_inst(cloned_inst);
        clone_ids.push((src_id, new_id));
    }
    {
        let insts = &mut func.block_mut(pred).insts;
        let term_pos = insts.len() - 1;
        insts.splice(
            term_pos..term_pos,
            clone_ids.iter().map(|&(_, new_id)| new_id),
        );
    }

    // The predecessor's branch now IS the backedge.
    func.inst_mut(pred_branch_id).operands = vec![MachOperand::Block(lp.header)];

    if let Some(provenance) = provenance {
        for &(src_id, new_id) in &clone_ids {
            provenance.record_clone(src_id, new_id, pass.clone());
        }
        provenance.record_in_place_transform(pred_branch_id, pass.clone());
    }

    // CFG maintenance: pred no longer feeds the chain; it exits where the
    // chain's conditionals exit and takes the backedge itself. (A cloned BCond
    // may legitimately target the chain head; adding edges after the retain
    // keeps that case consistent.)
    func.block_mut(pred).succs.clear();
    func.block_mut(chain.head)
        .preds
        .retain(|&other| other != pred);
    for &target in &chain.bcond_targets {
        add_edge_unique(func, pred, target);
    }
    add_edge_unique(func, pred, lp.header);
}

fn add_edge_unique(func: &mut MachFunction, from: BlockId, to: BlockId) {
    if !func.block(from).succs.contains(&to) {
        func.block_mut(from).succs.push(to);
    }
    if !func.block(to).preds.contains(&from) {
        func.block_mut(to).preds.push(from);
    }
}

fn next_block(func: &MachFunction, block: BlockId) -> Option<BlockId> {
    let pos = func.block_order.iter().position(|&bid| bid == block)?;
    func.block_order.get(pos + 1).copied()
}

fn move_block_after(func: &mut MachFunction, block: BlockId, after: BlockId) {
    func.block_order.retain(|&bid| bid != block);
    let insert_pos = func
        .block_order
        .iter()
        .position(|&bid| bid == after)
        .map(|pos| pos + 1)
        .unwrap_or(func.block_order.len());
    func.block_order.insert(insert_pos, block);
}

fn branch_target(inst: &MachInst) -> Option<BlockId> {
    inst.operands.iter().find_map(|op| match op {
        MachOperand::Block(block) => Some(*block),
        _ => None,
    })
}

fn decode_cond(encoding: u8) -> Option<CondCode> {
    match encoding {
        0b0000 => Some(CondCode::EQ),
        0b0001 => Some(CondCode::NE),
        0b0010 => Some(CondCode::HS),
        0b0011 => Some(CondCode::LO),
        0b0100 => Some(CondCode::MI),
        0b0101 => Some(CondCode::PL),
        0b0110 => Some(CondCode::VS),
        0b0111 => Some(CondCode::VC),
        0b1000 => Some(CondCode::HI),
        0b1001 => Some(CondCode::LS),
        0b1010 => Some(CondCode::GE),
        0b1011 => Some(CondCode::LT),
        0b1100 => Some(CondCode::GT),
        0b1101 => Some(CondCode::LE),
        0b1110 => Some(CondCode::AL),
        0b1111 => Some(CondCode::NV),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::{
        ProvenanceStatus, RegClass, Signature, SourceLoc, TransformKind, TrustIrInstId, VReg,
    };

    fn vreg_class(id: u32, class: RegClass) -> MachOperand {
        MachOperand::VReg(VReg::new(id, class))
    }

    fn vreg(id: u32) -> MachOperand {
        vreg_class(id, RegClass::Gpr64)
    }

    fn imm(value: i64) -> MachOperand {
        MachOperand::Imm(value)
    }

    fn block(id: BlockId) -> MachOperand {
        MachOperand::Block(id)
    }

    fn source_loc(line: u32) -> SourceLoc {
        SourceLoc {
            file: 0,
            line,
            col: 1,
        }
    }

    struct CountedLoopIds {
        header: BlockId,
        latch: BlockId,
        exit: BlockId,
        cmp: InstId,
        cset: InstId,
        branch: InstId,
        latch_branch: InstId,
    }

    fn push(func: &mut MachFunction, block_id: BlockId, inst: MachInst) -> InstId {
        let id = func.push_inst(inst);
        func.append_inst(block_id, id);
        id
    }

    fn make_counted_loop() -> (MachFunction, CountedLoopIds) {
        let mut func = MachFunction::new("counted".to_string(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let header = func.create_block();
        let latch = func.create_block();
        let exit = func.create_block();

        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::B, vec![block(header)]),
        );

        let cmp = push(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]),
        );
        let cset = push(
            &mut func,
            header,
            MachInst::new(
                AArch64Opcode::CSet,
                vec![vreg(2), imm(CondCode::LT.encoding() as i64)],
            ),
        );
        let branch = push(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::Cbnz, vec![vreg(2), block(latch)]),
        );
        push(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::B, vec![block(exit)]),
        );

        push(
            &mut func,
            latch,
            MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(0), imm(1)]),
        );
        push(
            &mut func,
            latch,
            MachInst::new(AArch64Opcode::MovR, vec![vreg(0), vreg(3)]),
        );
        let latch_branch = push(
            &mut func,
            latch,
            MachInst::new(AArch64Opcode::B, vec![block(header)]),
        );

        push(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        func.add_edge(entry, header);
        func.add_edge(header, latch);
        func.add_edge(header, exit);
        func.add_edge(latch, header);

        (
            func,
            CountedLoopIds {
                header,
                latch,
                exit,
                cmp,
                cset,
                branch,
                latch_branch,
            },
        )
    }

    fn run_pass(func: &mut MachFunction) -> bool {
        let mut pass = LoopLatchLayoutCombine;
        pass.run(func)
    }

    #[test]
    fn rewrites_counted_loop_to_latch_conditional_fallthrough() {
        let (mut func, ids) = make_counted_loop();

        assert!(run_pass(&mut func));

        let header_insts: Vec<_> = func
            .block(ids.header)
            .insts
            .iter()
            .map(|&id| func.inst(id).opcode)
            .collect();
        assert_eq!(
            header_insts,
            vec![AArch64Opcode::CmpRR, AArch64Opcode::BCond, AArch64Opcode::B]
        );
        assert_eq!(
            func.inst(ids.branch).operands,
            vec![imm(11), block(ids.latch)]
        );
        assert!(!func.block(ids.header).insts.contains(&ids.cset));

        let new_latch = next_block(&func, ids.latch).expect("split latch after body");
        assert_ne!(new_latch, ids.exit);

        let body_insts = &func.block(ids.latch).insts;
        let body_ops: Vec<_> = body_insts.iter().map(|&id| func.inst(id).opcode).collect();
        assert_eq!(body_ops, vec![AArch64Opcode::AddRI, AArch64Opcode::B]);
        let body_branch = func.inst(ids.latch_branch);
        assert_eq!(body_branch.opcode, AArch64Opcode::B);
        assert_eq!(body_branch.operands, vec![block(new_latch)]);

        let latch_ops: Vec<_> = func
            .block(new_latch)
            .insts
            .iter()
            .map(|&id| func.inst(id).opcode)
            .collect();
        assert_eq!(
            latch_ops,
            vec![
                AArch64Opcode::AddRI,
                AArch64Opcode::CmpRR,
                AArch64Opcode::BCond
            ]
        );
        let latch_branch_id = *func.block(new_latch).insts.last().unwrap();
        let latch_branch = func.inst(latch_branch_id);
        assert_eq!(
            latch_branch.operands,
            vec![imm(CondCode::LT.encoding() as i64), block(ids.latch)]
        );

        assert_eq!(func.block(ids.header).preds, vec![func.entry]);
        assert_eq!(func.block(ids.latch).succs, vec![new_latch]);
        assert!(func.block(ids.latch).preds.contains(&ids.header));
        assert!(func.block(ids.latch).preds.contains(&new_latch));
        assert_eq!(func.block(new_latch).succs, vec![ids.latch, ids.exit]);
        assert!(func.block(ids.exit).preds.contains(&new_latch));
    }

    #[test]
    fn rewrites_pre_fusion_cset_cmp_bcond_form() {
        let (mut func, ids) = make_counted_loop();
        let bool_cmp = func.push_inst(MachInst::new(AArch64Opcode::CmpRI, vec![vreg(2), imm(0)]));
        let header = func.block_mut(ids.header);
        let branch_pos = header
            .insts
            .iter()
            .position(|&id| id == ids.branch)
            .unwrap();
        header.insts.insert(branch_pos, bool_cmp);
        *func.inst_mut(ids.branch) = MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(CondCode::NE.encoding() as i64), block(ids.latch)],
        );

        assert!(run_pass(&mut func));
        let header_ops: Vec<_> = func
            .block(ids.header)
            .insts
            .iter()
            .map(|&id| func.inst(id).opcode)
            .collect();
        assert_eq!(
            header_ops,
            vec![AArch64Opcode::CmpRR, AArch64Opcode::BCond, AArch64Opcode::B]
        );
        assert!(!func.block(ids.header).insts.contains(&ids.cset));
        assert!(!func.block(ids.header).insts.contains(&bool_cmp));
    }

    #[test]
    fn rejects_materialized_predicate_with_non_branch_use() {
        let (mut func, ids) = make_counted_loop();
        let pred_use = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(9), vreg(2), imm(1)],
        ));
        func.block_mut(ids.latch).insts.insert(0, pred_use);

        let header_insts_before = func.block(ids.header).insts.clone();
        let latch_succs_before = func.block(ids.latch).succs.clone();

        assert!(!run_pass(&mut func));
        assert_eq!(func.block(ids.header).insts, header_insts_before);
        assert_eq!(func.inst(ids.branch).opcode, AArch64Opcode::Cbnz);
        assert!(func.block(ids.header).insts.contains(&ids.cset));
        assert_eq!(func.inst(ids.latch_branch).opcode, AArch64Opcode::B);
        assert_eq!(func.block(ids.latch).succs, latch_succs_before);
    }

    #[test]
    fn ignores_same_id_different_class_materialized_predicate_use() {
        let (mut func, ids) = make_counted_loop();
        let unrelated_fpr_use = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                vreg_class(9, RegClass::Fpr64),
                vreg_class(2, RegClass::Fpr64),
                imm(1),
            ],
        ));
        func.block_mut(ids.latch).insts.insert(0, unrelated_fpr_use);

        assert!(run_pass(&mut func));
        assert!(!func.block(ids.header).insts.contains(&ids.cset));
        assert!(func.block(ids.latch).insts.contains(&unrelated_fpr_use));
    }

    #[test]
    fn rejects_non_counted_loop_without_latch_update() {
        let (mut func, ids) = make_counted_loop();
        let mov_ids: HashSet<InstId> = func
            .block(ids.latch)
            .insts
            .iter()
            .copied()
            .filter(|&id| func.inst(id).opcode == AArch64Opcode::MovR)
            .collect();
        func.block_mut(ids.latch)
            .insts
            .retain(|id| !mov_ids.contains(id));

        assert!(!run_pass(&mut func));
        assert_eq!(func.inst(ids.latch_branch).opcode, AArch64Opcode::B);
        assert_eq!(func.block(ids.latch).succs, vec![ids.header]);
    }

    #[test]
    fn rejects_multi_latch_loop() {
        let (mut func, ids) = make_counted_loop();
        let second_latch = func.create_block();
        push(
            &mut func,
            second_latch,
            MachInst::new(AArch64Opcode::AddRI, vec![vreg(4), vreg(0), imm(1)]),
        );
        push(
            &mut func,
            second_latch,
            MachInst::new(AArch64Opcode::MovR, vec![vreg(0), vreg(4)]),
        );
        push(
            &mut func,
            second_latch,
            MachInst::new(AArch64Opcode::B, vec![block(ids.header)]),
        );
        func.block_mut(ids.header).succs.push(second_latch);
        func.block_mut(ids.header).preds.push(second_latch);
        func.block_mut(second_latch).preds.push(ids.header);
        func.block_mut(second_latch).succs.push(ids.header);

        assert!(!run_pass(&mut func));
        assert_eq!(func.inst(ids.latch_branch).opcode, AArch64Opcode::B);
    }

    #[test]
    fn rejects_when_exit_is_not_latch_fallthrough() {
        let (mut func, ids) = make_counted_loop();
        func.block_order = vec![func.entry, ids.header, ids.exit, ids.latch];

        assert!(!run_pass(&mut func));
        assert_eq!(func.inst(ids.latch_branch).opcode, AArch64Opcode::B);
        assert_eq!(func.block(ids.latch).succs, vec![ids.header]);
    }

    #[test]
    fn rejects_phi_block_param_shape() {
        let (mut func, ids) = make_counted_loop();
        let phi = func.push_inst(MachInst::new(
            AArch64Opcode::Phi,
            vec![
                vreg(9),
                vreg(0),
                block(func.entry),
                vreg(3),
                block(ids.latch),
            ],
        ));
        func.block_mut(ids.header).insts.insert(0, phi);

        assert!(!run_pass(&mut func));
        assert_eq!(func.inst(ids.latch_branch).opcode, AArch64Opcode::B);
    }

    #[test]
    fn rejects_backedge_copy_block_shape() {
        let (mut func, ids) = make_counted_loop();
        let copy_block = func.create_block();
        move_block_after(&mut func, copy_block, ids.latch);

        push(
            &mut func,
            copy_block,
            MachInst::new(AArch64Opcode::MovR, vec![vreg(8), vreg(0)]),
        );
        push(
            &mut func,
            copy_block,
            MachInst::new(AArch64Opcode::B, vec![block(ids.header)]),
        );

        func.inst_mut(ids.latch_branch).operands = vec![block(copy_block)];
        func.block_mut(ids.latch).succs = vec![copy_block];
        func.block_mut(copy_block).preds = vec![ids.latch];
        func.block_mut(copy_block).succs = vec![ids.header];
        func.block_mut(ids.header)
            .preds
            .retain(|&pred| pred != ids.latch);
        func.block_mut(ids.header).preds.push(copy_block);

        assert!(!run_pass(&mut func));
        assert_eq!(func.inst(ids.latch_branch).opcode, AArch64Opcode::B);
        assert_eq!(
            func.inst(ids.latch_branch).operands,
            vec![block(copy_block)]
        );
        assert_eq!(func.block(ids.latch).succs, vec![copy_block]);
    }

    struct RotatedSwapLoopIds {
        header: BlockId,
        swap: BlockId,
        cont: BlockId,
        latch: BlockId,
        exit: BlockId,
        cont_cmp: InstId,
        cont_bcond: InstId,
        latch_mov: InstId,
        swap_branch: InstId,
    }

    /// Bubblesort's rotated inner-loop shape: a header diamond whose swap arm
    /// reaches the pure latch chain (cont: cmp+b.cond exit; latch: carrier mov
    /// + backedge) only through an unconditional `B`.
    fn make_rotated_swap_loop() -> (MachFunction, RotatedSwapLoopIds) {
        let mut func = MachFunction::new("rotated".to_string(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let header = func.create_block();
        let swap = func.create_block();
        let cont = func.create_block();
        let latch = func.create_block();
        let exit = func.create_block();

        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::B, vec![block(header)]),
        );

        push(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::LdrRI, vec![vreg(20), vreg(1), imm(0)]),
        );
        push(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(20), vreg(21)]),
        );
        push(
            &mut func,
            header,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![imm(CondCode::GT.encoding() as i64), block(swap)],
            ),
        );
        push(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::B, vec![block(cont)]),
        );

        push(
            &mut func,
            swap,
            MachInst::new(AArch64Opcode::StrRI, vec![vreg(20), vreg(1), imm(0)]),
        );
        let swap_branch = push(
            &mut func,
            swap,
            MachInst::new(AArch64Opcode::B, vec![block(cont)]),
        );

        let cont_cmp = push(
            &mut func,
            cont,
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(2), vreg(3)]),
        );
        let cont_bcond = push(
            &mut func,
            cont,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![imm(CondCode::EQ.encoding() as i64), block(exit)],
            ),
        );
        push(
            &mut func,
            cont,
            MachInst::new(AArch64Opcode::B, vec![block(latch)]),
        );

        let latch_mov = push(
            &mut func,
            latch,
            MachInst::new(AArch64Opcode::MovR, vec![vreg(0), vreg(2)]),
        );
        push(
            &mut func,
            latch,
            MachInst::new(AArch64Opcode::B, vec![block(header)]),
        );

        push(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        func.add_edge(entry, header);
        func.add_edge(header, swap);
        func.add_edge(header, cont);
        func.add_edge(swap, cont);
        func.add_edge(cont, exit);
        func.add_edge(cont, latch);
        func.add_edge(latch, header);

        (
            func,
            RotatedSwapLoopIds {
                header,
                swap,
                cont,
                latch,
                exit,
                cont_cmp,
                cont_bcond,
                latch_mov,
                swap_branch,
            },
        )
    }

    #[test]
    fn tail_duplicates_pure_latch_chain_into_branching_pred() {
        let (mut func, ids) = make_rotated_swap_loop();

        assert!(run_pass(&mut func));

        // The swap arm now owns a clone of the whole chain: its stores, then
        // cmp + conditional exit + carrier writeback + backedge.
        let swap_ops: Vec<_> = func
            .block(ids.swap)
            .insts
            .iter()
            .map(|&id| func.inst(id).opcode)
            .collect();
        assert_eq!(
            swap_ops,
            vec![
                AArch64Opcode::StrRI,
                AArch64Opcode::CmpRR,
                AArch64Opcode::BCond,
                AArch64Opcode::MovR,
                AArch64Opcode::B
            ]
        );
        // Cloned operands are identical (targets included); the terminating
        // branch was retargeted in place at the header.
        let swap_insts = &func.block(ids.swap).insts;
        assert_eq!(
            func.inst(swap_insts[1]).operands,
            func.inst(ids.cont_cmp).operands
        );
        assert_eq!(
            func.inst(swap_insts[2]).operands,
            vec![imm(CondCode::EQ.encoding() as i64), block(ids.exit)]
        );
        assert_eq!(
            func.inst(swap_insts[3]).operands,
            func.inst(ids.latch_mov).operands
        );
        assert_eq!(func.inst(ids.swap_branch).operands, vec![block(ids.header)]);

        // CFG: swap exits where the chain exited and takes the backedge itself.
        assert_eq!(func.block(ids.swap).succs, vec![ids.exit, ids.header]);
        assert_eq!(func.block(ids.cont).preds, vec![ids.header]);
        assert!(func.block(ids.header).preds.contains(&ids.swap));
        assert!(func.block(ids.exit).preds.contains(&ids.swap));

        // The original chain is untouched for the fall-through path.
        let cont_ops: Vec<_> = func
            .block(ids.cont)
            .insts
            .iter()
            .map(|&id| func.inst(id).opcode)
            .collect();
        assert_eq!(
            cont_ops,
            vec![AArch64Opcode::CmpRR, AArch64Opcode::BCond, AArch64Opcode::B]
        );
        let latch_ops: Vec<_> = func
            .block(ids.latch)
            .insts
            .iter()
            .map(|&id| func.inst(id).opcode)
            .collect();
        assert_eq!(latch_ops, vec![AArch64Opcode::MovR, AArch64Opcode::B]);
    }

    #[test]
    fn taildup_rejects_impure_chain() {
        let (mut func, ids) = make_rotated_swap_loop();
        // A store in the chain makes it impure: duplication is refused.
        let store = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg(2), vreg(1), imm(0)],
        ));
        func.block_mut(ids.cont).insts.insert(0, store);

        assert!(!run_pass(&mut func));
        assert_eq!(func.inst(ids.swap_branch).operands, vec![block(ids.cont)]);
        assert_eq!(func.block(ids.swap).succs, vec![ids.cont]);
    }

    #[test]
    fn taildup_rejects_single_pred_chain_head() {
        let (mut func, ids) = make_rotated_swap_loop();
        // Make the header bypass `cont` (jump straight to the latch), leaving
        // the swap arm as the chain head's ONLY predecessor: nothing to
        // deduplicate, the chain would merely be moved.
        let header_b = *func.block(ids.header).insts.last().unwrap();
        func.inst_mut(header_b).operands = vec![block(ids.latch)];
        func.block_mut(ids.header).succs = vec![ids.swap, ids.latch];
        func.block_mut(ids.cont)
            .preds
            .retain(|&pred| pred != ids.header);
        func.block_mut(ids.latch).preds.push(ids.header);

        assert!(!run_pass(&mut func));
        assert_eq!(func.inst(ids.swap_branch).operands, vec![block(ids.cont)]);
    }

    #[test]
    fn taildup_rejects_phi_in_bcond_target() {
        let (mut func, ids) = make_rotated_swap_loop();
        let phi = func.push_inst(MachInst::new(
            AArch64Opcode::Phi,
            vec![vreg(9), vreg(2), block(ids.cont)],
        ));
        func.block_mut(ids.exit).insts.insert(0, phi);

        assert!(!run_pass(&mut func));
        assert_eq!(func.inst(ids.swap_branch).operands, vec![block(ids.cont)]);
    }

    #[test]
    fn taildup_records_clone_provenance() {
        let (mut func, ids) = make_rotated_swap_loop();
        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(20), &[ids.cont_cmp], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(21), &[ids.cont_bcond], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(22), &[ids.latch_mov], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(23), &[ids.swap_branch], PassId::new("isel"));

        let mut pass = LoopLatchLayoutCombine;
        assert!(pass.run_with_provenance(&mut func, &mut provenance));

        let swap_insts = func.block(ids.swap).insts.clone();
        let cloned_cmp_entry = provenance.get_entry(swap_insts[1]).unwrap();
        assert_eq!(cloned_cmp_entry.trust_ir_origins, vec![TrustIrInstId(20)]);
        assert_eq!(
            cloned_cmp_entry.transforms.last().unwrap().kind,
            TransformKind::Cloned {
                source: ids.cont_cmp
            }
        );
        let cloned_mov_entry = provenance.get_entry(swap_insts[3]).unwrap();
        assert_eq!(
            cloned_mov_entry.transforms.last().unwrap().kind,
            TransformKind::Cloned {
                source: ids.latch_mov
            }
        );
        let branch_entry = provenance.get_entry(ids.swap_branch).unwrap();
        assert_eq!(
            branch_entry.transforms.last().unwrap().kind,
            TransformKind::Survived
        );
    }

    #[test]
    fn preserves_source_loc_and_updates_provenance() {
        let (mut func, ids) = make_counted_loop();
        let cmp_loc = source_loc(17);
        let branch_loc = source_loc(29);
        func.inst_mut(ids.cmp).source_loc = Some(cmp_loc);
        func.inst_mut(ids.latch_branch).source_loc = Some(branch_loc);

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(10), &[ids.cmp], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(11), &[ids.cset], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(12), &[ids.branch], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(13), &[ids.latch_branch], PassId::new("isel"));

        let mut pass = LoopLatchLayoutCombine;
        assert!(pass.run_with_provenance(&mut func, &mut provenance));

        let new_latch = next_block(&func, ids.latch).expect("split latch after body");
        let latch_cmp_id = func
            .block(new_latch)
            .insts
            .iter()
            .copied()
            .find(|&id| func.inst(id).opcode == AArch64Opcode::CmpRR)
            .expect("cloned latch compare");
        let new_latch_branch_id = *func.block(new_latch).insts.last().unwrap();
        assert_eq!(func.inst(latch_cmp_id).source_loc, Some(cmp_loc));
        assert_eq!(func.inst(ids.latch_branch).source_loc, Some(branch_loc));
        assert_eq!(func.inst(new_latch_branch_id).source_loc, Some(branch_loc));

        let latch_cmp_entry = provenance.get_entry(latch_cmp_id).unwrap();
        assert_eq!(latch_cmp_entry.trust_ir_origins, vec![TrustIrInstId(10)]);
        let clone_record = latch_cmp_entry.transforms.last().unwrap();
        assert_eq!(clone_record.pass, PassId::new("loop-latch-layout"));
        assert_eq!(clone_record.kind, TransformKind::Cloned { source: ids.cmp });

        let branch_entry = provenance.get_entry(ids.latch_branch).unwrap();
        assert_eq!(
            branch_entry.transforms.last().unwrap().kind,
            TransformKind::Survived
        );

        let latch_branch_entry = provenance.get_entry(new_latch_branch_id).unwrap();
        assert_eq!(latch_branch_entry.trust_ir_origins, vec![TrustIrInstId(13)]);
        assert_eq!(
            latch_branch_entry.transforms.last().unwrap().kind,
            TransformKind::Cloned {
                source: ids.latch_branch
            }
        );

        let cset_entry = provenance.get_entry(ids.cset).unwrap();
        match &cset_entry.status {
            ProvenanceStatus::OptimizedAway {
                pass,
                justification,
            } => {
                assert_eq!(pass.name(), "loop-latch-layout");
                assert!(justification.contains("materialized loop predicate"));
            }
            other => panic!("expected optimized-away cset provenance, got {other:?}"),
        }
    }

    // ---- Tier 3a: inverted-guard two-block rotation (fib2 shape) ----

    struct CaseBLoopIds {
        entry: BlockId,
        header: BlockId,
        exit: BlockId,
        body: BlockId,
        exit_bcond: InstId,
        body_branch: InstId,
        carrier: InstId,
    }

    /// fib2's shape: a two-block loop whose header is an inverted zero-trip
    /// guard `cmp; b.cond EXIT; b BODY`, with the exit laid out BEFORE the body
    /// (so tier 1's exit-follows-latch precondition is not met).
    fn make_case_b_loop() -> (MachFunction, CaseBLoopIds) {
        let mut func = MachFunction::new("caseb".to_string(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let header = func.create_block();
        let exit = func.create_block();
        let body = func.create_block();

        // entry: iv := 10; b header
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Movz, vec![vreg(0), imm(10)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::B, vec![block(header)]),
        );

        // header: cmp iv, #2 ; b.lo exit ; b body
        push(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::CmpRI, vec![vreg(1), imm(2)]),
        );
        let exit_bcond = push(
            &mut func,
            header,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![imm(CondCode::LO.encoding() as i64), block(exit)],
            ),
        );
        let body_branch = push(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::B, vec![block(body)]),
        );

        // exit: ret
        push(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        // body: iv.next := iv - 1 ; iv := iv.next ; b header
        push(
            &mut func,
            body,
            MachInst::new(AArch64Opcode::SubRI, vec![vreg(2), vreg(1), imm(1)]),
        );
        let carrier = push(
            &mut func,
            body,
            MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(2)]),
        );
        push(
            &mut func,
            body,
            MachInst::new(AArch64Opcode::B, vec![block(header)]),
        );

        func.add_edge(entry, header);
        func.add_edge(header, exit);
        func.add_edge(header, body);
        func.add_edge(body, header);

        (
            func,
            CaseBLoopIds {
                entry,
                header,
                exit,
                body,
                exit_bcond,
                body_branch,
                carrier,
            },
        )
    }

    #[test]
    fn rotates_inverted_guard_two_block_loop() {
        let (mut func, ids) = make_case_b_loop();

        assert!(run_pass(&mut func));

        // Header keeps its own zero-trip guard, untouched.
        let header_ops: Vec<_> = func
            .block(ids.header)
            .insts
            .iter()
            .map(|&id| func.inst(id).opcode)
            .collect();
        assert_eq!(
            header_ops,
            vec![AArch64Opcode::CmpRI, AArch64Opcode::BCond, AArch64Opcode::B]
        );
        assert_eq!(
            func.inst(ids.exit_bcond).operands,
            vec![imm(CondCode::LO.encoding() as i64), block(ids.exit)]
        );
        assert_eq!(func.inst(ids.body_branch).operands, vec![block(ids.body)]);
        assert_eq!(func.block(ids.header).preds, vec![ids.entry]);

        // The body's carrier copy moved out; its backedge now feeds a split latch.
        let new_latch = next_block(&func, ids.body).expect("split latch after body");
        assert_ne!(new_latch, ids.exit);
        assert!(!func.block(ids.body).insts.contains(&ids.carrier));
        let body_ops: Vec<_> = func
            .block(ids.body)
            .insts
            .iter()
            .map(|&id| func.inst(id).opcode)
            .collect();
        assert_eq!(body_ops, vec![AArch64Opcode::SubRI, AArch64Opcode::B]);
        assert_eq!(func.block(ids.body).succs, vec![new_latch]);

        // The split latch re-tests on the updated iv with the CONTINUE condition
        // (inverse of the exit condition), back-edges to the body, and branches
        // to the exit.
        let latch_ops: Vec<_> = func
            .block(new_latch)
            .insts
            .iter()
            .map(|&id| func.inst(id).opcode)
            .collect();
        assert_eq!(
            latch_ops,
            vec![
                AArch64Opcode::AddRI, // hardened carrier copy
                AArch64Opcode::CmpRI,
                AArch64Opcode::BCond,
                AArch64Opcode::B,
            ]
        );
        let latch_insts = &func.block(new_latch).insts;
        // Continue condition = LO.invert() = HS, targeting the body.
        assert_eq!(
            func.inst(latch_insts[2]).operands,
            vec![imm(CondCode::HS.encoding() as i64), block(ids.body)]
        );
        assert_eq!(func.inst(latch_insts[3]).operands, vec![block(ids.exit)]);
        assert_eq!(func.block(new_latch).succs, vec![ids.body, ids.exit]);
        assert!(func.block(ids.exit).preds.contains(&new_latch));
    }

    #[test]
    fn case_b_rejects_shared_exit() {
        let (mut func, ids) = make_case_b_loop();
        // Give the exit a second predecessor: rotation must fail-closed because
        // the split latch would become a second predecessor of a shared exit.
        let other = func.create_block();
        push(
            &mut func,
            other,
            MachInst::new(AArch64Opcode::B, vec![block(ids.exit)]),
        );
        func.add_edge(func.entry, other);
        func.add_edge(other, ids.exit);

        assert!(!run_pass(&mut func));
        assert_eq!(func.inst(ids.body_branch).operands, vec![block(ids.body)]);
        assert!(func.block(ids.body).insts.contains(&ids.carrier));
    }

    // ---- Tier 3b: test-only-header duplication (ackermann shape) ----

    struct TestHeaderLoopIds {
        entry: BlockId,
        header: BlockId,
        exit: BlockId,
        body: BlockId,
        latch_a: BlockId,
        latch_b: BlockId,
        header_cbz: InstId,
        latch_a_branch: InstId,
        latch_b_branch: InstId,
    }

    /// ackermann's shape: a pure test-only `cbz iv, EXIT` header with TWO
    /// backedge predecessors (two latches), neither of which is the body-entry.
    fn make_test_only_header_loop() -> (MachFunction, TestHeaderLoopIds) {
        let mut func = MachFunction::new("testhdr".to_string(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let header = func.create_block();
        let exit = func.create_block();
        let body = func.create_block();
        let latch_a = func.create_block();
        let latch_b = func.create_block();

        // entry: iv := 5 ; one := 1 ; b header
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Movz, vec![vreg(0), imm(5)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(0)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::Movz, vec![vreg(9), imm(1)]),
        );
        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::B, vec![block(header)]),
        );

        // header (test-only): cbz iv, exit ; b body
        let header_cbz = push(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::Cbz, vec![vreg(2), block(exit)]),
        );
        push(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::B, vec![block(body)]),
        );

        // exit: ret
        push(&mut func, exit, MachInst::new(AArch64Opcode::Ret, vec![]));

        // body: iv.next := iv - 1 ; cbnz cond, latch_a ; b latch_b
        push(
            &mut func,
            body,
            MachInst::new(AArch64Opcode::SubRI, vec![vreg(3), vreg(2), imm(1)]),
        );
        push(
            &mut func,
            body,
            MachInst::new(AArch64Opcode::Cbnz, vec![vreg(9), block(latch_a)]),
        );
        push(
            &mut func,
            body,
            MachInst::new(AArch64Opcode::B, vec![block(latch_b)]),
        );

        // latch_a: iv := iv.next ; b header
        push(
            &mut func,
            latch_a,
            MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]),
        );
        let latch_a_branch = push(
            &mut func,
            latch_a,
            MachInst::new(AArch64Opcode::B, vec![block(header)]),
        );

        // latch_b: iv := iv.next ; b header
        push(
            &mut func,
            latch_b,
            MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]),
        );
        let latch_b_branch = push(
            &mut func,
            latch_b,
            MachInst::new(AArch64Opcode::B, vec![block(header)]),
        );

        func.add_edge(entry, header);
        func.add_edge(header, exit);
        func.add_edge(header, body);
        func.add_edge(body, latch_a);
        func.add_edge(body, latch_b);
        func.add_edge(latch_a, header);
        func.add_edge(latch_b, header);

        (
            func,
            TestHeaderLoopIds {
                entry,
                header,
                exit,
                body,
                latch_a,
                latch_b,
                header_cbz,
                latch_a_branch,
                latch_b_branch,
            },
        )
    }

    #[test]
    fn duplicates_test_only_header_into_latches() {
        let (mut func, ids) = make_test_only_header_loop();

        assert!(run_pass(&mut func));

        // The header survives only as the one-time entry guard.
        assert_eq!(func.block(ids.header).preds, vec![ids.entry]);
        let header_ops: Vec<_> = func
            .block(ids.header)
            .insts
            .iter()
            .map(|&id| func.inst(id).opcode)
            .collect();
        assert_eq!(header_ops, vec![AArch64Opcode::Cbz, AArch64Opcode::B]);

        // Each latch gained a clone of the header test and back-edges to the
        // body while exiting exactly where the header exited.
        for (latch, branch) in [
            (ids.latch_a, ids.latch_a_branch),
            (ids.latch_b, ids.latch_b_branch),
        ] {
            let ops: Vec<_> = func
                .block(latch)
                .insts
                .iter()
                .map(|&id| func.inst(id).opcode)
                .collect();
            assert_eq!(
                ops,
                vec![AArch64Opcode::MovR, AArch64Opcode::Cbz, AArch64Opcode::B]
            );
            let insts = &func.block(latch).insts;
            // Cloned cbz targets the exit; the reused branch now targets the body.
            assert_eq!(
                func.inst(insts[1]).operands,
                func.inst(ids.header_cbz).operands
            );
            assert_eq!(func.inst(branch).operands, vec![block(ids.body)]);
            assert_eq!(func.block(latch).succs, vec![ids.body, ids.exit]);
            assert!(func.block(ids.exit).preds.contains(&latch));
            assert!(func.block(ids.body).preds.contains(&latch));
        }
    }

    #[test]
    fn test_only_header_rejects_value_producing_header() {
        let (mut func, ids) = make_test_only_header_loop();
        // Insert a value-defining instruction into the header: cloning it into
        // every latch would create multiple definitions, so rotation must bail.
        let extra = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(20), vreg(2), imm(1)],
        ));
        func.block_mut(ids.header).insts.insert(0, extra);

        assert!(!run_pass(&mut func));
        assert_eq!(
            func.inst(ids.latch_a_branch).operands,
            vec![block(ids.header)]
        );
        assert_eq!(
            func.inst(ids.latch_b_branch).operands,
            vec![block(ids.header)]
        );
    }
    /// b1_mispredict's RNG while-loop shape: multi-block body, header =
    /// carrier copy + CmpRR + BCond(body) + B(exit) (the INVERTED
    /// orientation), single latch ending `b header`. Tier 3b must rotate:
    /// clone the test (with a renamed carrier temp) into the latch and
    /// retarget its terminal to the exit.
    #[test]
    fn rotates_multiblock_while_loop_with_carrier_copy_header() {
        // The extended rotation is default-on (kill switch
        // TCG_NO_LOOP_ROTATE_EXT); nothing in this binary sets it, so the
        // test exercises the production default.
        let mut func = MachFunction::new("b1shape".to_string(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let header = func.create_block();
        let body = func.create_block();
        let latch = func.create_block();
        let exit = func.create_block();
        func.next_vreg = 100;

        push(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::B, vec![block(header)]),
        );

        // header: MovR t, iv ; CmpRR t, n ; BCond cc -> body ; B exit
        push(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::MovR, vec![vreg(12), vreg(9)]),
        );
        push(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(12), vreg(1)]),
        );
        push(
            &mut func,
            header,
            MachInst::new(
                AArch64Opcode::BCond,
                vec![imm(CondCode::LO.encoding() as i64), block(body)],
            ),
        );
        push(
            &mut func,
            header,
            MachInst::new(AArch64Opcode::B, vec![block(exit)]),
        );

        // body: enough arithmetic to clear MIN_EXTENDED_ROTATE_LOOP_INSTS
        // (the profitability floor), then fall to latch.
        for k in 0..14u32 {
            push(
                &mut func,
                body,
                MachInst::new(AArch64Opcode::EorRR, vec![vreg(20 + k), vreg(9), vreg(1)]),
            );
        }
        push(
            &mut func,
            body,
            MachInst::new(AArch64Opcode::B, vec![block(latch)]),
        );

        // latch: iv update, b header
        push(
            &mut func,
            latch,
            MachInst::new(AArch64Opcode::AddRI, vec![vreg(9), vreg(9), imm(1)]),
        );
        let latch_b = push(
            &mut func,
            latch,
            MachInst::new(AArch64Opcode::B, vec![block(header)]),
        );

        func.add_edge(entry, header);
        func.add_edge(header, body);
        func.add_edge(header, exit);
        func.add_edge(body, latch);
        func.add_edge(latch, header);

        let changed = run_loop_latch_layout_combine(&mut func, None, true);
        assert!(changed, "tier 3b must rotate the inverted-orientation loop");

        // The latch's terminal must now target the EXIT (fallthrough-out), and
        // a cloned BCond -> body must precede it as the rotated backedge.
        let term = func.inst(latch_b);
        assert_eq!(term.opcode, AArch64Opcode::B);
        assert_eq!(
            branch_target(term),
            Some(exit),
            "terminal retargeted to exit"
        );
        let latch_insts = &func.block(latch).insts;
        let cloned_bcond = latch_insts
            .iter()
            .filter(|&&id| func.inst(id).opcode == AArch64Opcode::BCond)
            .count();
        assert_eq!(cloned_bcond, 1, "cloned conditional backedge present");
        // CFG: latch no longer feeds the header.
        assert!(!func.block(latch).succs.contains(&header));
        assert!(func.block(latch).succs.contains(&body));
        assert!(func.block(latch).succs.contains(&exit));
        // The cloned carrier copy must define a FRESH vreg, not vreg 12.
        let clone_movs: Vec<_> = latch_insts
            .iter()
            .filter(|&&id| func.inst(id).opcode == AArch64Opcode::MovR)
            .collect();
        assert_eq!(clone_movs.len(), 1, "carrier copy cloned once");
        let mov = func.inst(*clone_movs[0]);
        let MachOperand::VReg(d) = &mov.operands[0] else {
            panic!()
        };
        assert_ne!(d.id, 12, "cloned carrier dest renamed to a fresh vreg");
    }
}
