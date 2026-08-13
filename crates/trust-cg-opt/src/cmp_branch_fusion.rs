// trust-cg-opt - AArch64 Compare-and-Branch Fusion
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! AArch64 compare-and-branch fusion pass.
//!
//! Fuses separate compare/test + conditional branch instruction pairs into
//! single combined compare-and-branch instructions, reducing code size and
//! improving branch prediction on AArch64.
//!
//! # Patterns
//!
//! | Pattern | Transformation |
//! |---------|---------------|
//! | `CMP Rn, #0` + `B.EQ target` | `CBZ Rn, target` |
//! | `CMP Rn, #0` + `B.NE target` | `CBNZ Rn, target` |
//! | `TST Rn, #(1<<bit)` + `B.EQ target` | `TBZ Rn, #bit, target` |
//! | `TST Rn, #(1<<bit)` + `B.NE target` | `TBNZ Rn, #bit, target` |
//! | `CSET Rd, cc` + `...` + `CBNZ Rd, target` | `...` + `B.cc target` |
//! | `CSET Rd, cc` + `...` + `CBZ Rd, target` | `...` + `B.!cc target` |
//! | `LSL m, #1, amt; AND t, w, m; CBZ t` | `LSR t, w, amt; TBZ t, #0, target` |
//! | `LSL m, #1, amt; AND t, w, m; CBNZ t` | `LSR t, w, amt; TBNZ t, #0, target` |
//!
//! The last two rows are the VARIABLE single-bit test `w & (1 << amt)`
//! (nsieve-bits' `BTEST(p, x)` macro): instead of materializing the one-bit
//! mask and testing the AND result against zero, shift the tested WORD right
//! by the amount and test bit 0 — one instruction and one register (the
//! constant `1`) fewer, exactly what clang emits. SOUND for EVERY `amt`
//! because LSLV and LSRV both take the amount mod the register width in
//! hardware (`Rd = Rn <shift> (Rm & (width-1))`, modeled faithfully by
//! `encode_lsl_rr_masked`/`encode_lsr_rr_masked` in
//! `trust-cg-verify/src/aarch64_semantics.rs`): bit 0 of `w >> (amt mod W)`
//! IS bit `(amt mod W)` of `w`, the single bit `1 << (amt mod W)` selects.
//! See `try_fuse_single_bit_test_branch` for the fail-closed conditions.
//! Kill switch: `TCG_NO_BIT_TEST_BRANCH_FUSE`.
//!
//! # Safety Constraints
//!
//! - The CMP/TST and BCond must be consecutive in the basic block (no
//!   intervening flag-setting instructions).
//! - After fusion, the CMP/TST instruction is removed (it is dead because
//!   the fused instruction encodes the comparison implicitly).
//! - CBZ/CBNZ only works with compare-to-zero; non-zero immediate comparisons
//!   are not fusible.
//! - TBZ/TBNZ only works with TST against a single-bit mask (power of 2).
//! - The deferred `CSET + ... + CBZ/CBNZ` collapse requires the CSET result
//!   to be single-use, both instructions in the same block, and every
//!   intervening instruction provably NZCV-transparent (see
//!   `may_clobber_nzcv`) — the CSET captured the flags, and the rewritten
//!   `B.cc` re-reads them at the branch point, so the flags must be
//!   byte-identical at both points. Any doubt fails closed.
//!
//! # Relationship to Other Passes
//!
//! - The declarative `rewrite` framework handles single-instruction simplifications (e.g., `add x0, x1, #0` -> `mov`).
//! - `cmp_select.rs` handles diamond CFG patterns -> CSEL/CSET.
//! - This pass handles linear CMP/TST + BCond fusion -> CBZ/CBNZ/TBZ/TBNZ.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, BlockId, CondCode, InstFlags, InstId, MachFunction, MachInst, MachOperand,
    PassId, ProvenanceMap, VReg, regs::RegClass,
};

use crate::dom::DomTree;
use crate::pass_manager::{AnalysisCache, MachinePass};

/// AArch64 compare-and-branch fusion pass.
pub struct CmpBranchFusion;

impl MachinePass for CmpBranchFusion {
    fn name(&self) -> &str {
        "cmp-branch-fusion"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_cmp_branch_fusion(func, None, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_cmp_branch_fusion(func, None, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        // The dominator tree lets the single-bit test fusion accept a `#1`
        // constant materialized in a dominating block (the hoisted
        // loop-invariant `mov w, #1` shape). None of the fusions in this pass
        // change the CFG (branch targets, edges and blocks are preserved), so
        // the tree stays valid across every internal sweep.
        let dom = analyses.domtree(func);
        run_cmp_branch_fusion(func, Some(dom), Some(provenance))
    }
}

/// Drive [`cmp_branch_fusion_sweep`] to a fixpoint.
///
/// A single sweep can only make one fusion decision per instruction window, but
/// the two families compose: the imported-O0 shape `cmp; cset b, cc; cmp b, #0;
/// b.ne` first collapses (via [`try_fuse_cset_bool_branch`]) to `cmp Rn, #0;
/// b.cc`, and only THEN — on the next sweep — can `cmp Rn, #0 + b.eq/b.ne` fuse
/// to `CBZ/CBNZ` ([`try_fuse_cbz`]). The machine pipeline runs this pass with
/// `run_once` at `O1/O2/Os` (only `O3` iterates to a fixpoint), so without this
/// internal loop every `if (x == 0)` / `if (x != 0)` would keep a separate
/// `CMP #0` + `B.cond` pair at `O2` instead of the fused compare-and-branch.
/// Each sweep that reports `changed` strictly deletes at least one instruction,
/// so the loop is monotone and terminates; the cap is a defensive belt.
fn run_cmp_branch_fusion(
    func: &mut MachFunction,
    dom: Option<&DomTree>,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let mut any = false;
    // Bounded by the block instruction count (each productive sweep removes an
    // instruction); a small constant covers the compose depth (cset→cbz = 2).
    for _ in 0..16 {
        if cmp_branch_fusion_sweep(func, dom, provenance.as_deref_mut()) {
            any = true;
        } else {
            break;
        }
    }
    any
}

fn cmp_branch_fusion_sweep(
    func: &mut MachFunction,
    dom: Option<&DomTree>,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    let mut changed = false;
    let mut to_delete: HashSet<InstId> = HashSet::new();
    let mut fused_groups: Vec<FusedProvenance> = Vec::new();
    let use_counts = collect_vreg_uses(func);
    let cset_collapse_enabled = cset_branch_collapse_enabled();
    let bit_test_enabled = bit_test_branch_fuse_enabled();
    // Unique materialized-constant defs, for the single-bit test fusion's
    // `#1` operand. Computed once per sweep; the sweep's own rewrites never
    // add a def of an existing vreg nor delete a `MovI`/`Movz`, so the map
    // stays conservative (entries only ever OVER-approximate the def count).
    let unique_consts = if bit_test_enabled {
        Some(collect_unique_const_defs(func))
    } else {
        None
    };

    for block_id in func.block_order.clone() {
        let block = func.block(block_id);
        let insts = block.insts.clone();

        // Sliding window of consecutive pairs and imported-O0 boolean branches.
        if insts.len() < 2 {
            continue;
        }

        for window in insts.windows(4) {
            let flag_id = window[0];
            let cset_id = window[1];
            let cmp_zero_id = window[2];
            let bcond_id = window[3];

            if to_delete.contains(&flag_id)
                || to_delete.contains(&cset_id)
                || to_delete.contains(&cmp_zero_id)
            {
                continue;
            }

            let flag_inst = func.inst(flag_id);
            let cset_inst = func.inst(cset_id);
            let cmp_zero_inst = func.inst(cmp_zero_id);
            let bcond_inst = func.inst(bcond_id);

            if !sets_flags(flag_inst.opcode) {
                continue;
            }

            if let Some(mut fused) =
                try_fuse_cset_bool_branch(cset_inst, cmp_zero_inst, bcond_inst, &use_counts)
            {
                fused.source_loc = bcond_inst
                    .source_loc
                    .or(cmp_zero_inst.source_loc)
                    .or(cset_inst.source_loc)
                    .or(flag_inst.source_loc);
                *func.inst_mut(bcond_id) = fused;
                to_delete.insert(cset_id);
                to_delete.insert(cmp_zero_id);
                fused_groups.push(FusedProvenance {
                    consumed_sources: vec![cset_id, cmp_zero_id, bcond_id],
                    live_sources: vec![flag_id],
                    merged: bcond_id,
                });
                changed = true;
            }
        }

        for i in 0..insts.len() - 1 {
            let cmp_id = insts[i];
            let bcond_id = insts[i + 1];

            // Skip if the CMP is already marked for deletion.
            if to_delete.contains(&cmp_id) {
                continue;
            }

            let cmp_inst = func.inst(cmp_id);
            let bcond_inst = func.inst(bcond_id);

            // Second instruction must be BCond.
            if bcond_inst.opcode != AArch64Opcode::BCond {
                continue;
            }

            // Decode BCond operands: [Imm(cond_encoding), Block(target)]
            if bcond_inst.operands.len() < 2 {
                continue;
            }
            let cond_encoding = match bcond_inst.operands[0].as_imm() {
                Some(v) => v as u8,
                None => continue,
            };
            let target = match &bcond_inst.operands[1] {
                MachOperand::Block(bid) => *bid,
                _ => continue,
            };
            let cond = match decode_cond(cond_encoding) {
                Some(c) => c,
                None => continue,
            };

            // First instruction must be a flag-setting instruction.
            if !sets_flags(cmp_inst.opcode) {
                continue;
            }

            // Try CBZ/CBNZ fusion (compare-immediate Rn, #0).
            if let Some(mut fused) = try_fuse_cbz(cmp_inst, cond, target) {
                fused.source_loc = bcond_inst.source_loc.or(cmp_inst.source_loc);
                *func.inst_mut(bcond_id) = fused;
                to_delete.insert(cmp_id);
                fused_groups.push(FusedProvenance {
                    consumed_sources: vec![cmp_id, bcond_id],
                    live_sources: Vec::new(),
                    merged: bcond_id,
                });
                changed = true;
                continue;
            }

            // Try TBZ/TBNZ fusion (Tst Rn, #(1<<bit)).
            if let Some(mut fused) = try_fuse_tbz(cmp_inst, cond, target) {
                fused.source_loc = bcond_inst.source_loc.or(cmp_inst.source_loc);
                *func.inst_mut(bcond_id) = fused;
                to_delete.insert(cmp_id);
                fused_groups.push(FusedProvenance {
                    consumed_sources: vec![cmp_id, bcond_id],
                    live_sources: Vec::new(),
                    merged: bcond_id,
                });
                changed = true;
                continue;
            }
        }

        // Deferred CSET-then-branch collapse: `CSET Rd, cc; ...; CBNZ Rd`
        // becomes `...; B.cc` (CBZ inverts). The CSET and the branch need
        // NOT be adjacent — the CSET captured NZCV, and as long as no
        // intervening instruction can clobber the flags, `B.cc` at the
        // branch point reads the exact flag state the CSET observed.
        // Kill switch: `TCG_NO_CSET_BRANCH_COLLAPSE`.
        if cset_collapse_enabled {
            for (branch_idx, &branch_id) in insts.iter().enumerate() {
                if to_delete.contains(&branch_id) {
                    continue;
                }
                if let Some(collapse) = try_collapse_deferred_cset_branch(
                    func,
                    &insts,
                    branch_idx,
                    &use_counts,
                    &to_delete,
                ) {
                    *func.inst_mut(branch_id) = collapse.fused;
                    to_delete.insert(collapse.cset_id);
                    fused_groups.push(FusedProvenance {
                        consumed_sources: vec![collapse.cset_id, branch_id],
                        live_sources: collapse.live_flag_writer.into_iter().collect(),
                        merged: branch_id,
                    });
                    changed = true;
                }
            }
        }

        // Variable single-bit test: `LSL m, one(#1), amt; AND t, w, m;
        // CBZ/CBNZ t` -> `LSR t, w, amt; TBZ/TBNZ t, #0`. Runs after the
        // pair loops so it composes with the CBZ formation above within the
        // sweep-fixpoint (`CmpRI #0 + B.EQ` becomes `CBZ` first, then this
        // triple matches on a later pass over the block). Adjacency is
        // required on the LIVE instruction sequence (slots consumed by
        // earlier fusions this sweep no longer execute).
        // Kill switch: `TCG_NO_BIT_TEST_BRANCH_FUSE`.
        if bit_test_enabled && let Some(unique_consts) = unique_consts.as_ref() {
            let live: Vec<InstId> = insts
                .iter()
                .copied()
                .filter(|id| !to_delete.contains(id))
                .collect();
            for i in 0..live.len().saturating_sub(2) {
                let lsl_id = live[i];
                let and_id = live[i + 1];
                let branch_id = live[i + 2];
                if to_delete.contains(&lsl_id) {
                    // Consumed by a fusion earlier in THIS loop.
                    continue;
                }
                if let Some(fusion) = try_fuse_single_bit_test_branch(
                    func,
                    lsl_id,
                    and_id,
                    branch_id,
                    &live[..i],
                    block_id,
                    &use_counts,
                    unique_consts,
                    dom,
                ) {
                    *func.inst_mut(and_id) = fusion.lsr;
                    *func.inst_mut(branch_id) = fusion.tb;
                    to_delete.insert(lsl_id);
                    if let Some(provenance) = provenance.as_deref_mut() {
                        // The AND slot survives, rewritten in place to the LSR.
                        provenance
                            .record_in_place_transform(and_id, PassId::new("cmp-branch-fusion"));
                    }
                    fused_groups.push(FusedProvenance {
                        consumed_sources: vec![lsl_id, branch_id],
                        live_sources: vec![and_id],
                        merged: branch_id,
                    });
                    changed = true;
                }
            }
        }
    }

    // ------------------------------------------------------------------
    // Cross-block redundant compare elimination (the three-way comparator
    // `if (n > v) ... else if (n < v) ...`). The two identical `cmp n, v`
    // land in DIFFERENT blocks: one at the tail of a dominating block A
    // (`cmp; b.gt`) and one at the head of its single-successor branch's
    // fall-through block B (`cmp; b.lt`). clang reuses NZCV
    // (`cmp; b.gt; b.mi`); GVN skips NZCV for soundness and the same-block
    // redundant-compare peephole cannot reach across the edge. When A is
    // B's ONLY predecessor, A's compare is the LAST flag writer in A
    // (everything after it — including the terminator branch — provably
    // NZCV-transparent), B's compare is the FIRST flag writer in B
    // (everything before it NZCV-transparent), the two compares are
    // IDENTICAL (same opcode AND operands) and neither source register is
    // redefined on the connecting path, then B's compare recomputes the
    // exact NZCV that A produced — it is dead. Delete it and let B's
    // conditional branch reuse A's flags.
    //
    // Runs AFTER the cset/cmp-#0 collapse loops above so that a block whose
    // branch was materialized via `cset` has already been folded back to a
    // live `cmp; ...; b.cc` tail (A leaves live NZCV). Kill switch:
    // `TCG_NO_CROSS_BLOCK_CMP_ELIM`.
    if cross_block_cmp_elim_enabled() {
        for block_b in func.block_order.clone() {
            if let Some(elim) = try_cross_block_redundant_compare(func, block_b, dom, &to_delete) {
                to_delete.insert(elim.dead_cmp);
                fused_groups.push(FusedProvenance {
                    consumed_sources: vec![elim.dead_cmp, elim.provenance_anchor],
                    live_sources: vec![elim.live_cmp],
                    merged: elim.provenance_anchor,
                });
                changed = true;
            }
        }
    }

    // Record the CMP/TST provenance on the surviving fused branch, then
    // remove the now-dead compare/test instruction slots.
    if !to_delete.is_empty() {
        if let Some(provenance) = provenance {
            let pass = PassId::new("cmp-branch-fusion");

            fused_groups.sort_unstable();
            fused_groups.dedup();
            for group in fused_groups {
                if group.live_sources.is_empty() {
                    provenance.record_merge(&group.consumed_sources, group.merged, pass.clone());
                } else {
                    provenance.record_merge_with_live_sources(
                        &group.consumed_sources,
                        &group.live_sources,
                        group.merged,
                        pass.clone(),
                    );
                }
            }
        }

        for block_id in func.block_order.clone() {
            let block = func.block_mut(block_id);
            block.insts.retain(|id| !to_delete.contains(id));
        }
    }

    changed
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct FusedProvenance {
    consumed_sources: Vec<InstId>,
    live_sources: Vec<InstId>,
    merged: InstId,
}

/// Try to eliminate imported-O0 boolean branch materialization:
///
/// ```text
///   cmp ...
///   cset bool, cc
///   cmp bool, #0
///   b.ne target
/// ```
///
/// becomes `b.cc target`, using the flags from the original compare. For
/// `b.eq`, the branch condition is inverted. The caller guarantees a
/// consecutive flag-setting instruction before `cset`, and this helper checks
/// that the `cset` value is only consumed by the compare-to-zero.
fn try_fuse_cset_bool_branch(
    cset_inst: &MachInst,
    cmp_zero_inst: &MachInst,
    bcond_inst: &MachInst,
    use_counts: &HashMap<VReg, u32>,
) -> Option<MachInst> {
    if cset_inst.opcode != AArch64Opcode::CSet
        || cmp_zero_inst.opcode != AArch64Opcode::CmpRI
        || bcond_inst.opcode != AArch64Opcode::BCond
    {
        return None;
    }

    let cset_dst = match cset_inst.operands.first()? {
        MachOperand::VReg(v) => *v,
        _ => return None,
    };
    if use_counts.get(&cset_dst).copied().unwrap_or(0) != 1 {
        return None;
    }

    if !matches!(cmp_zero_inst.operands.first(), Some(MachOperand::VReg(v)) if *v == cset_dst) {
        return None;
    }
    if cmp_zero_inst.operands.get(1).and_then(MachOperand::as_imm) != Some(0) {
        return None;
    }

    let cset_cond = decode_cond(cset_inst.operands.get(1)?.as_imm()? as u8)?;
    let branch_cond = decode_cond(bcond_inst.operands.first()?.as_imm()? as u8)?;
    let fused_cond = match branch_cond {
        CondCode::NE => cset_cond,
        CondCode::EQ => invert_cond(cset_cond)?,
        _ => return None,
    };
    let target = match bcond_inst.operands.get(1)? {
        MachOperand::Block(block) => *block,
        _ => return None,
    };

    Some(MachInst::new(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(fused_cond.encoding() as i64),
            MachOperand::Block(target),
        ],
    ))
}

/// Kill switch for the deferred CSET-then-branch collapse
/// ([`try_collapse_deferred_cset_branch`]). Default ON; set
/// `TCG_NO_CSET_BRANCH_COLLAPSE` to disable only the deferred pattern (the
/// adjacent CBZ/CBNZ/TBZ/TBNZ and imported-O0 window fusions are unaffected).
fn cset_branch_collapse_enabled() -> bool {
    std::env::var_os("TCG_NO_CSET_BRANCH_COLLAPSE").is_none()
}

/// A proven deferred CSET-then-branch collapse (see
/// [`try_collapse_deferred_cset_branch`]).
struct DeferredCsetBranchCollapse {
    /// The now-dead `CSET` to delete.
    cset_id: InstId,
    /// The replacement `B.cc` for the `CBZ`/`CBNZ` slot.
    fused: MachInst,
    /// Nearest preceding in-block flag writer (stays live; provenance only).
    live_flag_writer: Option<InstId>,
}

/// Try to collapse a deferred CSET-then-branch pair in one block:
///
/// ```text
///   cset Rd, cc          ; captures NZCV
///   ...                  ; every instruction provably NZCV-transparent
///   cbnz Rd, target      ; (or cbz)
/// ```
///
/// becomes `...; b.cc target` (`cbz` branches on `Rd == 0`, i.e. on the
/// condition being FALSE, so it takes the inverted code), deleting the dead
/// `CSET`. This is the dual of [`try_fuse_cbz`]: instead of folding a compare
/// into the branch, it folds the branch back onto the flags the CSET
/// materialized. The scan loop in Quicksort's inner partition scan is the
/// motivating shape (`cmp w, wPivot; cset x, lt; ...; cbnz x`).
///
/// Every condition fails closed:
/// - the branch operand must be a VReg with exactly one use (the branch);
/// - walking backward from the branch, the FIRST instruction that mentions
///   the vreg must be the defining `CSET` (anything else — another def, an
///   unexpected use, a `CSET` already consumed by an earlier fusion this
///   sweep — declines), so the matched `CSET` is the reaching definition;
/// - no instruction between the `CSET` and the branch may clobber NZCV
///   ([`may_clobber_nzcv`] is deliberately conservative: calls, branches,
///   terminators, trap carriers and unknown pseudos all count as clobbers);
/// - the condition code must decode, and for `CBZ` must be invertible
///   (`AL`/`NV` decline).
fn try_collapse_deferred_cset_branch(
    func: &MachFunction,
    insts: &[InstId],
    branch_idx: usize,
    use_counts: &HashMap<VReg, u32>,
    to_delete: &HashSet<InstId>,
) -> Option<DeferredCsetBranchCollapse> {
    let branch_inst = func.inst(insts[branch_idx]);
    let invert = match branch_inst.opcode {
        AArch64Opcode::Cbnz => false,
        AArch64Opcode::Cbz => true,
        _ => return None,
    };
    let branch_vreg = match branch_inst.operands.first()? {
        MachOperand::VReg(v) => *v,
        _ => return None,
    };
    let target = match branch_inst.operands.get(1)? {
        MachOperand::Block(block) => *block,
        _ => return None,
    };
    // The branch must be the ONLY use of the CSET result, otherwise the
    // CSET is not dead after the rewrite.
    if use_counts.get(&branch_vreg).copied().unwrap_or(0) != 1 {
        return None;
    }

    // Walk backward from the branch looking for the defining CSET. The
    // first mention of the vreg must BE that CSET (reaching definition);
    // any NZCV clobber encountered first declines the collapse.
    let mut cset: Option<(usize, InstId)> = None;
    for probe_idx in (0..branch_idx).rev() {
        let probe_id = insts[probe_idx];
        let probe = func.inst(probe_id);
        if probe.opcode == AArch64Opcode::CSet
            && matches!(probe.operands.first(), Some(MachOperand::VReg(v)) if *v == branch_vreg)
        {
            // A CSET already consumed by another fusion this sweep no
            // longer exists after the retain — fail closed.
            if !to_delete.contains(&probe_id) {
                cset = Some((probe_idx, probe_id));
            }
            break;
        }
        // Any other mention of the vreg (a redefinition, or a use the
        // count model missed) breaks the reaching-def argument.
        if inst_mentions_vreg(probe, branch_vreg) {
            return None;
        }
        // A flag clobber between the CSET and the branch would make B.cc
        // read different flags than the CSET captured.
        if may_clobber_nzcv(probe) {
            return None;
        }
    }
    let (cset_idx, cset_id) = cset?;

    let cset_inst = func.inst(cset_id);
    let cset_cond = decode_cond(cset_inst.operands.get(1)?.as_imm()? as u8)?;
    let fused_cond = if invert {
        invert_cond(cset_cond)?
    } else {
        cset_cond
    };

    let mut fused = MachInst::new(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(fused_cond.encoding() as i64),
            MachOperand::Block(target),
        ],
    );
    fused.source_loc = branch_inst.source_loc.or(cset_inst.source_loc);

    // Nearest preceding in-block flag writer stays live (the fused branch
    // now reads its flags directly); record it for provenance like the
    // adjacent imported-O0 window fusion does. Flags may also be live-in
    // from a predecessor block, in which case there is nothing to record.
    let live_flag_writer = insts[..cset_idx]
        .iter()
        .rev()
        .copied()
        .find(|id| !to_delete.contains(id) && sets_flags(func.inst(*id).opcode));

    Some(DeferredCsetBranchCollapse {
        cset_id,
        fused,
        live_flag_writer,
    })
}

/// Does this instruction mention `vreg` in ANY explicit operand position
/// (def or use)? Used by the deferred CSET collapse to prove the matched
/// CSET is the reaching definition of the branch operand.
fn inst_mentions_vreg(inst: &MachInst, vreg: VReg) -> bool {
    inst.operands
        .iter()
        .any(|op| matches!(op, MachOperand::VReg(v) if *v == vreg))
}

/// May this instruction change NZCV between a CSET and its consuming branch?
///
/// Deliberately conservative: returns `true` (clobbers) unless the
/// instruction is provably NZCV-transparent. Beyond the architectural flag
/// writers ([`sets_flags`] / [`trust_cg_ir`] `writes_flags`), the following
/// all count as clobbers:
///
/// - **Calls** (`BL`/`BLR`): NZCV is caller-saved.
/// - **Branches/terminators**: control leaves the straight-line region.
/// - **Trap carriers** (`TrapBoundsCheckExact`, `TrapShiftRangeIfOOB`, ...):
///   these expand at codegen time into `CMP; B.LO; BRK` / `CBNZ; BRK`
///   sequences (see `trust-cg-codegen/src/lower.rs`), so they clobber NZCV
///   at runtime even though the carrier opcode itself is not a flag writer.
/// - **Pseudos** other than `Copy`/`Nop`: unknown expansion. `Copy` lowers
///   to a plain register move and `Nop` to nothing — both NZCV-transparent.
fn may_clobber_nzcv(inst: &MachInst) -> bool {
    use AArch64Opcode::*;
    if crate::effects::writes_flags(inst.opcode) {
        return true;
    }
    if matches!(
        inst.opcode,
        Brk | TrapOverflow
            | TrapBoundsCheck
            | TrapBoundsCheckExact
            | TrapNull
            | TrapNullIfZero
            | TrapDivZero
            | TrapDivZeroIfZero
            | TrapShiftRange
            | TrapShiftRangeIfOOB
            | TrapOverflowExact
    ) {
        return true;
    }
    // Consult both the instruction's own flags and the opcode defaults —
    // passes occasionally construct MachInsts with hand-set flags.
    let combined = inst.flags.union(inst.opcode.default_flags());
    if combined.contains(InstFlags::IS_CALL)
        || combined.contains(InstFlags::IS_BRANCH)
        || combined.contains(InstFlags::IS_TERMINATOR)
    {
        return true;
    }
    if combined.contains(InstFlags::IS_PSEUDO) {
        // Copy lowers to a plain MOV and Nop to nothing; every other pseudo
        // has an unknown expansion — fail closed.
        return !matches!(inst.opcode, Copy | Nop);
    }
    false
}

/// Kill switch for the variable single-bit test fusion
/// ([`try_fuse_single_bit_test_branch`]). Default ON; set
/// `TCG_NO_BIT_TEST_BRANCH_FUSE` to disable only that pattern (all other
/// fusions in this pass are unaffected).
fn bit_test_branch_fuse_enabled() -> bool {
    crate::env_lock::var_os("TCG_NO_BIT_TEST_BRANCH_FUSE").is_none()
}

/// Kill switch for cross-block redundant compare elimination
/// ([`try_cross_block_redundant_compare`]). Default ON; set
/// `TCG_NO_CROSS_BLOCK_CMP_ELIM` to disable only that pattern.
fn cross_block_cmp_elim_enabled() -> bool {
    crate::env_lock::var_os("TCG_NO_CROSS_BLOCK_CMP_ELIM").is_none()
}

/// A proven cross-block redundant compare elimination (see
/// [`try_cross_block_redundant_compare`]).
struct CrossBlockCmpElim {
    /// The redundant compare in block B to delete.
    dead_cmp: InstId,
    /// The dominating compare in block A whose flags B now reuses (stays
    /// live; provenance only).
    live_cmp: InstId,
    /// Surviving instruction in B (its terminator) to attach the deleted
    /// compare's provenance to.
    provenance_anchor: InstId,
}

/// Opcodes whose ONLY architectural output is NZCV (no register result), so
/// a provably-redundant instance can be deleted with a downstream branch
/// reusing the dominating flags. Excludes `ADDS`/`SUBS` (they also write a
/// GPR result) and `FCMP` (kept conservative to the integer three-way
/// comparator, the diagnosed shape).
fn is_pure_flag_compare(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::CmpRR
            | AArch64Opcode::CmpRI
            | AArch64Opcode::CMPWrr
            | AArch64Opcode::CMPXrr
            | AArch64Opcode::CMPWri
            | AArch64Opcode::CMPXri
            | AArch64Opcode::Tst
    )
}

/// Does this instruction READ NZCV (consume the flags)? A flag-reading
/// conditional select ([`crate::effects::reads_flags`]) OR a conditional
/// branch `B.cc` (`reads_flags` tracks branch flag-reads structurally, not
/// by opcode, so `BCond` is added explicitly here). Used to confirm the
/// redundant compare's flags are genuinely consumed in block B.
fn consumes_nzcv(inst: &MachInst) -> bool {
    crate::effects::reads_flags(inst.opcode) || inst.opcode == AArch64Opcode::BCond
}

/// May this instruction WRITE NZCV on a straight-line path? The dual of the
/// tail/head transparency walk used by the cross-block elimination. Unlike
/// [`may_clobber_nzcv`], a PURE branch/terminator (which never writes NZCV on
/// AArch64) is treated as transparent, so the connecting `...; b.gt` edge
/// does not count as a flag writer. Calls, trap carriers (which expand to
/// `cmp; b.lo; brk` at codegen time) and unknown pseudos still fail closed.
fn writes_nzcv_conservative(inst: &MachInst) -> bool {
    use AArch64Opcode::*;
    if crate::effects::writes_flags(inst.opcode) {
        return true;
    }
    if matches!(
        inst.opcode,
        Brk | TrapOverflow
            | TrapBoundsCheck
            | TrapBoundsCheckExact
            | TrapNull
            | TrapNullIfZero
            | TrapDivZero
            | TrapDivZeroIfZero
            | TrapShiftRange
            | TrapShiftRangeIfOOB
            | TrapOverflowExact
    ) {
        return true;
    }
    let combined = inst.flags.union(inst.opcode.default_flags());
    if combined.contains(InstFlags::IS_CALL) {
        return true;
    }
    if combined.contains(InstFlags::IS_BRANCH) || combined.contains(InstFlags::IS_TERMINATOR) {
        // Pure control transfer — AArch64 branches never write NZCV.
        return false;
    }
    if combined.contains(InstFlags::IS_PSEUDO) {
        // Copy lowers to a plain MOV and Nop to nothing; every other pseudo
        // has an unknown expansion — fail closed.
        return !matches!(inst.opcode, Copy | Nop);
    }
    false
}

/// Does `inst` define (write) any of the given register operands?
fn defines_any_operand(inst: &MachInst, regs: &[MachOperand]) -> bool {
    let mut hit = false;
    crate::effects::aarch64_for_each_def_position(inst.opcode, inst.operands.len(), |pos| {
        if let Some(op) = inst.operands.get(pos)
            && regs.contains(op)
        {
            hit = true;
        }
    });
    hit
}

/// Try to prove a cross-block redundant compare in block `block_b` (the
/// three-way comparator's second arm). Returns the deletion when every
/// fail-closed condition holds; see the call site for the full rationale.
///
/// SOUNDNESS: B has a SINGLE predecessor A, so the only runtime path into B
/// is the A->B edge and B's NZCV live-in equals A's NZCV at its exit. A's
/// compare is the LAST flag writer in A and B's the FIRST in B, so no
/// instruction between them writes NZCV; the two compares are IDENTICAL and
/// their source registers are unchanged on the connecting path, so B's
/// compare would reproduce exactly A's flags. Deleting it and letting B's
/// branch reuse the live-in NZCV is therefore semantics-preserving.
fn try_cross_block_redundant_compare(
    func: &MachFunction,
    block_b: BlockId,
    dom: Option<&DomTree>,
    to_delete: &HashSet<InstId>,
) -> Option<CrossBlockCmpElim> {
    // B must have EXACTLY ONE predecessor A (single incoming edge).
    let preds = &func.block(block_b).preds;
    if preds.len() != 1 {
        return None;
    }
    let block_a = preds[0];
    if block_a == block_b {
        return None;
    }
    // Belt: A must dominate B (single-pred already implies this; the explicit
    // check keeps it fail-closed when dominator info is available).
    if let Some(dom) = dom
        && !dom.dominates(block_a, block_b)
    {
        return None;
    }

    // Live instruction sequences (ignore slots already consumed this sweep).
    let b_insts: Vec<InstId> = func
        .block(block_b)
        .insts
        .iter()
        .copied()
        .filter(|id| !to_delete.contains(id))
        .collect();
    let a_insts: Vec<InstId> = func
        .block(block_a)
        .insts
        .iter()
        .copied()
        .filter(|id| !to_delete.contains(id))
        .collect();

    // C_B: the FIRST flag writer in B (everything before it is thus
    // NZCV-transparent). It must be a pure-flag compare.
    let cb_pos = b_insts
        .iter()
        .position(|id| writes_nzcv_conservative(func.inst(*id)))?;
    let dead_cmp = b_insts[cb_pos];
    let c_b = func.inst(dead_cmp);
    if !is_pure_flag_compare(c_b.opcode) {
        return None;
    }
    // A flag CONSUMER must follow C_B in B (its NZCV is genuinely used here —
    // the redundant three-way branch — and there is a terminator to anchor
    // provenance to).
    if !b_insts[cb_pos + 1..]
        .iter()
        .any(|id| consumes_nzcv(func.inst(*id)))
    {
        return None;
    }

    // C_A: the LAST flag writer in A (everything after it — including the
    // terminator branch — is NZCV-transparent). Must be IDENTICAL to C_B.
    let ca_pos = a_insts
        .iter()
        .rposition(|id| writes_nzcv_conservative(func.inst(*id)))?;
    let live_cmp = a_insts[ca_pos];
    let c_a = func.inst(live_cmp);
    if c_a.opcode != c_b.opcode || c_a.operands != c_b.operands {
        return None;
    }

    // No source operand of the compare may be redefined on the connecting
    // path: A's tail after C_A, then B's head before C_B. (No NZCV writer
    // lies there by construction, but a non-flag instruction could still
    // overwrite an operand register while leaving NZCV intact.)
    let srcs: Vec<MachOperand> = c_a
        .operands
        .iter()
        .filter(|op| matches!(op, MachOperand::VReg(_) | MachOperand::PReg(_)))
        .cloned()
        .collect();
    let redefines = |id: &InstId| defines_any_operand(func.inst(*id), &srcs);
    if a_insts[ca_pos + 1..].iter().any(redefines) || b_insts[..cb_pos].iter().any(redefines) {
        return None;
    }

    let provenance_anchor = *b_insts.last()?;
    if provenance_anchor == dead_cmp {
        return None;
    }

    Some(CrossBlockCmpElim {
        dead_cmp,
        live_cmp,
        provenance_anchor,
    })
}

/// The unique materialized-constant definition of a vreg (if any): the ONE
/// instruction in the whole function that defines it, when that instruction is
/// a simple `MovI`/`Movz` constant.
#[derive(Clone, Copy)]
struct UniqueConstDef {
    block: BlockId,
    inst: InstId,
    value: i64,
}

/// Map every vreg to its unique materialized-constant def, or `None` when the
/// vreg has multiple defs (including `Movz`+`Movk` pairs — the `Movk` is a
/// second def and poisons the entry) or a single non-constant def. Defs are
/// enumerated through the shared operand-role oracle so multi-def and tied
/// def-use instructions are all counted.
fn collect_unique_const_defs(func: &MachFunction) -> HashMap<VReg, Option<UniqueConstDef>> {
    let mut map: HashMap<VReg, Option<UniqueConstDef>> = HashMap::new();
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            let mut defs: Vec<VReg> = Vec::new();
            crate::effects::aarch64_for_each_def_position(
                inst.opcode,
                inst.operands.len(),
                |pos| {
                    if let Some(MachOperand::VReg(v)) = inst.operands.get(pos) {
                        defs.push(*v);
                    }
                },
            );
            for v in defs {
                match map.entry(v) {
                    std::collections::hash_map::Entry::Vacant(entry) => {
                        // Only a value-def at operand 0 of a simple constant
                        // materialization qualifies.
                        let constant = simple_materialized_constant(inst).filter(|_| {
                            matches!(inst.operands.first(), Some(MachOperand::VReg(d)) if *d == v)
                        });
                        entry.insert(constant.map(|value| UniqueConstDef {
                            block: block_id,
                            inst: inst_id,
                            value,
                        }));
                    }
                    std::collections::hash_map::Entry::Occupied(mut entry) => {
                        // A second def anywhere poisons the entry.
                        entry.insert(None);
                    }
                }
            }
        }
    }
    map
}

/// The constant a single `MovI`/`Movz` materializes, if it is a simple one
/// (same shape the peephole pass recognizes).
fn simple_materialized_constant(inst: &MachInst) -> Option<i64> {
    match inst.opcode {
        AArch64Opcode::MovI if inst.operands.len() == 2 => inst.operands.get(1)?.as_imm(),
        AArch64Opcode::Movz => {
            crate::reaching_const::movz_value(inst).map(|(_, value)| value as i64)
        }
        _ => None,
    }
}

/// The bit width of a GPR register class (32 for W, 64 for X); `None` for any
/// non-GPR class (fail-closed).
fn gpr_width(class: RegClass) -> Option<u32> {
    match class {
        RegClass::Gpr32 => Some(32),
        RegClass::Gpr64 => Some(64),
        _ => None,
    }
}

/// A proven variable single-bit test fusion: the replacement `LsrRR` for the
/// `AndRR` slot and the replacement `Tbz`/`Tbnz` for the branch slot (the
/// `LslRR` is deleted by the caller).
struct SingleBitTestFusion {
    lsr: MachInst,
    tb: MachInst,
}

/// Try to fuse the variable single-bit test-and-branch triple
///
/// ```text
///   LslRR m, one, amt     ; m = 1 << (amt mod W)   (one == constant 1)
///   AndRR t, w, m         ; t = w & m              (either AND operand order)
///   Cbz/Cbnz t, target    ; branch on t == 0 / t != 0
/// ```
///
/// into
///
/// ```text
///   LsrRR t, w, amt       ; t = w >> (amt mod W)
///   Tbz/Tbnz t, #0, target
/// ```
///
/// SOUNDNESS (exact, for EVERY `amt` and `w`; W = register width): LSLV
/// computes `m = (1 << (amt mod W)) mod 2^W = 2^(amt mod W)` — a single-bit
/// mask, no truncation since `amt mod W <= W-1`. So `t = w & m` is zero iff
/// bit `(amt mod W)` of `w` is zero. LSRV computes `t' = w >>logical (amt mod
/// W)`, whose bit 0 IS bit `(amt mod W)` of `w`. Hence `CBZ t` (taken iff
/// `t == 0`) and `TBZ t', #0` (taken iff bit 0 of `t'` is zero) branch
/// identically; `CBNZ`/`TBNZ` are the duals. None of the five instructions
/// reads or writes NZCV, and the rewrite preserves the branch target, so
/// flags and CFG are untouched.
///
/// Fail-closed conditions (each one declines the fusion):
/// - the three instructions are ADJACENT in the live sequence (nothing
///   executes between them, so no operand can be redefined mid-pattern);
/// - `t` is single-use (the branch) and `m` is single-use (the AND), so the
///   deleted mask chain is dead — the use counts are a pre-sweep
///   OVER-approximation (this sweep's rewrites only move or remove reads);
/// - `one` has a UNIQUE function-wide def that is a simple `MovI`/`Movz` of
///   exactly 1, and that def dominates the triple (same block: appears
///   earlier in the live sequence; otherwise: dominator-tree check — no
///   dominator info declines cross-block);
/// - every register is a vreg of the SAME GPR width (the mod-W arguments for
///   the LSLV and the LSRV must agree).
///
/// The rewrite reuses `t` as the LSR destination: its only reader was the
/// branch, which now reads the shifted word in the same slot.
#[allow(clippy::too_many_arguments)]
fn try_fuse_single_bit_test_branch(
    func: &MachFunction,
    lsl_id: InstId,
    and_id: InstId,
    branch_id: InstId,
    preceding_live: &[InstId],
    block: BlockId,
    use_counts: &HashMap<VReg, u32>,
    unique_consts: &HashMap<VReg, Option<UniqueConstDef>>,
    dom: Option<&DomTree>,
) -> Option<SingleBitTestFusion> {
    // Branch: Cbz -> Tbz (branch when the bit is 0), Cbnz -> Tbnz.
    let branch_inst = func.inst(branch_id);
    let tb_opcode = match branch_inst.opcode {
        AArch64Opcode::Cbz => AArch64Opcode::Tbz,
        AArch64Opcode::Cbnz => AArch64Opcode::Tbnz,
        _ => return None,
    };
    let t = branch_inst.operands.first()?.as_vreg()?;
    let target = match branch_inst.operands.get(1)? {
        MachOperand::Block(block) => *block,
        _ => return None,
    };
    // t's ONLY use is the branch (the AND result dies here).
    if use_counts.get(&t).copied().unwrap_or(0) != 1 {
        return None;
    }

    // AND: AndRR t, w, m (either source order; NEVER the flag-setting Tst —
    // opcode match is exact). All sources must be vregs.
    let and_inst = func.inst(and_id);
    if and_inst.opcode != AArch64Opcode::AndRR || and_inst.operands.len() != 3 {
        return None;
    }
    if and_inst.operands[0].as_vreg()? != t {
        return None;
    }
    let and_a = and_inst.operands[1].as_vreg()?;
    let and_b = and_inst.operands[2].as_vreg()?;

    // LSL: LslRR m, one, amt.
    let lsl_inst = func.inst(lsl_id);
    if lsl_inst.opcode != AArch64Opcode::LslRR || lsl_inst.operands.len() != 3 {
        return None;
    }
    let m = lsl_inst.operands[0].as_vreg()?;
    let one = lsl_inst.operands[1].as_vreg()?;
    let amt = lsl_inst.operands[2].as_vreg()?;

    // Match the mask operand of the AND (commutative — try both orders).
    let w = if and_a == m && and_b != m {
        and_b
    } else if and_b == m && and_a != m {
        and_a
    } else {
        return None;
    };
    // m's ONLY use is the AND (the mask dies there; a use in the LslRR's own
    // source slots — m as `one` or `amt` — would also raise the count).
    if use_counts.get(&m).copied().unwrap_or(0) != 1 {
        return None;
    }

    // Uniform GPR width: the LSLV mod and the LSRV mod must be the same W.
    let width = gpr_width(t.class)?;
    if gpr_width(m.class)? != width
        || gpr_width(w.class)? != width
        || gpr_width(one.class)? != width
        || gpr_width(amt.class)? != width
    {
        return None;
    }

    // `one` must be EXACTLY the constant 1 at this point: unique def in the
    // whole function, value 1, and the def reaches the triple.
    let const_def = (*unique_consts.get(&one)?)?;
    if const_def.value != 1 {
        return None;
    }
    if const_def.block == block {
        // Same block: the def must appear (live) before the LslRR.
        if !preceding_live.contains(&const_def.inst) {
            return None;
        }
    } else {
        // Cross-block: the def block must dominate this one. Being the
        // unique def of a vreg the program reads here, it dominates in any
        // ISel-derived function; the explicit check keeps this fail-closed.
        if !dom.is_some_and(|dom| dom.dominates(const_def.block, block)) {
            return None;
        }
    }

    let mut lsr = MachInst::new(
        AArch64Opcode::LsrRR,
        vec![
            MachOperand::VReg(t),
            MachOperand::VReg(w),
            MachOperand::VReg(amt),
        ],
    );
    lsr.source_loc = and_inst.source_loc.or(lsl_inst.source_loc);

    let mut tb = MachInst::new(
        tb_opcode,
        vec![
            MachOperand::VReg(t),
            MachOperand::Imm(0),
            MachOperand::Block(target),
        ],
    );
    tb.source_loc = branch_inst.source_loc;

    Some(SingleBitTestFusion { lsr, tb })
}

/// Try to fuse compare-immediate Rn, #0 + B.EQ/B.NE into CBZ/CBNZ.
///
/// - CmpRI Rn, #0 + B.EQ target -> CBZ Rn, target
/// - CmpRI Rn, #0 + B.NE target -> CBNZ Rn, target
/// - CMPWri/CMPXri aliases follow the same compare-to-zero rules.
fn try_fuse_cbz(
    cmp_inst: &MachInst,
    cond: CondCode,
    target: trust_cg_ir::BlockId,
) -> Option<MachInst> {
    // Must be compare-immediate with immediate 0.
    if !matches!(
        cmp_inst.opcode,
        AArch64Opcode::CmpRI | AArch64Opcode::CMPWri | AArch64Opcode::CMPXri
    ) {
        return None;
    }
    if cmp_inst.operands.len() < 2 {
        return None;
    }

    // Second operand must be immediate 0.
    let imm_val = cmp_inst.operands[1].as_imm()?;
    if imm_val != 0 {
        return None;
    }

    // Only EQ and NE conditions are fusible to CBZ/CBNZ.
    let opcode = match cond {
        CondCode::EQ => AArch64Opcode::Cbz,
        CondCode::NE => AArch64Opcode::Cbnz,
        _ => return None,
    };

    // CBZ/CBNZ operands: [Rn, Block(target)]
    let rn = branch_test_register(&cmp_inst.operands[0])?;
    Some(MachInst::new(opcode, vec![rn, MachOperand::Block(target)]))
}

/// Try to fuse TST Rn, #(1<<bit) + B.EQ/B.NE into TBZ/TBNZ.
///
/// - TST Rn, #(1<<bit) + B.EQ target -> TBZ Rn, #bit, target
/// - TST Rn, #(1<<bit) + B.NE target -> TBNZ Rn, #bit, target
fn try_fuse_tbz(
    cmp_inst: &MachInst,
    cond: CondCode,
    target: trust_cg_ir::BlockId,
) -> Option<MachInst> {
    // Must be TST.
    if cmp_inst.opcode != AArch64Opcode::Tst {
        return None;
    }
    if cmp_inst.operands.len() < 2 {
        return None;
    }

    // Second operand must be an immediate that is a power of 2.
    // Note: 1i64 << 63 is negative in i64 but valid as a 64-bit mask.
    // We cast to u64 for the power-of-two check.
    let mask = cmp_inst.operands[1].as_imm()?;
    let mask_u64 = mask as u64;
    if !is_power_of_two(mask_u64) {
        return None;
    }

    let bit = mask_u64.trailing_zeros() as i64;

    // Only EQ and NE conditions are fusible.
    // TST sets Z flag: B.EQ (Z=1) means bit was 0 -> TBZ
    //                  B.NE (Z=0) means bit was 1 -> TBNZ
    let opcode = match cond {
        CondCode::EQ => AArch64Opcode::Tbz,
        CondCode::NE => AArch64Opcode::Tbnz,
        _ => return None,
    };

    // TBZ/TBNZ operands: [Rn, Imm(bit), Block(target)]
    let rn = branch_test_register(&cmp_inst.operands[0])?;
    Some(MachInst::new(
        opcode,
        vec![rn, MachOperand::Imm(bit), MachOperand::Block(target)],
    ))
}

fn branch_test_register(operand: &MachOperand) -> Option<MachOperand> {
    match operand {
        MachOperand::VReg(_) | MachOperand::PReg(_) => Some(operand.clone()),
        _ => None,
    }
}

/// Returns true if `v` is a power of two (exactly one bit set).
fn is_power_of_two(v: u64) -> bool {
    v != 0 && (v & (v - 1)) == 0
}

fn collect_vreg_uses(func: &MachFunction) -> HashMap<VReg, u32> {
    let mut counts = HashMap::new();
    for block_id in &func.block_order {
        let block = func.block(*block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            for pos in
                crate::effects::aarch64_use_operand_positions(inst.opcode, inst.operands.len())
            {
                if let Some(MachOperand::VReg(vreg)) = inst.operands.get(pos) {
                    *counts.entry(*vreg).or_insert(0) += 1;
                }
            }
        }
    }
    counts
}

/// Decode a condition code encoding (0-15) to a CondCode variant.
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

fn invert_cond(cond: CondCode) -> Option<CondCode> {
    match cond {
        CondCode::EQ => Some(CondCode::NE),
        CondCode::NE => Some(CondCode::EQ),
        CondCode::HS => Some(CondCode::LO),
        CondCode::LO => Some(CondCode::HS),
        CondCode::MI => Some(CondCode::PL),
        CondCode::PL => Some(CondCode::MI),
        CondCode::VS => Some(CondCode::VC),
        CondCode::VC => Some(CondCode::VS),
        CondCode::HI => Some(CondCode::LS),
        CondCode::LS => Some(CondCode::HI),
        CondCode::GE => Some(CondCode::LT),
        CondCode::LT => Some(CondCode::GE),
        CondCode::GT => Some(CondCode::LE),
        CondCode::LE => Some(CondCode::GT),
        CondCode::AL | CondCode::NV => None,
    }
}

/// Returns true if the given opcode sets the NZCV condition flags.
fn sets_flags(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::CmpRR
            | AArch64Opcode::CmpRI
            | AArch64Opcode::CMPWrr
            | AArch64Opcode::CMPXrr
            | AArch64Opcode::CMPWri
            | AArch64Opcode::CMPXri
            | AArch64Opcode::Tst
            | AArch64Opcode::Fcmp
            | AArch64Opcode::AddsRR
            | AArch64Opcode::AddsRI
            | AArch64Opcode::SubsRR
            | AArch64Opcode::SubsRI
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pass_manager::MachinePass;
    use trust_cg_ir::{
        AArch64Opcode, BlockId, CondCode, MachFunction, MachInst, MachOperand, RegClass, Signature,
        SourceLoc, TransformKind, TrustIrInstId, VReg,
    };

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn vreg32(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
    }

    fn vreg_class(id: u32, class: RegClass) -> MachOperand {
        MachOperand::VReg(VReg::new(id, class))
    }

    fn imm(val: i64) -> MachOperand {
        MachOperand::Imm(val)
    }

    /// Build a function with CMP/TST + BCond as the last two instructions.
    /// The BCond targets a second block (bb1) containing only RET.
    fn make_func_with_branch(cmp: MachInst, cond: CondCode) -> MachFunction {
        let mut func = MachFunction::new("test_fusion".to_string(), Signature::new(vec![], vec![]));

        let bb0 = func.entry;
        let bb1 = func.create_block();

        // bb0: CMP + BCond
        let cmp_id = func.push_inst(cmp);
        func.append_inst(bb0, cmp_id);

        let bcond = MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(cond.encoding() as i64), MachOperand::Block(bb1)],
        );
        let bcond_id = func.push_inst(bcond);
        func.append_inst(bb0, bcond_id);

        // bb1: RET
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let ret_id = func.push_inst(ret);
        func.append_inst(bb1, ret_id);

        func.add_edge(bb0, bb1);

        func
    }

    // ---- CBZ fusion tests ----

    #[test]
    fn test_cbz_from_cmpri_zero_beq() {
        // CMP v0, #0; B.EQ bb1 -> CBZ v0, bb1
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(0), imm(0)]);
        let mut func = make_func_with_branch(cmp, CondCode::EQ);

        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        // CMP should be deleted, only fused CBZ remains.
        assert_eq!(block.insts.len(), 1);

        let fused = func.inst(block.insts[0]);
        assert_eq!(fused.opcode, AArch64Opcode::Cbz);
        assert_eq!(fused.operands[0], vreg(0));
        assert_eq!(fused.operands[1], MachOperand::Block(BlockId(1)));
    }

    #[test]
    fn test_cbnz_from_cmpri_zero_bne() {
        // CMP v0, #0; B.NE bb1 -> CBNZ v0, bb1
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(0), imm(0)]);
        let mut func = make_func_with_branch(cmp, CondCode::NE);

        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1);

        let fused = func.inst(block.insts[0]);
        assert_eq!(fused.opcode, AArch64Opcode::Cbnz);
        assert_eq!(fused.operands[0], vreg(0));
        assert_eq!(fused.operands[1], MachOperand::Block(BlockId(1)));
    }

    #[test]
    fn test_cbz_from_cmpwri_zero_beq() {
        // CMPWri w0, #0; B.EQ bb1 -> CBZ w0, bb1
        let cmp = MachInst::new(AArch64Opcode::CMPWri, vec![vreg32(0), imm(0)]);
        let mut func = make_func_with_branch(cmp, CondCode::EQ);

        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1);

        let fused = func.inst(block.insts[0]);
        assert_eq!(fused.opcode, AArch64Opcode::Cbz);
        assert_eq!(fused.operands[0], vreg32(0));
        assert_eq!(fused.operands[1], MachOperand::Block(BlockId(1)));
    }

    #[test]
    fn test_cbnz_from_cmpxri_zero_bne() {
        // CMPXri x0, #0; B.NE bb1 -> CBNZ x0, bb1
        let cmp = MachInst::new(AArch64Opcode::CMPXri, vec![vreg(0), imm(0)]);
        let mut func = make_func_with_branch(cmp, CondCode::NE);

        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1);

        let fused = func.inst(block.insts[0]);
        assert_eq!(fused.opcode, AArch64Opcode::Cbnz);
        assert_eq!(fused.operands[0], vreg(0));
        assert_eq!(fused.operands[1], MachOperand::Block(BlockId(1)));
    }

    #[test]
    fn test_source_loc_preserved_across_cbz_fusion() {
        let cmp_loc = SourceLoc {
            file: 1,
            line: 41,
            col: 9,
        };
        let branch_loc = SourceLoc {
            file: 1,
            line: 42,
            col: 13,
        };
        let cmp =
            MachInst::new(AArch64Opcode::CmpRI, vec![vreg(0), imm(0)]).with_source_loc(cmp_loc);
        let mut func = make_func_with_branch(cmp, CondCode::EQ);

        let bcond_id = func.block(func.entry).insts[1];
        func.inst_mut(bcond_id).source_loc = Some(branch_loc);

        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        let fused = func.inst(block.insts[0]);
        assert_eq!(fused.opcode, AArch64Opcode::Cbz);
        assert_eq!(
            fused.source_loc,
            Some(branch_loc),
            "cmp-branch fusion must keep the replaced BCond source_loc for DWARF line info"
        );
    }

    #[test]
    fn test_cmp_branch_fusion_provenance_merges_cmp_into_fused_bcond() {
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(0), imm(0)]);
        let mut func = make_func_with_branch(cmp, CondCode::EQ);
        let cmp_id = func.block(func.entry).insts[0];
        let bcond_id = func.block(func.entry).insts[1];
        let ret_id = func.block(BlockId(1)).insts[0];

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(40), &[cmp_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(41), &[bcond_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(42), &[ret_id], PassId::new("isel"));

        let mut pass = CmpBranchFusion;
        let mut analyses = AnalysisCache::new();
        assert!(pass.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance));

        let block = func.block(func.entry);
        assert_eq!(block.insts, vec![bcond_id]);

        let fused = func.inst(bcond_id);
        assert_eq!(fused.opcode, AArch64Opcode::Cbz);
        assert_eq!(fused.operands[0], vreg(0));
        assert_eq!(fused.operands[1], MachOperand::Block(BlockId(1)));

        let fused_entry = provenance.get_entry(bcond_id).unwrap();
        assert!(fused_entry.trust_ir_origins.contains(&TrustIrInstId(40)));
        assert!(fused_entry.trust_ir_origins.contains(&TrustIrInstId(41)));
        let transform = fused_entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("cmp-branch-fusion"));
        assert_eq!(
            transform.kind,
            TransformKind::Merged {
                sources: vec![cmp_id, bcond_id],
            }
        );
        assert!(fused_entry.is_active());

        assert!(provenance.get_entry(cmp_id).is_none());
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(40)).unwrap(),
            &[bcond_id]
        );
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(41)).unwrap(),
            &[bcond_id]
        );

        assert_eq!(provenance.get_entry(ret_id).unwrap().transforms.len(), 1);
    }

    #[test]
    fn test_cset_bool_branch_fuses_to_original_condition() {
        let mut func = MachFunction::new(
            "test_cset_bool_branch".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();

        let cmp_id = func.push_inst(MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]));
        func.append_inst(bb0, cmp_id);
        let cset_id = func.push_inst(MachInst::new(
            AArch64Opcode::CSet,
            vec![vreg(2), imm(CondCode::LT.encoding() as i64)],
        ));
        func.append_inst(bb0, cset_id);
        let cmp_zero_id =
            func.push_inst(MachInst::new(AArch64Opcode::CmpRI, vec![vreg(2), imm(0)]));
        func.append_inst(bb0, cmp_zero_id);
        let bcond_id = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(CondCode::NE.encoding() as i64), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, bcond_id);
        func.add_edge(bb0, bb1);

        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));

        let block = func.block(bb0);
        assert_eq!(block.insts, vec![cmp_id, bcond_id]);
        let branch = func.inst(bcond_id);
        assert_eq!(branch.opcode, AArch64Opcode::BCond);
        assert_eq!(branch.operands[0], imm(CondCode::LT.encoding() as i64));
        assert_eq!(branch.operands[1], MachOperand::Block(bb1));
    }

    #[test]
    fn test_cset_bool_branch_inverts_on_eq_zero() {
        let mut func = MachFunction::new(
            "test_cset_bool_branch_invert".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();

        let cmp_id = func.push_inst(MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]));
        func.append_inst(bb0, cmp_id);
        let cset_id = func.push_inst(MachInst::new(
            AArch64Opcode::CSet,
            vec![vreg(2), imm(CondCode::GE.encoding() as i64)],
        ));
        func.append_inst(bb0, cset_id);
        let cmp_zero_id =
            func.push_inst(MachInst::new(AArch64Opcode::CmpRI, vec![vreg(2), imm(0)]));
        func.append_inst(bb0, cmp_zero_id);
        let bcond_id = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(CondCode::EQ.encoding() as i64), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, bcond_id);
        func.add_edge(bb0, bb1);

        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));

        let block = func.block(bb0);
        assert_eq!(block.insts, vec![cmp_id, bcond_id]);
        let branch = func.inst(bcond_id);
        assert_eq!(branch.opcode, AArch64Opcode::BCond);
        assert_eq!(branch.operands[0], imm(CondCode::LT.encoding() as i64));
        assert_eq!(branch.operands[1], MachOperand::Block(bb1));
    }

    #[test]
    fn test_cset_bool_branch_provenance_keeps_live_flag_compare() {
        let mut func = MachFunction::new(
            "test_cset_bool_branch_provenance".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();

        let cmp_id = func.push_inst(MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]));
        func.append_inst(bb0, cmp_id);
        let cset_id = func.push_inst(MachInst::new(
            AArch64Opcode::CSet,
            vec![vreg(2), imm(CondCode::LT.encoding() as i64)],
        ));
        func.append_inst(bb0, cset_id);
        let cmp_zero_id =
            func.push_inst(MachInst::new(AArch64Opcode::CmpRI, vec![vreg(2), imm(0)]));
        func.append_inst(bb0, cmp_zero_id);
        let bcond_id = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(CondCode::NE.encoding() as i64), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, bcond_id);
        func.add_edge(bb0, bb1);

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(50), &[cmp_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(51), &[cset_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(52), &[cmp_zero_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(53), &[bcond_id], PassId::new("isel"));

        let mut pass = CmpBranchFusion;
        let mut analyses = AnalysisCache::new();
        assert!(pass.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance));

        assert!(
            provenance.get_entry(cmp_id).unwrap().is_active(),
            "flag-setting compare remains live after CSET branch fusion"
        );
        let branch_entry = provenance.get_entry(bcond_id).unwrap();
        for origin in [
            TrustIrInstId(50),
            TrustIrInstId(51),
            TrustIrInstId(52),
            TrustIrInstId(53),
        ] {
            assert!(
                branch_entry.trust_ir_origins.contains(&origin),
                "fused branch should retain origin {origin:?}"
            );
        }
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(50)).unwrap(),
            &[cmp_id, bcond_id],
            "live flag compare origin should map to both compare and fused branch"
        );
    }

    #[test]
    fn test_cset_bool_branch_declines_when_bool_has_other_use() {
        let mut func = MachFunction::new(
            "test_cset_bool_branch_multiuse".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();

        let cmp_id = func.push_inst(MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]));
        func.append_inst(bb0, cmp_id);
        let cset_id = func.push_inst(MachInst::new(
            AArch64Opcode::CSet,
            vec![vreg(2), imm(CondCode::LT.encoding() as i64)],
        ));
        func.append_inst(bb0, cset_id);
        let cmp_zero_id =
            func.push_inst(MachInst::new(AArch64Opcode::CmpRI, vec![vreg(2), imm(0)]));
        func.append_inst(bb0, cmp_zero_id);
        let bcond_id = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(CondCode::NE.encoding() as i64), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, bcond_id);
        func.add_edge(bb0, bb1);

        let other_block = func.create_block();
        let add_id = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(3), vreg(2), vreg(4)],
        ));
        func.append_inst(other_block, add_id);

        let mut pass = CmpBranchFusion;
        assert!(
            pass.run(&mut func),
            "generic cmp-zero branch fusion may still run, but CSET must remain live"
        );

        let block = func.block(bb0);
        assert_eq!(block.insts, vec![cmp_id, cset_id, bcond_id]);
        assert_eq!(func.inst(cset_id).opcode, AArch64Opcode::CSet);
        assert_eq!(func.inst(bcond_id).opcode, AArch64Opcode::Cbnz);
        assert_eq!(func.inst(bcond_id).operands[0], vreg(2));
        assert_eq!(func.block(other_block).insts, vec![add_id]);
    }

    #[test]
    fn test_cset_bool_branch_fuses_with_same_id_different_class_use() {
        let mut func = MachFunction::new(
            "test_cset_bool_branch_class_exact_use".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();

        let cmp_id = func.push_inst(MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]));
        func.append_inst(bb0, cmp_id);
        let cset_id = func.push_inst(MachInst::new(
            AArch64Opcode::CSet,
            vec![vreg(2), imm(CondCode::LT.encoding() as i64)],
        ));
        func.append_inst(bb0, cset_id);
        let cmp_zero_id =
            func.push_inst(MachInst::new(AArch64Opcode::CmpRI, vec![vreg(2), imm(0)]));
        func.append_inst(bb0, cmp_zero_id);
        let bcond_id = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(CondCode::NE.encoding() as i64), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, bcond_id);
        func.add_edge(bb0, bb1);

        let other_block = func.create_block();
        let other_class_use_id = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg_class(2, RegClass::Fpr64), imm(8)],
        ));
        func.append_inst(other_block, other_class_use_id);

        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));

        let block = func.block(bb0);
        assert_eq!(block.insts, vec![cmp_id, bcond_id]);
        let branch = func.inst(bcond_id);
        assert_eq!(branch.opcode, AArch64Opcode::BCond);
        assert_eq!(branch.operands[0], imm(CondCode::LT.encoding() as i64));
        assert_eq!(branch.operands[1], MachOperand::Block(bb1));
        assert_eq!(func.block(other_block).insts, vec![other_class_use_id]);
    }

    #[test]
    fn test_cset_bool_branch_declines_when_bool_has_tied_operand_zero_use() {
        let mut func = MachFunction::new(
            "test_cset_bool_branch_tied_operand_zero_use".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();

        let cmp_id = func.push_inst(MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]));
        func.append_inst(bb0, cmp_id);
        let cset_id = func.push_inst(MachInst::new(
            AArch64Opcode::CSet,
            vec![vreg(2), imm(CondCode::LT.encoding() as i64)],
        ));
        func.append_inst(bb0, cset_id);
        let cmp_zero_id =
            func.push_inst(MachInst::new(AArch64Opcode::CmpRI, vec![vreg(2), imm(0)]));
        func.append_inst(bb0, cmp_zero_id);
        let bcond_id = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(CondCode::NE.encoding() as i64), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, bcond_id);
        func.add_edge(bb0, bb1);

        let tied_use_block = func.create_block();
        let bfm_id = func.push_inst(MachInst::new(
            AArch64Opcode::Bfm,
            vec![vreg(2), vreg(4), imm(0), imm(7)],
        ));
        func.append_inst(tied_use_block, bfm_id);

        let mut pass = CmpBranchFusion;
        assert!(
            pass.run(&mut func),
            "generic cmp-zero branch fusion may still run, but CSET must remain live"
        );

        assert_eq!(func.block(bb0).insts, vec![cmp_id, cset_id, bcond_id]);
        assert_eq!(func.inst(cset_id).opcode, AArch64Opcode::CSet);
        assert_eq!(func.inst(bcond_id).opcode, AArch64Opcode::Cbnz);
        assert_eq!(func.inst(bcond_id).operands[0], vreg(2));
        assert_eq!(func.block(tied_use_block).insts, vec![bfm_id]);
    }

    // ---- TBZ fusion tests ----

    #[test]
    fn test_tbz_from_tst_beq() {
        // TST v0, #(1<<3); B.EQ bb1 -> TBZ v0, #3, bb1
        let tst = MachInst::new(AArch64Opcode::Tst, vec![vreg(0), imm(1 << 3)]);
        let mut func = make_func_with_branch(tst, CondCode::EQ);

        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1);

        let fused = func.inst(block.insts[0]);
        assert_eq!(fused.opcode, AArch64Opcode::Tbz);
        assert_eq!(fused.operands[0], vreg(0));
        assert_eq!(fused.operands[1], imm(3)); // bit number
        assert_eq!(fused.operands[2], MachOperand::Block(BlockId(1)));
    }

    #[test]
    fn test_tbnz_from_tst_bne() {
        // TST v0, #(1<<7); B.NE bb1 -> TBNZ v0, #7, bb1
        let tst = MachInst::new(AArch64Opcode::Tst, vec![vreg(0), imm(1 << 7)]);
        let mut func = make_func_with_branch(tst, CondCode::NE);

        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1);

        let fused = func.inst(block.insts[0]);
        assert_eq!(fused.opcode, AArch64Opcode::Tbnz);
        assert_eq!(fused.operands[0], vreg(0));
        assert_eq!(fused.operands[1], imm(7)); // bit number
        assert_eq!(fused.operands[2], MachOperand::Block(BlockId(1)));
    }

    #[test]
    fn test_source_loc_falls_back_to_tst_across_tbz_fusion() {
        let tst_loc = SourceLoc {
            file: 2,
            line: 77,
            col: 5,
        };
        let tst =
            MachInst::new(AArch64Opcode::Tst, vec![vreg(0), imm(1 << 3)]).with_source_loc(tst_loc);
        let mut func = make_func_with_branch(tst, CondCode::EQ);

        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        let fused = func.inst(block.insts[0]);
        assert_eq!(fused.opcode, AArch64Opcode::Tbz);
        assert_eq!(
            fused.source_loc,
            Some(tst_loc),
            "cmp-branch fusion must keep compare/test source_loc when BCond has none"
        );
    }

    #[test]
    fn test_tbz_bit_zero() {
        // TST v0, #1; B.EQ bb1 -> TBZ v0, #0, bb1
        let tst = MachInst::new(AArch64Opcode::Tst, vec![vreg(0), imm(1)]);
        let mut func = make_func_with_branch(tst, CondCode::EQ);

        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        let fused = func.inst(block.insts[0]);
        assert_eq!(fused.opcode, AArch64Opcode::Tbz);
        assert_eq!(fused.operands[1], imm(0));
    }

    #[test]
    fn test_tbz_bit_63() {
        // TST v0, #(1<<63); B.EQ bb1 -> TBZ v0, #63, bb1
        let tst = MachInst::new(AArch64Opcode::Tst, vec![vreg(0), imm(1i64 << 63)]);
        let mut func = make_func_with_branch(tst, CondCode::EQ);

        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        let fused = func.inst(block.insts[0]);
        assert_eq!(fused.opcode, AArch64Opcode::Tbz);
        // 1<<63 is negative in i64 but bit 63 as u64 trailing_zeros = 63
        assert_eq!(fused.operands[1], imm(63));
    }

    // ---- Negative tests ----

    #[test]
    fn test_no_fusion_cmp_nonzero() {
        // CMP v0, #42; B.EQ bb1 -> NO fusion (CBZ only for zero)
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(0), imm(42)]);
        let mut func = make_func_with_branch(cmp, CondCode::EQ);

        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // CMP + BCond both remain
    }

    #[test]
    fn test_no_fusion_cmpxri_nonzero() {
        // CMPXri x0, #42; B.EQ bb1 -> NO fusion (CBZ only for zero)
        let cmp = MachInst::new(AArch64Opcode::CMPXri, vec![vreg(0), imm(42)]);
        let mut func = make_func_with_branch(cmp, CondCode::EQ);

        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // CMP + BCond both remain
    }

    #[test]
    fn test_no_fusion_cmp_rr() {
        // CMP v0, v1; B.EQ bb1 -> NO fusion (CmpRR not fusible to CBZ)
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]);
        let mut func = make_func_with_branch(cmp, CondCode::EQ);

        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
    }

    #[test]
    fn test_no_fusion_cmp_zero_bge() {
        // CMP v0, #0; B.GE bb1 -> NO fusion (GE not fusible to CBZ/CBNZ)
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(0), imm(0)]);
        let mut func = make_func_with_branch(cmp, CondCode::GE);

        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
    }

    #[test]
    fn test_no_fusion_cmp_zero_non_register_operand() {
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![imm(7), imm(0)]);
        let mut func = make_func_with_branch(cmp, CondCode::EQ);

        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::CmpRI);
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::BCond);
    }

    #[test]
    fn test_no_fusion_tst_non_power_of_two() {
        // TST v0, #3; B.EQ bb1 -> NO fusion (3 is not a power of 2)
        let tst = MachInst::new(AArch64Opcode::Tst, vec![vreg(0), imm(3)]);
        let mut func = make_func_with_branch(tst, CondCode::EQ);

        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
    }

    #[test]
    fn test_no_fusion_tst_non_register_operand() {
        let tst = MachInst::new(AArch64Opcode::Tst, vec![imm(7), imm(1)]);
        let mut func = make_func_with_branch(tst, CondCode::EQ);

        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::Tst);
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::BCond);
    }

    #[test]
    fn test_no_fusion_tst_zero_mask() {
        // TST v0, #0; B.EQ bb1 -> NO fusion (0 is not a valid single-bit mask)
        let tst = MachInst::new(AArch64Opcode::Tst, vec![vreg(0), imm(0)]);
        let mut func = make_func_with_branch(tst, CondCode::EQ);

        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn test_no_fusion_tst_bge() {
        // TST v0, #4; B.GE bb1 -> NO fusion (GE not fusible)
        let tst = MachInst::new(AArch64Opcode::Tst, vec![vreg(0), imm(4)]);
        let mut func = make_func_with_branch(tst, CondCode::GE);

        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn test_no_fusion_non_consecutive() {
        // CMP v0, #0; ADD v1, v2, v3; B.EQ bb1
        // ADD between CMP and BCond breaks the pair.
        let mut func = MachFunction::new(
            "test_non_consecutive".to_string(),
            Signature::new(vec![], vec![]),
        );

        let bb0 = func.entry;
        let bb1 = func.create_block();

        let cmp_id = func.push_inst(MachInst::new(AArch64Opcode::CmpRI, vec![vreg(0), imm(0)]));
        func.append_inst(bb0, cmp_id);

        let add_id = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(1), vreg(2), vreg(3)],
        ));
        func.append_inst(bb0, add_id);

        let bcond_id = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(CondCode::EQ.encoding() as i64), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, bcond_id);

        let ret_id = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb1, ret_id);

        func.add_edge(bb0, bb1);

        let mut pass = CmpBranchFusion;
        // The CMP and BCond are not consecutive (ADD is between them),
        // so no fusion should occur.
        assert!(!pass.run(&mut func));

        let block = func.block(bb0);
        assert_eq!(block.insts.len(), 3);
    }

    // ---- Idempotency ----

    #[test]
    fn test_idempotent() {
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(0), imm(0)]);
        let mut func = make_func_with_branch(cmp, CondCode::EQ);

        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func)); // First: transforms
        assert!(!pass.run(&mut func)); // Second: no change
    }

    // ---- Edge cases ----

    #[test]
    fn test_empty_block_no_crash() {
        let mut func = MachFunction::new("empty".to_string(), Signature::new(vec![], vec![]));
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let ret_id = func.push_inst(ret);
        func.append_inst(func.entry, ret_id);

        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn test_single_instruction_block() {
        let mut func = MachFunction::new("single".to_string(), Signature::new(vec![], vec![]));
        // Block with only one instruction: no pair to fuse.
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(0), imm(0)]);
        let cmp_id = func.push_inst(cmp);
        func.append_inst(func.entry, cmp_id);

        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));
    }

    #[test]
    fn test_multiple_fusions_in_different_blocks() {
        // Two blocks, each with a fusible CMP+BCond.
        let mut func = MachFunction::new("multi_block".to_string(), Signature::new(vec![], vec![]));

        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        // bb0: CMP v0, #0; B.EQ bb1
        let cmp0_id = func.push_inst(MachInst::new(AArch64Opcode::CmpRI, vec![vreg(0), imm(0)]));
        func.append_inst(bb0, cmp0_id);
        let bcond0_id = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(CondCode::EQ.encoding() as i64), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, bcond0_id);

        // bb1: TST v1, #4; B.NE bb2
        let tst1_id = func.push_inst(MachInst::new(AArch64Opcode::Tst, vec![vreg(1), imm(4)]));
        func.append_inst(bb1, tst1_id);
        let bcond1_id = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(CondCode::NE.encoding() as i64), MachOperand::Block(bb2)],
        ));
        func.append_inst(bb1, bcond1_id);

        // bb2: RET
        let ret_id = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret_id);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);

        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));

        // bb0 should have 1 inst: CBZ
        let block0 = func.block(bb0);
        assert_eq!(block0.insts.len(), 1);
        assert_eq!(func.inst(block0.insts[0]).opcode, AArch64Opcode::Cbz);

        // bb1 should have 1 inst: TBNZ
        let block1 = func.block(bb1);
        assert_eq!(block1.insts.len(), 1);
        assert_eq!(func.inst(block1.insts[0]).opcode, AArch64Opcode::Tbnz);
        assert_eq!(func.inst(block1.insts[0]).operands[1], imm(2)); // bit 2 for mask 4
    }

    // ---- Deferred CSET-then-branch collapse tests ----

    /// Build `bb0: CMP v0,v1; CSET v2,<cset_cond>; <mid...>; <branch> v2, bb1`
    /// with `bb1: RET`. Returns the function; instruction ids are positional.
    fn make_deferred_cset_func(
        cset_cond: CondCode,
        mid: Vec<MachInst>,
        branch_opcode: AArch64Opcode,
    ) -> MachFunction {
        let mut func = MachFunction::new(
            "test_deferred_cset".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();

        let cmp_id = func.push_inst(MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]));
        func.append_inst(bb0, cmp_id);
        let cset_id = func.push_inst(MachInst::new(
            AArch64Opcode::CSet,
            vec![vreg(2), imm(cset_cond.encoding() as i64)],
        ));
        func.append_inst(bb0, cset_id);
        for inst in mid {
            let id = func.push_inst(inst);
            func.append_inst(bb0, id);
        }
        let branch_id = func.push_inst(MachInst::new(
            branch_opcode,
            vec![vreg(2), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, branch_id);

        let ret_id = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb1, ret_id);
        func.add_edge(bb0, bb1);
        func
    }

    #[test]
    fn test_deferred_cset_cbnz_collapses_across_flag_neutral_gap() {
        // CMP; CSET v2,LT; ADD; LDR; CBNZ v2 -> CMP; ADD; LDR; B.LT
        let mid = vec![
            MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(3), imm(4)]),
            MachInst::new(AArch64Opcode::LdrRI, vec![vreg(4), vreg(3), imm(0)]),
        ];
        let mut func = make_deferred_cset_func(CondCode::LT, mid, AArch64Opcode::Cbnz);

        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4, "CSET deleted, gap untouched");
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::CmpRR);
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::AddRI);
        assert_eq!(func.inst(block.insts[2]).opcode, AArch64Opcode::LdrRI);
        let branch = func.inst(block.insts[3]);
        assert_eq!(branch.opcode, AArch64Opcode::BCond);
        assert_eq!(branch.operands[0], imm(CondCode::LT.encoding() as i64));
        assert_eq!(branch.operands[1], MachOperand::Block(BlockId(1)));
    }

    #[test]
    fn test_deferred_cset_cbz_inverts_condition() {
        // CBZ branches when the CSET condition was FALSE -> B.GE for CSET LT.
        let mid = vec![MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(3), vreg(3), imm(1)],
        )];
        let mut func = make_deferred_cset_func(CondCode::LT, mid, AArch64Opcode::Cbz);

        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3);
        let branch = func.inst(block.insts[2]);
        assert_eq!(branch.opcode, AArch64Opcode::BCond);
        assert_eq!(branch.operands[0], imm(CondCode::GE.encoding() as i64));
    }

    #[test]
    fn test_deferred_cset_adjacent_collapses() {
        let mut func = make_deferred_cset_func(CondCode::HI, vec![], AArch64Opcode::Cbnz);

        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::CmpRR);
        let branch = func.inst(block.insts[1]);
        assert_eq!(branch.opcode, AArch64Opcode::BCond);
        assert_eq!(branch.operands[0], imm(CondCode::HI.encoding() as i64));
    }

    #[test]
    fn test_deferred_cset_declines_on_intervening_flag_writer() {
        // A second CMP between CSET and CBNZ clobbers the captured flags.
        let mid = vec![MachInst::new(AArch64Opcode::CmpRI, vec![vreg(5), imm(3)])];
        let mut func = make_deferred_cset_func(CondCode::LT, mid, AArch64Opcode::Cbnz);

        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4, "everything preserved");
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::CSet);
        assert_eq!(func.inst(block.insts[3]).opcode, AArch64Opcode::Cbnz);
    }

    #[test]
    fn test_deferred_cset_declines_on_intervening_call() {
        // BL clobbers NZCV (caller-saved).
        let mid = vec![MachInst::new(AArch64Opcode::Bl, vec![])];
        let mut func = make_deferred_cset_func(CondCode::LT, mid, AArch64Opcode::Cbnz);

        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block(func.entry).insts.len(), 4);
    }

    #[test]
    fn test_deferred_cset_declines_on_intervening_trap_carrier() {
        // TrapBoundsCheckExact expands to `CMP; B.LO; BRK` at codegen time,
        // so it clobbers NZCV even though writes_flags() is false for it.
        let mid = vec![MachInst::new(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![vreg(6), vreg(7), imm(10)],
        )];
        let mut func = make_deferred_cset_func(CondCode::LT, mid, AArch64Opcode::Cbnz);

        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block(func.entry).insts.len(), 4);
    }

    #[test]
    fn test_deferred_cset_declines_on_multi_use_bool() {
        // The CSET result is also consumed by an ADD -> not dead, keep it.
        let mid = vec![MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg(3), vreg(2), vreg(4)],
        )];
        let mut func = make_deferred_cset_func(CondCode::LT, mid, AArch64Opcode::Cbnz);

        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block(func.entry).insts.len(), 4);
    }

    #[test]
    fn test_deferred_cset_declines_on_vreg_redefinition() {
        // v2 is redefined between the CSET and the branch: the branch reads
        // the MOV's value, not the CSET's — must not collapse. (MovR's source
        // v9 is unused elsewhere; use counts still see exactly one v2 use.)
        let mid = vec![MachInst::new(AArch64Opcode::MovR, vec![vreg(2), vreg(9)])];
        let mut func = make_deferred_cset_func(CondCode::LT, mid, AArch64Opcode::Cbnz);

        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block(func.entry).insts.len(), 4);
    }

    #[test]
    fn test_deferred_cset_declines_cross_block() {
        // CSET in bb0, CBNZ in bb1 -> no in-block reaching def, decline.
        let mut func = MachFunction::new(
            "test_deferred_cset_cross_block".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();

        let cmp_id = func.push_inst(MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]));
        func.append_inst(bb0, cmp_id);
        let cset_id = func.push_inst(MachInst::new(
            AArch64Opcode::CSet,
            vec![vreg(2), imm(CondCode::LT.encoding() as i64)],
        ));
        func.append_inst(bb0, cset_id);

        let branch_id = func.push_inst(MachInst::new(
            AArch64Opcode::Cbnz,
            vec![vreg(2), MachOperand::Block(bb2)],
        ));
        func.append_inst(bb1, branch_id);
        let ret_id = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret_id);
        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);

        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block(bb0).insts, vec![cmp_id, cset_id]);
        assert_eq!(func.inst(branch_id).opcode, AArch64Opcode::Cbnz);
    }

    #[test]
    fn test_deferred_cset_cbz_declines_on_al_condition() {
        // CSET AL cannot be inverted -> CBZ collapse must decline.
        let mut func = make_deferred_cset_func(CondCode::AL, vec![], AArch64Opcode::Cbz);

        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));
        assert_eq!(func.block(func.entry).insts.len(), 3);
    }

    #[test]
    fn test_deferred_cset_provenance_merges_and_keeps_flag_compare_live() {
        let mid = vec![MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(3), vreg(3), imm(4)],
        )];
        let mut func = make_deferred_cset_func(CondCode::LT, mid, AArch64Opcode::Cbnz);
        let insts = func.block(func.entry).insts.clone();
        let (cmp_id, cset_id, add_id, branch_id) = (insts[0], insts[1], insts[2], insts[3]);

        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(60), &[cmp_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(61), &[cset_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(62), &[add_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(63), &[branch_id], PassId::new("isel"));

        let mut pass = CmpBranchFusion;
        let mut analyses = AnalysisCache::new();
        assert!(pass.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance));

        assert_eq!(
            func.block(func.entry).insts,
            vec![cmp_id, add_id, branch_id]
        );
        assert_eq!(func.inst(branch_id).opcode, AArch64Opcode::BCond);

        assert!(
            provenance.get_entry(cmp_id).unwrap().is_active(),
            "flag-setting compare remains live after deferred CSET collapse"
        );
        let branch_entry = provenance.get_entry(branch_id).unwrap();
        for origin in [TrustIrInstId(60), TrustIrInstId(61), TrustIrInstId(63)] {
            assert!(
                branch_entry.trust_ir_origins.contains(&origin),
                "fused branch should retain origin {origin:?}"
            );
        }
    }

    #[test]
    fn test_deferred_cset_composes_with_cmp_zero_fusion() {
        // `cmp; cset lt; add; cmp bool,#0; b.ne` needs BOTH families: the
        // pair loop first forms `cbnz bool`, then (next sweep) the deferred
        // collapse folds it back onto the original flags -> `cmp; add; b.lt`.
        let mut func = MachFunction::new(
            "test_deferred_cset_compose".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();

        let cmp_id = func.push_inst(MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]));
        func.append_inst(bb0, cmp_id);
        let cset_id = func.push_inst(MachInst::new(
            AArch64Opcode::CSet,
            vec![vreg(2), imm(CondCode::LT.encoding() as i64)],
        ));
        func.append_inst(bb0, cset_id);
        let add_id = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(3), vreg(3), imm(4)],
        ));
        func.append_inst(bb0, add_id);
        let cmp_zero_id =
            func.push_inst(MachInst::new(AArch64Opcode::CmpRI, vec![vreg(2), imm(0)]));
        func.append_inst(bb0, cmp_zero_id);
        let bcond_id = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(CondCode::NE.encoding() as i64), MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, bcond_id);
        let ret_id = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb1, ret_id);
        func.add_edge(bb0, bb1);

        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));

        let block = func.block(bb0);
        assert_eq!(block.insts, vec![cmp_id, add_id, bcond_id]);
        let branch = func.inst(bcond_id);
        assert_eq!(branch.opcode, AArch64Opcode::BCond);
        assert_eq!(branch.operands[0], imm(CondCode::LT.encoding() as i64));
    }

    // ---- Helper function tests ----

    #[test]
    fn test_is_power_of_two() {
        assert!(is_power_of_two(1));
        assert!(is_power_of_two(2));
        assert!(is_power_of_two(4));
        assert!(is_power_of_two(1 << 63));
        assert!(!is_power_of_two(0));
        assert!(!is_power_of_two(3));
        assert!(!is_power_of_two(6));
        assert!(!is_power_of_two(u64::MAX));
    }

    #[test]
    fn test_decode_cond_all_values() {
        assert_eq!(decode_cond(0b0000), Some(CondCode::EQ));
        assert_eq!(decode_cond(0b0001), Some(CondCode::NE));
        assert_eq!(decode_cond(0b0010), Some(CondCode::HS));
        assert_eq!(decode_cond(0b0011), Some(CondCode::LO));
        assert_eq!(decode_cond(0b1110), Some(CondCode::AL));
        assert_eq!(decode_cond(0b1111), Some(CondCode::NV));
        assert_eq!(decode_cond(16), None);
    }

    #[test]
    fn test_sets_flags() {
        assert!(sets_flags(AArch64Opcode::CmpRR));
        assert!(sets_flags(AArch64Opcode::CmpRI));
        assert!(sets_flags(AArch64Opcode::Tst));
        assert!(sets_flags(AArch64Opcode::AddsRR));
        assert!(!sets_flags(AArch64Opcode::AddRR));
        assert!(!sets_flags(AArch64Opcode::MovR));
        assert!(!sets_flags(AArch64Opcode::B));
    }

    // ------------------------------------------------------------------
    // Variable single-bit test fusion:
    //   LslRR m, one(#1), amt ; AndRR t, w, m ; Cbz/Cbnz t
    //     ->  LsrRR t, w, amt ; Tbz/Tbnz t, #0
    // ------------------------------------------------------------------

    /// Build: bb0 = [prefix..., LslRR m(5),one(1),amt(2); AndRR t(6),w(4),m(5);
    /// branch t(6) -> bb1], bb1 = RET. `one` (v1) is materialized in bb0 by
    /// default (same-block const def).
    fn make_bit_test_func(branch_op: AArch64Opcode, one_imm: i64) -> MachFunction {
        let mut func = MachFunction::new("bit_test".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let movi = MachInst::new(AArch64Opcode::MovI, vec![vreg32(1), imm(one_imm)]);
        let lsl = MachInst::new(AArch64Opcode::LslRR, vec![vreg32(5), vreg32(1), vreg32(2)]);
        let and = MachInst::new(AArch64Opcode::AndRR, vec![vreg32(6), vreg32(4), vreg32(5)]);
        let br = MachInst::new(branch_op, vec![vreg32(6), MachOperand::Block(bb1)]);
        for inst in [movi, lsl, and, br] {
            let id = func.push_inst(inst);
            func.append_inst(bb0, id);
        }
        let ret_id = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb1, ret_id);
        func.add_edge(bb0, bb1);
        func
    }

    #[test]
    fn bit_test_cbz_becomes_lsr_tbz() {
        let mut func = make_bit_test_func(AArch64Opcode::Cbz, 1);
        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));
        let insts = &func.block(func.entry).insts;
        // MovI survives (dead-code cleanup is DCE's job); LslRR deleted.
        assert_eq!(insts.len(), 3);
        assert_eq!(func.inst(insts[0]).opcode, AArch64Opcode::MovI);
        let lsr = func.inst(insts[1]);
        assert_eq!(lsr.opcode, AArch64Opcode::LsrRR);
        assert_eq!(lsr.operands[0], vreg32(6)); // t reused as dst
        assert_eq!(lsr.operands[1], vreg32(4)); // w (tested word)
        assert_eq!(lsr.operands[2], vreg32(2)); // amt
        let tb = func.inst(insts[2]);
        assert_eq!(tb.opcode, AArch64Opcode::Tbz);
        assert_eq!(tb.operands[0], vreg32(6));
        assert_eq!(tb.operands[1], imm(0));
    }

    #[test]
    fn bit_test_cbnz_becomes_lsr_tbnz() {
        let mut func = make_bit_test_func(AArch64Opcode::Cbnz, 1);
        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));
        let insts = &func.block(func.entry).insts;
        assert_eq!(func.inst(insts[1]).opcode, AArch64Opcode::LsrRR);
        assert_eq!(func.inst(insts[2]).opcode, AArch64Opcode::Tbnz);
    }

    /// AND operand order is commutative: `AndRR t, m, w` also fuses.
    #[test]
    fn bit_test_commuted_and_order() {
        let mut func = make_bit_test_func(AArch64Opcode::Cbz, 1);
        // Swap the AND sources: [t, m, w].
        let and_id = func.block(func.entry).insts[2];
        func.inst_mut(and_id).operands = vec![vreg32(6), vreg32(5), vreg32(4)];
        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));
        let lsr = func.inst(func.block(func.entry).insts[1]);
        assert_eq!(lsr.opcode, AArch64Opcode::LsrRR);
        assert_eq!(lsr.operands[1], vreg32(4)); // w correctly identified
    }

    /// Composes with CBZ formation in the same run: the pre-fusion shape
    /// `...; AndRR t; CmpRI t, #0; B.EQ` first becomes `...; AndRR t; CBZ t`
    /// (sweep 1), then the triple fuses (sweep 2).
    #[test]
    fn bit_test_composes_with_cmp_zero_fusion() {
        let mut func =
            MachFunction::new("bit_test_cmp".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        for inst in [
            MachInst::new(AArch64Opcode::MovI, vec![vreg32(1), imm(1)]),
            MachInst::new(AArch64Opcode::LslRR, vec![vreg32(5), vreg32(1), vreg32(2)]),
            MachInst::new(AArch64Opcode::AndRR, vec![vreg32(6), vreg32(4), vreg32(5)]),
            MachInst::new(AArch64Opcode::CmpRI, vec![vreg32(6), imm(0)]),
            MachInst::new(
                AArch64Opcode::BCond,
                vec![imm(CondCode::EQ.encoding() as i64), MachOperand::Block(bb1)],
            ),
        ] {
            let id = func.push_inst(inst);
            func.append_inst(bb0, id);
        }
        let ret_id = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb1, ret_id);
        func.add_edge(bb0, bb1);

        let mut pass = CmpBranchFusion;
        assert!(pass.run(&mut func));
        let insts = &func.block(func.entry).insts;
        assert_eq!(insts.len(), 3); // MovI + LsrRR + Tbz
        assert_eq!(func.inst(insts[1]).opcode, AArch64Opcode::LsrRR);
        assert_eq!(func.inst(insts[2]).opcode, AArch64Opcode::Tbz);
    }

    /// The `#1` may be materialized in a DOMINATING block (the hoisted
    /// loop-invariant shape) — accepted on the analyses path (dominator tree).
    #[test]
    fn bit_test_dominating_const_one() {
        let mut func =
            MachFunction::new("bit_test_dom".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        // bb0: one = #1; b bb1
        for inst in [
            MachInst::new(AArch64Opcode::MovI, vec![vreg32(1), imm(1)]),
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
        ] {
            let id = func.push_inst(inst);
            func.append_inst(bb0, id);
        }
        // bb1: the triple.
        for inst in [
            MachInst::new(AArch64Opcode::LslRR, vec![vreg32(5), vreg32(1), vreg32(2)]),
            MachInst::new(AArch64Opcode::AndRR, vec![vreg32(6), vreg32(4), vreg32(5)]),
            MachInst::new(AArch64Opcode::Cbz, vec![vreg32(6), MachOperand::Block(bb2)]),
        ] {
            let id = func.push_inst(inst);
            func.append_inst(bb1, id);
        }
        let ret_id = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret_id);
        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);

        let mut pass = CmpBranchFusion;
        // Plain run (no dominator info): fails closed — cross-block const.
        let mut unfused = func.clone();
        assert!(!pass.run(&mut unfused));
        // Analyses path: the dominating const is proven, the triple fuses.
        let mut provenance = ProvenanceMap::new();
        let mut analyses = crate::pass_manager::AnalysisCache::new();
        assert!(pass.run_with_analyses_and_provenance(&mut func, &mut analyses, &mut provenance));
        let insts = &func.block(bb1).insts;
        assert_eq!(func.inst(insts[0]).opcode, AArch64Opcode::LsrRR);
        assert_eq!(func.inst(insts[1]).opcode, AArch64Opcode::Tbz);
    }

    /// `one` is NOT 1 — must not fire.
    #[test]
    fn bit_test_declines_non_one_constant() {
        let mut func = make_bit_test_func(AArch64Opcode::Cbz, 2);
        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));
    }

    /// The mask `m` has a second reader — must not fire.
    #[test]
    fn bit_test_declines_multi_use_mask() {
        let mut func = make_bit_test_func(AArch64Opcode::Cbz, 1);
        let bb1 = match func.inst(func.block(func.entry).insts[3]).operands[1] {
            MachOperand::Block(b) => b,
            _ => unreachable!(),
        };
        // Read m (v5) again in the successor (the EOR of a flip path).
        let eor = func.push_inst(MachInst::new(
            AArch64Opcode::EorRR,
            vec![vreg32(9), vreg32(4), vreg32(5)],
        ));
        let bb1_insts = func.block(bb1).insts.clone();
        func.block_mut(bb1).insts = std::iter::once(eor).chain(bb1_insts).collect();
        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));
    }

    /// The AND result `t` has a second reader — must not fire.
    #[test]
    fn bit_test_declines_multi_use_test_value() {
        let mut func = make_bit_test_func(AArch64Opcode::Cbz, 1);
        let bb1 = match func.inst(func.block(func.entry).insts[3]).operands[1] {
            MachOperand::Block(b) => b,
            _ => unreachable!(),
        };
        let use_t = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRR,
            vec![vreg32(6), vreg32(6)],
        ));
        let bb1_insts = func.block(bb1).insts.clone();
        func.block_mut(bb1).insts = std::iter::once(use_t).chain(bb1_insts).collect();
        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));
    }

    /// A second def of `one` anywhere poisons the constant — must not fire.
    #[test]
    fn bit_test_declines_multi_def_one() {
        let mut func = make_bit_test_func(AArch64Opcode::Cbz, 1);
        let bb1 = match func.inst(func.block(func.entry).insts[3]).operands[1] {
            MachOperand::Block(b) => b,
            _ => unreachable!(),
        };
        let redef = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg32(1), imm(7)]));
        let bb1_insts = func.block(bb1).insts.clone();
        func.block_mut(bb1).insts = std::iter::once(redef).chain(bb1_insts).collect();
        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));
    }

    /// An intervening instruction between the AND and the branch breaks the
    /// required adjacency — must not fire.
    #[test]
    fn bit_test_declines_non_adjacent() {
        let mut func = make_bit_test_func(AArch64Opcode::Cbz, 1);
        let bb0 = func.entry;
        let filler = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg32(8), vreg32(7), imm(1)],
        ));
        let insts = func.block(bb0).insts.clone();
        // Insert the filler between AndRR (idx 2) and the branch (idx 3).
        let mut new_insts = insts.clone();
        new_insts.insert(3, filler);
        func.block_mut(bb0).insts = new_insts;
        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));
    }

    /// Register-width mismatch between the LSL and the AND — must not fire.
    #[test]
    fn bit_test_declines_width_mismatch() {
        let mut func = make_bit_test_func(AArch64Opcode::Cbz, 1);
        let lsl_id = func.block(func.entry).insts[1];
        // 64-bit mask register feeding the 32-bit AND.
        func.inst_mut(lsl_id).operands[0] = vreg_class(5, RegClass::Gpr64);
        let and_id = func.block(func.entry).insts[2];
        func.inst_mut(and_id).operands[2] = vreg_class(5, RegClass::Gpr64);
        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));
    }

    // ------------------------------------------------------------------
    // Cross-block redundant compare elimination (three-way comparator):
    //   A: cmp v0,v1; b.gt bbGt; b bbElse
    //   bbElse(B): cmp v0,v1; b.lt bbLt; b bbEq
    //     ->  bbElse: b.lt bbLt; b bbEq   (B's cmp deleted; reuses A's NZCV)
    // ------------------------------------------------------------------

    /// Build the three-way comparator. `a_tail` is inserted in A between the
    /// compare and the conditional branch; `b_head` is inserted in B before
    /// the compare. Returns (func, A_cmp_id, B_cmp_id).
    fn make_three_way(
        a_cmp: MachInst,
        b_cmp: MachInst,
        a_tail: Vec<MachInst>,
        b_head: Vec<MachInst>,
    ) -> (MachFunction, InstId, InstId) {
        let mut func = MachFunction::new("three_way".to_string(), Signature::new(vec![], vec![]));
        let bb_a = func.entry;
        let bb_gt = func.create_block();
        let bb_b = func.create_block(); // the else arm (fall-through)
        let bb_lt = func.create_block();
        let bb_eq = func.create_block();

        // A: cmp; <a_tail...>; b.gt bb_gt; b bb_b
        let a_cmp_id = func.push_inst(a_cmp);
        func.append_inst(bb_a, a_cmp_id);
        for inst in a_tail {
            let id = func.push_inst(inst);
            func.append_inst(bb_a, id);
        }
        let a_bgt = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![
                imm(CondCode::GT.encoding() as i64),
                MachOperand::Block(bb_gt),
            ],
        ));
        func.append_inst(bb_a, a_bgt);
        let a_b = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb_b)],
        ));
        func.append_inst(bb_a, a_b);

        // B: <b_head...>; cmp; b.lt bb_lt; b bb_eq
        for inst in b_head {
            let id = func.push_inst(inst);
            func.append_inst(bb_b, id);
        }
        let b_cmp_id = func.push_inst(b_cmp);
        func.append_inst(bb_b, b_cmp_id);
        let b_blt = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![
                imm(CondCode::LT.encoding() as i64),
                MachOperand::Block(bb_lt),
            ],
        ));
        func.append_inst(bb_b, b_blt);
        let b_b = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb_eq)],
        ));
        func.append_inst(bb_b, b_b);

        for bb in [bb_gt, bb_lt, bb_eq] {
            let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
            func.append_inst(bb, ret);
        }

        func.add_edge(bb_a, bb_gt);
        func.add_edge(bb_a, bb_b);
        func.add_edge(bb_b, bb_lt);
        func.add_edge(bb_b, bb_eq);

        (func, a_cmp_id, b_cmp_id)
    }

    #[test]
    fn cross_block_redundant_cmp_deleted() {
        let (mut func, _a_cmp, b_cmp) = make_three_way(
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]),
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]),
            vec![],
            vec![],
        );
        let bb_b = func.block(func.entry).succs[1];
        // Keep the kill switch logically absent on this thread.
        let fired =
            crate::env_lock::with_env_overrides_removed(&["TCG_NO_CROSS_BLOCK_CMP_ELIM"], || {
                CmpBranchFusion.run(&mut func)
            });
        assert!(fired);
        // B's compare is deleted; its branch (now b.lt) reuses A's NZCV.
        let b = func.block(bb_b);
        assert!(
            !b.insts.contains(&b_cmp),
            "redundant B compare must be gone"
        );
        assert_eq!(func.inst(b.insts[0]).opcode, AArch64Opcode::BCond);
        assert_eq!(
            func.inst(b.insts[0]).operands[0],
            imm(CondCode::LT.encoding() as i64)
        );
        // A's compare stays.
        assert_eq!(
            func.inst(func.block(func.entry).insts[0]).opcode,
            AArch64Opcode::CmpRR
        );
    }

    #[test]
    fn cross_block_redundant_cmpri_deleted() {
        let (mut func, _a, b_cmp) = make_three_way(
            MachInst::new(AArch64Opcode::CmpRI, vec![vreg(0), imm(5)]),
            MachInst::new(AArch64Opcode::CmpRI, vec![vreg(0), imm(5)]),
            vec![],
            vec![],
        );
        let bb_b = func.block(func.entry).succs[1];
        let fired =
            crate::env_lock::with_env_overrides_removed(&["TCG_NO_CROSS_BLOCK_CMP_ELIM"], || {
                CmpBranchFusion.run(&mut func)
            });
        assert!(fired);
        assert!(!func.block(bb_b).insts.contains(&b_cmp));
    }

    #[test]
    fn cross_block_declines_on_different_immediate() {
        let (mut func, _a, b_cmp) = make_three_way(
            MachInst::new(AArch64Opcode::CmpRI, vec![vreg(0), imm(5)]),
            MachInst::new(AArch64Opcode::CmpRI, vec![vreg(0), imm(6)]),
            vec![],
            vec![],
        );
        let bb_b = func.block(func.entry).succs[1];
        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));
        assert!(func.block(bb_b).insts.contains(&b_cmp));
    }

    #[test]
    fn cross_block_declines_on_flag_writer_in_a_tail() {
        // A second CMP in A after C_A clobbers the flags before the edge.
        let (mut func, _a, b_cmp) = make_three_way(
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]),
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]),
            vec![MachInst::new(AArch64Opcode::CmpRI, vec![vreg(4), imm(3)])],
            vec![],
        );
        let bb_b = func.block(func.entry).succs[1];
        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));
        assert!(func.block(bb_b).insts.contains(&b_cmp));
    }

    #[test]
    fn cross_block_declines_on_operand_redef_in_b_head() {
        // v0 is rewritten in B before the compare -> B's cmp reads a
        // different value than A's; must not reuse A's flags.
        let (mut func, _a, b_cmp) = make_three_way(
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]),
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]),
            vec![],
            vec![MachInst::new(
                AArch64Opcode::AddRI,
                vec![vreg(0), vreg(0), imm(1)],
            )],
        );
        let bb_b = func.block(func.entry).succs[1];
        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));
        assert!(func.block(bb_b).insts.contains(&b_cmp));
    }

    #[test]
    fn cross_block_declines_on_multiple_predecessors() {
        // Give B a second predecessor: the A->B edge is no longer the only
        // path in, so B's NZCV live-in is not guaranteed to be A's.
        let (mut func, _a, b_cmp) = make_three_way(
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]),
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]),
            vec![],
            vec![],
        );
        let bb_a = func.entry;
        let bb_b = func.block(bb_a).succs[1];
        let bb_extra = func.create_block();
        let br = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb_b)],
        ));
        func.append_inst(bb_extra, br);
        func.add_edge(bb_extra, bb_b);
        let mut pass = CmpBranchFusion;
        assert!(!pass.run(&mut func));
        assert!(func.block(bb_b).insts.contains(&b_cmp));
    }

    #[test]
    fn cross_block_kill_switch() {
        let (func, fired, b_cmp) =
            crate::env_lock::with_env_overrides(&[("TCG_NO_CROSS_BLOCK_CMP_ELIM", "1")], || {
                let (mut func, _a, b_cmp) = make_three_way(
                    MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]),
                    MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]),
                    vec![],
                    vec![],
                );
                let fired = CmpBranchFusion.run(&mut func);
                (func, fired, b_cmp)
            });
        assert!(!fired);
        let bb_b = func.block(func.entry).succs[1];
        assert!(func.block(bb_b).insts.contains(&b_cmp));
    }

    /// Kill switch: `TCG_NO_BIT_TEST_BRANCH_FUSE` disables only this fusion.
    #[test]
    fn bit_test_kill_switch() {
        let (func, fired) =
            crate::env_lock::with_env_overrides(&[("TCG_NO_BIT_TEST_BRANCH_FUSE", "1")], || {
                let mut func = make_bit_test_func(AArch64Opcode::Cbz, 1);
                let fired = CmpBranchFusion.run(&mut func);
                (func, fired)
            });
        assert!(!fired);
        assert_eq!(
            func.inst(func.block(func.entry).insts[3]).opcode,
            AArch64Opcode::Cbz
        );
    }
}
