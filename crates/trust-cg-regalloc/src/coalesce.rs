// trust-cg-regalloc/coalesce.rs - Copy coalescing for register allocation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Copy coalescing for phi-elimination copies.
//!
//! After phi elimination inserts `PSEUDO_COPY` instructions, many of these
//! copies can be eliminated by merging the live intervals of the source and
//! destination when they don't interfere. This pass computes a deferred edit
//! plan rather than mutating the `MachFunction` directly; the returned
//! removals and rewrites can be applied later with [`apply_coalescing`].
//!
//! The algorithm uses union-find for transitive coalescing: if A is coalesced
//! into B and B into C, all references to A resolve to C.
//!
//! Reference: LLVM `RegisterCoalescer.cpp` — simplified to pure virtual
//! register coalescing without sub-register handling.

use crate::liveness::{LiveInterval, LiveRange, number_insts};
use crate::machine_types::{InstId, MachFunction, MachOperand, RegClass, VReg};
use crate::phi_elim;
use std::collections::{BTreeMap, BTreeSet};

/// Target-supplied tuning for the pre-RA copy coalescer beyond plain
/// non-overlapping merges. Opcode values are the target enum's `u16`s and are
/// therefore TARGET-SPECIFIC: each target's `AllocConfig` constructor supplies
/// its own sets, and the empty default (used by the x86-64 configs, whose
/// opcode namespace numerically collides with AArch64's) disables both
/// extensions entirely.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CoalesceTuning {
    /// "Move-like" opcodes with shape `def d, use s, Imm(0)` to NORMALIZE into
    /// real copy instructions before the pre-alloc snapshot is taken — the
    /// `LoopLatchLayoutCombine` hardened `AddRI dst, src, #0` latch guard
    /// copies. Hardening exists to protect the rotated-latch parallel-copy
    /// semantics from OPT-level copy propagation and from post-RA retargeting;
    /// the regalloc coalescer's interference-checked interval merging (further
    /// certified by the always-on hardened translation validator) is exactly
    /// the machinery that CAN handle them soundly, so inside `allocate` they
    /// become ordinary copies again. An unmerged survivor lowers to a plain
    /// `mov` — same cost as the `add #0` it replaced.
    pub move_like_zero_ops: BTreeSet<u16>,
    /// Full-register vreg-to-vreg MOVE opcodes to NORMALIZE into real copy
    /// instructions (AArch64 `MovR`/`MOVWrr`/`MOVXrr`/`FmovFprFpr`): some ISel
    /// paths emit these directly instead of `Copy`, hiding block-param copies
    /// from the coalescer entirely. Normalization is shape-gated to same-class
    /// vreg-vreg moves whose encoding is class-driven, so the class-aware Copy
    /// re-lowering emits the identical instruction for any survivor. The map
    /// value constrains the REQUIRED register class (`None` = any, as long as
    /// dst/src classes are equal): `MOVWrr` is W-form only (a W-form mov of
    /// Gpr64 vregs is a deliberate 32-bit truncation idiom and must NOT become
    /// a class-driven Copy).
    pub reg_move_ops: BTreeMap<u16, Option<RegClass>>,
    /// Whole-vector-register MOVE idioms with shape `def d, use s, use s` (the
    /// SAME source vreg TWICE) to NORMALIZE into real copy instructions:
    /// AArch64 `NeonOrrV d, s, s` (`ORR Vd.16B, Vn.16B, Vn.16B`, the
    /// architectural `MOV Vd.16B, Vn.16B` alias). The NEON vectorizers emit
    /// this as a defensive copy of the loaded FMA addend ahead of an in-place
    /// `FMLA` accumulator (`neon_fmap` / `neon_farray` / `neon_butterfly`);
    /// hidden from the coalescer it costs one `mov.16b` per vector lane-group
    /// per iteration (the Linpack daxpy tail). Normalization is shape-gated to
    /// `Fpr128` dst/src with IDENTICAL source vregs: the post-alloc class-aware
    /// Copy re-lowering maps an `Fpr128` survivor back to exactly
    /// `NeonOrrV d, s, s` (see codegen `lower_copies`), so an unmerged copy
    /// costs the same instruction it replaced. A two-distinct-source `NeonOrrV`
    /// is a genuine bitwise OR and is never touched, and scalar-class (`Fpr64`
    /// etc.) forms are excluded because their re-lowering forces the `.16B`
    /// Q=1 arrangement rather than the class-implied `.8B` encoding.
    /// (`post_ra_coalesce` already treats the `NeonOrrV d, s, s` shape as a
    /// copy post-RA — this is the pre-RA mirror, where interference-checked
    /// interval merging can retarget the producer instead of just renaming.)
    pub vec_move_ops: BTreeSet<u16>,
    /// Producer opcodes PROVEN to encode as a single machine instruction that
    /// reads all its register sources before writing its single destination
    /// (no multi-instruction expansion that could use the destination as a
    /// scratch). A copy `d <- s` whose only interval overlap with `s` is the
    /// kill-then-def at such a producer (d's last use feeds the instruction
    /// that defines s) may be merged: the retargeted producer becomes an
    /// in-place update (`add d, d, #1` / `fadd d, d, x` / `csel d, a, d`).
    /// Empty disables the kill-at-def rule.
    pub kill_def_producers: BTreeSet<u16>,
    /// Subset of [`Self::kill_def_producers`] whose SECOND register source
    /// (`uses[1]`, the shifted `Rm` of the AArch64 shifted-register ALU forms)
    /// must NOT be the coalesced destination. For these opcodes `Rm` feeds the
    /// shifter, and making it the loop-carried in-place register measurably
    /// lengthens the recurrence on real cores: retargeting
    /// `eor t, x, d, lsr #11; d <- t` to `eor d, x, d, lsr #11` regressed
    /// `m2_call_heavy` 35 -> 51 ms (1.46x, reproduced with a one-word binary
    /// patch of just that destination field), while the same merge carried
    /// through the un-shifted `Rn` (`eor d, d, t, ror #55`, p5_struct_acc)
    /// closed a 1.023x gap entirely. The merge is refused (fail-closed, the
    /// copy simply stays) whenever the killed value resolves to the `uses[1]`
    /// slot; membership here is only meaningful for opcodes also present in
    /// `kill_def_producers`.
    pub kill_def_rn_only_producers: BTreeSet<u16>,
}

impl CoalesceTuning {
    /// AArch64 tuning: normalize the hardened `AddRI #0` guard copies, and
    /// allow kill-at-def merges across the simple single-instruction ALU/FP
    /// producers that appear in loop-carried updates. Every opcode listed is a
    /// one-to-one encoded instruction with a single register destination
    /// written after all source reads (standard AArch64 read-then-write
    /// semantics; none has an early-clobber or multi-instruction expansion in
    /// this backend's encoder).
    pub fn aarch64() -> Self {
        use trust_cg_ir::inst::AArch64Opcode as A;
        let move_like_zero_ops = [A::AddRI as u16].into_iter().collect();
        let reg_move_ops = [
            (A::MovR as u16, None),
            (A::MOVWrr as u16, Some(RegClass::Gpr32)),
            (A::MOVXrr as u16, Some(RegClass::Gpr64)),
            (A::FmovFprFpr as u16, None),
        ]
        .into_iter()
        .collect();
        // `NeonOrrV d, s, s` addend/accumulator copies (see `vec_move_ops`).
        // Kill switch `TCG_AARCH64_NEON_ORR_COALESCE_OFF`: with the opcode
        // absent the normalizer never rewrites it and the emitted object is
        // byte-identical to the pre-lever compiler.
        let vec_move_ops = if std::env::var_os("TCG_AARCH64_NEON_ORR_COALESCE_OFF").is_some() {
            BTreeSet::new()
        } else {
            [A::NeonOrrV as u16].into_iter().collect()
        };
        let kill_def_producers = [
            A::AddRR as u16,
            A::AddRI as u16,
            A::SubRR as u16,
            A::SubRI as u16,
            A::MulRR as u16,
            A::Madd as u16,
            A::Msub as u16,
            A::Csel as u16,
            A::FaddRR as u16,
            A::FsubRR as u16,
            A::FmulRR as u16,
            // FMADD Rd, Rn, Rm, Ra — scalar FUSED multiply-add. Same proof
            // obligation as FaddRR/FmulRR, one extra source: `encode_fp_madd`
            // emits a SINGLE 32-bit word (no expansion), Rd is a pure def
            // written after all three source reads (Rn/Rm/Ra), no early-clobber
            // and no tied operand (isel gives it a fresh `Rd` vreg). It carries
            // the `llvm.fmuladd` FP-reduction accumulator whose loop-carried
            // latch copy this rule can now merge into an in-place update.
            A::FmaddRR as u16,
            // Logical ops, register and bitmask-immediate forms — the x86-64
            // tuning already trusts And/Or/Xor {RR,RI}; the AArch64 encoder
            // arms are the same shape as the trusted AddRR/AddRI: one
            // `encode_logical_shifted_reg` / `encode_logical_immediate` word,
            // single pure def written after all source reads, fail-closed on
            // an unencodable immediate (Err, never a multi-instruction
            // expansion). Carries `acc ^= x` / `acc &= m` / `acc |= m`
            // loop-carried latch updates.
            A::AndRR as u16,
            A::AndRI as u16,
            A::OrrRR as u16,
            A::OrrRI as u16,
            A::EorRR as u16,
            A::EorRI as u16,
            // Shifted-second-source ALU fusions (`add d, n, m, lsl|lsr #k`,
            // `sub d, n, m, lsl #k`, `eor d, n, m, ror|lsl|lsr #k`) — each is
            // ONE `encode_add_sub_shifted_reg` / `encode_logical_shifted_reg`
            // word with a single pure def, all register sources read before
            // the write, and a fail-closed range check on the shift amount.
            // These carry the struct-accumulator latch shapes
            // (`b += a >> 3` -> AddRRShiftLsr, `c ^= rotl(t, k)` ->
            // EorRRShift, p5_struct_acc) that the plain-opcode list missed.
            // All six are ALSO in `kill_def_rn_only_producers`: the merge is
            // allowed only when the loop-carried value sits in the un-shifted
            // `Rn` slot (see that field's doc for the measured `Rm` hazard).
            //
            // The single-source immediate shifts (`LslRI`/`LsrRI`/`AsrRI`/
            // `RorRI`) are deliberately NOT listed even though their UBFM/EXTR
            // encodings meet the single-word proof obligation: their only
            // register source feeds the shifter, so an in-place merge would
            // always create the `Rm`-slot recurrence hazard, and no corpus
            // program benefits from them.
            A::AddRRShift as u16,
            A::AddRRShiftLsr as u16,
            A::SubRRShift as u16,
            A::EorRRShift as u16,
            A::EorRRLsl as u16,
            A::EorRRLsr as u16,
        ]
        .into_iter()
        .collect();
        let kill_def_rn_only_producers = [
            A::AddRRShift as u16,
            A::AddRRShiftLsr as u16,
            A::SubRRShift as u16,
            A::EorRRShift as u16,
            A::EorRRLsl as u16,
            A::EorRRLsr as u16,
        ]
        .into_iter()
        .collect();
        Self {
            move_like_zero_ops,
            reg_move_ops,
            vec_move_ops,
            kill_def_producers,
            kill_def_rn_only_producers,
        }
    }

    /// x86-64 tuning: allow kill-at-def merges across the simple
    /// single-instruction, single-def, read-then-write ALU producers that
    /// appear in loop-carried latch updates (`acc <- acc + x`, `iv <- iv + 1`).
    ///
    /// Every opcode listed is a genuine two-address x86 ALU instruction that
    /// reads all its register/immediate sources and then writes its single
    /// destination register in place, with no multi-instruction expansion that
    /// could use the destination as a scratch. Merging the loop-carried copy
    /// `d <- op(s, ..)` into an in-place `op d, ..` is semantically identical
    /// (RFLAGS is filtered to `None` and never enters `implicit_defs`, so the
    /// ALU flag-def does not block the merge). MOV copies are already
    /// normalized to `PSEUDO_COPY` upstream, so no `reg_move_ops` /
    /// `move_like_zero_ops` normalization is required here.
    ///
    /// Opcodes are the `X86Opcode` enum ordinals (`X86Opcode as u16`), matching
    /// the numbering the x86 pipeline feeds the allocator
    /// (`x86_regalloc_opcode_for_isel_inst` returns `inst.opcode as u16`).
    pub fn x86_64() -> Self {
        use trust_cg_ir::x86_64_ops::X86Opcode as X;
        let kill_def_producers = [
            X::AddRR as u16,
            X::AddRI as u16,
            X::SubRR as u16,
            X::SubRI as u16,
            X::ImulRR as u16,
            X::AndRR as u16,
            X::AndRI as u16,
            X::OrRR as u16,
            X::OrRI as u16,
            X::XorRR as u16,
            X::XorRI as u16,
            X::ShlRI as u16,
            X::ShrRI as u16,
            X::SarRI as u16,
        ]
        .into_iter()
        .collect();
        Self {
            move_like_zero_ops: BTreeSet::new(),
            reg_move_ops: BTreeMap::new(),
            vec_move_ops: BTreeSet::new(),
            kill_def_producers,
            kill_def_rn_only_producers: BTreeSet::new(),
        }
    }
}

/// Normalize "move-like" instructions (`op d, s, #0` for `op` in
/// `move_like_zero_ops`) into real `IR_COPY_OPCODE` copies. Run by
/// [`crate::allocate`] BEFORE the validator's pre-alloc snapshot is cloned, so
/// spec and implementation agree that these are copies (the hardened guard is
/// semantically `d = s + 0`, an identity move; AArch64 `ADD (immediate)` sets
/// no flags). Shape-gated: exactly one vreg def, one vreg use of the same
/// class, a literal `Imm(0)`, no implicit operands, no tied operands, no
/// special flags.
pub fn normalize_move_like_copies(func: &mut MachFunction, tuning: &CoalesceTuning) {
    if tuning.move_like_zero_ops.is_empty()
        && tuning.reg_move_ops.is_empty()
        && tuning.vec_move_ops.is_empty()
    {
        return;
    }
    for inst in &mut func.insts {
        let zero_add = tuning.move_like_zero_ops.contains(&inst.opcode);
        let reg_move = tuning.reg_move_ops.get(&inst.opcode);
        let vec_move = tuning.vec_move_ops.contains(&inst.opcode);
        if !zero_add && reg_move.is_none() && !vec_move {
            continue;
        }
        if !inst.implicit_defs.is_empty()
            || !inst.implicit_uses.is_empty()
            || !inst.tied_operands.is_empty()
            || inst.flags != crate::machine_types::InstFlags::default()
        {
            continue;
        }
        let [MachOperand::VReg(d)] = inst.defs.as_slice() else {
            continue;
        };
        if zero_add {
            let [MachOperand::VReg(s), MachOperand::Imm(0)] = inst.uses.as_slice() else {
                continue;
            };
            if d.class != s.class {
                continue;
            }
            inst.opcode = phi_elim::IR_COPY_OPCODE;
            inst.uses.truncate(1);
        } else if vec_move {
            let [MachOperand::VReg(s), MachOperand::VReg(s2)] = inst.uses.as_slice() else {
                continue;
            };
            // A copy ONLY when both sources name the SAME vreg (two distinct
            // sources are a genuine bitwise OR), and Fpr128-only so the
            // survivor re-lowering reproduces the identical `.16B` encoding
            // (see the `vec_move_ops` doc).
            if s != s2 || d.class != RegClass::Fpr128 || s.class != RegClass::Fpr128 {
                continue;
            }
            inst.opcode = phi_elim::IR_COPY_OPCODE;
            inst.uses.truncate(1);
        } else if let Some(required_class) = reg_move {
            let [MachOperand::VReg(s)] = inst.uses.as_slice() else {
                continue;
            };
            if d.class != s.class {
                continue;
            }
            if let Some(rc) = required_class
                && d.class != *rc
            {
                continue;
            }
            inst.opcode = phi_elim::IR_COPY_OPCODE;
        }
    }
}

/// Result of copy coalescing.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CoalesceResult {
    /// Number of copy instructions that can be removed.
    pub copies_removed: u32,
    /// Number of interval merges that were performed.
    pub intervals_merged: u32,
    /// Copy instructions to remove from their containing blocks.
    pub removals: Vec<InstId>,
    /// VReg rewrites: old virtual register -> coalesced representative.
    pub rewrites: BTreeMap<VReg, VReg>,
}

/// Scan the function for coalescible `PSEUDO_COPY` instructions.
///
/// For each copy `dst <- src`, if the current representative intervals of
/// `dst` and `src` do not overlap, `src` is coalesced into `dst`.
/// The function mutates the provided interval map but does not mutate
/// the `MachFunction`; instead it returns the copy removals and vreg rewrites
/// needed to apply the coalescing later.
pub fn coalesce_copies(
    func: &MachFunction,
    intervals: &mut BTreeMap<u32, LiveInterval>,
) -> CoalesceResult {
    coalesce_copies_tuned(func, intervals, &CoalesceTuning::default())
}

/// [`coalesce_copies`] with target [`CoalesceTuning`] (the kill-at-def and
/// pass-through-copy overlap acceptances). The default tuning reproduces the
/// historical behavior exactly.
pub fn coalesce_copies_tuned(
    func: &MachFunction,
    intervals: &mut BTreeMap<u32, LiveInterval>,
    tuning: &CoalesceTuning,
) -> CoalesceResult {
    let inst_numbering = number_insts(func);
    coalesce_copies_tuned_with_numbering(func, intervals, tuning, &inst_numbering)
}

/// [`coalesce_copies_tuned`] when the caller ALREADY holds the instruction
/// numbering for this exact `func`.
///
/// The allocator computes liveness once and keeps `inst_numbering` alongside the
/// intervals it passes here, so recomputing it inside was a whole redundant
/// liveness pass per function. The numbering MUST have been computed against the
/// same, unmutated `func` the intervals were built from — a stale numbering
/// would misplace the copy position in the overlap acceptances and silently
/// change coalescing decisions.
pub fn coalesce_copies_tuned_with_numbering(
    func: &MachFunction,
    intervals: &mut BTreeMap<u32, LiveInterval>,
    tuning: &CoalesceTuning,
    inst_numbering: &BTreeMap<InstId, u32>,
) -> CoalesceResult {
    // Dense id-indexed union-find (`parent[id]`, `None` = self-root) instead of
    // a BTreeMap<VReg,VReg> — vreg ids are a contiguous 0..next_vreg range, so
    // find/union become O(1)-per-step. `seen` accumulates every queried vreg
    // (with its class) so the final rewrite pass can iterate them without the
    // map keys.
    let mut n_vregs = func.next_vreg as usize;
    for inst in &func.insts {
        for op in inst.defs.iter().chain(inst.uses.iter()) {
            if let Some(v) = op.as_vreg() {
                n_vregs = n_vregs.max(v.id as usize + 1);
            }
        }
    }
    let mut parent: Vec<Option<VReg>> = vec![None; n_vregs];
    let mut seen: Vec<VReg> = Vec::new();
    let mut result = CoalesceResult::default();
    let debug_decisions = std::env::var("TRUST_CG_DEBUG_COALESCE").is_ok();

    // The conflated-position liveness model reports v0 and v1 as
    // overlapping at the copy instruction whenever v0's last use is the
    // copy itself: the use kill and the new def share one position. The
    // copy is a register move, so the source and destination occupy the
    // same physical storage at that instruction; the apparent overlap
    // does not reflect actual interference. Pre-compute the
    // per-instruction numbering so we can recognize and accept this case.
    // Numbering supplied by the caller: see `coalesce_copies_tuned_with_numbering`.
    // Reverse map (position -> inst) for the kill-at-def / pass-through-copy
    // overlap acceptances, which must inspect the instruction AT an overlap
    // position. Built only when a tuning extension is active.
    let pos_to_inst: BTreeMap<u32, InstId> = if tuning.kill_def_producers.is_empty() {
        BTreeMap::new()
    } else {
        inst_numbering.iter().map(|(&id, &pos)| (pos, id)).collect()
    };

    // Walk blocks in program order.
    let block_indices: Vec<usize> = if func.block_order.is_empty() {
        (0..func.blocks.len()).collect()
    } else {
        func.block_order
            .iter()
            .map(|block_id| block_id.0 as usize)
            .collect()
    };

    for block_idx in block_indices {
        let block = &func.blocks[block_idx];

        for &inst_id in &block.insts {
            let inst = &func.insts[inst_id.0 as usize];
            if !phi_elim::is_copy_opcode(inst.opcode) {
                continue;
            }

            let Some(dst_vreg) = inst.defs.first().and_then(MachOperand::as_vreg) else {
                continue;
            };
            let Some(src_vreg) = inst.uses.first().and_then(MachOperand::as_vreg) else {
                continue;
            };

            seen.push(dst_vreg);
            seen.push(src_vreg);
            let dst_root = find_root_vec(&mut parent, dst_vreg);
            let src_root = find_root_vec(&mut parent, src_vreg);

            // Already coalesced through an earlier copy in the chain.
            if dst_root == src_root {
                result.removals.push(inst_id);
                result.copies_removed += 1;
                continue;
            }

            // Only coalesce within the same register class.
            if dst_root.class != src_root.class {
                continue;
            }

            let dst_interval = intervals
                .get(&dst_root.id)
                .cloned()
                .unwrap_or_else(|| LiveInterval::new(dst_root));
            let src_interval = intervals
                .get(&src_root.id)
                .cloned()
                .unwrap_or_else(|| LiveInterval::new(src_root));

            // If the only "overlap" between dst and src lives at the copy
            // instruction itself, the move places the same physical value
            // in the same physical slot — there is no real interference.
            // This is the kill-then-def case from
            // `docs/regalloc_coalescer_singleblock_bug.md`.
            //
            // With target tuning, two further single-position overlap shapes
            // are accepted (see [`overlap_positions_all_mergeable`]): the
            // kill-at-def of a whitelisted producer (the loop-carried
            // `d <- op(d, ..)` latch update) and a pass-through copy relating
            // the same two coalescing classes (block-param chains).
            let overlap_ok = |dst_interval: &LiveInterval, src_interval: &LiveInterval| {
                overlap_is_copy_point_only(dst_interval, src_interval, inst_id, &inst_numbering)
                    || (!tuning.kill_def_producers.is_empty()
                        && overlap_positions_all_mergeable(OverlapMergeQuery {
                            dst_interval,
                            src_interval,
                            copy_inst: inst_id,
                            inst_numbering: &inst_numbering,
                            pos_to_inst: &pos_to_inst,
                            func,
                            parent: &parent,
                            dst_root,
                            src_root,
                            tuning,
                        }))
            };
            if dst_interval.overlaps(&src_interval) && !overlap_ok(&dst_interval, &src_interval) {
                if debug_decisions {
                    eprintln!(
                        "  coalesce REFUSE {:?}: dst {} {:?} src {} {:?} copy_pos {:?}",
                        inst_id,
                        dst_root,
                        dst_interval
                            .ranges
                            .iter()
                            .map(|r| (r.start, r.end))
                            .collect::<Vec<_>>(),
                        src_root,
                        src_interval
                            .ranges
                            .iter()
                            .map(|r| (r.start, r.end))
                            .collect::<Vec<_>>(),
                        inst_numbering.get(&inst_id),
                    );
                }
                continue;
            }

            if debug_decisions {
                eprintln!(
                    "  coalesce MERGE {:?}: {} <- {}",
                    inst_id, dst_root, src_root
                );
            }
            // Coalesce: merge src into dst in the union-find.
            parent[src_root.id as usize] = Some(dst_root);
            merge_interval(intervals, dst_root.id, dst_root.class, src_root.id);

            result.removals.push(inst_id);
            result.copies_removed += 1;
            result.intervals_merged += 1;
        }
    }

    // Build final rewrite map with path compression. Iterate the DISTINCT
    // vregs that were ever queried (the map-keys equivalent).
    seen.sort_unstable_by_key(|v| v.id);
    seen.dedup();
    for vreg in seen {
        let root = find_root_vec(&mut parent, vreg);
        if root != vreg {
            result.rewrites.insert(vreg, root);
        }
    }

    result
}

/// Apply the removals and rewrites produced by [`coalesce_copies`].
///
/// Copy instructions are removed from block instruction lists, and all vreg
/// operands matching a full `VReg` identity are rewritten according to
/// `rewrites`.
pub fn apply_coalescing(
    func: &mut MachFunction,
    removals: &[InstId],
    rewrites: &BTreeMap<VReg, VReg>,
) {
    let removal_set: BTreeSet<InstId> = removals.iter().copied().collect();

    for block in &mut func.blocks {
        block.insts.retain(|inst_id| !removal_set.contains(inst_id));
    }

    if rewrites.is_empty() {
        return;
    }

    for inst in &mut func.insts {
        rewrite_operands(&mut inst.defs, rewrites);
        rewrite_operands(&mut inst.uses, rewrites);
    }
}

/// Decide whether `dst_interval` and `src_interval` overlap only at the
/// natural-index position of the `copy_inst` instruction.
///
/// Under the conflated-position liveness model a use kill and a same-position
/// new def look identical and produce an apparent overlap at that single
/// instruction. For a register copy `dst <- src` the move places the same
/// physical value in the same physical slot, so the overlap is spurious and
/// the copy is safe to coalesce. Any overlap that extends beyond the copy
/// instruction itself is real interference and the copy must stay.
fn overlap_is_copy_point_only(
    dst_interval: &LiveInterval,
    src_interval: &LiveInterval,
    copy_inst: InstId,
    inst_numbering: &BTreeMap<InstId, u32>,
) -> bool {
    let Some(&copy_pos) = inst_numbering.get(&copy_inst) else {
        return false;
    };
    // The natural-index point range that the copy contributes to both vregs
    // (def of dst, use of src kill).
    let copy_range = LiveRange::new(copy_pos, copy_pos + 1);

    for src_range in &src_interval.ranges {
        for dst_range in &dst_interval.ranges {
            if !src_range.overlaps(dst_range) {
                continue;
            }
            // Overlap region: max(starts) .. min(ends).
            let overlap_start = src_range.start.max(dst_range.start);
            let overlap_end = src_range.end.min(dst_range.end);
            // The only acceptable overlap is the copy instruction's
            // point range; any other overlapping slot is real
            // interference.
            if overlap_start < copy_range.start || overlap_end > copy_range.end {
                return false;
            }
        }
    }
    true
}

/// Inputs to [`overlap_positions_all_mergeable`].
struct OverlapMergeQuery<'a> {
    dst_interval: &'a LiveInterval,
    src_interval: &'a LiveInterval,
    copy_inst: InstId,
    inst_numbering: &'a BTreeMap<InstId, u32>,
    pos_to_inst: &'a BTreeMap<u32, InstId>,
    func: &'a MachFunction,
    parent: &'a [Option<VReg>],
    dst_root: VReg,
    src_root: VReg,
    tuning: &'a CoalesceTuning,
}

/// Read-only union-find resolve (no path compression) for the overlap
/// acceptance checks, which run under an immutable borrow of `parent`.
fn resolve_root_readonly(parent: &[Option<VReg>], vreg: VReg) -> VReg {
    let mut current = vreg;
    let mut steps = 0usize;
    while let Some(next) = parent.get(current.id as usize).copied().flatten() {
        if next == current || steps >= parent.len() {
            break;
        }
        current = next;
        steps += 1;
    }
    current
}

/// Decide whether EVERY overlap between `dst` and `src` is a single-position
/// same-storage transition, so merging the copy `dst <- src` is sound. Each
/// overlapping (range, range) pair's region must be exactly ONE position `p`
/// satisfying one of:
///
///  1. **The copy point** (`p == copy_pos`): the historical kill-then-def at
///     the move itself ([`overlap_is_copy_point_only`]).
///
///  2. **Kill-at-def of a whitelisted producer**: `p` is simultaneously the
///     END of dst's range (`dst_range.end == p + 1`, i.e. dst's last read in
///     that range, confirmed by a recorded use position) and the START of
///     src's range at src's own def (`src_range.start == p`, def position
///     recorded), and the instruction at `p` is a whitelisted
///     single-instruction producer (single explicit def resolving to src's
///     class, no implicit operands, no call, no tied operands). Merging makes
///     the producer an in-place update: the one machine instruction reads the
///     shared register (dst's dying value) before writing it (src's value) —
///     the loop-carried `d = op(d, ..)` latch shape.
///
///  3. **A pass-through copy between the same two classes**: the instruction
///     at `p` is itself a copy whose {def, use} resolve to exactly
///     {dst_root, src_root}. At that instruction the value moves between the
///     two storages being merged, so the apparent overlap is the same
///     kill-then-def-of-identical-value as case 1 (block-param chains have
///     copies in BOTH directions across a loop, e.g. `x <- y` on one edge and
///     `y <- x` on the back edge).
///
/// Anything else — any multi-position region, or a single position that fails
/// all three cases — refuses the merge (fail-closed; the copy simply stays).
/// The always-on translation validator independently certifies the resulting
/// allocation against the original spec.
fn overlap_positions_all_mergeable(q: OverlapMergeQuery<'_>) -> bool {
    let Some(&copy_pos) = q.inst_numbering.get(&q.copy_inst) else {
        return false;
    };

    for src_range in &q.src_interval.ranges {
        for dst_range in &q.dst_interval.ranges {
            if !src_range.overlaps(dst_range) {
                continue;
            }
            let overlap_start = src_range.start.max(dst_range.start);
            let overlap_end = src_range.end.min(dst_range.end);
            // Case 1: entirely within the copy's own point range.
            if overlap_start >= copy_pos && overlap_end <= copy_pos + 1 {
                continue;
            }
            // All other acceptances require a SINGLE position.
            if overlap_end != overlap_start + 1 {
                return false;
            }
            let p = overlap_start;
            let Some(&inst_id) = q.pos_to_inst.get(&p) else {
                return false;
            };
            let Some(inst) = q.func.insts.get(inst_id.0 as usize) else {
                return false;
            };

            // Case 3: a pass-through copy between the same two classes.
            if phi_elim::is_copy_opcode(inst.opcode) {
                let dv = inst.defs.first().and_then(MachOperand::as_vreg);
                let sv = inst.uses.first().and_then(MachOperand::as_vreg);
                if let (Some(dv), Some(sv)) = (dv, sv) {
                    let dr = resolve_root_readonly(q.parent, dv);
                    let sr = resolve_root_readonly(q.parent, sv);
                    if (dr == q.dst_root && sr == q.src_root)
                        || (dr == q.src_root && sr == q.dst_root)
                    {
                        continue;
                    }
                }
                return false;
            }

            // Case 2: kill-at-def of a whitelisted single-instruction producer.
            if !q.tuning.kill_def_producers.contains(&inst.opcode) {
                return false;
            }
            // Rn-only producers: the merge would make dst the producer's
            // in-place register, so dst must not be the SHIFTED second source
            // (`uses[1]`) — a loop-carried dependence through the shifter port
            // is a measured recurrence-latency hazard (see
            // `CoalesceTuning::kill_def_rn_only_producers`). Fail closed on a
            // malformed shape (missing/non-vreg `uses[1]`).
            if q.tuning.kill_def_rn_only_producers.contains(&inst.opcode) {
                let Some(rm_v) = inst.uses.get(1).and_then(MachOperand::as_vreg) else {
                    return false;
                };
                if resolve_root_readonly(q.parent, rm_v) == q.dst_root {
                    return false;
                }
            }
            if inst.flags.is_call()
                || !inst.implicit_defs.is_empty()
                || !inst.implicit_uses.is_empty()
                || !inst.tied_operands.is_empty()
                || inst.defs.len() != 1
            {
                return false;
            }
            // The def at `p` must be src's own def (resolving to src_root).
            let Some(def_v) = inst.defs.first().and_then(MachOperand::as_vreg) else {
                return false;
            };
            if resolve_root_readonly(q.parent, def_v) != q.src_root {
                return false;
            }
            // src's range is BORN at p (recorded def), dst's range DIES at p
            // (range ends p+1 with a recorded read at p): the single machine
            // instruction reads the shared register, then writes it.
            let src_born_here =
                src_range.start == p && q.src_interval.def_positions.binary_search(&p).is_ok();
            let dst_dies_here =
                dst_range.end == p + 1 && q.dst_interval.use_positions.binary_search(&p).is_ok();
            if !(src_born_here && dst_dies_here) {
                return false;
            }
        }
    }
    true
}

// --- Union-find helpers ---

fn find_root(parent: &mut BTreeMap<VReg, VReg>, vreg: VReg) -> VReg {
    let mut current = vreg;
    loop {
        let next = *parent.entry(current).or_insert(current);
        if next == current {
            break;
        }
        current = next;
    }

    // Path compression.
    let root = current;
    let mut current = vreg;
    loop {
        let next = *parent.entry(current).or_insert(current);
        if next == current {
            break;
        }
        parent.insert(current, root);
        current = next;
    }

    root
}

/// Vec-indexed union-find `find` with path compression, over a dense
/// `parent[id]` array (`None` = a self-root). Semantically identical to the
/// `BTreeMap` [`find_root`] above but O(1)-per-step instead of O(log n) —
/// `find_root` was a profiled core-pipeline cost. The vreg CLASS travels with
/// the stored `VReg` values, so the returned root carries its correct class.
fn find_root_vec(parent: &mut [Option<VReg>], vreg: VReg) -> VReg {
    let mut current = vreg;
    while let Some(next) = parent[current.id as usize] {
        if next == current {
            break;
        }
        current = next;
    }
    let root = current;
    // Path compression: point every node on the path directly at the root.
    let mut current = vreg;
    while let Some(next) = parent[current.id as usize] {
        if next == current {
            break;
        }
        parent[current.id as usize] = Some(root);
        current = next;
    }
    root
}

// --- Interval merging ---

fn merge_interval(
    intervals: &mut BTreeMap<u32, LiveInterval>,
    dst_id: u32,
    dst_class: RegClass,
    src_id: u32,
) {
    if dst_id == src_id {
        return;
    }

    let src_interval = intervals.remove(&src_id);

    match (intervals.get_mut(&dst_id), src_interval) {
        (Some(dst_interval), Some(src_interval)) => {
            merge_interval_contents(dst_interval, src_interval, dst_id, dst_class);
        }
        (None, Some(mut src_interval)) => {
            src_interval.vreg = VReg {
                id: dst_id,
                class: dst_class,
            };
            intervals.insert(dst_id, src_interval);
        }
        (Some(dst_interval), None) => {
            dst_interval.vreg = VReg {
                id: dst_id,
                class: dst_class,
            };
        }
        (None, None) => {}
    }
}

fn merge_interval_contents(
    dst_interval: &mut LiveInterval,
    src_interval: LiveInterval,
    dst_id: u32,
    dst_class: RegClass,
) {
    dst_interval.vreg = VReg {
        id: dst_id,
        class: dst_class,
    };

    for range in src_interval.ranges {
        dst_interval.add_range(range.start, range.end);
    }

    dst_interval
        .use_positions
        .extend(src_interval.use_positions);
    dst_interval.use_positions.sort_unstable();
    dst_interval.use_positions.dedup();

    dst_interval
        .def_positions
        .extend(src_interval.def_positions);
    dst_interval.def_positions.sort_unstable();
    dst_interval.def_positions.dedup();

    dst_interval.spill_weight += src_interval.spill_weight;
    dst_interval.is_fixed |= src_interval.is_fixed;
}

// --- Operand rewriting ---

fn rewrite_operands(operands: &mut [MachOperand], rewrites: &BTreeMap<VReg, VReg>) {
    for operand in operands {
        if let MachOperand::VReg(vreg) = operand {
            *vreg = resolve_rewrite(*vreg, rewrites);
        }
    }
}

fn resolve_rewrite(mut vreg: VReg, rewrites: &BTreeMap<VReg, VReg>) -> VReg {
    let mut steps = 0usize;
    while let Some(&next) = rewrites.get(&vreg) {
        if next == vreg || steps >= rewrites.len() {
            break;
        }
        vreg = next;
        steps += 1;
    }
    vreg
}

// ---------------------------------------------------------------------------
// Coalescing mode and stateful coalescer
// ---------------------------------------------------------------------------

/// Coalescing aggressiveness mode.
///
/// Controls how eagerly the coalescer merges live intervals:
/// - **Aggressive:** merges whenever intervals do not interfere (the default
///   and the behavior of [`coalesce_copies`]).
/// - **Conservative:** additionally rejects merges that would increase
///   register pressure by creating a longer combined interval whose total
///   extent exceeds the sum of the individual extents.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CoalesceMode {
    /// Coalesce whenever intervals do not overlap.
    #[default]
    Aggressive,
    /// Coalesce only when the merged interval's extent (max end - min start)
    /// does not exceed the sum of the individual extents — a heuristic to
    /// avoid creating live ranges that span wide program regions and increase
    /// register pressure. Adjacent intervals are always accepted; intervals
    /// with a gap between them are rejected proportionally to the gap size.
    Conservative,
}

/// Summary statistics for a coalescing pass.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CoalesceStats {
    /// Number of copy instructions that were eliminated.
    pub copies_eliminated: u32,
    /// Number of copy instructions that could not be eliminated.
    pub copies_remaining: u32,
    /// Number of live-interval merges performed.
    pub intervals_merged: u32,
}

impl CoalesceResult {
    /// Derive summary statistics given the total number of `PSEUDO_COPY`
    /// instructions in the function.
    pub fn stats(&self, total_copies: u32) -> CoalesceStats {
        CoalesceStats {
            copies_eliminated: self.copies_removed,
            copies_remaining: total_copies.saturating_sub(self.copies_removed),
            intervals_merged: self.intervals_merged,
        }
    }
}

/// Compute the total span (sum of range lengths) of a [`LiveInterval`].
#[cfg(test)]
fn interval_span(interval: &LiveInterval) -> u32 {
    interval.ranges.iter().map(|r| r.end - r.start).sum()
}

/// Compute the extent (max_end - min_start) of a [`LiveInterval`].
///
/// Returns 0 for empty intervals. The extent captures how wide the live
/// range is in program order — a merged interval with the same total span
/// but a much larger extent occupies a register across a wider code region,
/// increasing pressure.
fn interval_extent(interval: &LiveInterval) -> u32 {
    match (interval.ranges.first(), interval.ranges.last()) {
        (Some(first), Some(last)) => last.end.saturating_sub(first.start),
        _ => 0,
    }
}

/// Stateful copy coalescer with configurable aggressiveness.
///
/// Wraps the same union-find + overlap-check algorithm as [`coalesce_copies`],
/// but exposes individual operations (`can_coalesce`, `merge_intervals`,
/// `update_uses`) for callers that need finer-grained control.
///
/// # Example
///
/// ```text
/// let mut coalescer = CopyCoalescer::new(CoalesceMode::Aggressive);
/// let result = coalescer.coalesce(&func, &mut intervals);
/// apply_coalescing(&mut func, &result.removals, &result.rewrites);
/// ```
pub struct CopyCoalescer {
    /// Aggressiveness mode.
    mode: CoalesceMode,
    /// Union-find parent map for transitive coalescing.
    parent: BTreeMap<VReg, VReg>,
}

impl CopyCoalescer {
    /// Create a new coalescer with the given mode.
    pub fn new(mode: CoalesceMode) -> Self {
        Self {
            mode,
            parent: BTreeMap::new(),
        }
    }

    /// Reset union-find state so the coalescer can be reused on a different
    /// function.
    pub fn reset(&mut self) {
        self.parent.clear();
    }

    /// Return the current coalescing mode.
    pub fn mode(&self) -> CoalesceMode {
        self.mode
    }

    /// Check whether two intervals can be coalesced.
    ///
    /// In **Aggressive** mode, intervals are coalescible when they do not
    /// overlap.  In **Conservative** mode, the merged interval's *extent*
    /// (max end - min start) must also not exceed the sum of the individual
    /// extents. This rejects merges that would create a single live range
    /// spanning a much wider program region than the two originals combined,
    /// which would increase register pressure.
    pub fn can_coalesce(&self, src_interval: &LiveInterval, dst_interval: &LiveInterval) -> bool {
        if src_interval.overlaps(dst_interval) {
            return false;
        }
        match self.mode {
            CoalesceMode::Aggressive => true,
            CoalesceMode::Conservative => {
                let merged = Self::merge_intervals(src_interval, dst_interval);
                let merged_extent = interval_extent(&merged);
                let sum_extent = interval_extent(src_interval) + interval_extent(dst_interval);
                merged_extent <= sum_extent
            }
        }
    }

    /// Merge two non-overlapping intervals into a single combined interval.
    ///
    /// The result uses the destination interval's VReg identity. Spill
    /// weights are summed and use/def positions are combined.
    pub fn merge_intervals(src: &LiveInterval, dst: &LiveInterval) -> LiveInterval {
        let mut merged = dst.clone();
        for range in &src.ranges {
            merged.add_range(range.start, range.end);
        }
        merged.use_positions.extend(&src.use_positions);
        merged.use_positions.sort_unstable();
        merged.use_positions.dedup();
        merged.def_positions.extend(&src.def_positions);
        merged.def_positions.sort_unstable();
        merged.def_positions.dedup();
        merged.spill_weight += src.spill_weight;
        merged.is_fixed |= src.is_fixed;
        merged
    }

    /// Rewrite all occurrences of `old_vreg` to `new_vreg` in the function.
    ///
    /// This updates both defs and uses across all instructions.
    pub fn update_uses(func: &mut MachFunction, old_vreg: VReg, new_vreg: VReg) {
        let rewrites = BTreeMap::from([(old_vreg, new_vreg)]);
        for inst in &mut func.insts {
            rewrite_operands(&mut inst.defs, &rewrites);
            rewrite_operands(&mut inst.uses, &rewrites);
        }
    }

    /// Run the coalescing pass over the entire function.
    ///
    /// In **Aggressive** mode this delegates directly to [`coalesce_copies`].
    /// In **Conservative** mode it applies an additional span check before
    /// each merge.
    pub fn coalesce(
        &mut self,
        func: &MachFunction,
        intervals: &mut BTreeMap<u32, LiveInterval>,
    ) -> CoalesceResult {
        self.parent.clear();

        if self.mode == CoalesceMode::Aggressive {
            return coalesce_copies(func, intervals);
        }

        // Conservative mode: inline the algorithm with the extra check.
        let mut result = CoalesceResult::default();

        let block_indices: Vec<usize> = if func.block_order.is_empty() {
            (0..func.blocks.len()).collect()
        } else {
            func.block_order
                .iter()
                .map(|block_id| block_id.0 as usize)
                .collect()
        };

        for block_idx in block_indices {
            let block = &func.blocks[block_idx];

            for &inst_id in &block.insts {
                let inst = &func.insts[inst_id.0 as usize];
                if !phi_elim::is_copy_opcode(inst.opcode) {
                    continue;
                }

                let Some(dst_vreg) = inst.defs.first().and_then(MachOperand::as_vreg) else {
                    continue;
                };
                let Some(src_vreg) = inst.uses.first().and_then(MachOperand::as_vreg) else {
                    continue;
                };

                let dst_root = find_root(&mut self.parent, dst_vreg);
                let src_root = find_root(&mut self.parent, src_vreg);

                if dst_root == src_root {
                    result.removals.push(inst_id);
                    result.copies_removed += 1;
                    continue;
                }

                if dst_root.class != src_root.class {
                    continue;
                }

                let dst_interval = intervals
                    .get(&dst_root.id)
                    .cloned()
                    .unwrap_or_else(|| LiveInterval::new(dst_root));
                let src_interval = intervals
                    .get(&src_root.id)
                    .cloned()
                    .unwrap_or_else(|| LiveInterval::new(src_root));

                if !self.can_coalesce(&src_interval, &dst_interval) {
                    continue;
                }

                self.parent.insert(src_root, dst_root);
                merge_interval(intervals, dst_root.id, dst_root.class, src_root.id);

                result.removals.push(inst_id);
                result.copies_removed += 1;
                result.intervals_merged += 1;
            }
        }

        // Build final rewrite map with path compression.
        let seen_vregs: Vec<VReg> = self.parent.keys().copied().collect();
        for vreg in seen_vregs {
            let root = find_root(&mut self.parent, vreg);
            if root != vreg {
                result.rewrites.insert(vreg, root);
            }
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::liveness::compute_live_intervals;
    use crate::machine_types::{
        BlockId, InstFlags, MachBlock, MachFunction, MachInst, MachOperand, RegClass, VReg,
    };
    use std::collections::BTreeMap;

    fn vreg(id: u32) -> VReg {
        VReg {
            id,
            class: RegClass::Gpr64,
        }
    }

    fn generic_inst(opcode: u16, defs: Vec<VReg>, uses: Vec<VReg>) -> MachInst {
        MachInst {
            opcode,
            defs: defs.into_iter().map(MachOperand::VReg).collect(),
            uses: uses.into_iter().map(MachOperand::VReg).collect(),
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        }
    }

    fn copy_inst(dst: VReg, src: VReg) -> MachInst {
        generic_inst(crate::phi_elim::PSEUDO_COPY, vec![dst], vec![src])
    }

    fn interval(id: u32, ranges: &[(u32, u32)]) -> LiveInterval {
        let mut interval = LiveInterval::new(vreg(id));
        for &(start, end) in ranges {
            interval.add_range(start, end);
        }
        interval
    }

    fn interval_ranges(interval: &LiveInterval) -> Vec<(u32, u32)> {
        interval
            .ranges
            .iter()
            .map(|range| (range.start, range.end))
            .collect()
    }

    fn make_function(blocks_insts: Vec<Vec<MachInst>>) -> MachFunction {
        let mut insts = Vec::new();
        let mut blocks = Vec::new();
        let mut block_order = Vec::new();

        for block_insts in blocks_insts {
            let block_id = BlockId(blocks.len() as u32);
            let mut inst_ids = Vec::new();

            for inst in block_insts {
                let inst_id = InstId(insts.len() as u32);
                insts.push(inst);
                inst_ids.push(inst_id);
            }

            blocks.push(MachBlock {
                insts: inst_ids,
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            });
            block_order.push(block_id);
        }

        MachFunction {
            name: "test".into(),
            insts,
            blocks,
            block_order,
            entry_block: BlockId(0),
            next_vreg: 32,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        }
    }

    /// `number_insts` must agree EXACTLY with the numbering the full liveness
    /// pass produces, on every shape.
    ///
    /// Coalescing used to open by running a second whole-function
    /// `compute_live_intervals` purely to re-derive this map, throwing away the
    /// intervals. It now takes the caller's. If the two ever diverge, the copy
    /// position in the kill-at-def / pass-through overlap acceptances would be
    /// misidentified and coalescing decisions would silently change — so pin the
    /// equivalence rather than assume it.
    #[test]
    fn numbering_matches_full_liveness() {
        let cases = vec![
            // Single block.
            vec![vec![
                generic_inst(1, vec![vreg(7)], vec![]),
                copy_inst(vreg(1), vreg(0)),
                generic_inst(2, vec![], vec![vreg(1)]),
            ]],
            // Several blocks of differing lengths.
            vec![
                vec![generic_inst(1, vec![vreg(0)], vec![])],
                vec![
                    copy_inst(vreg(1), vreg(0)),
                    generic_inst(2, vec![vreg(2)], vec![vreg(1)]),
                    generic_inst(3, vec![], vec![vreg(2)]),
                ],
                vec![generic_inst(4, vec![], vec![vreg(0)])],
            ],
            // A block with no instructions at all.
            vec![
                vec![generic_inst(1, vec![vreg(0)], vec![])],
                vec![],
                vec![generic_inst(2, vec![], vec![vreg(0)])],
            ],
        ];
        for (i, blocks) in cases.into_iter().enumerate() {
            let func = make_function(blocks);
            assert_eq!(
                number_insts(&func),
                compute_live_intervals(&func).inst_numbering,
                "case {i}: number_insts diverged from the full liveness numbering"
            );
        }
    }

    #[test]
    fn test_coalesce_non_overlapping() {
        let func = make_function(vec![vec![
            generic_inst(1, vec![vreg(7)], vec![]),
            copy_inst(vreg(1), vreg(0)),
            generic_inst(2, vec![], vec![vreg(1)]),
        ]]);
        let copy_id = func.blocks[0].insts[1];

        let mut intervals =
            BTreeMap::from([(0, interval(0, &[(0, 1)])), (1, interval(1, &[(1, 2)]))]);

        let result = coalesce_copies(&func, &mut intervals);

        assert_eq!(result.copies_removed, 1);
        assert_eq!(result.intervals_merged, 1);
        assert_eq!(result.removals, vec![copy_id]);
        assert_eq!(result.rewrites.get(&vreg(0)), Some(&vreg(1)));
        assert_eq!(intervals.len(), 1);
        assert_eq!(interval_ranges(intervals.get(&1).unwrap()), vec![(0, 2)]);
    }

    #[test]
    fn test_coalesce_skips_overlapping() {
        let func = make_function(vec![vec![copy_inst(vreg(1), vreg(0))]]);

        let mut intervals =
            BTreeMap::from([(0, interval(0, &[(0, 2)])), (1, interval(1, &[(1, 3)]))]);

        let result = coalesce_copies(&func, &mut intervals);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(result.intervals_merged, 0);
        assert!(result.removals.is_empty());
        assert!(result.rewrites.is_empty());
        assert_eq!(intervals.len(), 2);
    }

    #[test]
    fn test_coalesce_transitive_chain() {
        let func = make_function(vec![vec![
            copy_inst(vreg(1), vreg(0)),
            copy_inst(vreg(2), vreg(1)),
        ]]);
        let copy1 = func.blocks[0].insts[0];
        let copy2 = func.blocks[0].insts[1];

        let mut intervals = BTreeMap::from([
            (0, interval(0, &[(0, 1)])),
            (1, interval(1, &[(1, 2)])),
            (2, interval(2, &[(2, 3)])),
        ]);

        let result = coalesce_copies(&func, &mut intervals);

        assert_eq!(result.copies_removed, 2);
        assert_eq!(result.intervals_merged, 2);
        assert_eq!(result.removals, vec![copy1, copy2]);
        assert_eq!(intervals.len(), 1);
    }

    #[test]
    fn test_coalesce_duplicate_copies() {
        let func = make_function(vec![vec![
            copy_inst(vreg(1), vreg(0)),
            copy_inst(vreg(1), vreg(0)),
        ]]);

        let mut intervals =
            BTreeMap::from([(0, interval(0, &[(0, 1)])), (1, interval(1, &[(1, 2)]))]);

        let result = coalesce_copies(&func, &mut intervals);

        assert_eq!(result.copies_removed, 2);
        assert_eq!(result.intervals_merged, 1);
    }

    #[test]
    fn test_apply_coalescing() {
        let mut func = make_function(vec![
            vec![
                generic_inst(1, vec![vreg(0)], vec![]),
                copy_inst(vreg(1), vreg(0)),
            ],
            vec![
                copy_inst(vreg(2), vreg(1)),
                generic_inst(2, vec![vreg(3)], vec![vreg(0), vreg(1), vreg(2)]),
            ],
        ]);

        let def_id = func.blocks[0].insts[0];
        let copy1_id = func.blocks[0].insts[1];
        let copy2_id = func.blocks[1].insts[0];
        let user_id = func.blocks[1].insts[1];

        let rewrites = BTreeMap::from([(vreg(0), vreg(1)), (vreg(1), vreg(2))]);
        apply_coalescing(&mut func, &[copy1_id, copy2_id], &rewrites);

        assert_eq!(func.blocks[0].insts, vec![def_id]);
        assert_eq!(func.blocks[1].insts, vec![user_id]);

        let def_vreg = func.insts[def_id.0 as usize].defs[0].as_vreg().unwrap();
        assert_eq!(def_vreg.id, 2);

        let use_ids: Vec<u32> = func.insts[user_id.0 as usize]
            .uses
            .iter()
            .map(|operand| operand.as_vreg().unwrap().id)
            .collect();
        assert_eq!(use_ids, vec![2, 2, 2]);
    }

    #[test]
    fn test_apply_coalescing_rewrites_full_vreg_identity() {
        let fpr0 = VReg {
            id: 0,
            class: RegClass::Fpr64,
        };
        let mut func = make_function(vec![vec![generic_inst(
            1,
            vec![vreg(0)],
            vec![fpr0, vreg(0)],
        )]]);
        let inst_id = func.blocks[0].insts[0];

        let rewrites = BTreeMap::from([(vreg(0), vreg(2))]);
        apply_coalescing(&mut func, &[], &rewrites);

        assert_eq!(
            func.insts[inst_id.0 as usize].defs,
            vec![MachOperand::VReg(vreg(2))]
        );
        assert_eq!(
            func.insts[inst_id.0 as usize].uses,
            vec![MachOperand::VReg(fpr0), MachOperand::VReg(vreg(2))]
        );
    }

    // -----------------------------------------------------------------------
    // Additional edge-case tests (issue #139)
    // -----------------------------------------------------------------------

    #[test]
    fn test_coalesce_rejects_cross_class_copy() {
        let dst = vreg(1);
        let src = VReg {
            id: 0,
            class: RegClass::Fpr64,
        };
        let func = make_function(vec![vec![copy_inst(dst, src)]]);

        let mut src_interval = LiveInterval::new(src);
        src_interval.add_range(0, 1);
        let mut intervals = BTreeMap::from([(0, src_interval), (1, interval(1, &[(1, 2)]))]);

        let result = coalesce_copies(&func, &mut intervals);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(result.intervals_merged, 0);
        assert!(result.removals.is_empty());
        assert!(result.rewrites.is_empty());
        assert_eq!(intervals.len(), 2);
        assert_eq!(intervals.get(&0).unwrap().vreg.class, RegClass::Fpr64);
        assert_eq!(interval_ranges(intervals.get(&1).unwrap()), vec![(1, 2)]);
    }

    #[test]
    fn test_coalesce_empty_function_no_instructions() {
        let func = make_function(vec![vec![]]);
        let mut intervals = BTreeMap::from([(0, interval(0, &[(0, 1)]))]);

        let result = coalesce_copies(&func, &mut intervals);

        assert_eq!(result, CoalesceResult::default());
        assert_eq!(intervals.len(), 1);
        assert_eq!(interval_ranges(intervals.get(&0).unwrap()), vec![(0, 1)]);
    }

    #[test]
    fn test_coalesce_across_multiple_blocks() {
        let func = make_function(vec![
            vec![copy_inst(vreg(1), vreg(0))],
            vec![copy_inst(vreg(2), vreg(1))],
        ]);
        let copy1 = func.blocks[0].insts[0];
        let copy2 = func.blocks[1].insts[0];

        let mut intervals = BTreeMap::from([
            (0, interval(0, &[(0, 1)])),
            (1, interval(1, &[(1, 2)])),
            (2, interval(2, &[(2, 3)])),
        ]);

        let result = coalesce_copies(&func, &mut intervals);

        assert_eq!(result.copies_removed, 2);
        assert_eq!(result.intervals_merged, 2);
        assert_eq!(result.removals, vec![copy1, copy2]);
        assert_eq!(
            result.rewrites,
            BTreeMap::from([(vreg(0), vreg(2)), (vreg(1), vreg(2))])
        );
        assert_eq!(intervals.len(), 1);
        assert_eq!(interval_ranges(intervals.get(&2).unwrap()), vec![(0, 3)]);
    }

    #[test]
    fn test_coalesce_with_missing_intervals_for_src_and_dst() {
        let func = make_function(vec![vec![copy_inst(vreg(1), vreg(0))]]);
        let copy_id = func.blocks[0].insts[0];
        let mut intervals = BTreeMap::new();

        let result = coalesce_copies(&func, &mut intervals);

        assert_eq!(result.copies_removed, 1);
        assert_eq!(result.intervals_merged, 1);
        assert_eq!(result.removals, vec![copy_id]);
        assert_eq!(result.rewrites.get(&vreg(0)), Some(&vreg(1)));
        assert!(intervals.is_empty());
    }

    #[test]
    fn test_apply_coalescing_without_removals() {
        let mut func = make_function(vec![vec![
            generic_inst(1, vec![vreg(0)], vec![]),
            generic_inst(2, vec![vreg(3)], vec![vreg(0), vreg(1)]),
        ]]);
        let def_id = func.blocks[0].insts[0];
        let user_id = func.blocks[0].insts[1];

        let rewrites = BTreeMap::from([(vreg(0), vreg(1)), (vreg(1), vreg(2))]);
        apply_coalescing(&mut func, &[], &rewrites);

        assert_eq!(func.blocks[0].insts, vec![def_id, user_id]);

        let def_vreg = func.insts[def_id.0 as usize].defs[0].as_vreg().unwrap();
        assert_eq!(def_vreg.id, 2);

        let user_def = func.insts[user_id.0 as usize].defs[0].as_vreg().unwrap();
        assert_eq!(user_def.id, 3);

        let use_ids: Vec<u32> = func.insts[user_id.0 as usize]
            .uses
            .iter()
            .map(|operand| operand.as_vreg().unwrap().id)
            .collect();
        assert_eq!(use_ids, vec![2, 2]);
    }

    #[test]
    fn test_apply_coalescing_without_rewrites() {
        let mut func = make_function(vec![vec![
            generic_inst(1, vec![vreg(0)], vec![]),
            copy_inst(vreg(1), vreg(0)),
            generic_inst(2, vec![vreg(2)], vec![vreg(1)]),
        ]]);
        let def_id = func.blocks[0].insts[0];
        let copy_id = func.blocks[0].insts[1];
        let user_id = func.blocks[0].insts[2];

        apply_coalescing(&mut func, &[copy_id], &BTreeMap::new());

        assert_eq!(func.blocks[0].insts, vec![def_id, user_id]);

        let def_vreg = func.insts[def_id.0 as usize].defs[0].as_vreg().unwrap();
        assert_eq!(def_vreg.id, 0);

        let use_ids: Vec<u32> = func.insts[user_id.0 as usize]
            .uses
            .iter()
            .map(|operand| operand.as_vreg().unwrap().id)
            .collect();
        assert_eq!(use_ids, vec![1]);
    }

    #[test]
    fn test_coalesce_long_transitive_chain() {
        let func = make_function(vec![vec![
            copy_inst(vreg(1), vreg(0)),
            copy_inst(vreg(2), vreg(1)),
            copy_inst(vreg(3), vreg(2)),
            copy_inst(vreg(4), vreg(3)),
        ]]);
        let copy1 = func.blocks[0].insts[0];
        let copy2 = func.blocks[0].insts[1];
        let copy3 = func.blocks[0].insts[2];
        let copy4 = func.blocks[0].insts[3];

        let mut intervals = BTreeMap::from([
            (0, interval(0, &[(0, 1)])),
            (1, interval(1, &[(1, 2)])),
            (2, interval(2, &[(2, 3)])),
            (3, interval(3, &[(3, 4)])),
            (4, interval(4, &[(4, 5)])),
        ]);

        let result = coalesce_copies(&func, &mut intervals);

        assert_eq!(result.copies_removed, 4);
        assert_eq!(result.intervals_merged, 4);
        assert_eq!(result.removals, vec![copy1, copy2, copy3, copy4]);
        assert_eq!(
            result.rewrites,
            BTreeMap::from([
                (vreg(0), vreg(4)),
                (vreg(1), vreg(4)),
                (vreg(2), vreg(4)),
                (vreg(3), vreg(4))
            ])
        );
        assert_eq!(intervals.len(), 1);
        assert_eq!(interval_ranges(intervals.get(&4).unwrap()), vec![(0, 5)]);
    }

    #[test]
    fn test_coalesce_skips_when_all_intervals_overlap() {
        let func = make_function(vec![vec![
            copy_inst(vreg(1), vreg(0)),
            copy_inst(vreg(2), vreg(1)),
        ]]);

        let mut intervals = BTreeMap::from([
            (0, interval(0, &[(0, 4)])),
            (1, interval(1, &[(1, 5)])),
            (2, interval(2, &[(2, 6)])),
        ]);

        let result = coalesce_copies(&func, &mut intervals);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(result.intervals_merged, 0);
        assert!(result.removals.is_empty());
        assert!(result.rewrites.is_empty());
        assert_eq!(intervals.len(), 3);
        assert_eq!(interval_ranges(intervals.get(&0).unwrap()), vec![(0, 4)]);
        assert_eq!(interval_ranges(intervals.get(&1).unwrap()), vec![(1, 5)]);
        assert_eq!(interval_ranges(intervals.get(&2).unwrap()), vec![(2, 6)]);
    }

    #[test]
    fn test_coalesce_uses_block_indices_when_block_order_is_empty() {
        let mut func = make_function(vec![
            vec![copy_inst(vreg(1), vreg(0))],
            vec![copy_inst(vreg(2), vreg(1))],
        ]);
        let copy1 = func.blocks[0].insts[0];
        let copy2 = func.blocks[1].insts[0];
        func.block_order.clear();

        let mut intervals = BTreeMap::from([
            (0, interval(0, &[(0, 1)])),
            (1, interval(1, &[(1, 2)])),
            (2, interval(2, &[(2, 3)])),
        ]);

        let result = coalesce_copies(&func, &mut intervals);

        assert_eq!(result.copies_removed, 2);
        assert_eq!(result.intervals_merged, 2);
        assert_eq!(result.removals, vec![copy1, copy2]);
        assert_eq!(
            result.rewrites,
            BTreeMap::from([(vreg(0), vreg(2)), (vreg(1), vreg(2))])
        );
        assert_eq!(intervals.len(), 1);
        assert_eq!(interval_ranges(intervals.get(&2).unwrap()), vec![(0, 3)]);
    }

    #[test]
    fn test_apply_coalescing_detects_rewrite_cycles() {
        let rewrites = BTreeMap::from([(vreg(0), vreg(1)), (vreg(1), vreg(2)), (vreg(2), vreg(0))]);
        assert_eq!(resolve_rewrite(vreg(0), &rewrites), vreg(0));
        assert_eq!(resolve_rewrite(vreg(1), &rewrites), vreg(1));
        assert_eq!(resolve_rewrite(vreg(2), &rewrites), vreg(2));

        let mut func = make_function(vec![vec![generic_inst(
            1,
            vec![vreg(0)],
            vec![vreg(1), vreg(2)],
        )]]);
        let inst_id = func.blocks[0].insts[0];

        apply_coalescing(&mut func, &[], &rewrites);

        let def_vreg = func.insts[inst_id.0 as usize].defs[0].as_vreg().unwrap();
        assert_eq!(def_vreg.id, 0);

        let use_ids: Vec<u32> = func.insts[inst_id.0 as usize]
            .uses
            .iter()
            .map(|operand| operand.as_vreg().unwrap().id)
            .collect();
        assert_eq!(use_ids, vec![1, 2]);
    }

    #[test]
    fn test_coalesce_merge_preserves_spill_weight() {
        let func = make_function(vec![vec![copy_inst(vreg(1), vreg(0))]]);

        let mut src_interval = interval(0, &[(0, 1)]);
        src_interval.spill_weight = 1.5;

        let mut dst_interval = interval(1, &[(1, 2)]);
        dst_interval.spill_weight = 2.25;

        let mut intervals = BTreeMap::from([(0, src_interval), (1, dst_interval)]);

        let result = coalesce_copies(&func, &mut intervals);

        assert_eq!(result.copies_removed, 1);
        assert_eq!(result.intervals_merged, 1);
        assert_eq!(result.rewrites.get(&vreg(0)), Some(&vreg(1)));
        assert_eq!(intervals.len(), 1);
        assert_eq!(interval_ranges(intervals.get(&1).unwrap()), vec![(0, 2)]);
        assert_eq!(intervals.get(&1).unwrap().spill_weight, 3.75);
    }

    #[test]
    fn test_coalesce_multiple_copies_across_multiple_blocks() {
        let func = make_function(vec![
            vec![copy_inst(vreg(1), vreg(0)), copy_inst(vreg(3), vreg(2))],
            vec![copy_inst(vreg(5), vreg(4))],
            vec![copy_inst(vreg(7), vreg(6))],
        ]);
        let copy1 = func.blocks[0].insts[0];
        let copy2 = func.blocks[0].insts[1];
        let copy3 = func.blocks[1].insts[0];
        let copy4 = func.blocks[2].insts[0];

        let mut intervals = BTreeMap::from([
            (0, interval(0, &[(0, 1)])),
            (1, interval(1, &[(1, 2)])),
            (2, interval(2, &[(2, 3)])),
            (3, interval(3, &[(3, 4)])),
            (4, interval(4, &[(4, 5)])),
            (5, interval(5, &[(5, 6)])),
            (6, interval(6, &[(6, 7)])),
            (7, interval(7, &[(7, 8)])),
        ]);

        let result = coalesce_copies(&func, &mut intervals);

        assert_eq!(result.copies_removed, 4);
        assert_eq!(result.intervals_merged, 4);
        assert_eq!(result.removals, vec![copy1, copy2, copy3, copy4]);
        assert_eq!(
            result.rewrites,
            BTreeMap::from([
                (vreg(0), vreg(1)),
                (vreg(2), vreg(3)),
                (vreg(4), vreg(5)),
                (vreg(6), vreg(7))
            ])
        );
        assert_eq!(intervals.len(), 4);
        assert_eq!(interval_ranges(intervals.get(&1).unwrap()), vec![(0, 2)]);
        assert_eq!(interval_ranges(intervals.get(&3).unwrap()), vec![(2, 4)]);
        assert_eq!(interval_ranges(intervals.get(&5).unwrap()), vec![(4, 6)]);
        assert_eq!(interval_ranges(intervals.get(&7).unwrap()), vec![(6, 8)]);
    }

    // -----------------------------------------------------------------------
    // CopyCoalescer, CoalesceMode, and CoalesceStats tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_coalescer_aggressive_mode_same_as_functional() {
        // Aggressive mode should produce the same result as coalesce_copies.
        let func = make_function(vec![vec![
            copy_inst(vreg(1), vreg(0)),
            copy_inst(vreg(2), vreg(1)),
        ]]);

        let mut intervals_a = BTreeMap::from([
            (0, interval(0, &[(0, 1)])),
            (1, interval(1, &[(1, 2)])),
            (2, interval(2, &[(2, 3)])),
        ]);
        let mut intervals_b = intervals_a.clone();

        let result_fn = coalesce_copies(&func, &mut intervals_a);

        let mut coalescer = CopyCoalescer::new(CoalesceMode::Aggressive);
        let result_struct = coalescer.coalesce(&func, &mut intervals_b);

        assert_eq!(result_fn.copies_removed, result_struct.copies_removed);
        assert_eq!(result_fn.intervals_merged, result_struct.intervals_merged);
        assert_eq!(result_fn.removals, result_struct.removals);
        assert_eq!(result_fn.rewrites, result_struct.rewrites);
    }

    #[test]
    fn test_coalescer_conservative_rejects_wide_gap() {
        // Two intervals with a wide gap between them. Conservative mode uses
        // extent (max_end - min_start) to detect that merging would occupy a
        // register across a much wider program region:
        //
        // src: [0, 2)   -> extent = 2
        // dst: [10, 12) -> extent = 2
        // sum_extent = 4
        // merged: [0, 2) + [10, 12) -> extent = 12
        // 12 > 4 -> REJECT
        //
        // Aggressive mode allows this because the intervals don't overlap.

        let func = make_function(vec![vec![copy_inst(vreg(1), vreg(0))]]);
        let mut intervals =
            BTreeMap::from([(0, interval(0, &[(0, 2)])), (1, interval(1, &[(10, 12)]))]);

        let mut coalescer = CopyCoalescer::new(CoalesceMode::Conservative);
        let result = coalescer.coalesce(&func, &mut intervals);

        // Conservative rejects due to extent increase.
        assert_eq!(result.copies_removed, 0);
        assert_eq!(result.intervals_merged, 0);

        // But aggressive would accept:
        let mut intervals2 =
            BTreeMap::from([(0, interval(0, &[(0, 2)])), (1, interval(1, &[(10, 12)]))]);
        let mut aggressive = CopyCoalescer::new(CoalesceMode::Aggressive);
        let result2 = aggressive.coalesce(&func, &mut intervals2);
        assert_eq!(result2.copies_removed, 1);
        assert_eq!(result2.intervals_merged, 1);
    }

    #[test]
    fn test_coalescer_conservative_allows_non_overlapping() {
        let func = make_function(vec![vec![copy_inst(vreg(1), vreg(0))]]);
        let mut intervals =
            BTreeMap::from([(0, interval(0, &[(0, 1)])), (1, interval(1, &[(1, 2)]))]);

        let mut coalescer = CopyCoalescer::new(CoalesceMode::Conservative);
        let result = coalescer.coalesce(&func, &mut intervals);

        assert_eq!(result.copies_removed, 1);
        assert_eq!(result.intervals_merged, 1);
    }

    #[test]
    fn test_coalescer_conservative_chain() {
        // Test that conservative mode handles transitive chains.
        let func = make_function(vec![vec![
            copy_inst(vreg(1), vreg(0)),
            copy_inst(vreg(2), vreg(1)),
            copy_inst(vreg(3), vreg(2)),
        ]]);

        let mut intervals = BTreeMap::from([
            (0, interval(0, &[(0, 1)])),
            (1, interval(1, &[(1, 2)])),
            (2, interval(2, &[(2, 3)])),
            (3, interval(3, &[(3, 4)])),
        ]);

        let mut coalescer = CopyCoalescer::new(CoalesceMode::Conservative);
        let result = coalescer.coalesce(&func, &mut intervals);

        assert_eq!(result.copies_removed, 3);
        assert_eq!(result.intervals_merged, 3);
        assert_eq!(intervals.len(), 1);
    }

    #[test]
    fn test_can_coalesce_non_overlapping() {
        let coalescer = CopyCoalescer::new(CoalesceMode::Aggressive);
        let src = interval(0, &[(0, 2)]);
        let dst = interval(1, &[(3, 5)]);

        assert!(coalescer.can_coalesce(&src, &dst));
    }

    #[test]
    fn test_can_coalesce_overlapping_rejected() {
        let coalescer = CopyCoalescer::new(CoalesceMode::Aggressive);
        let src = interval(0, &[(0, 4)]);
        let dst = interval(1, &[(2, 6)]);

        assert!(!coalescer.can_coalesce(&src, &dst));
    }

    #[test]
    fn test_can_coalesce_conservative_mode() {
        let conservative = CopyCoalescer::new(CoalesceMode::Conservative);
        let aggressive = CopyCoalescer::new(CoalesceMode::Aggressive);

        // Non-overlapping, adjacent — both modes accept (extent equals sum).
        // src: [0, 2) extent=2, dst: [2, 4) extent=2, sum=4, merged=[0,4) extent=4
        let src_adj = interval(0, &[(0, 2)]);
        let dst_adj = interval(1, &[(2, 4)]);
        assert!(conservative.can_coalesce(&src_adj, &dst_adj));
        assert!(aggressive.can_coalesce(&src_adj, &dst_adj));

        // Non-overlapping, wide gap — conservative rejects, aggressive accepts.
        // src: [0, 2) extent=2, dst: [10, 12) extent=2, sum=4
        // merged: [0,2)+[10,12) extent=12 > 4 -> REJECT
        let src_gap = interval(0, &[(0, 2)]);
        let dst_gap = interval(1, &[(10, 12)]);
        assert!(!conservative.can_coalesce(&src_gap, &dst_gap));
        assert!(aggressive.can_coalesce(&src_gap, &dst_gap));

        // Overlapping — both modes reject.
        let src_overlap = interval(0, &[(0, 4)]);
        let dst_overlap = interval(1, &[(2, 6)]);
        assert!(!conservative.can_coalesce(&src_overlap, &dst_overlap));
        assert!(!aggressive.can_coalesce(&src_overlap, &dst_overlap));
    }

    #[test]
    fn test_can_coalesce_empty_intervals() {
        let coalescer = CopyCoalescer::new(CoalesceMode::Aggressive);
        let empty_a = LiveInterval::new(vreg(0));
        let empty_b = LiveInterval::new(vreg(1));

        assert!(coalescer.can_coalesce(&empty_a, &empty_b));
    }

    #[test]
    fn test_merge_intervals_public_api() {
        let src = interval(0, &[(0, 2)]);
        let dst = interval(1, &[(3, 5)]);

        let merged = CopyCoalescer::merge_intervals(&src, &dst);

        // Merged should use dst's VReg identity.
        assert_eq!(merged.vreg.id, 1);
        // Should contain both ranges.
        let ranges: Vec<(u32, u32)> = merged.ranges.iter().map(|r| (r.start, r.end)).collect();
        assert_eq!(ranges, vec![(0, 2), (3, 5)]);
    }

    #[test]
    fn test_merge_intervals_adjacent_ranges() {
        let src = interval(0, &[(0, 3)]);
        let dst = interval(1, &[(3, 6)]);

        let merged = CopyCoalescer::merge_intervals(&src, &dst);

        // Adjacent ranges should be merged into one.
        let ranges: Vec<(u32, u32)> = merged.ranges.iter().map(|r| (r.start, r.end)).collect();
        assert_eq!(ranges, vec![(0, 6)]);
    }

    #[test]
    fn test_merge_intervals_preserves_spill_weight() {
        let mut src = interval(0, &[(0, 2)]);
        src.spill_weight = 1.5;
        let mut dst = interval(1, &[(3, 5)]);
        dst.spill_weight = 2.5;

        let merged = CopyCoalescer::merge_intervals(&src, &dst);

        assert_eq!(merged.spill_weight, 4.0);
    }

    #[test]
    fn test_merge_intervals_preserves_use_def_positions() {
        let mut src = interval(0, &[(0, 2)]);
        src.use_positions = vec![0, 1];
        src.def_positions = vec![0];
        let mut dst = interval(1, &[(3, 5)]);
        dst.use_positions = vec![3, 4];
        dst.def_positions = vec![3];

        let merged = CopyCoalescer::merge_intervals(&src, &dst);

        assert_eq!(merged.use_positions, vec![0, 1, 3, 4]);
        assert_eq!(merged.def_positions, vec![0, 3]);
    }

    #[test]
    fn test_merge_intervals_is_fixed_propagates() {
        let mut src = interval(0, &[(0, 2)]);
        src.is_fixed = true;
        let dst = interval(1, &[(3, 5)]);

        let merged = CopyCoalescer::merge_intervals(&src, &dst);
        assert!(merged.is_fixed);
    }

    #[test]
    fn test_update_uses_public_api() {
        let mut func = make_function(vec![vec![
            generic_inst(1, vec![vreg(0)], vec![]),
            generic_inst(2, vec![vreg(1)], vec![vreg(0)]),
            generic_inst(3, vec![], vec![vreg(0), vreg(1)]),
        ]]);

        CopyCoalescer::update_uses(&mut func, vreg(0), vreg(5));

        // All occurrences of vreg 0 should now be vreg 5.
        let def0 = func.insts[0].defs[0].as_vreg().unwrap();
        assert_eq!(def0.id, 5);

        let use1 = func.insts[1].uses[0].as_vreg().unwrap();
        assert_eq!(use1.id, 5);

        let use2_0 = func.insts[2].uses[0].as_vreg().unwrap();
        assert_eq!(use2_0.id, 5);

        // vreg 1 should be unchanged.
        let def1 = func.insts[1].defs[0].as_vreg().unwrap();
        assert_eq!(def1.id, 1);
        let use2_1 = func.insts[2].uses[1].as_vreg().unwrap();
        assert_eq!(use2_1.id, 1);
    }

    #[test]
    fn test_coalesce_stats_tracking() {
        let result = CoalesceResult {
            copies_removed: 3,
            intervals_merged: 2,
            removals: Vec::new(),
            rewrites: BTreeMap::new(),
        };

        let stats = result.stats(5);

        assert_eq!(stats.copies_eliminated, 3);
        assert_eq!(stats.copies_remaining, 2);
        assert_eq!(stats.intervals_merged, 2);
    }

    #[test]
    fn test_coalesce_stats_zero_total() {
        let result = CoalesceResult::default();
        let stats = result.stats(0);

        assert_eq!(stats.copies_eliminated, 0);
        assert_eq!(stats.copies_remaining, 0);
        assert_eq!(stats.intervals_merged, 0);
    }

    #[test]
    fn test_coalesce_stats_all_eliminated() {
        let result = CoalesceResult {
            copies_removed: 10,
            intervals_merged: 8,
            removals: Vec::new(),
            rewrites: BTreeMap::new(),
        };
        let stats = result.stats(10);

        assert_eq!(stats.copies_eliminated, 10);
        assert_eq!(stats.copies_remaining, 0);
        assert_eq!(stats.intervals_merged, 8);
    }

    #[test]
    fn test_coalescer_reset() {
        let mut coalescer = CopyCoalescer::new(CoalesceMode::Aggressive);

        // Run on one function.
        let func = make_function(vec![vec![copy_inst(vreg(1), vreg(0))]]);
        let mut intervals =
            BTreeMap::from([(0, interval(0, &[(0, 1)])), (1, interval(1, &[(1, 2)]))]);
        let result = coalescer.coalesce(&func, &mut intervals);
        assert_eq!(result.copies_removed, 1);

        // Reset and run again on a fresh function.
        coalescer.reset();

        let func2 = make_function(vec![vec![copy_inst(vreg(3), vreg(2))]]);
        let mut intervals2 =
            BTreeMap::from([(2, interval(2, &[(0, 1)])), (3, interval(3, &[(1, 2)]))]);
        let result2 = coalescer.coalesce(&func2, &mut intervals2);
        assert_eq!(result2.copies_removed, 1);
        assert_eq!(result2.intervals_merged, 1);
    }

    #[test]
    fn test_coalescer_mode_accessor() {
        let aggressive = CopyCoalescer::new(CoalesceMode::Aggressive);
        assert_eq!(aggressive.mode(), CoalesceMode::Aggressive);

        let conservative = CopyCoalescer::new(CoalesceMode::Conservative);
        assert_eq!(conservative.mode(), CoalesceMode::Conservative);
    }

    #[test]
    fn test_coalesce_mode_default_is_aggressive() {
        assert_eq!(CoalesceMode::default(), CoalesceMode::Aggressive);
    }

    #[test]
    fn test_interval_span_helper() {
        let i = interval(0, &[(0, 3), (5, 8)]);
        assert_eq!(interval_span(&i), 6); // 3 + 3
    }

    #[test]
    fn test_interval_span_empty() {
        let i = LiveInterval::new(vreg(0));
        assert_eq!(interval_span(&i), 0);
    }

    // -----------------------------------------------------------------------
    // Extent-based conservative heuristic tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_interval_extent_single_range() {
        let i = interval(0, &[(3, 7)]);
        assert_eq!(interval_extent(&i), 4);
    }

    #[test]
    fn test_interval_extent_multiple_ranges() {
        let i = interval(0, &[(0, 3), (10, 15)]);
        assert_eq!(interval_extent(&i), 15); // 15 - 0
    }

    #[test]
    fn test_interval_extent_empty() {
        let i = LiveInterval::new(vreg(0));
        assert_eq!(interval_extent(&i), 0);
    }

    #[test]
    fn test_conservative_rejects_distant_intervals() {
        // Intervals far apart: conservative should reject because merged
        // extent far exceeds sum of individual extents.
        // src: [0, 1) extent=1, dst: [100, 101) extent=1
        // sum_extent = 2, merged_extent = 101 -> REJECT
        let coalescer = CopyCoalescer::new(CoalesceMode::Conservative);
        let src = interval(0, &[(0, 1)]);
        let dst = interval(1, &[(100, 101)]);
        assert!(!coalescer.can_coalesce(&src, &dst));
    }

    #[test]
    fn test_conservative_accepts_adjacent_intervals() {
        // Adjacent intervals: merged extent == sum of extents.
        // src: [0, 5) extent=5, dst: [5, 10) extent=5
        // sum_extent = 10, merged_extent = 10 -> ACCEPT
        let coalescer = CopyCoalescer::new(CoalesceMode::Conservative);
        let src = interval(0, &[(0, 5)]);
        let dst = interval(1, &[(5, 10)]);
        assert!(coalescer.can_coalesce(&src, &dst));
    }

    #[test]
    fn test_conservative_rejects_small_gap() {
        // Even a small gap causes rejection: merged extent barely exceeds sum.
        // src: [0, 3) extent=3, dst: [4, 7) extent=3
        // sum_extent = 6, merged_extent = 7 -> 7 > 6 -> REJECT
        let coalescer = CopyCoalescer::new(CoalesceMode::Conservative);
        let src = interval(0, &[(0, 3)]);
        let dst = interval(1, &[(4, 7)]);
        assert!(!coalescer.can_coalesce(&src, &dst));
    }

    #[test]
    fn test_conservative_multi_range_intervals() {
        // Multi-range src with large internal gap: extent already large.
        // src: [0, 2), [8, 10) -> extent = 10
        // dst: [10, 12) -> extent = 2
        // sum_extent = 12
        // merged: [0,2), [8,12) -> extent = 12
        // 12 <= 12 -> ACCEPT
        let coalescer = CopyCoalescer::new(CoalesceMode::Conservative);
        let src = interval(0, &[(0, 2), (8, 10)]);
        let dst = interval(1, &[(10, 12)]);
        assert!(coalescer.can_coalesce(&src, &dst));
    }

    #[test]
    fn test_conservative_multi_range_rejects_when_far() {
        // src: [0, 2), [3, 5) -> extent = 5
        // dst: [50, 52) -> extent = 2
        // sum_extent = 7
        // merged: [0,2), [3,5), [50,52) -> extent = 52
        // 52 > 7 -> REJECT
        let coalescer = CopyCoalescer::new(CoalesceMode::Conservative);
        let src = interval(0, &[(0, 2), (3, 5)]);
        let dst = interval(1, &[(50, 52)]);
        assert!(!coalescer.can_coalesce(&src, &dst));
    }

    #[test]
    fn test_conservative_coalesce_partial_chain() {
        // A chain where the first merge is accepted (adjacent) but the second
        // is rejected (wide gap) by conservative mode.
        //
        // copy v1 <- v0 (intervals adjacent, accepted)
        // copy v2 <- v1 (v1 now has extent [0,2), v2 at [20,21) -> rejected)
        let func = make_function(vec![vec![
            copy_inst(vreg(1), vreg(0)),
            copy_inst(vreg(2), vreg(1)),
        ]]);

        let mut intervals = BTreeMap::from([
            (0, interval(0, &[(0, 1)])),
            (1, interval(1, &[(1, 2)])),
            (2, interval(2, &[(20, 21)])),
        ]);

        let mut coalescer = CopyCoalescer::new(CoalesceMode::Conservative);
        let result = coalescer.coalesce(&func, &mut intervals);

        // First copy: v0 [0,1) and v1 [1,2) are adjacent -> accepted.
        // After merge: v1 has extent [0,2).
        // Second copy: merged v1 [0,2) and v2 [20,21):
        //   sum_extent = 2 + 1 = 3, merged_extent = 21 -> REJECT
        assert_eq!(result.copies_removed, 1);
        assert_eq!(result.intervals_merged, 1);

        // Compare with aggressive which accepts both:
        let mut intervals2 = BTreeMap::from([
            (0, interval(0, &[(0, 1)])),
            (1, interval(1, &[(1, 2)])),
            (2, interval(2, &[(20, 21)])),
        ]);
        let mut aggressive = CopyCoalescer::new(CoalesceMode::Aggressive);
        let result2 = aggressive.coalesce(&func, &mut intervals2);
        assert_eq!(result2.copies_removed, 2);
        assert_eq!(result2.intervals_merged, 2);
    }

    #[test]
    fn test_conservative_empty_src_accepted() {
        // Empty src merged with non-empty dst: extent stays same.
        let coalescer = CopyCoalescer::new(CoalesceMode::Conservative);
        let src = LiveInterval::new(vreg(0));
        let dst = interval(1, &[(5, 10)]);
        assert!(coalescer.can_coalesce(&src, &dst));
    }

    #[test]
    fn test_conservative_empty_dst_accepted() {
        let coalescer = CopyCoalescer::new(CoalesceMode::Conservative);
        let src = interval(0, &[(5, 10)]);
        let dst = LiveInterval::new(vreg(1));
        assert!(coalescer.can_coalesce(&src, &dst));
    }

    #[test]
    fn test_aggressive_vs_conservative_stats_differ() {
        // Construct a function where aggressive coalesces more than conservative.
        let func = make_function(vec![vec![
            copy_inst(vreg(1), vreg(0)),
            copy_inst(vreg(3), vreg(2)),
        ]]);

        // First pair: adjacent -> both modes accept.
        // Second pair: wide gap -> conservative rejects.
        let mut intervals_agg = BTreeMap::from([
            (0, interval(0, &[(0, 1)])),
            (1, interval(1, &[(1, 2)])),
            (2, interval(2, &[(3, 4)])),
            (3, interval(3, &[(50, 51)])),
        ]);
        let mut intervals_con = intervals_agg.clone();

        let mut aggressive = CopyCoalescer::new(CoalesceMode::Aggressive);
        let result_agg = aggressive.coalesce(&func, &mut intervals_agg);

        let mut conservative = CopyCoalescer::new(CoalesceMode::Conservative);
        let result_con = conservative.coalesce(&func, &mut intervals_con);

        // Aggressive: both copies coalesced.
        assert_eq!(result_agg.copies_removed, 2);
        assert_eq!(result_agg.intervals_merged, 2);

        // Conservative: only the first (adjacent) copy coalesced.
        assert_eq!(result_con.copies_removed, 1);
        assert_eq!(result_con.intervals_merged, 1);

        // Stats should reflect the difference.
        let stats_agg = result_agg.stats(2);
        let stats_con = result_con.stats(2);
        assert_eq!(stats_agg.copies_eliminated, 2);
        assert_eq!(stats_agg.copies_remaining, 0);
        assert_eq!(stats_con.copies_eliminated, 1);
        assert_eq!(stats_con.copies_remaining, 1);
    }
}
#[cfg(test)]
mod tuning_tests {
    use super::*;
    use crate::liveness::compute_live_intervals;
    use crate::machine_types::*;
    use crate::phi_elim::IR_COPY_OPCODE;

    fn v32(id: u32) -> VReg {
        VReg {
            id,
            class: RegClass::Gpr32,
        }
    }

    fn mk(opcode: u16, defs: Vec<MachOperand>, uses: Vec<MachOperand>) -> MachInst {
        MachInst {
            opcode,
            defs,
            uses,
            implicit_defs: vec![],
            implicit_uses: vec![],
            flags: InstFlags::default(),
            tied_operands: vec![],
        }
    }

    /// The loop-carried latch shape: carriers updated by whitelisted producers
    /// (csel), copies back at the latch. The kill-at-def rule must merge both
    /// carrier/update pairs.
    #[test]
    fn kill_at_def_merges_latch_carrier_updates() {
        let csel: u16 = trust_cg_ir::inst::AArch64Opcode::Csel as u16;
        // b0: v0=..; v1=..; b1(loop): v2=csel(v1,v0); v3=csel(v1,v2);
        //     copy v0<-v2; copy v1<-v3; br b1/b2; b2: use v0
        let insts = vec![
            mk(
                1,
                vec![MachOperand::VReg(v32(0))],
                vec![MachOperand::Imm(0)],
            ),
            mk(
                1,
                vec![MachOperand::VReg(v32(1))],
                vec![MachOperand::Imm(9)],
            ),
            mk(
                csel,
                vec![MachOperand::VReg(v32(2))],
                vec![MachOperand::VReg(v32(1)), MachOperand::VReg(v32(0))],
            ),
            mk(
                csel,
                vec![MachOperand::VReg(v32(3))],
                vec![MachOperand::VReg(v32(1)), MachOperand::VReg(v32(2))],
            ),
            mk(
                IR_COPY_OPCODE,
                vec![MachOperand::VReg(v32(0))],
                vec![MachOperand::VReg(v32(2))],
            ),
            mk(
                IR_COPY_OPCODE,
                vec![MachOperand::VReg(v32(1))],
                vec![MachOperand::VReg(v32(3))],
            ),
            MachInst {
                opcode: 0xBB,
                defs: vec![],
                uses: vec![
                    MachOperand::VReg(v32(0)),
                    MachOperand::Block(BlockId(1)),
                    MachOperand::Block(BlockId(2)),
                ],
                implicit_defs: vec![],
                implicit_uses: vec![],
                flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
                tied_operands: vec![],
            },
            mk(2, vec![], vec![MachOperand::VReg(v32(0))]),
        ];
        let func = MachFunction {
            name: "latch".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![InstId(0), InstId(1)],
                    preds: vec![],
                    succs: vec![BlockId(1)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(2), InstId(3), InstId(4), InstId(5), InstId(6)],
                    preds: vec![BlockId(0), BlockId(1)],
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 1,
                },
                MachBlock {
                    insts: vec![InstId(7)],
                    preds: vec![BlockId(1)],
                    succs: vec![],
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
            entry_block: BlockId(0),
            next_vreg: 4,
            next_stack_slot: 0,
            stack_slots: std::collections::BTreeMap::new(),
        };
        // Without tuning: the historical coalescer refuses (interval overlap).
        let mut intervals = compute_live_intervals(&func).intervals;
        let untuned = coalesce_copies(&func, &mut intervals);
        assert_eq!(
            untuned.copies_removed, 0,
            "control: historical coalescer must refuse the latch merges"
        );
        // With aarch64 tuning: both carrier/update pairs merge.
        let mut intervals = compute_live_intervals(&func).intervals;
        let tuned = coalesce_copies_tuned(&func, &mut intervals, &CoalesceTuning::aarch64());
        assert_eq!(tuned.copies_removed, 2, "kill-at-def must merge both pairs");
        assert_eq!(tuned.rewrites.get(&v32(2)), Some(&v32(0)));
        assert_eq!(tuned.rewrites.get(&v32(3)), Some(&v32(1)));
    }

    /// A NON-whitelisted producer must refuse the kill-at-def merge (the
    /// fail-closed default for opcodes whose encoding is not proven
    /// single-instruction read-then-write).
    #[test]
    fn kill_at_def_refuses_non_whitelisted_producer() {
        let insts = vec![
            mk(
                1,
                vec![MachOperand::VReg(v32(0))],
                vec![MachOperand::Imm(0)],
            ),
            // Producer opcode 0x77 is NOT in the whitelist.
            mk(
                0x77,
                vec![MachOperand::VReg(v32(2))],
                vec![MachOperand::VReg(v32(0))],
            ),
            mk(
                IR_COPY_OPCODE,
                vec![MachOperand::VReg(v32(0))],
                vec![MachOperand::VReg(v32(2))],
            ),
            MachInst {
                opcode: 0xBB,
                defs: vec![],
                uses: vec![
                    MachOperand::VReg(v32(0)),
                    MachOperand::Block(BlockId(1)),
                    MachOperand::Block(BlockId(2)),
                ],
                implicit_defs: vec![],
                implicit_uses: vec![],
                flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
                tied_operands: vec![],
            },
            mk(2, vec![], vec![MachOperand::VReg(v32(0))]),
        ];
        let func = MachFunction {
            name: "nowhite".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![InstId(0)],
                    preds: vec![],
                    succs: vec![BlockId(1)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(1), InstId(2), InstId(3)],
                    preds: vec![BlockId(0), BlockId(1)],
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 1,
                },
                MachBlock {
                    insts: vec![InstId(4)],
                    preds: vec![BlockId(1)],
                    succs: vec![],
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
            entry_block: BlockId(0),
            next_vreg: 3,
            next_stack_slot: 0,
            stack_slots: std::collections::BTreeMap::new(),
        };
        let mut intervals = compute_live_intervals(&func).intervals;
        let tuned = coalesce_copies_tuned(&func, &mut intervals, &CoalesceTuning::aarch64());
        assert_eq!(
            tuned.copies_removed, 0,
            "non-whitelisted producer must fail closed"
        );
    }

    /// Rn-only producers (the shifted-register ALU forms): the kill-at-def
    /// merge is allowed when the loop-carried value feeds the UN-shifted `Rn`
    /// slot (`uses[0]`), and refused when it feeds the shifted `Rm` slot
    /// (`uses[1]`) — the measured m2_call_heavy recurrence hazard (the merged
    /// in-place update would route the loop-carried dependence through the
    /// shifter).
    #[test]
    fn kill_at_def_rn_only_producer_slot_gating() {
        let eor_lsr: u16 = trust_cg_ir::inst::AArch64Opcode::EorRRLsr as u16;
        // Loop shape (m2_call_heavy latch, carrier v0, invariant-ish v1):
        //   b0: v0=..; v1=..
        //   b1: v2 = EorRRLsr(rn, rm, #11); copy v0<-v2; br b1/b2
        //   b2: use v0
        // Parameterized over which slot the carrier v0 occupies.
        let build = |rn: u32, rm: u32| {
            let insts = vec![
                mk(
                    1,
                    vec![MachOperand::VReg(v32(0))],
                    vec![MachOperand::Imm(0)],
                ),
                mk(
                    1,
                    vec![MachOperand::VReg(v32(1))],
                    vec![MachOperand::Imm(9)],
                ),
                mk(
                    eor_lsr,
                    vec![MachOperand::VReg(v32(2))],
                    vec![
                        MachOperand::VReg(v32(rn)),
                        MachOperand::VReg(v32(rm)),
                        MachOperand::Imm(11),
                    ],
                ),
                // Filler between producer and latch copy (the real latch has
                // the IV update here); without it the conflated-position
                // liveness model fuses the carrier's kill and redef into one
                // range and the overlap is multi-position for BOTH slots.
                mk(2, vec![], vec![MachOperand::VReg(v32(1))]),
                mk(
                    IR_COPY_OPCODE,
                    vec![MachOperand::VReg(v32(0))],
                    vec![MachOperand::VReg(v32(2))],
                ),
                MachInst {
                    opcode: 0xBB,
                    defs: vec![],
                    uses: vec![
                        MachOperand::VReg(v32(0)),
                        MachOperand::VReg(v32(1)),
                        MachOperand::Block(BlockId(1)),
                        MachOperand::Block(BlockId(2)),
                    ],
                    implicit_defs: vec![],
                    implicit_uses: vec![],
                    flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
                    tied_operands: vec![],
                },
                mk(2, vec![], vec![MachOperand::VReg(v32(0))]),
            ];
            MachFunction {
                name: "rnonly".into(),
                insts,
                blocks: vec![
                    MachBlock {
                        insts: vec![InstId(0), InstId(1)],
                        preds: vec![],
                        succs: vec![BlockId(1)],
                        loop_depth: 0,
                    },
                    MachBlock {
                        insts: vec![InstId(2), InstId(3), InstId(4), InstId(5)],
                        preds: vec![BlockId(0), BlockId(1)],
                        succs: vec![BlockId(1), BlockId(2)],
                        loop_depth: 1,
                    },
                    MachBlock {
                        insts: vec![InstId(6)],
                        preds: vec![BlockId(1)],
                        succs: vec![],
                        loop_depth: 0,
                    },
                ],
                block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
                entry_block: BlockId(0),
                next_vreg: 3,
                next_stack_slot: 0,
                stack_slots: std::collections::BTreeMap::new(),
            }
        };

        // Carrier in the un-shifted Rn slot: merge (p5_struct_acc shape).
        let func = build(0, 1);
        let mut intervals = compute_live_intervals(&func).intervals;
        let tuned = coalesce_copies_tuned(&func, &mut intervals, &CoalesceTuning::aarch64());
        assert_eq!(
            tuned.copies_removed, 1,
            "carrier in the un-shifted Rn slot must merge"
        );
        assert_eq!(tuned.rewrites.get(&v32(2)), Some(&v32(0)));

        // Carrier in the shifted Rm slot: refuse (m2_call_heavy hazard).
        let func = build(1, 0);
        let mut intervals = compute_live_intervals(&func).intervals;
        let tuned = coalesce_copies_tuned(&func, &mut intervals, &CoalesceTuning::aarch64());
        assert_eq!(
            tuned.copies_removed, 0,
            "carrier in the shifted Rm slot must fail closed"
        );
    }

    /// Normalization: hardened `AddRI d, s, #0` and same-class `MovR` become
    /// real copies; a width-mismatched `MOVWrr` over Gpr64 (a truncation
    /// idiom) must NOT be rewritten.
    #[test]
    fn normalization_shapes() {
        use trust_cg_ir::inst::AArch64Opcode as A;
        let v64 = |id| VReg {
            id,
            class: RegClass::Gpr64,
        };
        let insts = vec![
            // Hardened guard copy -> Copy.
            mk(
                A::AddRI as u16,
                vec![MachOperand::VReg(v32(0))],
                vec![MachOperand::VReg(v32(1)), MachOperand::Imm(0)],
            ),
            // Genuine add #5 -> untouched.
            mk(
                A::AddRI as u16,
                vec![MachOperand::VReg(v32(2))],
                vec![MachOperand::VReg(v32(1)), MachOperand::Imm(5)],
            ),
            // Same-class MovR -> Copy.
            mk(
                A::MovR as u16,
                vec![MachOperand::VReg(v32(3))],
                vec![MachOperand::VReg(v32(1))],
            ),
            // W-form mov over Gpr64 vregs (truncation idiom) -> untouched.
            mk(
                A::MOVWrr as u16,
                vec![MachOperand::VReg(v64(4))],
                vec![MachOperand::VReg(v64(5))],
            ),
        ];
        let mut func = MachFunction {
            name: "norm".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![InstId(0), InstId(1), InstId(2), InstId(3)],
                preds: vec![],
                succs: vec![],
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 6,
            next_stack_slot: 0,
            stack_slots: std::collections::BTreeMap::new(),
        };
        normalize_move_like_copies(&mut func, &CoalesceTuning::aarch64());
        assert_eq!(func.insts[0].opcode, IR_COPY_OPCODE);
        assert_eq!(func.insts[0].uses.len(), 1);
        assert_eq!(func.insts[1].opcode, A::AddRI as u16);
        assert_eq!(func.insts[2].opcode, IR_COPY_OPCODE);
        assert_eq!(func.insts[3].opcode, A::MOVWrr as u16);
    }

    /// `NeonOrrV d, s, s` normalization (the vectorizer FMA-addend copy —
    /// Linpack daxpy `mov.16b`): the same-source `Fpr128` form becomes a real
    /// copy; a two-distinct-source `NeonOrrV` (genuine bitwise OR) and a
    /// scalar-class same-source form (whose survivor re-lowering would change
    /// the `.8B`/`.16B` arrangement) must NOT be rewritten; and with
    /// `vec_move_ops` cleared (the `TCG_AARCH64_NEON_ORR_COALESCE_OFF` kill
    /// switch) nothing is rewritten at all.
    #[test]
    fn neon_orrv_normalization_shapes() {
        use trust_cg_ir::inst::AArch64Opcode as A;
        let vq = |id| VReg {
            id,
            class: RegClass::Fpr128,
        };
        let vd = |id| VReg {
            id,
            class: RegClass::Fpr64,
        };
        let orr = A::NeonOrrV as u16;
        let insts = vec![
            // Same-source Fpr128 whole-register move -> Copy.
            mk(
                orr,
                vec![MachOperand::VReg(vq(0))],
                vec![MachOperand::VReg(vq(1)), MachOperand::VReg(vq(1))],
            ),
            // Genuine bitwise OR of two distinct sources -> untouched.
            mk(
                orr,
                vec![MachOperand::VReg(vq(2))],
                vec![MachOperand::VReg(vq(1)), MachOperand::VReg(vq(3))],
            ),
            // Scalar-class same-source form -> untouched (arrangement gate).
            mk(
                orr,
                vec![MachOperand::VReg(vd(4))],
                vec![MachOperand::VReg(vd(5)), MachOperand::VReg(vd(5))],
            ),
        ];
        let mk_func = |insts: Vec<MachInst>| MachFunction {
            name: "orrv_norm".into(),
            insts,
            blocks: vec![MachBlock {
                insts: vec![InstId(0), InstId(1), InstId(2)],
                preds: vec![],
                succs: vec![],
                loop_depth: 0,
            }],
            block_order: vec![BlockId(0)],
            entry_block: BlockId(0),
            next_vreg: 6,
            next_stack_slot: 0,
            stack_slots: std::collections::BTreeMap::new(),
        };
        let mut func = mk_func(insts.clone());
        normalize_move_like_copies(&mut func, &CoalesceTuning::aarch64());
        assert_eq!(func.insts[0].opcode, IR_COPY_OPCODE);
        assert_eq!(func.insts[0].uses.len(), 1);
        assert_eq!(func.insts[0].uses[0], MachOperand::VReg(vq(1)));
        assert_eq!(func.insts[1].opcode, orr, "distinct sources = genuine OR");
        assert_eq!(func.insts[2].opcode, orr, "scalar class must stay NeonOrrV");
        // Kill switch: an empty `vec_move_ops` leaves every NeonOrrV untouched.
        let mut off = CoalesceTuning::aarch64();
        off.vec_move_ops.clear();
        let mut func_off = mk_func(insts);
        normalize_move_like_copies(&mut func_off, &off);
        assert_eq!(func_off.insts[0].opcode, orr);
        assert_eq!(func_off.insts[0].uses.len(), 2);
    }

    /// The FP-reduction accumulator latch shape: loop-carried FMADD
    /// accumulators (`acc = n*m + acc`, the `llvm.fmuladd` carrier) whose
    /// loop-carried latch copies the kill-at-def rule must merge into in-place
    /// `FMADD acc, n, m, acc`. This is the per-iteration `fmov` spectral-norm
    /// carried because `FmaddRR` was absent from the aarch64 whitelist. The
    /// structure mirrors `kill_at_def_merges_latch_carrier_updates` with the
    /// csel producers swapped for FMADD (same carrier use pattern: `Ra`/`Rn`
    /// carry the loop-carried operands, `Rm` a loop invariant). The
    /// `without_fmadd` control proves the merge is gated SPECIFICALLY on the new
    /// whitelist entry (every other producer present, still refused).
    #[test]
    fn kill_at_def_merges_fmadd_accumulator() {
        use trust_cg_ir::inst::AArch64Opcode as A;
        let fmadd = A::FmaddRR as u16;
        let vf = |id| VReg {
            id,
            class: RegClass::Fpr64,
        };
        // b0: v0=acc0; v1=acc1; v11=m (loop invariant)
        // b1(loop): v2 = FMADD(Rn=v1, Rm=v11, Ra=v0);
        //           v3 = FMADD(Rn=v1, Rm=v11, Ra=v2);
        //           copy v0<-v2; copy v1<-v3; br v0 b1/b2
        // b2: use v0
        let insts = vec![
            mk(1, vec![MachOperand::VReg(vf(0))], vec![MachOperand::Imm(0)]),
            mk(1, vec![MachOperand::VReg(vf(1))], vec![MachOperand::Imm(9)]),
            mk(
                1,
                vec![MachOperand::VReg(vf(11))],
                vec![MachOperand::Imm(2)],
            ),
            // FMADD operands [Rd, Rn, Rm, Ra]: Rd is a pure def; the accumulator
            // v0 enters as the Ra source and dies here.
            mk(
                fmadd,
                vec![MachOperand::VReg(vf(2))],
                vec![
                    MachOperand::VReg(vf(1)),
                    MachOperand::VReg(vf(11)),
                    MachOperand::VReg(vf(0)),
                ],
            ),
            mk(
                fmadd,
                vec![MachOperand::VReg(vf(3))],
                vec![
                    MachOperand::VReg(vf(1)),
                    MachOperand::VReg(vf(11)),
                    MachOperand::VReg(vf(2)),
                ],
            ),
            mk(
                IR_COPY_OPCODE,
                vec![MachOperand::VReg(vf(0))],
                vec![MachOperand::VReg(vf(2))],
            ),
            mk(
                IR_COPY_OPCODE,
                vec![MachOperand::VReg(vf(1))],
                vec![MachOperand::VReg(vf(3))],
            ),
            MachInst {
                opcode: 0xBB,
                defs: vec![],
                uses: vec![
                    MachOperand::VReg(vf(0)),
                    MachOperand::Block(BlockId(1)),
                    MachOperand::Block(BlockId(2)),
                ],
                implicit_defs: vec![],
                implicit_uses: vec![],
                flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
                tied_operands: vec![],
            },
            mk(2, vec![], vec![MachOperand::VReg(vf(0))]),
        ];
        let func = MachFunction {
            name: "fmadd_acc".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![InstId(0), InstId(1), InstId(2)],
                    preds: vec![],
                    succs: vec![BlockId(1)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(3), InstId(4), InstId(5), InstId(6), InstId(7)],
                    preds: vec![BlockId(0), BlockId(1)],
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 1,
                },
                MachBlock {
                    insts: vec![InstId(8)],
                    preds: vec![BlockId(1)],
                    succs: vec![],
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
            entry_block: BlockId(0),
            next_vreg: 12,
            next_stack_slot: 0,
            stack_slots: std::collections::BTreeMap::new(),
        };
        // Control: the plain (untuned) coalescer refuses the interval overlap.
        let mut intervals = compute_live_intervals(&func).intervals;
        let untuned = coalesce_copies(&func, &mut intervals);
        assert_eq!(
            untuned.copies_removed, 0,
            "control: plain coalescer refuses the FMADD latch merges"
        );
        // Control: aarch64 tuning with FmaddRR *removed* still refuses — proving
        // the merge is gated specifically on the new whitelist entry, not on any
        // pre-existing producer.
        let mut without_fmadd = CoalesceTuning::aarch64();
        without_fmadd.kill_def_producers.remove(&fmadd);
        let mut intervals = compute_live_intervals(&func).intervals;
        let no_fmadd = coalesce_copies_tuned(&func, &mut intervals, &without_fmadd);
        assert_eq!(
            no_fmadd.copies_removed, 0,
            "FmaddRR absent from the whitelist -> the latch copies survive (spectral-norm fmov)"
        );
        // With the fix: both accumulator latch copies coalesce; each FMADD
        // becomes an in-place `FMADD acc, n, m, acc`.
        let mut intervals = compute_live_intervals(&func).intervals;
        let tuned = coalesce_copies_tuned(&func, &mut intervals, &CoalesceTuning::aarch64());
        assert_eq!(
            tuned.copies_removed, 2,
            "kill-at-def must merge both FMADD accumulator latch copies"
        );
        assert_eq!(tuned.intervals_merged, 2);
        assert_eq!(
            tuned.rewrites.get(&vf(2)),
            Some(&vf(0)),
            "FMADD dst v2 rewritten to the accumulator v0 (in-place FMADD)"
        );
        assert_eq!(tuned.rewrites.get(&vf(3)), Some(&vf(1)));
    }

    /// The whitelist widens the kill-at-def REASONING, not the safety
    /// conditions. When the FMADD result (`v2`, the copy's source) is genuinely
    /// still live PAST the latch copy — a real interference, not a clean
    /// kill-then-def — the merge must stay REFUSED even though `FmaddRR` is now
    /// whitelisted: coalescing `v2` into `v0` would clobber the value the later
    /// use of `v2` needs. This is the multi-position overlap the single-position
    /// gate fails closed on.
    #[test]
    fn kill_at_def_refuses_fmadd_result_still_live() {
        use trust_cg_ir::inst::AArch64Opcode as A;
        let fmadd = A::FmaddRR as u16;
        let vf = |id| VReg {
            id,
            class: RegClass::Fpr64,
        };
        // b1: v2 = FMADD(v10, v11, v0); copy v0<-v2; use v2 (STILL LIVE); br
        let insts = vec![
            mk(1, vec![MachOperand::VReg(vf(0))], vec![MachOperand::Imm(0)]),
            mk(
                1,
                vec![MachOperand::VReg(vf(10))],
                vec![MachOperand::Imm(1)],
            ),
            mk(
                1,
                vec![MachOperand::VReg(vf(11))],
                vec![MachOperand::Imm(2)],
            ),
            mk(
                fmadd,
                vec![MachOperand::VReg(vf(2))],
                vec![
                    MachOperand::VReg(vf(10)),
                    MachOperand::VReg(vf(11)),
                    MachOperand::VReg(vf(0)),
                ],
            ),
            mk(
                IR_COPY_OPCODE,
                vec![MachOperand::VReg(vf(0))],
                vec![MachOperand::VReg(vf(2))],
            ),
            // Second, independent use of the FMADD result: v2 is live past the
            // latch copy, so v0-new and v2 genuinely interfere over >1 position.
            mk(2, vec![], vec![MachOperand::VReg(vf(2))]),
            MachInst {
                opcode: 0xBB,
                defs: vec![],
                uses: vec![
                    MachOperand::VReg(vf(0)),
                    MachOperand::Block(BlockId(1)),
                    MachOperand::Block(BlockId(2)),
                ],
                implicit_defs: vec![],
                implicit_uses: vec![],
                flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
                tied_operands: vec![],
            },
            mk(2, vec![], vec![MachOperand::VReg(vf(0))]),
        ];
        let func = MachFunction {
            name: "fmadd_live".into(),
            insts,
            blocks: vec![
                MachBlock {
                    insts: vec![InstId(0), InstId(1), InstId(2)],
                    preds: vec![],
                    succs: vec![BlockId(1)],
                    loop_depth: 0,
                },
                MachBlock {
                    insts: vec![InstId(3), InstId(4), InstId(5), InstId(6)],
                    preds: vec![BlockId(0), BlockId(1)],
                    succs: vec![BlockId(1), BlockId(2)],
                    loop_depth: 1,
                },
                MachBlock {
                    insts: vec![InstId(7)],
                    preds: vec![BlockId(1)],
                    succs: vec![],
                    loop_depth: 0,
                },
            ],
            block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
            entry_block: BlockId(0),
            next_vreg: 12,
            next_stack_slot: 0,
            stack_slots: std::collections::BTreeMap::new(),
        };
        // Even with FmaddRR whitelisted, the genuine interference is refused.
        let mut intervals = compute_live_intervals(&func).intervals;
        let tuned = coalesce_copies_tuned(&func, &mut intervals, &CoalesceTuning::aarch64());
        assert_eq!(
            tuned.copies_removed, 0,
            "FMADD result live past the copy -> genuine interference -> merge must be refused"
        );
    }
}
