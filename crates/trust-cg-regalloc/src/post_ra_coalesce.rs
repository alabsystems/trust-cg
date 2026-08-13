// trust-cg-regalloc/post_ra_coalesce.rs - Post-register-allocation copy coalescing
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Post-register-allocation copy coalescing.
//!
//! After register allocation assigns physical registers, the code may contain
//! redundant copy instructions:
//!
//! 1. **Identity copies:** `PSEUDO_COPY Xd <- Xd` where source and destination
//!    are the same physical register. These arise when the allocator assigns
//!    the same PReg to both sides of a phi-elimination copy.
//!
//! 2. **Rename-coalescible copies:** `PSEUDO_COPY Xd <- Xs` where `Xd != Xs`
//!    but renaming all subsequent uses of `Xd` to `Xs` within the block is
//!    safe (no interference). This eliminates the copy entirely by adjusting
//!    later operands.
//!
//! 3. **Backward def coalescing:** `PSEUDO_COPY Xd <- Xs` where `Xs` was
//!    produced by a nearby same-block computation and is otherwise unused.
//!    When retargeting that computation to define `Xd` cannot clobber a live
//!    value, the copy is deleted and the value is produced directly in `Xd`.
//!
//! This pass runs on the regalloc-level `MachFunction` (with separated
//! defs/uses and `u16` opcodes), operating entirely on physical registers.
//! It is a block-local transformation — no cross-block analysis is performed,
//! keeping the algorithm fast and simple.
//!
//! ## Algorithm (block-local rename coalescing)
//!
//! For each `PSEUDO_COPY Xd <- Xs` where `Xd != Xs`:
//! 1. Scan forward from the copy to find all uses of `Xd` in the block.
//! 2. Check that `Xs` is not redefined (clobbered) before the last use of `Xd`.
//! 3. Check that `Xd` is not used as an implicit operand of any intervening
//!    instruction that also implicitly uses/defines `Xs`.
//! 4. If safe, rename all uses of `Xd` to `Xs` and delete the copy.
//! 5. If no forward rename is possible, look backward for a same-block
//!    retargetable source definition and delete the copy when the def can be
//!    changed to write `Xd` directly.
//!
//! Conservative safety: we do NOT rename across calls, returns, or any
//! instruction that has implicit defs/uses of the destination register.
//!
//! Reference: LLVM `PeepholeOptimizer.cpp` — post-RA copy elimination.

use crate::machine_types::{InstFlags, InstId, MachFunction, MachInst, MachOperand, PReg};
use std::collections::BTreeSet;

/// A no-op pseudo-instruction opcode for deleted instructions.
/// We reuse the existing NOP pattern: opcode 0 with empty operands.
const NOP_OPCODE: u16 = 0xFFFF;

/// Kill switch for the WIDE backward-def retargeting allowlist
/// (see [`is_retargetable_opcode`]). When set, `can_retarget_source_def`
/// falls back to the historical narrow set — six register-register opcodes
/// plus the self-referential `AddRI`/`SubRI` carrier shape — and the emitted
/// objects are byte-identical to the pre-widening compiler.
const WIDE_BACKDEF_KILL_SWITCH: &str = "TCG_NO_WIDE_BACKDEF_COALESCE";

/// Kill switch for the SUB-REGISTER copy transforms — the cross-width GPR
/// self-copy (`Copy Wr <- Xr`, emitted `mov wr, wr`) and the narrow-return
/// zero-extension collapse (`UXTW Xd, Ws`, emitted `mov wd, ws`). When set,
/// both shapes are left alone exactly as before.
const SUBREG_COPY_KILL_SWITCH: &str = "TCG_NO_SUBREG_COPY_COALESCE";

/// Which of the two independently-killable transforms this run may perform.
/// Read once per pass invocation and threaded down, so a single run makes one
/// decision for the whole function (and unit tests can drive every setting
/// without touching process environment state).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PostRACoalesceConfig {
    /// Admit the wide pure-single-def ALU allowlist for backward-def
    /// retargeting (`TCG_NO_WIDE_BACKDEF_COALESCE` clears it).
    pub wide_backdef: bool,
    /// Admit the sub-register GPR32/GPR64 copy transforms
    /// (`TCG_NO_SUBREG_COPY_COALESCE` clears it).
    pub subreg_copies: bool,
}

impl PostRACoalesceConfig {
    /// The historical behaviour: both widenings off.
    pub const NARROW: Self = Self {
        wide_backdef: false,
        subreg_copies: false,
    };

    /// Everything on.
    pub const ALL: Self = Self {
        wide_backdef: true,
        subreg_copies: true,
    };

    /// Derive the configuration from the process environment kill switches.
    fn from_env() -> Self {
        Self {
            wide_backdef: std::env::var_os(WIDE_BACKDEF_KILL_SWITCH).is_none(),
            subreg_copies: std::env::var_os(SUBREG_COPY_KILL_SWITCH).is_none(),
        }
    }
}

/// Statistics from the post-RA copy coalescing pass.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PostRACoalesceResult {
    /// Total number of copy instructions removed.
    pub copies_removed: u32,
    /// Number of identity copies removed (src == dst).
    pub identity_copies: u32,
    /// Number of copies removed by rename coalescing (src != dst).
    pub rename_coalesced: u32,
}

/// Run post-register-allocation copy coalescing on the given function.
///
/// This pass modifies the function in-place, removing redundant copy
/// instructions. Deleted copies are replaced with NOP pseudo-instructions
/// (opcode `NOP_OPCODE` with empty operands).
///
/// Returns statistics about what was eliminated.
///
/// ## Liveness staleness and the recompute strategy
///
/// `coalesce_block` consults whole-function physical liveness (`live_out` of
/// the block being processed) to prove transforms safe. The historical
/// implementation recomputed `compute_physical_liveness(func)` at the top of
/// EVERY block iteration — O(blocks² × insts) — which made regalloc the
/// dominant compile-time cost on large machine functions (a 3,921-block /
/// 29,229-inst function spent ~55s here).
///
/// ### Which liveness facts can go stale, and why we never use stale facts
///
/// The pass performs exactly three kinds of mutation, all local to the block
/// `B` currently being processed:
///
/// 1. NOP-ing a copy (`nop_inst`): removes one def of `dst` and one use of
///    `src` from `B`.
/// 2. Rename coalescing (`try_rename_coalesce` phase 2): rewrites explicit
///    uses of `dst` to `src` in later instructions of `B`, then NOPs the copy.
/// 3. Backward def retargeting (`try_backward_def_coalesce`): rewrites the
///    def operand of an earlier instruction in `B` from `src` to `dst`, then
///    NOPs the copy.
///
/// Each mutation changes the dataflow transfer function of `B` only. That can
/// change `live_in[B]`, which propagates backward to `live_out`/`live_in` of
/// every block that can REACH `B` in the CFG — including `B` itself when `B`
/// sits on a cycle (the common case inside loops). Crucially the change is
/// NOT always shrinking: removing the copy's def of `dst` can EXPOSE a
/// previously-killed upward use of a register that aliases `dst` (e.g. a `W`
/// sub-register use below a removed `X`-register def), GROWING true liveness.
/// A grown fact that a stale cache still reports as dead would let a later
/// block coalesce a copy whose destination is in fact live — a miscompile.
/// Because an under-approximating stale fact is unsafe and proving the
/// absence of the alias-exposure channel is not tractable here, we never act
/// on stale liveness at all: the cache is invalidated whenever a mutation
/// occurs and recomputed before the next block that could consult it.
///
/// ### Decision identity with the per-block-recompute reference
///
/// This function is decision-for-decision identical to
/// [`post_ra_coalesce_reference`] (the historical implementation, kept as a
/// test oracle and as the fallback):
///
/// - `coalesce_block` reads only `func` and the block's `live_out` set; its
///   processing order over blocks/instructions is unchanged.
/// - A mutation occurs if and only if `result.copies_removed` is incremented
///   (every mutating path — identity NOP, rename+NOP, retarget+NOP —
///   increments it; all other paths are read-only).
/// - If no mutation occurred since the cache was (re)computed,
///   `compute_physical_liveness` is a pure function of an unchanged `func`,
///   so the reference's fresh recompute would return exactly the cached
///   value.
/// - The cached fixpoint itself is computed block-summary-wise on bitsets but
///   sweeps in the same order, with the same convergence test and the same
///   iteration cap as `compute_physical_liveness`, and the per-block transfer
///   function is extensionally equal (see `block_summary`), so every sweep —
///   and therefore the result, converged or capped — is set-for-set equal.
/// - Blocks containing no copy-like opcode are skipped without procuring
///   liveness: `coalesce_block` `continue`s on every instruction of such a
///   block, never reading `live_out` and never mutating, so skipping the
///   procurement (not the call semantics) is observationally identical.
/// - Within a block, the reference uses the liveness snapshot taken at block
///   start for ALL copies in that block (even after intra-block mutations);
///   the cache reproduces exactly that snapshot semantics by refreshing only
///   at block boundaries.
///
/// Functions containing a physical register whose encoding does not fit the
/// fixed-width bitset (`PRegSet`) fall back to the reference implementation
/// (slow but exact).
pub fn post_ra_coalesce(func: &mut MachFunction) -> PostRACoalesceResult {
    post_ra_coalesce_with_config(func, PostRACoalesceConfig::from_env())
}

/// [`post_ra_coalesce`] with the wide backward-def allowlist forced on or off.
/// The public entry point derives `wide` from the
/// `TCG_NO_WIDE_BACKDEF_COALESCE` kill switch; tests drive both settings here
/// without mutating process environment state.
#[doc(hidden)]
pub fn post_ra_coalesce_with_config(
    func: &mut MachFunction,
    cfg: PostRACoalesceConfig,
) -> PostRACoalesceResult {
    // Fall back to the exact historical implementation if any physical
    // register encoding exceeds the bitset capacity. Mutations never
    // introduce register encodings that are not already present (renames use
    // `src`, retargets use `dst`, NOPs only clear), so a single up-front scan
    // suffices.
    if function_has_out_of_range_preg(func) {
        return post_ra_coalesce_reference_with_config(func, cfg);
    }

    let mut result = PostRACoalesceResult::default();

    // Process each block independently (block-local analysis).
    let block_indices: Vec<usize> = if func.block_order.is_empty() {
        (0..func.blocks.len()).collect()
    } else {
        func.block_order
            .iter()
            .map(|block_id| block_id.0 as usize)
            .collect()
    };

    let mut cache = CachedLiveness::new(func.blocks.len());

    for block_idx in block_indices {
        let block_insts: Vec<InstId> = func.blocks[block_idx].insts.clone();

        // Fast skip: a block with no copy-like opcode cannot mutate anything
        // and never reads `live_out` (`coalesce_block` skips every inst), so
        // we avoid procuring liveness for it entirely.
        let has_copy_candidate = block_insts.iter().any(|&inst_id| {
            is_coalesce_candidate_opcode(func.insts[inst_id.0 as usize].opcode, cfg)
        });
        if !has_copy_candidate {
            continue;
        }

        // Reproduce the reference's block-start liveness snapshot: recompute
        // (from per-block summaries) iff a mutation occurred since the last
        // fixpoint.
        let block_live_out: BTreeSet<PReg> = cache.live_out_at_block_start(func, block_idx);

        let copies_before = result.copies_removed;
        coalesce_block(func, &block_insts, &block_live_out, &mut result, cfg);
        if result.copies_removed != copies_before {
            // The block's transfer function may have changed; its summary must
            // be rebuilt and the global fixpoint refreshed before the next
            // block consults liveness.
            cache.note_block_mutated(block_idx);
        }
    }

    // Remove NOP'd instructions from block instruction lists.
    for block in &mut func.blocks {
        block.insts.retain(|inst_id| {
            let inst = &func.insts[inst_id.0 as usize];
            inst.opcode != NOP_OPCODE
        });
    }

    result
}

/// Historical implementation: recompute whole-function physical liveness at
/// the top of every block iteration — O(blocks² × insts).
///
/// Kept verbatim for two purposes:
/// - the test oracle for decision-identity of the cached fast path, and
/// - the exact fallback for functions whose register encodings do not fit
///   the fixed-width bitset used by the fast path.
#[doc(hidden)]
pub fn post_ra_coalesce_reference(func: &mut MachFunction) -> PostRACoalesceResult {
    post_ra_coalesce_reference_with_config(func, PostRACoalesceConfig::from_env())
}

/// [`post_ra_coalesce_reference`] with the wide backward-def allowlist forced.
#[doc(hidden)]
pub fn post_ra_coalesce_reference_with_config(
    func: &mut MachFunction,
    cfg: PostRACoalesceConfig,
) -> PostRACoalesceResult {
    let mut result = PostRACoalesceResult::default();

    // Process each block independently (block-local analysis).
    let block_indices: Vec<usize> = if func.block_order.is_empty() {
        (0..func.blocks.len()).collect()
    } else {
        func.block_order
            .iter()
            .map(|block_id| block_id.0 as usize)
            .collect()
    };

    for block_idx in block_indices {
        let liveness = compute_physical_liveness(func);
        let block_live_out = &liveness.live_out[block_idx];
        let block_insts: Vec<InstId> = func.blocks[block_idx].insts.clone();
        coalesce_block(func, &block_insts, block_live_out, &mut result, cfg);
    }

    // Remove NOP'd instructions from block instruction lists.
    for block in &mut func.blocks {
        block.insts.retain(|inst_id| {
            let inst = &func.insts[inst_id.0 as usize];
            inst.opcode != NOP_OPCODE
        });
    }

    result
}

/// Process a single basic block for copy coalescing.
fn coalesce_block(
    func: &mut MachFunction,
    block_insts: &[InstId],
    block_live_out: &BTreeSet<PReg>,
    result: &mut PostRACoalesceResult,
    cfg: PostRACoalesceConfig,
) {
    // We process copies in forward order. When a copy is coalesced by
    // renaming, we update subsequent instructions in the block immediately.
    // This means later copies in the same block see the already-renamed
    // operands, enabling chained coalescing.

    for (pos, &inst_id) in block_insts.iter().enumerate() {
        let inst = &func.insts[inst_id.0 as usize];

        // Case 0: the narrow-return zero-extension `UXTW Xd, Ws` — encoded as
        // `mov wd, ws`. It is not a copy opcode, so it is handled first and on
        // its own terms (see `try_narrow_zext_collapse`).
        if cfg.subreg_copies
            && inst.opcode == trust_cg_ir::inst::AArch64Opcode::Uxtw as u16
            && !inst.flags.is_call_arg_setup()
            && let Some((ext_dst, ext_src)) = narrow_zext_operands(inst)
        {
            let prior_insts = &block_insts[..pos];
            let remaining_insts = &block_insts[pos + 1..];
            if try_narrow_zext_collapse(
                func,
                prior_insts,
                remaining_insts,
                block_live_out,
                ext_dst,
                ext_src,
                cfg,
            ) {
                nop_inst(&mut func.insts[inst_id.0 as usize]);
                result.copies_removed += 1;
                result.rename_coalesced += 1;
            }
            continue;
        }

        // Process copy pseudo-instructions and already-selected AArch64
        // register moves. Some ISel paths emit MovR directly before regalloc,
        // so waiting for copy lowering is too late to coalesce them.
        if !is_post_ra_copy_opcode(inst.opcode) {
            continue;
        }

        // Extract the physical register operands (`None` covers VReg copies —
        // shouldn't happen post-RA — and a NeonOrrV whose two sources differ,
        // which is a genuine OR, not a move).
        let Some((dst_preg, src_preg)) = post_ra_copy_operands(inst) else {
            continue;
        };

        // Call lowering's physical ABI setup copies form a logical parallel
        // assignment.  Their source identities are consumed by the AArch64
        // post-RA repair pass.  Renaming or deleting one here erases the only
        // exact distinction between a genuine argument source and a later
        // sequential spill/materialization move, so retain every marked copy
        // (including identities) until that repair has run.
        if inst.flags.is_call_arg_setup() {
            continue;
        }

        // Case 1: unmarked identity copies are removable. Exact call-argument
        // identities returned above via IS_CALL_ARG_SETUP.
        //
        // EXCEPT the 32-bit TRUNCATION IDIOM: the encoder pins `MOVWrr` to a
        // 32-bit `mov wd, wn` from the OPCODE, not from the operands' register
        // class ("Regalloc deliberately preserves MOVWrr over Gpr64 vregs as a
        // 32-bit truncation idiom" — `aarch64/encode.rs`). `MOVWrr Xr, Xr` is
        // therefore NOT a no-op: it zeroes bits 63:32 of `Xr`. Deleting it as
        // an identity would let the untruncated high half escape, so it goes
        // only when that high half is provably dead.
        if dst_preg == src_preg {
            if trust_cg_ir::regs::preg_class(dst_preg) == trust_cg_ir::regs::RegClass::Gpr64
                && inst.opcode == trust_cg_ir::inst::AArch64Opcode::MOVWrr as u16
                && !gpr64_high_half_dead(func, &block_insts[pos + 1..], block_live_out, dst_preg)
            {
                continue;
            }
            nop_inst(&mut func.insts[inst_id.0 as usize]);
            result.copies_removed += 1;
            result.identity_copies += 1;
            continue;
        }

        // Case 1b: the CROSS-WIDTH GPR self-copy. A formal-argument
        // materialization arrives as `Copy Wr <- Xr` — the destination is the
        // GPR32 encoding, the source the GPR64 encoding of the SAME hardware
        // register (the incoming argument preg), because the ABI source operand
        // is a fixed 64-bit preg while the value's vreg is GPR32. `lower_copies`
        // takes the width from the DESTINATION class, so this emits
        // `mov wr, wr`. The plain identity test above misses it (the two
        // encodings are not equal) and `can_coalesce_copy_registers` refuses it
        // outright (the classes differ), so on this path it survived to the
        // final object — one dead `mov` at the head of every function taking a
        // narrow integer parameter.
        if cfg.subreg_copies
            && let Some(same_reg_wide) = cross_width_self_copy_source(dst_preg, src_preg)
        {
            let remaining_insts = &block_insts[pos + 1..];
            if gpr64_high_half_dead(func, remaining_insts, block_live_out, same_reg_wide) {
                nop_inst(&mut func.insts[inst_id.0 as usize]);
                result.copies_removed += 1;
                result.identity_copies += 1;
            }
            continue;
        }

        if !can_coalesce_copy_registers(dst_preg, src_preg) {
            continue;
        }

        // Case 2: Try rename coalescing.
        let remaining_insts = &block_insts[pos + 1..];
        if try_rename_coalesce(func, remaining_insts, block_live_out, dst_preg, src_preg) {
            nop_inst(&mut func.insts[inst_id.0 as usize]);
            result.copies_removed += 1;
            result.rename_coalesced += 1;
            continue;
        }

        // Case 3: Try retargeting a same-block source def to the copy
        // destination. This removes loop-carried commit copies such as
        // `mul xtmp, ...; copy xacc <- xtmp` when the old destination value is
        // no longer read before the copy.
        let prior_insts = &block_insts[..pos];
        if try_backward_def_coalesce(
            func,
            prior_insts,
            remaining_insts,
            block_live_out,
            dst_preg,
            src_preg,
            cfg,
        ) {
            nop_inst(&mut func.insts[inst_id.0 as usize]);
            result.copies_removed += 1;
            result.rename_coalesced += 1;
        }
    }
}

/// Attempt rename coalescing: rename all uses of `dst` to `src` in the
/// remaining instructions of the block, then delete the copy.
///
/// Returns true if coalescing was successful and the copy can be removed.
fn try_rename_coalesce(
    func: &mut MachFunction,
    remaining_insts: &[InstId],
    block_live_out: &BTreeSet<PReg>,
    dst: PReg,
    src: PReg,
) -> bool {
    // Phase 1: Validate — scan forward to check safety.
    //
    // We need to verify:
    // (a) `src` is not redefined before the last use of `dst`
    // (b) No instruction between the copy and the last use of `dst`
    //     implicitly clobbers `src`
    // (c) `dst` is not used in an implicit_uses list of any instruction
    //     that also implicitly uses/defines `src` (would break semantics)
    // (d) We don't cross calls or returns (conservative)

    let mut last_dst_use_pos: Option<usize> = None;
    let mut src_redef_pos: Option<usize> = None;
    let mut dst_redef_pos: Option<usize> = None;
    // Position of the first call that stopped the forward scan, if any. The
    // scan does not rename across a call, so uses of `dst` AFTER the call are
    // never visited; removing the copy is only safe if `dst` is dead from the
    // call onward (checked below).
    let mut call_barrier: Option<usize> = None;

    for (i, &inst_id) in remaining_insts.iter().enumerate() {
        let inst = &func.insts[inst_id.0 as usize];

        // Check for terminator/call — stop scanning.
        // We could rename through non-call instructions, but calls are
        // conservative barriers because of implicit clobbers.
        if inst.flags.is_call() {
            // We never rename uses of `dst` across a call. Record the barrier
            // so the post-loop check can verify `dst` is not live across it.
            call_barrier = Some(i);
            break;
        }

        // An instruction that BOTH reads and writes `dst` (a DefUse / tied
        // operand — e.g. an LSE `CAS`'s Rs register, which holds the expected
        // value on input and the loaded value on output) makes this copy
        // load-bearing: the read consumes the copied value. It is also
        // un-renameable, because renaming that operand to `src` would make the
        // instruction's WRITE clobber `src` too. The def/use bookkeeping below
        // records the def before the use, so a naive scan would treat the read
        // as reading the post-write value and drop the copy as dead — the exact
        // miscompile this guards (silently dropping `mov Rs, expected` before a
        // `CAS`). Bail out conservatively and keep the copy.
        if defines_preg_or_alias(inst, dst) && uses_preg(inst, dst) {
            return false;
        }

        // Track definitions of src and dst, including narrower aliases such as
        // W0 redefining the value observed through X0.
        if defines_preg_or_alias(inst, src) && src_redef_pos.is_none() {
            src_redef_pos = Some(i);
        }
        if defines_preg_or_alias(inst, dst) && dst_redef_pos.is_none() {
            dst_redef_pos = Some(i);
        }

        // Track uses of dst (explicit and implicit).
        if inst
            .implicit_uses
            .iter()
            .any(|&preg| pregs_overlap(preg, dst))
        {
            return false;
        }

        if uses_preg(inst, dst) {
            // If src has already been redefined, renaming this use of dst
            // to src would produce wrong results.
            if src_redef_pos.is_some() {
                return false;
            }

            // If dst has already been redefined, this use reads the NEW
            // value of dst (not our copy's dst), so we must not rename it.
            if dst_redef_pos.is_some() {
                break;
            }

            last_dst_use_pos = Some(i);
        }

        // If dst has been redefined and we've seen all its uses up to
        // the redefinition, we can stop scanning.
        if let Some(redef) = dst_redef_pos
            && i >= redef
        {
            break;
        }
    }

    // If dst is never used after the copy, we can trivially remove it.
    // (Dead copy elimination.)
    if last_dst_use_pos.is_none() {
        // dst is dead after the copy. But only remove if dst is also
        // not live-out of the block (conservative: if dst is redefined
        // before end, it's safe; if not, dst might be live-out).
        if let Some(redef) = dst_redef_pos {
            // `dst_redef_pos` was found via `defines_preg_or_alias`, which is
            // overlap-based: a NARROWER-alias write (e.g. `mov w0, #imm`, which
            // only writes the low 32 bits of `x0`) counts as "redefining" `x0`.
            // A narrow write does NOT kill the full-width value: a later wide
            // consumer — notably a call that reads `x0` as an argument via
            // implicit_uses — still observes the value delivered by this copy.
            // Treating a narrow-alias write as a full kill and deleting the copy
            // drops a value that is live across the call: the classic
            // value-live-across-a-call miscompile (a misaligned callout pointer
            // / dropped loop-carried call argument).
            //
            // Only take the dead-copy shortcut when the redefinition EXACTLY
            // (full-width) redefines `dst`. Then every later read of `dst`
            // observes the new value, so the copy's value is genuinely dead and
            // the copy can be removed. For a partial/narrow redef, keep the copy.
            let redef_inst = &func.insts[remaining_insts[redef].0 as usize];
            if defines_preg(redef_inst, dst) {
                // A full-width redef kills `dst` for EXPLICIT readers, but a
                // later call can still read `dst` as an ABI argument via
                // `implicit_uses` (the schedule inserts save/restore copies
                // around the scratch register-reuse AFTER coalescing, assuming
                // this copy still defines `dst`). Deleting the copy then drops a
                // value live across the call — the misaligned-callout-pointer
                // SIGABRT on indirect-call loops. Keep the copy when any later
                // instruction is a call that reads `dst`. Conservative: this
                // only ever PRESERVES a copy, never miscompiles. (The no-call
                // dead-copy case — `test_dead_copy_with_redef` — still removes,
                // since `call_reads_dst` is false there.)
                let call_reads_dst = remaining_insts[redef + 1..].iter().any(|&iid| {
                    let inst = &func.insts[iid.0 as usize];
                    inst.flags.is_call() && uses_preg_or_alias(inst, dst)
                });
                if call_reads_dst {
                    return false;
                }
                return true;
            }
            return false;
        }
        // dst might be live-out — don't remove without global liveness info.
        // For safety, skip this case.
        return false;
    }

    // last_dst_use_pos is guaranteed Some here (None case returns early above).
    let Some(last_use) = last_dst_use_pos else {
        return false;
    };

    // src must not be redefined before the last use of dst.
    if let Some(src_redef) = src_redef_pos
        && src_redef <= last_use
    {
        return false;
    }

    // The forward scan stops at the first call without visiting later
    // instructions. If `dst` is not redefined before that call, any use of
    // `dst` AFTER the call was neither seen nor renamed, so removing the copy
    // would leave that use reading an undefined register (the classic
    // value-live-across-a-call miscompile). Only remove the copy when `dst` is
    // dead from the call onward: no post-call use before a redefinition, and
    // not live-out (the live-out case is handled separately below).
    if let Some(call_pos) = call_barrier
        && dst_redef_pos.is_none_or(|redef| redef > call_pos)
    {
        for &inst_id in &remaining_insts[call_pos..] {
            let inst = &func.insts[inst_id.0 as usize];
            if uses_preg_or_alias(inst, dst) {
                return false;
            }
            if defines_preg_or_alias(inst, dst) {
                break;
            }
        }
    }

    // Renaming same-block uses is not enough when the copy destination is
    // live-out on a successor edge. In that case the copy is also a commit of
    // the edge value, so deleting it would leave successors seeing the old
    // physical register value even if the local condition/test was rewritten.
    if dst_redef_pos.is_none()
        && block_live_out
            .iter()
            .any(|&live_preg| pregs_overlap(live_preg, dst))
    {
        return false;
    }

    // Check that no instruction in [0..=last_use] has an implicit def/use
    // conflict. Specifically, if an instruction implicitly defines `src`,
    // we can't rename dst->src in uses after that point.
    for (i, &inst_id) in remaining_insts[..=last_use].iter().enumerate() {
        let inst = &func.insts[inst_id.0 as usize];

        // If src is implicitly defined by this instruction, and we have
        // uses of dst after this point, renaming would be incorrect.
        if inst
            .implicit_defs
            .iter()
            .any(|&preg| pregs_overlap(preg, src))
            && i < last_use
        {
            return false;
        }

        // If this instruction implicitly uses src AND we're about to rename
        // a use of dst to src in the same instruction, verify it's safe.
        // (Two explicit uses of the same register is fine on AArch64.)
    }

    // Phase 2: Apply — rename all uses of dst to src in [0..=last_use].
    for &inst_id in &remaining_insts[..=last_use] {
        let inst = &mut func.insts[inst_id.0 as usize];
        rename_preg_uses(inst, dst, src);
    }

    true
}

/// Attempt copy coalescing by retargeting the reaching source definition to
/// write the copy destination directly.
///
/// This is deliberately narrower than a full post-RA liveness rewrite. It only
/// handles same-block, single-def AArch64 integer computations that can safely
/// write a register also used as an input (for example `add xN, xN, xM`), and
/// only when the copied source physical register is proven dead after the copy.
fn try_backward_def_coalesce(
    func: &mut MachFunction,
    prior_insts: &[InstId],
    remaining_insts: &[InstId],
    block_live_out: &BTreeSet<PReg>,
    dst: PReg,
    src: PReg,
    cfg: PostRACoalesceConfig,
) -> bool {
    if preg_live_after_copy(func, remaining_insts, block_live_out, src) {
        return false;
    }

    for &inst_id in prior_insts.iter().rev() {
        let inst = &func.insts[inst_id.0 as usize];

        if inst.opcode == NOP_OPCODE {
            continue;
        }

        if defines_preg(inst, src) {
            if !can_retarget_source_def(inst, src, dst, cfg) {
                return false;
            }

            let inst = &mut func.insts[inst_id.0 as usize];
            for operand in &mut inst.defs {
                if let MachOperand::PReg(preg) = operand
                    && *preg == src
                {
                    *preg = dst;
                }
            }
            return true;
        }

        // Between the source def and the copy, the source must be used only by
        // the copy, and the old destination value must not be read after the
        // retargeted def would clobber it.
        //
        // `defines_preg_or_alias(inst, src)` is checked too — and it is NOT
        // subsumed by the exact `defines_preg` test above. A NARROW-alias write
        // (`mov w5, ...` when `src` is `x5`) is not an exact def of `src`, yet
        // on AArch64 it fully redefines the 64-bit register (a W write zeroes
        // the top half; an S/D write zeroes the rest of the V register). Walking
        // PAST such a write to retarget an OLDER exact def would delete the copy
        // while the value it actually transferred came from the narrow write —
        // the copy destination would then receive the stale older value.
        if uses_preg_or_alias(inst, src)
            || defines_preg_or_alias(inst, src)
            || uses_preg_or_alias(inst, dst)
            || defines_preg_or_alias(inst, dst)
        {
            return false;
        }

        if inst.flags.is_call() {
            return false;
        }
    }

    false
}

/// Recognize a CROSS-WIDTH GPR self-copy: `dst` is the GPR32 encoding and
/// `src` the GPR64 encoding of the SAME hardware register. Returns the GPR64
/// encoding when so.
///
/// `lower_copies` derives the move width from the DESTINATION class, so this
/// shape emits `mov wr, wr` — an identity on the low 32 bits that also ZEROES
/// bits 63:32 of `Xr`. It is therefore not unconditionally removable; see
/// [`gpr64_high_half_dead`].
///
/// The mirrored shape (`dst` GPR64, `src` GPR32 of the same register) is NOT
/// recognized: it would emit a 64-bit `mov xr, xr`, whose source read includes
/// the high half the allocator believes holds only a 32-bit value. Nothing is
/// known to emit it; fail closed.
fn cross_width_self_copy_source(dst: PReg, src: PReg) -> Option<PReg> {
    use trust_cg_ir::regs::RegClass;
    if trust_cg_ir::regs::preg_class(dst) != RegClass::Gpr32
        || trust_cg_ir::regs::preg_class(src) != RegClass::Gpr64
    {
        return None;
    }
    (trust_cg_ir::regs::gpr64_to_gpr32(src) == Some(dst)).then_some(src)
}

/// Explicit operands of a narrow-return zero extension `UXTW Xd, Ws`, as
/// `(Xd, Ws)`, when the instruction has exactly the pure two-register shape
/// this pass reasons about.
fn narrow_zext_operands(inst: &MachInst) -> Option<(PReg, PReg)> {
    use trust_cg_ir::regs::RegClass;
    if !inst.implicit_defs.is_empty() || !inst.implicit_uses.is_empty() {
        return None;
    }
    if inst.defs.len() != 1 || inst.uses.len() != 1 {
        return None;
    }
    let dst = inst.defs.first().and_then(MachOperand::as_preg)?;
    let src = inst.uses.first().and_then(MachOperand::as_preg)?;
    if trust_cg_ir::regs::preg_class(dst) != RegClass::Gpr64
        || trust_cg_ir::regs::preg_class(src) != RegClass::Gpr32
    {
        return None;
    }
    Some((dst, src))
}

/// Are bits 63:32 of the GPR64 register `wide_preg` dead from this point on?
///
/// Answers the ONE question that makes a `mov wr, wr` removable: the move is an
/// identity on the low half, so the only state it establishes is the zeroed
/// high half. Scanning forward through the rest of the block:
///
/// * a read of the EXACT GPR64 encoding (explicit or implicit — a call's
///   argument register, a `ret`'s returned value) observes the high half, so
///   the zeroing is live: answer `false`;
/// * a write to ANY alias re-establishes the register's contents (every
///   AArch64 32-bit register write zeroes bits 63:32, and a 64-bit write
///   replaces them outright), so the zeroing is dead from there: answer `true`;
/// * reads of the GPR32 view are irrelevant — they cannot observe bits 63:32.
///
/// Falling off the end of the block, the GPR64 encoding must not be live-out.
/// Physical liveness records the exact encoding each instruction names, so a
/// live-out set holding only the GPR32 view proves the high half dead.
fn gpr64_high_half_dead(
    func: &MachFunction,
    remaining_insts: &[InstId],
    block_live_out: &BTreeSet<PReg>,
    wide_preg: PReg,
) -> bool {
    for &inst_id in remaining_insts {
        let inst = &func.insts[inst_id.0 as usize];

        if inst
            .uses
            .iter()
            .filter_map(MachOperand::as_preg)
            .any(|p| p == wide_preg)
            || inst.implicit_uses.contains(&wide_preg)
        {
            return false;
        }

        if defines_preg_or_alias(inst, wide_preg) {
            return true;
        }
    }

    !block_live_out.contains(&wide_preg)
}

/// Does a GPR32 destination operand on this opcode provably encode a 32-BIT
/// register write — the write that zeroes bits 63:32 of the enclosing X
/// register?
///
/// **This is NOT implied by the destination's register class.** The AArch64
/// encoder derives the `sf` width bit from the destination operand for the
/// integer data-processing forms, but several opcodes hardcode it:
/// `FcvtzsRR`/`FcvtzuRR`/`ScvtfRR`/`UcvtfRR` always emit the 64-bit form
/// (`fcvtzu x1, d0`) even when the machine IR gives them a GPR32 destination —
/// the backend's deliberate "always-64-bit convert, then truncate"
/// characterization, pinned by
/// `trust-cg-codegen/tests/e2e_fp_to_int_saturation.rs::narrow_width_register_model`.
/// Folding a following truncation into such a producer DELETES the truncation
/// and lets the full 64-bit conversion result escape.
///
/// Membership is therefore audited directly against the encoder: every opcode
/// below takes its width from `sf_from_operand(inst, 0)` (the destination), or
/// is width-pinned to 32 bits by the opcode itself (`MOVWrr`). Deliberately
/// absent, each for a concrete reason:
///
/// * `FcvtzsRR`, `FcvtzuRR`, `ScvtfRR`, `UcvtfRR` — hardcoded `sf = 1`.
/// * `Smull`, `Umull`, `Umulh`, `Smulh` — architecturally 64-bit destinations.
/// * `Sxtw`, `Uxtw`, `Sxtb`, `Sxth`, `Uxtb`, `Uxth` — width comes from the
///   opcode's own bitfield template, not the destination operand.
/// * `FmovGprFpr`, `FmovFprGpr` — cross-bank moves whose width is tied to the
///   FP operand size as well as the GPR class.
/// * `MOVXrr` — width-pinned to 64 bits by the opcode.
fn writes_narrow_view_zero_extended(opcode: u16) -> bool {
    use trust_cg_ir::inst::AArch64Opcode;
    const ZEXT_SAFE_NARROW_PRODUCERS: &[AArch64Opcode] = {
        use AArch64Opcode::*;
        &[
            AddRR,
            AddRI,
            SubRR,
            SubRI,
            MulRR,
            Madd,
            Msub,
            SDiv,
            UDiv,
            Neg,
            AndRR,
            AndRI,
            OrrRR,
            OrrRI,
            EorRR,
            EorRI,
            OrnRR,
            BicRR,
            AddRRShift,
            SubRRShift,
            AddRRShiftLsr,
            EorRRShift,
            EorRRLsl,
            EorRRLsr,
            LslRR,
            LsrRR,
            AsrRR,
            LslRI,
            LsrRI,
            AsrRI,
            RorRI,
            Rbit,
            Ubfm,
            Sbfm,
            Csel,
            Csinc,
            Csinv,
            Csneg,
            CSet,
            MovR,
            MovI,
            Movz,
            Movn,
            MOVZWi,
            MOVWrr,
        ]
    };
    ZEXT_SAFE_NARROW_PRODUCERS
        .iter()
        .any(|&candidate| candidate as u16 == opcode)
}

/// Collapse a narrow-return zero extension `UXTW Xd, Ws` into its producer.
///
/// `UXTW Xd, Ws` is `Xd = zext32(Ws)`, encoded as `mov wd, ws`. It is what the
/// AArch64 return path emits to widen a 32-bit result into the 64-bit return
/// register — the second half of the redundant-move pair
/// `add w1, w0, #1 ; mov w0, w1` where clang emits `add w0, w0, #1` alone.
///
/// When `Ws` is produced in this block by a retargetable instruction and is
/// otherwise unused, redirecting that producer to write `Wd` and deleting the
/// extension is exact: the producer's def operand is `Ws`, a GPR32 register, so
/// the retargeted instruction is a 32-bit register write, and EVERY AArch64
/// 32-bit register write zeroes bits 63:32 of the enclosing X register. `Xd`
/// therefore ends up holding `zext32(value)` — bit for bit what the extension
/// produced — one instruction earlier.
///
/// The window conditions mirror [`try_backward_def_coalesce`], with the
/// extension's 64-bit destination `Xd` used for the alias-aware `dst` checks so
/// both register views are covered.
#[allow(clippy::too_many_arguments)]
fn try_narrow_zext_collapse(
    func: &mut MachFunction,
    prior_insts: &[InstId],
    remaining_insts: &[InstId],
    block_live_out: &BTreeSet<PReg>,
    ext_dst: PReg,
    ext_src: PReg,
    cfg: PostRACoalesceConfig,
) -> bool {
    let Some(narrow_dst) = trust_cg_ir::regs::gpr64_to_gpr32(ext_dst) else {
        return false;
    };

    // The `narrow_dst == ext_src` shape (`uxtw xr, wr`) is a different proof —
    // nothing is retargeted, the extension is simply redundant when the
    // reaching def already wrote the GPR32 view. Not handled here; fail closed.
    if narrow_dst == ext_src {
        return false;
    }

    // The extended value must be consumed only by this extension.
    if preg_live_after_copy(func, remaining_insts, block_live_out, ext_src) {
        return false;
    }

    for &inst_id in prior_insts.iter().rev() {
        let inst = &func.insts[inst_id.0 as usize];

        if inst.opcode == NOP_OPCODE {
            continue;
        }

        if defines_preg(inst, ext_src) {
            if !can_retarget_source_def(inst, ext_src, narrow_dst, cfg)
                || !writes_narrow_view_zero_extended(inst.opcode)
            {
                return false;
            }

            let inst = &mut func.insts[inst_id.0 as usize];
            for operand in &mut inst.defs {
                if let MachOperand::PReg(preg) = operand
                    && *preg == ext_src
                {
                    *preg = narrow_dst;
                }
            }
            return true;
        }

        if uses_preg_or_alias(inst, ext_src)
            || defines_preg_or_alias(inst, ext_src)
            || uses_preg_or_alias(inst, ext_dst)
            || defines_preg_or_alias(inst, ext_dst)
        {
            return false;
        }

        if inst.flags.is_call() {
            return false;
        }
    }

    false
}

fn preg_live_after_copy(
    func: &MachFunction,
    remaining_insts: &[InstId],
    block_live_out: &BTreeSet<PReg>,
    preg: PReg,
) -> bool {
    for &inst_id in remaining_insts {
        let inst = &func.insts[inst_id.0 as usize];

        if uses_preg_or_alias(inst, preg) {
            return true;
        }

        if defines_preg_or_alias(inst, preg) {
            return false;
        }
    }

    block_live_out
        .iter()
        .any(|&live_preg| pregs_overlap(live_preg, preg))
}

fn can_coalesce_copy_registers(dst: PReg, src: PReg) -> bool {
    let dst_class = trust_cg_ir::regs::preg_class(dst);
    let src_class = trust_cg_ir::regs::preg_class(src);
    dst_class == src_class && dst_class != trust_cg_ir::regs::RegClass::System
}

#[derive(Debug, Clone, Default)]
struct PhysicalLiveness {
    live_out: Vec<BTreeSet<PReg>>,
}

fn compute_physical_liveness(func: &MachFunction) -> PhysicalLiveness {
    let num_blocks = func.blocks.len();
    let mut live_in: Vec<BTreeSet<PReg>> = vec![BTreeSet::new(); num_blocks];
    let mut live_out: Vec<BTreeSet<PReg>> = vec![BTreeSet::new(); num_blocks];
    let block_order: Vec<_> = if func.block_order.is_empty() {
        (0..num_blocks)
            .map(|block_idx| crate::machine_types::BlockId(block_idx as u32))
            .collect()
    } else {
        func.block_order.clone()
    };

    let max_iterations = num_blocks * 2 + 10;
    for _ in 0..max_iterations {
        let mut changed = false;

        for &block_id in block_order.iter().rev() {
            let block_idx = block_id.0 as usize;
            let block = &func.blocks[block_idx];

            let mut new_live_out = BTreeSet::new();
            for &succ_id in &block.succs {
                let succ_idx = succ_id.0 as usize;
                if let Some(succ_live_in) = live_in.get(succ_idx) {
                    new_live_out.extend(succ_live_in.iter().copied());
                }
            }

            let mut new_live_in = new_live_out.clone();
            for &inst_id in block.insts.iter().rev() {
                let inst = &func.insts[inst_id.0 as usize];
                remove_physical_defs(&mut new_live_in, inst);
                add_physical_uses(&mut new_live_in, inst);
            }

            if new_live_in != live_in[block_idx] || new_live_out != live_out[block_idx] {
                changed = true;
                live_in[block_idx] = new_live_in;
                live_out[block_idx] = new_live_out;
            }
        }

        if !changed {
            break;
        }
    }

    PhysicalLiveness { live_out }
}

fn add_physical_uses(live: &mut BTreeSet<PReg>, inst: &MachInst) {
    for op in &inst.uses {
        if let MachOperand::PReg(preg) = op {
            live.insert(*preg);
        }
    }
    live.extend(inst.implicit_uses.iter().copied());
}

fn remove_physical_defs(live: &mut BTreeSet<PReg>, inst: &MachInst) {
    for op in &inst.defs {
        if let MachOperand::PReg(preg) = op {
            remove_overlapping_pregs(live, *preg);
        }
    }
    for &preg in &inst.implicit_defs {
        remove_overlapping_pregs(live, preg);
    }
}

fn remove_overlapping_pregs(live: &mut BTreeSet<PReg>, preg: PReg) {
    live.retain(|&live_preg| !pregs_overlap(live_preg, preg));
}

// ---------------------------------------------------------------------------
// Cached liveness for the fast path
//
// The fast path computes the SAME fixpoint as `compute_physical_liveness`,
// but:
//   - register sets are fixed-width bitsets (`PRegSet`) instead of
//     `BTreeSet<PReg>`,
//   - each block's instruction walk is pre-summarized into a (GEN, KILL)
//     transfer function, rebuilt only for blocks the pass mutated, and
//   - the fixpoint is recomputed only when a mutation occurred since the last
//     computation (see `post_ra_coalesce` doc comment for the staleness
//     argument).
//
// ## Transfer-function equality lemma
//
// `compute_physical_liveness` walks a block's instructions backward applying
// per-instruction `f_i(S) = (S \ ovl(D_i)) ∪ U_i`, where `ovl(D_i)` is the
// set of registers overlapping any def (explicit PReg operands + implicit
// defs) of instruction `i`, and `U_i` is the exact set of used registers
// (explicit PReg operands + implicit uses). Composing over the block's
// instructions i_1..i_k in program order (i_1 first):
//
//     live_in = f_{i_1}(f_{i_2}(... f_{i_k}(live_out)))
//
// By induction on k:
//
//     F(S) = GEN ∪ (S \ KILL)
//     KILL = ∪_j ovl(D_j)
//     GEN  = ∪_j (U_j \ ∪_{l<j} ovl(D_l))
//
// Base k=1: f_{i_1}(S) = (S \ ovl(D_1)) ∪ U_1 — matches with GEN = U_1,
// KILL = ovl(D_1). Step: F_k(S) = F_{k-1}(f_{i_k}(S))
//   = GEN_{k-1} ∪ (((S \ ovl(D_k)) ∪ U_k) \ KILL_{k-1})
//   = GEN_{k-1} ∪ (U_k \ KILL_{k-1}) ∪ (S \ (KILL_{k-1} ∪ ovl(D_k))).
// So GEN/KILL are computable in one FORWARD walk: for each instruction,
// `GEN |= U_j \ KILL_so_far` first (an instruction's own defs do not mask its
// own uses, mirroring remove-defs-then-add-uses in the backward walk), then
// `KILL_so_far |= ovl(D_j)`. `block_summary` implements exactly this.
//
// The fixpoint driver (`recompute`) replicates `compute_physical_liveness`'s
// sweep schedule verbatim: same block order (`block_order`, reversed; or
// `0..n` when empty), same `live_in.get(succ)` out-of-range tolerance, same
// per-block changed test on (live_in, live_out), same global iteration cap
// `num_blocks * 2 + 10`. With extensionally equal per-block transfers and an
// identical schedule, every sweep produces set-for-set equal states, so the
// final result is equal whether the loop converges or hits the cap.
// ---------------------------------------------------------------------------

/// Number of 64-bit words in a `PRegSet`. 640 bits covers every current
/// allocator PReg encoding (AArch64 uses 0..=228, x86-64 uses 512..=559)
/// with headroom; encodings outside the range divert the whole pass to the
/// reference implementation (`function_has_out_of_range_preg`).
const PREG_SET_WORDS: usize = 10;
const PREG_SET_BITS: u16 = (PREG_SET_WORDS * 64) as u16;

/// Fixed-width bitset over PReg encodings.
#[derive(Clone, Copy, PartialEq, Eq)]
struct PRegSet([u64; PREG_SET_WORDS]);

impl PRegSet {
    const EMPTY: PRegSet = PRegSet([0; PREG_SET_WORDS]);

    #[inline]
    fn insert(&mut self, preg: PReg) {
        let e = preg.encoding() as usize;
        debug_assert!(e < PREG_SET_WORDS * 64);
        self.0[e / 64] |= 1u64 << (e % 64);
    }

    #[inline]
    fn union_with(&mut self, other: &PRegSet) {
        for (w, o) in self.0.iter_mut().zip(other.0.iter()) {
            *w |= o;
        }
    }

    #[inline]
    fn subtract(&mut self, other: &PRegSet) {
        for (w, o) in self.0.iter_mut().zip(other.0.iter()) {
            *w &= !o;
        }
    }

    /// Materialize the exact member set for handing to `coalesce_block`,
    /// which expects the same `BTreeSet<PReg>` shape the reference produces.
    fn to_btree_set(self) -> BTreeSet<PReg> {
        let mut set = BTreeSet::new();
        for (word_idx, &word) in self.0.iter().enumerate() {
            let mut bits = word;
            while bits != 0 {
                let bit = bits.trailing_zeros() as usize;
                set.insert(PReg::new((word_idx * 64 + bit) as u16));
                bits &= bits - 1;
            }
        }
        set
    }
}

/// `overlap_masks()[q]` = the set of all encodings `m` with
/// `pregs_overlap(PReg(m), PReg(q))` — the exact orientation used by both
/// `remove_overlapping_pregs` (kill side) and the `live_out` overlap queries.
/// Built once per process directly from `allocator_pregs_overlap`, so it is
/// correct by construction for every target the allocator models.
fn overlap_masks() -> &'static [PRegSet] {
    use std::sync::OnceLock;
    static MASKS: OnceLock<Vec<PRegSet>> = OnceLock::new();
    MASKS.get_or_init(|| {
        let mut masks = vec![PRegSet::EMPTY; PREG_SET_BITS as usize];
        for (q, mask) in masks.iter_mut().enumerate() {
            let q_reg = PReg::new(q as u16);
            for m in 0..PREG_SET_BITS {
                let m_reg = PReg::new(m);
                if pregs_overlap(m_reg, q_reg) {
                    mask.insert(m_reg);
                }
            }
        }
        masks
    })
}

/// True if any physical register mentioned by the function does not fit the
/// fixed-width bitset. Such functions use the reference path.
fn function_has_out_of_range_preg(func: &MachFunction) -> bool {
    func.insts.iter().any(|inst| {
        inst.defs
            .iter()
            .chain(inst.uses.iter())
            .filter_map(MachOperand::as_preg)
            .chain(inst.implicit_defs.iter().copied())
            .chain(inst.implicit_uses.iter().copied())
            .any(|preg| preg.encoding() >= PREG_SET_BITS)
    })
}

/// Per-block liveness transfer function: `live_in = gen ∪ (live_out \ kill)`.
/// Extensionally equal to the backward instruction walk in
/// `compute_physical_liveness` (see the lemma above).
#[derive(Clone, Copy)]
struct BlockSummary {
    gen_set: PRegSet,
    kill: PRegSet,
}

fn block_summary(func: &MachFunction, block_idx: usize, masks: &[PRegSet]) -> BlockSummary {
    let mut gen_set = PRegSet::EMPTY;
    let mut kill = PRegSet::EMPTY;
    // FORWARD walk; see the composition lemma. NOP'd instructions have empty
    // defs/uses/implicits and contribute nothing — identical to the reference
    // walking the same NOP'd instruction.
    for &inst_id in &func.blocks[block_idx].insts {
        let inst = &func.insts[inst_id.0 as usize];

        // Uses first: an instruction's own defs do not mask its own uses.
        let mut used = PRegSet::EMPTY;
        for op in &inst.uses {
            if let MachOperand::PReg(preg) = op {
                used.insert(*preg);
            }
        }
        for &preg in &inst.implicit_uses {
            used.insert(preg);
        }
        used.subtract(&kill);
        gen_set.union_with(&used);

        // Then defs (overlap-expanded) into KILL.
        for op in &inst.defs {
            if let MachOperand::PReg(preg) = op {
                kill.union_with(&masks[preg.encoding() as usize]);
            }
        }
        for &preg in &inst.implicit_defs {
            kill.union_with(&masks[preg.encoding() as usize]);
        }
    }
    BlockSummary { gen_set, kill }
}

/// Whole-function liveness cache with mutation-driven invalidation.
struct CachedLiveness {
    summaries: Vec<BlockSummary>,
    live_out: Vec<PRegSet>,
    /// Blocks whose contents changed since `summaries` was last built.
    /// `None` means everything (initial state).
    stale_blocks: Option<Vec<usize>>,
    /// False whenever a mutation occurred after the last fixpoint.
    valid: bool,
}

impl CachedLiveness {
    fn new(num_blocks: usize) -> Self {
        CachedLiveness {
            summaries: vec![
                BlockSummary {
                    gen_set: PRegSet::EMPTY,
                    kill: PRegSet::EMPTY,
                };
                num_blocks
            ],
            live_out: vec![PRegSet::EMPTY; num_blocks],
            stale_blocks: None,
            valid: false,
        }
    }

    fn note_block_mutated(&mut self, block_idx: usize) {
        if let Some(stale) = &mut self.stale_blocks {
            stale.push(block_idx);
        }
        self.valid = false;
    }

    /// The block-start `live_out` snapshot for `block_idx`: equal to
    /// `compute_physical_liveness(func).live_out[block_idx]` evaluated on the
    /// current (post-mutation) function, exactly as the reference does at the
    /// top of each block iteration.
    fn live_out_at_block_start(&mut self, func: &MachFunction, block_idx: usize) -> BTreeSet<PReg> {
        if !self.valid {
            self.recompute(func);
        }
        self.live_out[block_idx].to_btree_set()
    }

    fn recompute(&mut self, func: &MachFunction) {
        let masks = overlap_masks();

        // Rebuild summaries only for blocks whose contents changed.
        match self.stale_blocks.take() {
            None => {
                for block_idx in 0..func.blocks.len() {
                    self.summaries[block_idx] = block_summary(func, block_idx, masks);
                }
            }
            Some(stale) => {
                for block_idx in stale {
                    self.summaries[block_idx] = block_summary(func, block_idx, masks);
                }
            }
        }
        self.stale_blocks = Some(Vec::new());

        // Fixpoint: schedule replicated verbatim from
        // `compute_physical_liveness` (order, changed test, iteration cap).
        let num_blocks = func.blocks.len();
        let mut live_in: Vec<PRegSet> = vec![PRegSet::EMPTY; num_blocks];
        let mut live_out: Vec<PRegSet> = vec![PRegSet::EMPTY; num_blocks];
        let block_order: Vec<crate::machine_types::BlockId> = if func.block_order.is_empty() {
            (0..num_blocks)
                .map(|block_idx| crate::machine_types::BlockId(block_idx as u32))
                .collect()
        } else {
            func.block_order.clone()
        };

        let max_iterations = num_blocks * 2 + 10;
        for _ in 0..max_iterations {
            let mut changed = false;

            for &block_id in block_order.iter().rev() {
                let block_idx = block_id.0 as usize;
                let block = &func.blocks[block_idx];

                let mut new_live_out = PRegSet::EMPTY;
                for &succ_id in &block.succs {
                    let succ_idx = succ_id.0 as usize;
                    if let Some(succ_live_in) = live_in.get(succ_idx) {
                        new_live_out.union_with(succ_live_in);
                    }
                }

                let summary = &self.summaries[block_idx];
                let mut new_live_in = new_live_out;
                new_live_in.subtract(&summary.kill);
                new_live_in.union_with(&summary.gen_set);

                if new_live_in != live_in[block_idx] || new_live_out != live_out[block_idx] {
                    changed = true;
                    live_in[block_idx] = new_live_in;
                    live_out[block_idx] = new_live_out;
                }
            }

            if !changed {
                break;
            }
        }

        self.live_out = live_out;
        self.valid = true;
    }
}

/// Can the definition of `src` in `inst` be redirected to write `dst` instead?
///
/// ## The soundness argument this shares with every admitted opcode
///
/// Let `P` be this producer at position `q` and `C` the copy `dst <- src` at
/// position `p > q`, both in the same block. The caller
/// ([`try_backward_def_coalesce`]) has already proved:
///
/// * **(1) `src` is dead after `C`** — no read of `src` (or an alias) before it
///   is redefined in the rest of the block, and `src` is not live-out.
/// * **(2) the window `(q, p)` is clean** — no instruction strictly between `P`
///   and `C` reads `src`, reads `dst`, writes `src`, or writes `dst` (all
///   alias-aware), and none of them is a call.
///
/// This function adds:
///
/// * **(3) `P` writes exactly one register, exactly `src`, and nothing else** —
///   one explicit def operand equal to `src`, no implicit defs, no implicit
///   uses, not a call, and an opcode whose ONLY architectural effect is writing
///   operand 0 (no memory, no NZCV, no trap, no writeback, no tied
///   read-modify-write destination).
/// * **(4) `P` does not read `src`** — otherwise the retarget would drop an
///   input.
///
/// Given (1)-(4), rewriting `P`'s def from `src` to `dst` and deleting `C`
/// preserves the machine state at every program point:
///
/// * `P`'s inputs are untouched, so the value it computes is unchanged.
/// * `dst` receives that value at `q` instead of at `p`. By (2) nothing in
///   `(q, p)` reads `dst`, so no reader sees the difference; `dst`'s old value
///   was going to be overwritten by `C` at `p` regardless, so nothing observes
///   its loss. From `p` onward `dst` holds the same value as before.
/// * `src` keeps whatever it held before `q` instead of `P`'s result. By (2)
///   nothing in `(q, p)` reads `src`, and by (1) nothing reads it after `p`
///   before a redefinition, and it is not live-out — so no reader sees the
///   difference either.
/// * When `P` reads `dst` (`Madd t, x, y, dst`, `add t, dst, #k`), the retarget
///   makes it read and write `dst` in one instruction. Every admitted opcode is
///   a data-processing form whose sources are read before the destination is
///   written, and `Rd == Rn/Rm/Ra` is architecturally defined for all of them
///   (the UNPREDICTABLE `Rd == Rn` cases are load/store writeback and load-pair
///   forms, which fail (3) — they have two defs or a `DefUse` base).
///
/// Note what this argument does NOT depend on: whether the block sits on a
/// loop back edge, and whether `P`'s source registers happen to coincide with
/// `dst`. Those were the discriminators of the historical `AddRI`/`SubRI`
/// SELF-REFERENTIAL guard (kept intact under the kill switch, see below); the
/// cross-carrier "lost-copy" shape it refused — `t_a = b ± k; mov a, t_a` with
/// `b != a` — is covered by (2): the retargeted `add a, b, #k` still reads `b`
/// at `q`, before any later write to `b`, and writes only `a`. What genuinely
/// must stay refused is a producer that READS the copy destination through a
/// register the window analysis does not cover, which (4) and (2) between them
/// rule out.
fn can_retarget_source_def(
    inst: &MachInst,
    src: PReg,
    dst: PReg,
    cfg: PostRACoalesceConfig,
) -> bool {
    if inst.flags.is_call() || !inst.implicit_defs.is_empty() || !inst.implicit_uses.is_empty() {
        return false;
    }

    if inst.defs.len() != 1 || inst.defs.first().and_then(MachOperand::as_preg) != Some(src) {
        return false;
    }

    // Do not rewrite two-address/read-write forms that read the old source
    // register value as an input. This also catches every `DefUse` (tied)
    // operand, because the regalloc conversion puts a tied operand in BOTH the
    // `defs` and the `uses` list.
    if uses_preg(inst, src) {
        return false;
    }

    // Call lowering marks the physical ABI setup instructions that deliver
    // arguments; the AArch64 post-RA repair pass consumes their destination
    // identity. Retargeting one moves the argument to a different register
    // behind that pass's back, so leave every marked producer alone.
    if inst.flags.is_call_arg_setup() {
        return false;
    }

    // Fail-closed backstop for relocation/frame provenance. The regalloc view
    // BLINDS `Symbol` / `JumpTableIndex` / `IncomingArg` operands to `Imm(0)`
    // placeholders, and the IR rebuild re-associates each such instruction with
    // its original by matching operands EXACTLY on physical registers. Changing
    // a def preg on an opaque-operand carrier therefore breaks provenance
    // recovery (a hard `PipelineError`, e.g. an `AddRI vreg, FP,
    // IncomingArg(off)` stack-formal address). Regalloc cannot tell a blinded
    // placeholder from a genuine zero, so refuse every producer carrying an
    // `Imm(0)` — the tight sound proxy, and a superset of the historical
    // LoopLatchLayoutCombine `AddRI dst, src, #0` hardening barrier (a copy in
    // disguise that must never be coalesced).
    if has_blinded_opaque_operand(inst) {
        return false;
    }

    is_retargetable_opcode(inst, dst, cfg.wide_backdef)
}

/// True when an explicit operand is `Imm(0)` — the blinded form of every
/// regalloc-opaque operand (`Symbol`, `JumpTableIndex`, `IncomingArg`).
fn has_blinded_opaque_operand(inst: &MachInst) -> bool {
    inst.defs
        .iter()
        .chain(inst.uses.iter())
        .any(|operand| matches!(operand, MachOperand::Imm(0)))
}

/// Opcode admission for backward-def retargeting.
///
/// `wide == false` restores the historical narrow set exactly (kill switch
/// `TCG_NO_WIDE_BACKDEF_COALESCE`), so objects are byte-identical to the
/// pre-widening compiler.
fn is_retargetable_opcode(inst: &MachInst, dst: PReg, wide: bool) -> bool {
    use trust_cg_ir::inst::AArch64Opcode;

    let opcode = inst.opcode;

    // -- Historical narrow set -------------------------------------------
    //
    // Register-register forms: each writes exactly its destination register from
    // its source operands with no other effect. Madd/Msub (`Rd = Ra ± Rn*Rm`) are
    // the multiply-accumulate forms — the hot-loop reduction shape
    // (`acc = acc*k + i`), where eliminating the follow-on `mov acc, tmp` removes
    // a copy from the loop's carried-dependency critical path.
    if opcode == AArch64Opcode::AddRR as u16
        || opcode == AArch64Opcode::SubRR as u16
        || opcode == AArch64Opcode::MulRR as u16
        || opcode == AArch64Opcode::Madd as u16
        || opcode == AArch64Opcode::Msub as u16
        || opcode == AArch64Opcode::Rbit as u16
    {
        return true;
    }

    if !wide {
        // Add/Sub-immediate forms under the historical SELF-REFERENTIAL guard:
        // the producer's base source register must be exactly the copy
        // destination (`carrier_next = carrier ± k`), which is the
        // reduction-split loop-carrier shape. The non-zero immediate
        // requirement is subsumed by the `Imm(0)` backstop above but restated
        // here so the LoopLatchLayoutCombine hardening barrier is visible at
        // the decision site.
        //
        // Post-RA operand layout for these forms is
        // `defs=[dst_reg], uses=[base, imm]`.
        if opcode == AArch64Opcode::AddRI as u16 || opcode == AArch64Opcode::SubRI as u16 {
            let base_is_dst = inst.uses.first().and_then(MachOperand::as_preg) == Some(dst);
            let imm_nonzero = matches!(inst.uses.get(1), Some(MachOperand::Imm(v)) if *v != 0);
            return base_is_dst && imm_nonzero;
        }
        return false;
    }

    // -- Wide set ---------------------------------------------------------
    //
    // Every entry below is audited against the SAME four-part argument the six
    // historical opcodes rely on (see `can_retarget_source_def`). Admission
    // requires ALL of:
    //
    //   * `opcode_effect` is Pure — reads and writes no memory, is not a
    //     barrier, is not a call. (Loads are therefore excluded; see the
    //     DECLINED list.)
    //   * Not a flag writer and not a trap pseudo — so the instruction's only
    //     architectural effect is the operand-0 write. Flag READERS (`Csel`,
    //     `CSet`, `Adc`) are unaffected by a destination rename because the
    //     retarget neither moves the instruction nor touches NZCV; they are
    //     admitted or declined on other grounds.
    //   * Operand 0 is a plain `Def`, never a tied `DefUse`, and the
    //     instruction has exactly one def — no writeback base register, no
    //     second data register, no read-modify-write destination.
    //   * `Rd == Rn/Rm/Ra` is architecturally defined (true for every AArch64
    //     data-processing form; the UNPREDICTABLE cases are all writeback /
    //     load-pair shapes, excluded by the one-def rule).
    //
    // DECLINED, and why (fail closed — each would need its own proof):
    //   * `Bfm`, `Movk`, and the NEON accumulate forms (`NeonUdotV`,
    //     `NeonFmlaV`, `NeonInsGen`, ...): TIED destination — the prior value
    //     of `Rd` is an input that does not appear in the operand list.
    //   * All loads (`LdrRI`, `LdrRO`, `Ldp*`, `Ldar`, ...) and all stores:
    //     non-Pure memory effect. A plain load's destination retarget would in
    //     fact be sound, but the writeback (`LdrPreIndex`) and pair (`LdpRI`)
    //     members of the family carry a second def, and the common
    //     `ldr Rt, [Rn, #0]` shape is refused by the `Imm(0)` backstop anyway
    //     — so the family is left for a separate, separately-measured lever.
    //   * `AddsRR/AddsRI/SubsRR/SubsRI`, `CmpRR/CmpRI/Tst/Fcmp`: write NZCV.
    //   * `Adc`/`Sbc`: pure and single-def, but they consume the carry of a
    //     specific preceding flag setter as part of a multi-register i128
    //     sequence; the pairing is not modeled here, so they stay refused.
    //   * `Adrp`, `Adr`, `AddPCRel`, `AddRIShift12`, `AddTprelHi12/Lo12`,
    //     `LdrGot`, `LdrTlvp`, `LdrGottprel`: relocation- and TLS-sequence
    //     bearing (also caught by the `Imm(0)` backstop, but excluded by name
    //     so the intent survives any future operand-shape change).
    //   * NEON data-processing forms: sound by the same argument, but vector
    //     programs are not in the measured band and every entry would need its
    //     own tied/lane audit. Separate lever.
    //   * Trap pseudos and `Mrs`: side-effecting control flow / sysreg read.
    WIDE_RETARGETABLE_OPCODES
        .iter()
        .any(|&candidate| candidate as u16 == opcode)
}

/// Opcodes admitted by the wide backward-def allowlist. See
/// [`is_retargetable_opcode`] for the admission rule and the declined set.
const WIDE_RETARGETABLE_OPCODES: &[trust_cg_ir::inst::AArch64Opcode] = {
    use trust_cg_ir::inst::AArch64Opcode::*;
    &[
        // Integer arithmetic, immediate forms (`Rd = Rn ± imm12`). The
        // SELF-REFERENTIAL restriction is dropped here: see the
        // `can_retarget_source_def` proof for why `base == dst` is not a
        // soundness discriminator. The `#0` hardening barrier is preserved by
        // the `Imm(0)` backstop.
        AddRI,
        SubRI, // Integer arithmetic, register forms not already in the narrow set.
        Smull,
        Umull,
        Umulh,
        Smulh,
        SDiv,
        UDiv,
        Neg,
        // Logical, register and bitmask-immediate forms.
        AndRR,
        AndRI,
        OrrRR,
        OrrRI,
        EorRR,
        EorRI,
        OrnRR,
        BicRR,
        // Arithmetic / logical with one shifted source operand.
        AddRRShift,
        SubRRShift,
        AddRRShiftLsr,
        EorRRShift,
        EorRRLsl,
        EorRRLsr,
        // Shifts and rotates.
        LslRR,
        LsrRR,
        AsrRR,
        LslRI,
        LsrRI,
        AsrRI,
        RorRI,
        // Sign/zero extension and the NON-tied bitfield moves. `Bfm` is a
        // bitfield INSERT (tied destination) and is deliberately absent.
        Sxtw,
        Uxtw,
        Sxtb,
        Sxth,
        Uxtb,
        Uxth,
        Ubfm,
        Sbfm,
        // Conditional select / set. These READ NZCV, which a destination
        // rename cannot disturb (the instruction does not move), and write
        // only `Rd`.
        Csel,
        Csinc,
        Csinv,
        Csneg,
        CSet,
        FcselRR,
        // Register moves and constant materialization. `Movk` is a tied
        // insert and is deliberately absent — which also protects
        // `Movz`+`Movk` constant chains, since the backward scan stops at the
        // LAST def before the copy (the `Movk`) and refuses there.
        MovR,
        MOVWrr,
        MOVXrr,
        MovI,
        Movz,
        Movn,
        MOVZWi,
        MOVZXi,
        FmovImm,
        // Scalar floating-point arithmetic, conversion and bitcast. All are
        // single-def and pure; FP exception flags in FPSR are cumulative and
        // unaffected by which register receives the result.
        FaddRR,
        FsubRR,
        FmulRR,
        FdivRR,
        FmaddRR,
        FminnmRR,
        FmaxnmRR,
        FnegRR,
        FabsRR,
        FsqrtRR,
        FrintmRR,
        FrintpRR,
        FrintzRR,
        FcvtzsRR,
        FcvtzuRR,
        ScvtfRR,
        UcvtfRR,
        FcvtSD,
        FcvtDS,
        FcvtHS,
        FcvtHD,
        FcvtSH,
        FcvtDH,
        FmovGprFpr,
        FmovFprGpr,
        FmovFprFpr,
    ]
};

/// Opcodes `coalesce_block` can act on: the copy-like moves plus, when the
/// sub-register transforms are enabled, the narrow-return zero extension.
/// Blocks containing none of these are skipped without procuring liveness, so
/// this predicate must stay a superset of every mutating path.
fn is_coalesce_candidate_opcode(opcode: u16, cfg: PostRACoalesceConfig) -> bool {
    is_post_ra_copy_opcode(opcode)
        || (cfg.subreg_copies && opcode == trust_cg_ir::inst::AArch64Opcode::Uxtw as u16)
}

fn is_post_ra_copy_opcode(opcode: u16) -> bool {
    crate::phi_elim::is_copy_opcode(opcode)
        || opcode == trust_cg_ir::inst::AArch64Opcode::MovR as u16
        || opcode == trust_cg_ir::inst::AArch64Opcode::MOVWrr as u16
        || opcode == trust_cg_ir::inst::AArch64Opcode::MOVXrr as u16
        || opcode == trust_cg_ir::inst::AArch64Opcode::FmovFprFpr as u16
        || opcode == trust_cg_ir::inst::AArch64Opcode::NeonOrrV as u16
}

/// Extract the (dst, src) physical registers of a post-RA copy-like
/// instruction, or `None` if the instruction is not a plain register copy.
///
/// `NeonOrrV` (`orr vD.16b, vN.16b, vM.16b`) is a copy ONLY when both source
/// operands name the SAME register; a genuine bitwise-or of two different
/// registers is not a move and is skipped.
fn post_ra_copy_operands(inst: &MachInst) -> Option<(PReg, PReg)> {
    let dst = inst.defs.first().and_then(MachOperand::as_preg)?;
    let src = inst.uses.first().and_then(MachOperand::as_preg)?;
    if inst.opcode == trust_cg_ir::inst::AArch64Opcode::NeonOrrV as u16 {
        let src2 = inst.uses.get(1).and_then(MachOperand::as_preg)?;
        if src2 != src {
            return None;
        }
    }
    Some((dst, src))
}

/// Check if an instruction uses (reads) a physical register, either
/// explicitly or implicitly.
fn uses_preg(inst: &MachInst, preg: PReg) -> bool {
    // Check explicit uses.
    for op in &inst.uses {
        if let MachOperand::PReg(p) = op
            && *p == preg
        {
            return true;
        }
    }
    // Check implicit uses.
    inst.implicit_uses.contains(&preg)
}

/// Check if an instruction defines (writes) a physical register, either
/// explicitly or implicitly.
fn defines_preg(inst: &MachInst, preg: PReg) -> bool {
    // Check explicit defs.
    for op in &inst.defs {
        if let MachOperand::PReg(p) = op
            && *p == preg
        {
            return true;
        }
    }
    // Check implicit defs.
    inst.implicit_defs.contains(&preg)
}

fn uses_preg_or_alias(inst: &MachInst, preg: PReg) -> bool {
    inst.uses
        .iter()
        .filter_map(MachOperand::as_preg)
        .any(|used| pregs_overlap(used, preg))
        || inst
            .implicit_uses
            .iter()
            .any(|&used| pregs_overlap(used, preg))
}

fn defines_preg_or_alias(inst: &MachInst, preg: PReg) -> bool {
    inst.defs
        .iter()
        .filter_map(MachOperand::as_preg)
        .any(|defined| pregs_overlap(defined, preg))
        || inst
            .implicit_defs
            .iter()
            .any(|&defined| pregs_overlap(defined, preg))
}

fn pregs_overlap(a: PReg, b: PReg) -> bool {
    crate::greedy::allocator_pregs_overlap(a, b)
}

/// Rename all explicit uses of `old` to `new` in an instruction.
/// Does NOT rename implicit uses (those are fixed by the ISA).
fn rename_preg_uses(inst: &mut MachInst, old: PReg, new: PReg) {
    for op in &mut inst.uses {
        if let MachOperand::PReg(p) = op
            && *p == old
        {
            *p = new;
        }
    }
}

/// Replace an instruction with a NOP (will be removed from block later).
fn nop_inst(inst: &mut MachInst) {
    inst.opcode = NOP_OPCODE;
    inst.defs.clear();
    inst.uses.clear();
    inst.implicit_defs.clear();
    inst.implicit_uses.clear();
    inst.flags = InstFlags::default();
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine_types::{
        BlockId, InstFlags, InstId, MachBlock, MachFunction, MachInst, MachOperand, PReg, RegClass,
    };
    use crate::phi_elim::PSEUDO_COPY;
    use std::collections::BTreeMap;

    // AArch64 register constants (matching trust-cg-ir encoding).
    const X0: PReg = PReg::new(0);
    const X1: PReg = PReg::new(1);
    const X2: PReg = PReg::new(2);
    const X3: PReg = PReg::new(3);
    const X4: PReg = PReg::new(4);
    const X8: PReg = PReg::new(8);
    const X19: PReg = PReg::new(19);
    const X20: PReg = PReg::new(20);
    const X22: PReg = PReg::new(22);
    const X23: PReg = PReg::new(23);
    const X24: PReg = PReg::new(24);
    const X28: PReg = PReg::new(28);
    const W0: PReg = PReg::new(32);
    const W1: PReg = PReg::new(33);
    const W2: PReg = PReg::new(34);
    const W20: PReg = PReg::new(52);
    const W24: PReg = PReg::new(56);
    const W27: PReg = PReg::new(59);

    /// Helper: create a PSEUDO_COPY from src to dst (both PRegs).
    fn preg_copy(dst: PReg, src: PReg) -> MachInst {
        preg_copy_with_opcode(PSEUDO_COPY, dst, src)
    }

    /// Helper: create a copy-like instruction from src to dst (both PRegs).
    fn preg_copy_with_opcode(opcode: u16, dst: PReg, src: PReg) -> MachInst {
        MachInst {
            opcode,
            defs: vec![MachOperand::PReg(dst)],
            uses: vec![MachOperand::PReg(src)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        }
    }

    /// Helper: create a generic instruction with PReg defs and uses.
    fn preg_inst(opcode: u16, defs: &[PReg], uses: &[PReg]) -> MachInst {
        MachInst {
            opcode,
            defs: defs.iter().map(|p| MachOperand::PReg(*p)).collect(),
            uses: uses.iter().map(|p| MachOperand::PReg(*p)).collect(),
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        }
    }

    /// Helper: create a call instruction with implicit clobbers.
    fn call_inst(implicit_defs: Vec<PReg>) -> MachInst {
        MachInst {
            opcode: 0xCA,
            defs: Vec::new(),
            uses: Vec::new(),
            implicit_defs,
            implicit_uses: Vec::new(),
            flags: InstFlags::IS_CALL.union(InstFlags::HAS_SIDE_EFFECTS),
            tied_operands: vec![],
        }
    }

    /// Helper: create a return instruction with implicit ABI uses.
    fn ret_inst(implicit_uses: Vec<PReg>) -> MachInst {
        MachInst {
            opcode: trust_cg_ir::inst::AArch64Opcode::Ret as u16,
            defs: Vec::new(),
            uses: Vec::new(),
            implicit_defs: Vec::new(),
            implicit_uses,
            flags: InstFlags::IS_RETURN.union(InstFlags::IS_TERMINATOR),
            tied_operands: vec![],
        }
    }

    /// Helper: create an instruction with implicit defs.
    fn inst_with_implicit_defs(
        opcode: u16,
        defs: &[PReg],
        uses: &[PReg],
        implicit_defs: Vec<PReg>,
    ) -> MachInst {
        MachInst {
            opcode,
            defs: defs.iter().map(|p| MachOperand::PReg(*p)).collect(),
            uses: uses.iter().map(|p| MachOperand::PReg(*p)).collect(),
            implicit_defs,
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        }
    }

    /// Build a MachFunction from a list of blocks, each being a list of MachInsts.
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
            name: "test_post_ra".into(),
            insts,
            blocks,
            block_order,
            entry_block: BlockId(0),
            next_vreg: 0,
            next_stack_slot: 0,
            stack_slots: BTreeMap::new(),
        }
    }

    // -- Identity copy tests --

    #[test]
    fn test_identity_copy_removed() {
        // PSEUDO_COPY X0 <- X0 → removed
        let mut func = make_function(vec![vec![preg_copy(X0, X0), preg_inst(1, &[X1], &[X0])]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 1);
        assert_eq!(result.identity_copies, 1);
        assert_eq!(result.rename_coalesced, 0);
        // Block should have only the use instruction left.
        assert_eq!(func.blocks[0].insts.len(), 1);
    }

    #[test]
    fn test_identity_call_arg_marker_is_preserved() {
        let call_uses_x0 = MachInst {
            opcode: 0xCA,
            defs: Vec::new(),
            uses: Vec::new(),
            implicit_defs: vec![X0, X1, X2, X3],
            implicit_uses: vec![X0],
            flags: InstFlags::IS_CALL.union(InstFlags::HAS_SIDE_EFFECTS),
            tied_operands: vec![],
        };
        let mut marked = preg_copy(X0, X0);
        marked.flags.insert(InstFlags::IS_CALL_ARG_SETUP);
        let mut func = make_function(vec![vec![marked, call_uses_x0]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(func.blocks[0].insts.len(), 2);
        let marker = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert_eq!(post_ra_copy_operands(marker), Some((X0, X0)));
    }

    #[test]
    fn test_unmarked_identity_before_call_is_removed() {
        let call_uses_x0 = MachInst {
            opcode: 0xCA,
            defs: Vec::new(),
            uses: Vec::new(),
            implicit_defs: vec![X0, X1, X2, X3],
            implicit_uses: vec![X0],
            flags: InstFlags::IS_CALL.union(InstFlags::HAS_SIDE_EFFECTS),
            tied_operands: vec![],
        };
        let mut func = make_function(vec![vec![
            preg_copy(X0, X0),
            preg_inst(1, &[X0], &[X2]),
            call_uses_x0,
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 1);
        assert_eq!(result.identity_copies, 1);
        assert_eq!(func.blocks[0].insts.len(), 2);
    }

    #[test]
    fn test_multiple_identity_copies() {
        let mut func = make_function(vec![vec![
            preg_copy(X0, X0),
            preg_copy(X1, X1),
            preg_copy(X2, X2),
            preg_inst(1, &[], &[X0, X1, X2]),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 3);
        assert_eq!(result.identity_copies, 3);
        assert_eq!(func.blocks[0].insts.len(), 1);
    }

    // -- Rename coalescing tests --

    #[test]
    fn test_rename_simple() {
        // PSEUDO_COPY X1 <- X0 (X0 is not redefined, X1 used once after)
        // ADD X2, X1, X3  → should become ADD X2, X0, X3
        let mut func = make_function(vec![vec![
            preg_inst(1, &[X0], &[]),       // def X0
            preg_copy(X1, X0),              // copy X1 <- X0
            preg_inst(2, &[X2], &[X1, X3]), // use X1
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 1);
        assert_eq!(result.rename_coalesced, 1);
        // Block should have 2 instructions (def + renamed use).
        assert_eq!(func.blocks[0].insts.len(), 2);
        // Verify the use was renamed: X1 → X0
        let use_inst = &func.insts[func.blocks[0].insts[1].0 as usize];
        assert_eq!(use_inst.uses[0], MachOperand::PReg(X0));
    }

    #[test]
    fn test_rename_blocked_when_copy_destination_live_out() {
        // PSEUDO_COPY X1 <- X0
        // CMP X1, X4
        // successor uses X1
        //
        // The local CMP could be rewritten to X0, but the copy also commits
        // X1 for the successor edge. Removing it would expose the old X1 value
        // on that edge.
        let mut func = make_function(vec![
            vec![preg_copy(X1, X0), preg_inst(2, &[], &[X1, X4])],
            vec![preg_inst(3, &[X2], &[X1])],
        ]);
        func.blocks[0].succs = vec![BlockId(1)];
        func.blocks[1].preds = vec![BlockId(0)];

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(result.rename_coalesced, 0);
        assert_eq!(func.blocks[0].insts.len(), 2);

        let copy = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert_eq!(copy.defs, vec![MachOperand::PReg(X1)]);
        assert_eq!(copy.uses, vec![MachOperand::PReg(X0)]);

        let cmp = &func.insts[func.blocks[0].insts[1].0 as usize];
        assert_eq!(cmp.uses[0], MachOperand::PReg(X1));
    }

    #[test]
    fn test_rename_multiple_uses() {
        // PSEUDO_COPY X1 <- X0
        // use X1  (twice)
        // use X1
        let mut func = make_function(vec![vec![
            preg_inst(1, &[X0], &[]),
            preg_copy(X1, X0),
            preg_inst(2, &[X2], &[X1]),
            preg_inst(3, &[X3], &[X1]),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 1);
        assert_eq!(result.rename_coalesced, 1);
        assert_eq!(func.blocks[0].insts.len(), 3);

        // Both uses should be renamed.
        let inst1 = &func.insts[func.blocks[0].insts[1].0 as usize];
        assert_eq!(inst1.uses[0], MachOperand::PReg(X0));
        let inst2 = &func.insts[func.blocks[0].insts[2].0 as usize];
        assert_eq!(inst2.uses[0], MachOperand::PReg(X0));
    }

    #[test]
    fn test_rename_blocked_by_src_redef() {
        // PSEUDO_COPY X1 <- X0
        // def X0 (src is redefined!)
        // use X1 → cannot rename because X0 is clobbered
        let mut func = make_function(vec![vec![
            preg_copy(X1, X0),
            preg_inst(1, &[X0], &[X2]), // redefines X0
            preg_inst(2, &[X3], &[X1]), // uses X1 (after X0 redef)
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(func.blocks[0].insts.len(), 3);
    }

    #[test]
    fn test_rename_blocked_by_src_alias_redef_before_dst_use() {
        // PSEUDO_COPY X4 <- X0
        // def W0 (redefines the X0 source alias)
        // use X4 -> cannot rename to X0 because W0 clobbers it first.
        let mut func = make_function(vec![vec![
            preg_copy(X4, X0),
            preg_inst(trust_cg_ir::inst::AArch64Opcode::Movz as u16, &[W0], &[]),
            preg_inst(2, &[X3], &[X4]),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(result.rename_coalesced, 0);
        assert_eq!(func.blocks[0].insts.len(), 3);

        let copy = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert_eq!(copy.defs, vec![MachOperand::PReg(X4)]);
        assert_eq!(copy.uses, vec![MachOperand::PReg(X0)]);

        let use_inst = &func.insts[func.blocks[0].insts[2].0 as usize];
        assert_eq!(use_inst.uses[0], MachOperand::PReg(X4));
    }

    #[test]
    fn test_rename_rejects_mixed_width_store_use() {
        // PSEUDO_COPY W0 <- X2
        // STR W0, [X1]
        //
        // StrRI derives its access size from the value register class. Renaming
        // W0 to X2 would turn the store from 4 bytes into 8 bytes. The copy is
        // cross-WIDTH but not a cross-width SELF-copy (W0 and X2 name different
        // hardware registers), so no transform may touch it.
        let mut func = make_function(vec![vec![
            preg_copy(W0, X2),
            preg_inst(
                trust_cg_ir::inst::AArch64Opcode::StrRI as u16,
                &[],
                &[W0, X1],
            ),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(result.rename_coalesced, 0);
        assert_eq!(func.blocks[0].insts.len(), 2);

        let copy = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert!(crate::phi_elim::is_copy_opcode(copy.opcode));
        assert_eq!(copy.defs, vec![MachOperand::PReg(W0)]);
        assert_eq!(copy.uses, vec![MachOperand::PReg(X2)]);

        let store = &func.insts[func.blocks[0].insts[1].0 as usize];
        assert_eq!(
            store.uses,
            vec![MachOperand::PReg(W0), MachOperand::PReg(X1)]
        );
    }

    #[test]
    fn test_cross_width_self_copy_removed_before_narrow_store() {
        // PSEUDO_COPY W0 <- X0  (emitted `mov w0, w0`)
        // STR W0, [X1]
        //
        // The copy is an identity on the low 32 bits; its ONLY effect is
        // zeroing bits 63:32 of X0. The store reads W0, no later instruction
        // reads the 64-bit X0, and X0 is not live-out — so the zeroing is dead
        // and the whole instruction goes. Nothing is renamed, so the store
        // keeps its 4-byte value register (the hazard pinned by
        // `test_rename_rejects_mixed_width_store_use`).
        let mut func = make_function(vec![vec![
            preg_copy(W0, X0),
            preg_inst(
                trust_cg_ir::inst::AArch64Opcode::StrRI as u16,
                &[],
                &[W0, X1],
            ),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 1);
        assert_eq!(result.identity_copies, 1);
        assert_eq!(func.blocks[0].insts.len(), 1);
        let store = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert_eq!(
            store.uses,
            vec![MachOperand::PReg(W0), MachOperand::PReg(X1)]
        );
    }

    #[test]
    fn test_cross_width_self_copy_kept_when_wide_view_read() {
        // The same copy, but a later instruction reads the FULL 64-bit X0. The
        // zeroed high half is then observable, so the copy must stay.
        let mut func = make_function(vec![vec![preg_copy(W0, X0), preg_inst(2, &[X3], &[X0])]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(func.blocks[0].insts.len(), 2);
    }

    #[test]
    fn test_cross_width_self_copy_kept_when_wide_view_implicitly_read() {
        // A call reading X0 as an ABI argument observes the high half through
        // `implicit_uses`; the copy must stay.
        let mut func = make_function(vec![vec![preg_copy(W0, X0), {
            let mut call = call_inst(vec![]);
            call.implicit_uses = vec![X0];
            call
        }]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(func.blocks[0].insts.len(), 2);
    }

    #[test]
    fn test_cross_width_self_copy_kept_when_wide_view_live_out() {
        // Two blocks: the successor reads X0 as 64 bits, so X0 (the GPR64
        // encoding) is live-out of the copy's block and the zeroing is live.
        let mut func = make_function(vec![
            vec![preg_copy(W0, X0)],
            vec![preg_inst(2, &[X3], &[X0])],
        ]);
        func.blocks[0].succs = vec![BlockId(1)];
        func.blocks[1].preds = vec![BlockId(0)];

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(func.blocks[0].insts.len(), 1);
    }

    #[test]
    fn test_cross_width_self_copy_kept_under_kill_switch() {
        let mut func = make_function(vec![vec![
            preg_copy(W0, X0),
            preg_inst(
                trust_cg_ir::inst::AArch64Opcode::StrRI as u16,
                &[],
                &[W0, X1],
            ),
        ]]);

        let result = post_ra_coalesce_with_config(&mut func, PostRACoalesceConfig::NARROW);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(func.blocks[0].insts.len(), 2);
    }

    /// Helper: `UXTW Xd, Ws` — the narrow-return zero extension.
    fn uxtw_inst(dst: PReg, src: PReg) -> MachInst {
        preg_inst(
            trust_cg_ir::inst::AArch64Opcode::Uxtw as u16,
            &[dst],
            &[src],
        )
    }

    #[test]
    fn test_narrow_zext_collapses_into_producer() {
        // add w1, w0, #1        (producer, GPR32 def)
        // uxtw x0, w1           (the narrow-return widening, `mov w0, w1`)
        // ret (implicitly uses x0)
        //
        // Retargeting the producer to write W0 makes it a 32-bit register
        // write, which zeroes bits 63:32 of X0 — bit for bit what the UXTW
        // produced — so the extension goes.
        let mut func = make_function(vec![vec![
            imm_form_inst(trust_cg_ir::inst::AArch64Opcode::AddRI as u16, W1, W0, 1),
            uxtw_inst(X0, W1),
            ret_inst(vec![X0]),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 1);
        assert_eq!(func.blocks[0].insts.len(), 2);
        let add = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert_eq!(add.defs, vec![MachOperand::PReg(W0)]);
        assert_eq!(add.uses, vec![MachOperand::PReg(W0), MachOperand::Imm(1)]);
    }

    #[test]
    fn test_narrow_zext_kept_when_source_still_live() {
        // The extended value is read again after the extension, so the
        // producer cannot be redirected away from W1.
        let mut func = make_function(vec![vec![
            imm_form_inst(trust_cg_ir::inst::AArch64Opcode::AddRI as u16, W1, W0, 1),
            uxtw_inst(X0, W1),
            preg_inst(2, &[X3], &[W1]),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(func.blocks[0].insts.len(), 3);
    }

    #[test]
    fn test_narrow_zext_kept_when_destination_read_between() {
        // W0 (an alias of the extension destination X0) is read between the
        // producer and the extension; retargeting would clobber it early.
        let mut func = make_function(vec![vec![
            imm_form_inst(trust_cg_ir::inst::AArch64Opcode::AddRI as u16, W1, W2, 1),
            preg_inst(2, &[X3], &[W0]),
            uxtw_inst(X0, W1),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(func.blocks[0].insts.len(), 3);
    }

    #[test]
    fn test_narrow_zext_kept_when_producer_is_a_load() {
        // A load is not on the retargetable allowlist (non-pure memory
        // effect), so the extension stays.
        let mut func = make_function(vec![vec![
            preg_inst(trust_cg_ir::inst::AArch64Opcode::LdrRI as u16, &[W1], &[X2]),
            uxtw_inst(X0, W1),
            ret_inst(vec![X0]),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(func.blocks[0].insts.len(), 3);
    }

    #[test]
    fn test_narrow_zext_kept_under_kill_switch() {
        let mut func = make_function(vec![vec![
            imm_form_inst(trust_cg_ir::inst::AArch64Opcode::AddRI as u16, W1, W0, 1),
            uxtw_inst(X0, W1),
            ret_inst(vec![X0]),
        ]]);

        let result = post_ra_coalesce_with_config(&mut func, PostRACoalesceConfig::NARROW);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(func.blocks[0].insts.len(), 3);
    }

    #[test]
    fn test_rename_safe_when_src_redef_after_last_use() {
        // PSEUDO_COPY X1 <- X0
        // use X1
        // def X0 (src redefined AFTER last use of X1 — safe!)
        let mut func = make_function(vec![vec![
            preg_copy(X1, X0),
            preg_inst(2, &[X3], &[X1]), // uses X1
            preg_inst(1, &[X0], &[X2]), // redefines X0 after
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 1);
        assert_eq!(result.rename_coalesced, 1);
    }

    #[test]
    fn test_rename_blocked_by_call() {
        // PSEUDO_COPY X1 <- X0
        // call (barrier)
        // use X1 → cannot rename across call
        let mut func = make_function(vec![vec![
            preg_copy(X1, X0),
            call_inst(vec![X0, X1, X2, X3]),
            preg_inst(2, &[X3], &[X1]),
        ]]);

        let result = post_ra_coalesce(&mut func);

        // Should not rename across the call.
        assert_eq!(result.rename_coalesced, 0);
    }

    #[test]
    fn test_rename_blocked_by_return_implicit_use_of_dst() {
        // PSEUDO_COPY X0 <- X1
        // RET implicit-use X0
        // The return ABI use cannot be rewritten to X1, so the copy must stay.
        let mut func = make_function(vec![vec![preg_copy(X0, X1), ret_inst(vec![X0])]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(result.rename_coalesced, 0);
        assert_eq!(func.blocks[0].insts.len(), 2);

        let copy = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert!(crate::phi_elim::is_copy_opcode(copy.opcode));
        assert_eq!(copy.defs, vec![MachOperand::PReg(X0)]);
        assert_eq!(copy.uses, vec![MachOperand::PReg(X1)]);

        let ret = &func.insts[func.blocks[0].insts[1].0 as usize];
        assert_eq!(ret.implicit_uses, vec![X0]);
    }

    #[test]
    fn test_rename_blocked_by_implicit_def_of_src() {
        // PSEUDO_COPY X1 <- X0
        // inst that implicitly defines X0
        // use X1 → cannot rename because X0 is implicitly clobbered
        let mut func = make_function(vec![vec![
            preg_copy(X1, X0),
            inst_with_implicit_defs(5, &[X2], &[X3], vec![X0]),
            preg_inst(2, &[X3], &[X1]),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.rename_coalesced, 0);
    }

    #[test]
    fn test_rename_chain() {
        // PSEUDO_COPY X1 <- X0
        // PSEUDO_COPY X2 <- X1  → after first rename, becomes X2 <- X0
        // use X2               → after second rename, uses X0
        let mut func = make_function(vec![vec![
            preg_inst(1, &[X0], &[]),
            preg_copy(X1, X0),
            preg_copy(X2, X1),
            preg_inst(2, &[X3], &[X2]),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 2);
        assert_eq!(result.rename_coalesced, 2);
        // Only the def and the final use should remain.
        assert_eq!(func.blocks[0].insts.len(), 2);
        let use_inst = &func.insts[func.blocks[0].insts[1].0 as usize];
        assert_eq!(use_inst.uses[0], MachOperand::PReg(X0));
    }

    #[test]
    fn test_dead_copy_with_redef() {
        // PSEUDO_COPY X1 <- X0
        // def X1 (overwrites dst — copy is dead)
        // use X1 (uses the NEW X1)
        let mut func = make_function(vec![vec![
            preg_copy(X1, X0),
            preg_inst(1, &[X1], &[X2]),
            preg_inst(2, &[X3], &[X1]),
        ]]);

        let result = post_ra_coalesce(&mut func);

        // The copy is dead (X1 is immediately redefined).
        assert_eq!(result.copies_removed, 1);
        assert_eq!(func.blocks[0].insts.len(), 2);
    }

    #[test]
    fn test_dead_copy_not_removed_when_narrow_alias_redef_then_call_uses_dst() {
        // Regression for the misaligned-callout-pointer SIGABRT on indirect-call
        // loops. The copy sets up `x0` (a call argument). A later `mov w0, #imm`
        // only writes the LOW 32 bits of `x0` (a narrow alias), and is followed
        // by a call that reads `x0` as an argument via implicit_uses. The narrow
        // write must NOT be treated as a full kill of `x0`: the copy delivers the
        // value the call needs, so it must be preserved.
        let call_uses_x0 = MachInst {
            opcode: 0xCA,
            defs: Vec::new(),
            uses: Vec::new(),
            implicit_defs: vec![X1, X2, X3, X8], // caller-saved clobbers
            implicit_uses: vec![X0],             // x0 is the first call argument
            flags: InstFlags::IS_CALL.union(InstFlags::HAS_SIDE_EFFECTS),
            tied_operands: vec![],
        };
        let mut func = make_function(vec![vec![
            preg_copy(X0, X24),         // x0 = out-buffer pointer (call arg0)
            preg_inst(1, &[W0], &[]),   // mov w0, #1 -> narrow write of x0's low half
            preg_inst(2, &[X3], &[W0]), // x3 = w0 (build another call arg)
            call_uses_x0,               // call reads x0 as arg0
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(
            result.copies_removed, 0,
            "the x0 arg-setup copy must be preserved across the narrow w0 write and the call"
        );
        // The copy instruction must still be present (not NOP'd).
        let copy = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert_eq!(copy.defs[0], MachOperand::PReg(X0));
        assert_eq!(copy.uses[0], MachOperand::PReg(X24));
    }

    #[test]
    fn test_no_coalescing_on_non_copy() {
        // Regular instructions should not be touched.
        let mut func = make_function(vec![vec![
            preg_inst(1, &[X0], &[]),
            preg_inst(2, &[X1], &[X0]),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(func.blocks[0].insts.len(), 2);
    }

    #[test]
    fn test_multi_block() {
        // Two blocks, each with an identity copy.
        let mut func = make_function(vec![
            vec![preg_copy(X0, X0), preg_inst(1, &[], &[X0])],
            vec![preg_copy(X1, X1), preg_inst(2, &[], &[X1])],
        ]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 2);
        assert_eq!(result.identity_copies, 2);
        assert_eq!(func.blocks[0].insts.len(), 1);
        assert_eq!(func.blocks[1].insts.len(), 1);
    }

    #[test]
    fn test_vreg_copy_ignored() {
        // PSEUDO_COPY with VRegs (shouldn't happen post-RA but should not crash).
        use crate::machine_types::VReg;
        let vreg0 = VReg {
            id: 0,
            class: RegClass::Gpr64,
        };
        let vreg1 = VReg {
            id: 1,
            class: RegClass::Gpr64,
        };
        let mut func = make_function(vec![vec![MachInst {
            opcode: PSEUDO_COPY,
            defs: vec![MachOperand::VReg(vreg1)],
            uses: vec![MachOperand::VReg(vreg0)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        }]]);

        let result = post_ra_coalesce(&mut func);

        // VReg copies are skipped, not counted.
        assert_eq!(result.copies_removed, 0);
    }

    #[test]
    fn test_rename_stops_at_dst_redef() {
        // PSEUDO_COPY X1 <- X0
        // use X1
        // def X1 (redefined)
        // use X1  ← this use reads the NEW X1, not our copy target
        let mut func = make_function(vec![vec![
            preg_copy(X1, X0),
            preg_inst(2, &[X2], &[X1]), // use X1 (from copy)
            preg_inst(3, &[X1], &[X3]), // redef X1
            preg_inst(4, &[X8], &[X1]), // use new X1
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 1);
        assert_eq!(result.rename_coalesced, 1);
        // First use should be renamed.
        let inst_use1 = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert_eq!(inst_use1.uses[0], MachOperand::PReg(X0));
        // Last use should NOT be renamed (reads new X1).
        let inst_use2 = &func.insts[func.blocks[0].insts[2].0 as usize];
        assert_eq!(inst_use2.uses[0], MachOperand::PReg(X1));
    }

    #[test]
    fn test_backward_def_coalesce_retargets_add_mul_commits() {
        // Mirrors the xxh3 loop backedge shape after allocation:
        //   mul x20, x19, x22
        //   add x19, x28, x23
        //   copy x24 <- x20
        //   copy x28 <- x19
        //
        // The old loop-carried x24/x28 values are not read after the
        // computations, so the computations can define the committed registers
        // directly and both copies can be removed.
        let mut func = make_function(vec![vec![
            preg_inst(
                trust_cg_ir::inst::AArch64Opcode::MulRR as u16,
                &[X20],
                &[X19, X22],
            ),
            preg_inst(
                trust_cg_ir::inst::AArch64Opcode::AddRR as u16,
                &[X19],
                &[X28, X23],
            ),
            preg_copy(X24, X20),
            preg_copy(X28, X19),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 2);
        assert_eq!(result.rename_coalesced, 2);
        assert_eq!(func.blocks[0].insts.len(), 2);

        let mul = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert_eq!(mul.defs, vec![MachOperand::PReg(X24)]);
        assert_eq!(
            mul.uses,
            vec![MachOperand::PReg(X19), MachOperand::PReg(X22)]
        );

        let add = &func.insts[func.blocks[0].insts[1].0 as usize];
        assert_eq!(add.defs, vec![MachOperand::PReg(X28)]);
        assert_eq!(
            add.uses,
            vec![MachOperand::PReg(X28), MachOperand::PReg(X23)]
        );
    }

    #[test]
    fn test_backward_def_coalesce_handles_selected_movr() {
        let mut func = make_function(vec![vec![
            preg_inst(
                trust_cg_ir::inst::AArch64Opcode::MulRR as u16,
                &[X20],
                &[X19, X22],
            ),
            preg_copy_with_opcode(trust_cg_ir::inst::AArch64Opcode::MovR as u16, X24, X20),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 1);
        assert_eq!(func.blocks[0].insts.len(), 1);

        let mul = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert_eq!(mul.defs, vec![MachOperand::PReg(X24)]);
    }

    #[test]
    fn test_backward_def_coalesce_retargets_rbit_to_return_register() {
        let mut func = make_function(vec![vec![
            preg_inst(trust_cg_ir::inst::AArch64Opcode::Rbit as u16, &[W27], &[W0]),
            preg_copy(W0, W27),
            ret_inst(vec![W0]),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 1);
        assert_eq!(result.rename_coalesced, 1);
        assert_eq!(func.blocks[0].insts.len(), 2);

        let rbit = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert_eq!(rbit.defs, vec![MachOperand::PReg(W0)]);
        assert_eq!(rbit.uses, vec![MachOperand::PReg(W0)]);
        assert_eq!(
            func.insts[func.blocks[0].insts[1].0 as usize].opcode,
            trust_cg_ir::inst::AArch64Opcode::Ret as u16
        );
    }

    #[test]
    fn test_backward_def_coalesce_retargets_subrr_commit() {
        let mut func = make_function(vec![vec![
            preg_inst(
                trust_cg_ir::inst::AArch64Opcode::SubRR as u16,
                &[X20],
                &[X19, X22],
            ),
            preg_copy(X24, X20),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 1);
        assert_eq!(result.rename_coalesced, 1);
        assert_eq!(func.blocks[0].insts.len(), 1);

        let sub = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert_eq!(sub.defs, vec![MachOperand::PReg(X24)]);
        assert_eq!(
            sub.uses,
            vec![MachOperand::PReg(X19), MachOperand::PReg(X22)]
        );
    }

    #[test]
    fn test_backward_def_coalesce_blocks_subrr_read_write_source() {
        let mut func = make_function(vec![vec![
            preg_inst(
                trust_cg_ir::inst::AArch64Opcode::SubRR as u16,
                &[X20],
                &[X20, X22],
            ),
            preg_copy(X24, X20),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(result.rename_coalesced, 0);
        assert_eq!(func.blocks[0].insts.len(), 2);

        let sub = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert_eq!(sub.defs, vec![MachOperand::PReg(X20)]);
        assert_eq!(
            sub.uses,
            vec![MachOperand::PReg(X20), MachOperand::PReg(X22)]
        );
    }

    #[test]
    fn test_backward_def_coalesce_blocked_by_post_copy_src_use() {
        let mut func = make_function(vec![vec![
            preg_inst(
                trust_cg_ir::inst::AArch64Opcode::MulRR as u16,
                &[X20],
                &[X19, X22],
            ),
            preg_copy(X24, X20),
            preg_inst(2, &[X3], &[X20, X8]),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(result.rename_coalesced, 0);
        assert_eq!(func.blocks[0].insts.len(), 3);

        let mul = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert_eq!(mul.defs, vec![MachOperand::PReg(X20)]);

        let copy = &func.insts[func.blocks[0].insts[1].0 as usize];
        assert!(crate::phi_elim::is_copy_opcode(copy.opcode));
        assert_eq!(copy.defs, vec![MachOperand::PReg(X24)]);
        assert_eq!(copy.uses, vec![MachOperand::PReg(X20)]);
    }

    #[test]
    fn test_backward_def_coalesce_blocked_by_post_copy_src_live_out() {
        let mut func = make_function(vec![
            vec![
                preg_inst(
                    trust_cg_ir::inst::AArch64Opcode::MulRR as u16,
                    &[X20],
                    &[X19, X22],
                ),
                preg_copy(X24, X20),
            ],
            vec![preg_inst(2, &[X3], &[X20])],
        ]);
        func.blocks[0].succs.push(BlockId(1));
        func.blocks[1].preds.push(BlockId(0));

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(result.rename_coalesced, 0);
        assert_eq!(func.blocks[0].insts.len(), 2);

        let mul = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert_eq!(mul.defs, vec![MachOperand::PReg(X20)]);
    }

    #[test]
    fn test_backward_def_coalesce_blocked_by_dst_use() {
        let mut func = make_function(vec![vec![
            preg_inst(
                trust_cg_ir::inst::AArch64Opcode::MulRR as u16,
                &[X20],
                &[X19, X22],
            ),
            preg_inst(2, &[X3], &[X24]),
            preg_copy(X24, X20),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(func.blocks[0].insts.len(), 3);
    }

    #[test]
    fn test_backward_def_coalesce_blocked_by_src_use() {
        let mut func = make_function(vec![vec![
            preg_inst(
                trust_cg_ir::inst::AArch64Opcode::MulRR as u16,
                &[X20],
                &[X19, X22],
            ),
            preg_inst(2, &[X3], &[X20]),
            preg_copy(X24, X20),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(func.blocks[0].insts.len(), 3);
    }

    /// Helper: build an immediate-form ALU inst `op dst, base, #imm`
    /// (post-RA layout: defs=[dst], uses=[base, Imm]).
    fn imm_form_inst(opcode: u16, dst: PReg, base: PReg, imm: i64) -> MachInst {
        MachInst {
            opcode,
            defs: vec![MachOperand::PReg(dst)],
            uses: vec![MachOperand::PReg(base), MachOperand::Imm(imm)],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        }
    }

    #[test]
    fn test_backward_def_coalesce_retargets_self_referential_addri() {
        // reduction-split loop-carried tracker/iv advance:
        //   add x20, x19, #28      ; carrier_next = carrier + stride
        //   mov x19, x20           ; carrier = carrier_next
        // The producer is self-referential (base x19 == copy dst x19) with a
        // non-zero stride, so it retargets in place to `add x19, x19, #28`
        // and the loop-carried mov is removed.
        let mut func = make_function(vec![vec![
            imm_form_inst(trust_cg_ir::inst::AArch64Opcode::AddRI as u16, X20, X19, 28),
            preg_copy(X19, X20),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 1);
        assert_eq!(result.rename_coalesced, 1);
        assert_eq!(func.blocks[0].insts.len(), 1);

        let add = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert_eq!(add.defs, vec![MachOperand::PReg(X19)]);
        assert_eq!(add.uses, vec![MachOperand::PReg(X19), MachOperand::Imm(28)]);
    }

    #[test]
    fn test_backward_def_coalesce_retargets_self_referential_subri() {
        // Decreasing self-referential carrier: `sub x20, x19, #4; mov x19, x20`.
        let mut func = make_function(vec![vec![
            imm_form_inst(trust_cg_ir::inst::AArch64Opcode::SubRI as u16, X20, X19, 4),
            preg_copy(X19, X20),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 1);
        assert_eq!(result.rename_coalesced, 1);
        let sub = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert_eq!(sub.defs, vec![MachOperand::PReg(X19)]);
        assert_eq!(sub.uses, vec![MachOperand::PReg(X19), MachOperand::Imm(4)]);
    }

    #[test]
    fn test_backward_def_coalesce_blocks_addri_zero_immediate() {
        // A `+#0` immediate is the LoopLatchLayout HARDENING disguise
        // (`dst = src + 0`, a copy that deliberately blocks coalescing). Even
        // though base x19 == dst x19, the zero immediate must NOT be retargeted,
        // preserving the hardening barrier.
        let mut func = make_function(vec![vec![
            imm_form_inst(trust_cg_ir::inst::AArch64Opcode::AddRI as u16, X20, X19, 0),
            preg_copy(X19, X20),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(result.rename_coalesced, 0);
        assert_eq!(func.blocks[0].insts.len(), 2);
        let add = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert_eq!(add.defs, vec![MachOperand::PReg(X20)]);
    }

    #[test]
    fn test_backward_def_coalesce_blocks_non_self_referential_addri_under_kill_switch() {
        // Cross-carrier update `x20 = x22 + 28` feeding `mov x19, x20` reads a
        // DIFFERENT register (x22) than the copy destination (x19). The
        // historical SELF-REFERENTIAL guard refuses it; the kill switch
        // `TCG_NO_WIDE_BACKDEF_COALESCE` restores exactly that decision.
        let mut func = make_function(vec![vec![
            imm_form_inst(trust_cg_ir::inst::AArch64Opcode::AddRI as u16, X20, X22, 28),
            preg_copy(X19, X20),
        ]]);

        let result = post_ra_coalesce_with_config(&mut func, PostRACoalesceConfig::NARROW);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(result.rename_coalesced, 0);
        assert_eq!(func.blocks[0].insts.len(), 2);
        let add = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert_eq!(add.defs, vec![MachOperand::PReg(X20)]);
        assert_eq!(add.uses, vec![MachOperand::PReg(X22), MachOperand::Imm(28)]);
    }

    #[test]
    fn test_backward_def_coalesce_retargets_non_self_referential_addri_when_wide() {
        // The same cross-carrier shape IS retargetable: `add x19, x22, #28`
        // reads x22 at the producer's position exactly as before, writes only
        // x19, and the window between producer and copy is clean. The
        // self-referential guard was over-conservative, not a soundness
        // discriminator (see `can_retarget_source_def`).
        let mut func = make_function(vec![vec![
            imm_form_inst(trust_cg_ir::inst::AArch64Opcode::AddRI as u16, X20, X22, 28),
            preg_copy(X19, X20),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 1);
        assert_eq!(func.blocks[0].insts.len(), 1);
        let add = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert_eq!(add.defs, vec![MachOperand::PReg(X19)]);
        assert_eq!(add.uses, vec![MachOperand::PReg(X22), MachOperand::Imm(28)]);
    }

    #[test]
    fn test_backward_def_coalesce_retargets_wide_alu_forms() {
        // One representative per admitted wide family: logical register,
        // shift-immediate, bitfield move, conditional select, division.
        for (opcode, uses) in [
            (
                trust_cg_ir::inst::AArch64Opcode::AndRR as u16,
                vec![MachOperand::PReg(X22), MachOperand::PReg(X23)],
            ),
            (
                trust_cg_ir::inst::AArch64Opcode::LslRI as u16,
                vec![MachOperand::PReg(X22), MachOperand::Imm(3)],
            ),
            (
                trust_cg_ir::inst::AArch64Opcode::Ubfm as u16,
                vec![
                    MachOperand::PReg(X22),
                    MachOperand::Imm(1),
                    MachOperand::Imm(7),
                ],
            ),
            (
                trust_cg_ir::inst::AArch64Opcode::Csel as u16,
                vec![
                    MachOperand::PReg(X22),
                    MachOperand::PReg(X23),
                    MachOperand::Imm(11),
                ],
            ),
            (
                trust_cg_ir::inst::AArch64Opcode::SDiv as u16,
                vec![MachOperand::PReg(X22), MachOperand::PReg(X23)],
            ),
        ] {
            let producer = MachInst {
                opcode,
                defs: vec![MachOperand::PReg(X20)],
                uses,
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            };
            let mut func = make_function(vec![vec![producer, preg_copy(X19, X20)]]);

            let result = post_ra_coalesce(&mut func);

            assert_eq!(result.copies_removed, 1, "opcode {opcode} should retarget");
            let retargeted = &func.insts[func.blocks[0].insts[0].0 as usize];
            assert_eq!(retargeted.defs, vec![MachOperand::PReg(X19)]);
        }
    }

    #[test]
    fn test_backward_def_coalesce_refuses_tied_and_impure_producers() {
        // Movk (tied destination), Bfm (bitfield INSERT, tied destination),
        // LdrRI (memory effect), AddsRR (writes NZCV) and AddPCRel-style
        // opaque `Imm(0)` carriers must all stay refused.
        for (opcode, uses) in [
            (
                trust_cg_ir::inst::AArch64Opcode::Movk as u16,
                vec![MachOperand::Imm(7), MachOperand::Imm(16)],
            ),
            (
                trust_cg_ir::inst::AArch64Opcode::Bfm as u16,
                vec![
                    MachOperand::PReg(X22),
                    MachOperand::Imm(1),
                    MachOperand::Imm(7),
                ],
            ),
            (
                trust_cg_ir::inst::AArch64Opcode::LdrRI as u16,
                vec![MachOperand::PReg(X22), MachOperand::Imm(8)],
            ),
            (
                trust_cg_ir::inst::AArch64Opcode::AddsRR as u16,
                vec![MachOperand::PReg(X22), MachOperand::PReg(X23)],
            ),
            (
                trust_cg_ir::inst::AArch64Opcode::AddRI as u16,
                vec![MachOperand::PReg(X22), MachOperand::Imm(0)],
            ),
        ] {
            let producer = MachInst {
                opcode,
                defs: vec![MachOperand::PReg(X20)],
                uses,
                implicit_defs: Vec::new(),
                implicit_uses: Vec::new(),
                flags: InstFlags::default(),
                tied_operands: vec![],
            };
            let mut func = make_function(vec![vec![producer, preg_copy(X19, X20)]]);

            let result = post_ra_coalesce(&mut func);

            assert_eq!(result.copies_removed, 0, "opcode {opcode} must be refused");
        }
    }

    #[test]
    fn test_backward_def_coalesce_refuses_call_arg_setup_producer() {
        let mut producer = preg_inst(
            trust_cg_ir::inst::AArch64Opcode::AddRR as u16,
            &[X20],
            &[X22, X23],
        );
        producer.flags = InstFlags::IS_CALL_ARG_SETUP;
        let mut func = make_function(vec![vec![producer, preg_copy(X19, X20)]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
    }

    #[test]
    fn test_backward_def_coalesce_refuses_narrow_alias_def_in_window() {
        // `add x20, x22, x23 ; mov w20, w24 ; mov x19, x20`
        //
        // The W-width write fully redefines x20, so the copy transfers ITS
        // result, not the add's. Walking past it to retarget the add would
        // deliver the stale value.
        let mut func = make_function(vec![vec![
            preg_inst(
                trust_cg_ir::inst::AArch64Opcode::AddRR as u16,
                &[X20],
                &[X22, X23],
            ),
            preg_copy_with_opcode(trust_cg_ir::inst::AArch64Opcode::MOVWrr as u16, W20, W24),
            preg_copy(X19, X20),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        let add = &func.insts[func.blocks[0].insts[0].0 as usize];
        assert_eq!(add.defs, vec![MachOperand::PReg(X20)]);
    }

    #[test]
    fn test_backward_def_coalesce_blocks_self_ref_addri_with_intervening_dst_read() {
        // Even a self-referential producer must not fold when the carrier (dst)
        // is read between the producer and the copy — that read needs the OLD
        // carrier value, which an in-place retarget would clobber (the lost-copy
        // hazard). The existing intervening-dst-use guard rejects it.
        let mut func = make_function(vec![vec![
            imm_form_inst(trust_cg_ir::inst::AArch64Opcode::AddRI as u16, X20, X19, 28),
            preg_inst(2, &[X3], &[X19, X8]), // reads x19 (old carrier)
            preg_copy(X19, X20),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 0);
        assert_eq!(result.rename_coalesced, 0);
        assert_eq!(func.blocks[0].insts.len(), 3);
    }

    #[test]
    fn test_empty_block() {
        let mut func = make_function(vec![vec![]]);
        let result = post_ra_coalesce(&mut func);
        assert_eq!(result.copies_removed, 0);
    }

    #[test]
    fn test_callee_saved_rename() {
        // Callee-saved registers (X19, X20) should still be coalescible
        // when no interference exists.
        let mut func = make_function(vec![vec![
            preg_inst(1, &[X19], &[]),
            preg_copy(X20, X19),
            preg_inst(2, &[X3], &[X20]),
        ]]);

        let result = post_ra_coalesce(&mut func);

        assert_eq!(result.copies_removed, 1);
        assert_eq!(result.rename_coalesced, 1);
        let use_inst = &func.insts[func.blocks[0].insts[1].0 as usize];
        assert_eq!(use_inst.uses[0], MachOperand::PReg(X19));
    }

    // -----------------------------------------------------------------------
    // Decision-identity oracle: the cached fast path must make EXACTLY the
    // same coalescing decisions as the historical per-block-recompute
    // reference, on randomized functions exercising aliasing (X/W),
    // calls/returns with implicit operands, retargetable ops, copy chains,
    // and cyclic CFGs.
    // -----------------------------------------------------------------------

    /// Deterministic xorshift64 RNG — no external dependency.
    struct XorShift(u64);

    impl XorShift {
        fn new(seed: u64) -> Self {
            Self(seed | 1)
        }

        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }

        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    /// Random GPR from X0-X28 / W0-W28 — exercises sub-register aliasing.
    fn random_preg(rng: &mut XorShift) -> PReg {
        let n = rng.below(29) as u16;
        if rng.below(2) == 0 {
            PReg::new(n) // Xn
        } else {
            PReg::new(32 + n) // Wn (aliases Xn)
        }
    }

    fn random_pregs(rng: &mut XorShift, max: u64) -> Vec<PReg> {
        (0..rng.below(max + 1)).map(|_| random_preg(rng)).collect()
    }

    fn random_inst(rng: &mut XorShift) -> MachInst {
        match rng.below(12) {
            // Generic computation; opcodes in 0x2000.. never collide with
            // copy/retargetable/NOP opcodes.
            0..=2 => {
                let defs = random_pregs(rng, 2);
                let uses = random_pregs(rng, 3);
                preg_inst(0x2000 + rng.below(8) as u16, &defs, &uses)
            }
            // Retargetable ALU ops (backward def coalescing candidates).
            3 | 4 => {
                let op = match rng.below(4) {
                    0 => trust_cg_ir::inst::AArch64Opcode::AddRR,
                    1 => trust_cg_ir::inst::AArch64Opcode::SubRR,
                    2 => trust_cg_ir::inst::AArch64Opcode::MulRR,
                    _ => trust_cg_ir::inst::AArch64Opcode::Rbit,
                };
                preg_inst(
                    op as u16,
                    &[random_preg(rng)],
                    &[random_preg(rng), random_preg(rng)],
                )
            }
            // Copy-like instructions (sometimes identity copies).
            5..=7 => {
                let opcode = match rng.below(4) {
                    0 => PSEUDO_COPY,
                    1 => trust_cg_ir::inst::AArch64Opcode::MovR as u16,
                    2 => trust_cg_ir::inst::AArch64Opcode::MOVWrr as u16,
                    _ => trust_cg_ir::inst::AArch64Opcode::MOVXrr as u16,
                };
                let dst = random_preg(rng);
                let src = if rng.below(5) == 0 {
                    dst // identity copy
                } else {
                    random_preg(rng)
                };
                preg_copy_with_opcode(opcode, dst, src)
            }
            // Call with implicit clobbers and implicit argument uses.
            8 => MachInst {
                opcode: 0xCA,
                defs: Vec::new(),
                uses: Vec::new(),
                implicit_defs: random_pregs(rng, 4),
                implicit_uses: random_pregs(rng, 2),
                flags: InstFlags::IS_CALL.union(InstFlags::HAS_SIDE_EFFECTS),
                tied_operands: vec![],
            },
            // Return with implicit ABI uses.
            9 => ret_inst(random_pregs(rng, 2)),
            // Computation with implicit defs (e.g. flag-setting).
            10 => inst_with_implicit_defs(
                0x2100 + rng.below(4) as u16,
                &random_pregs(rng, 1),
                &random_pregs(rng, 2),
                random_pregs(rng, 2),
            ),
            // Operand-free instruction.
            _ => preg_inst(0x2200, &[], &[]),
        }
    }

    /// Random function with a random (possibly cyclic, possibly self-looping)
    /// CFG.
    fn random_function(rng: &mut XorShift, max_blocks: u64, max_insts: u64) -> MachFunction {
        let num_blocks = 1 + rng.below(max_blocks) as usize;
        let mut blocks_insts = Vec::with_capacity(num_blocks);
        for _ in 0..num_blocks {
            let n_insts = rng.below(max_insts + 1) as usize;
            blocks_insts.push((0..n_insts).map(|_| random_inst(rng)).collect());
        }
        let mut func = make_function(blocks_insts);
        for b in 0..num_blocks {
            for _ in 0..rng.below(3) {
                let succ = rng.below(num_blocks as u64) as usize;
                func.blocks[b].succs.push(BlockId(succ as u32));
                func.blocks[succ].preds.push(BlockId(b as u32));
            }
        }
        func
    }

    fn assert_funcs_identical(a: &MachFunction, b: &MachFunction, ctx: &str) {
        assert_eq!(a.insts.len(), b.insts.len(), "inst count mismatch ({ctx})");
        for (i, (x, y)) in a.insts.iter().zip(b.insts.iter()).enumerate() {
            assert_eq!(x.opcode, y.opcode, "inst {i} opcode mismatch ({ctx})");
            assert_eq!(x.defs, y.defs, "inst {i} defs mismatch ({ctx})");
            assert_eq!(x.uses, y.uses, "inst {i} uses mismatch ({ctx})");
            assert_eq!(
                x.implicit_defs, y.implicit_defs,
                "inst {i} implicit_defs mismatch ({ctx})"
            );
            assert_eq!(
                x.implicit_uses, y.implicit_uses,
                "inst {i} implicit_uses mismatch ({ctx})"
            );
            assert_eq!(x.flags, y.flags, "inst {i} flags mismatch ({ctx})");
        }
        assert_eq!(
            a.blocks.len(),
            b.blocks.len(),
            "block count mismatch ({ctx})"
        );
        for (i, (x, y)) in a.blocks.iter().zip(b.blocks.iter()).enumerate() {
            assert_eq!(x.insts, y.insts, "block {i} insts mismatch ({ctx})");
        }
    }

    /// Run both implementations on clones of the same function and require
    /// identical outputs and statistics. Returns copies removed.
    fn check_decision_identity(func: &MachFunction, ctx: &str) -> u64 {
        let mut fast = func.clone();
        let mut reference = func.clone();
        let fast_result = post_ra_coalesce(&mut fast);
        let ref_result = post_ra_coalesce_reference(&mut reference);
        assert_eq!(fast_result, ref_result, "stats mismatch ({ctx})");
        assert_funcs_identical(&fast, &reference, ctx);
        fast_result.copies_removed as u64
    }

    #[test]
    fn test_decision_identity_randomized_small() {
        let mut total_removed = 0u64;
        for seed in 0..400u64 {
            let mut rng = XorShift::new(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0xA5A5);
            let func = random_function(&mut rng, 10, 12);
            total_removed += check_decision_identity(&func, &format!("small seed {seed}"));
        }
        // The corpus must actually exercise coalescing, or the oracle is
        // vacuous.
        assert!(
            total_removed > 100,
            "randomized corpus exercised too little coalescing: {total_removed}"
        );
    }

    #[test]
    fn test_decision_identity_randomized_medium() {
        let mut total_removed = 0u64;
        for seed in 0..40u64 {
            let mut rng = XorShift::new(seed.wrapping_mul(0xD134_2543_DE82_EF95) ^ 0x5A5A);
            let func = random_function(&mut rng, 120, 10);
            total_removed += check_decision_identity(&func, &format!("medium seed {seed}"));
        }
        assert!(
            total_removed > 100,
            "randomized corpus exercised too little coalescing: {total_removed}"
        );
    }

    #[test]
    fn test_decision_identity_empty_block_order() {
        // Exercise the `block_order.is_empty()` fallback ordering.
        for seed in 0..50u64 {
            let mut rng = XorShift::new(seed.wrapping_mul(0xBF58_476D_1CE4_E5B9) ^ 0x33);
            let mut func = random_function(&mut rng, 8, 10);
            func.block_order.clear();
            check_decision_identity(&func, &format!("empty-order seed {seed}"));
        }
    }

    // -----------------------------------------------------------------------
    // Liveness-lemma check: the bitset/summary fixpoint must produce
    // set-for-set identical `live_out` to `compute_physical_liveness`.
    // -----------------------------------------------------------------------

    #[test]
    fn test_summary_liveness_equals_reference_liveness() {
        for seed in 0..200u64 {
            let mut rng = XorShift::new(seed.wrapping_mul(0x94D0_49BB_1331_11EB) ^ 0x77);
            let func = random_function(&mut rng, 16, 10);

            let reference = compute_physical_liveness(&func);
            let mut cache = CachedLiveness::new(func.blocks.len());
            cache.recompute(&func);

            for block_idx in 0..func.blocks.len() {
                assert_eq!(
                    cache.live_out[block_idx].to_btree_set(),
                    reference.live_out[block_idx],
                    "live_out mismatch at block {block_idx} (seed {seed})"
                );
            }
        }
    }

    // -----------------------------------------------------------------------
    // Performance regression guard: a ~2000-block function (the shape that
    // made TY's fused-BFS regalloc take ~55s) must coalesce identically and
    // dramatically faster than the per-block-recompute reference.
    // -----------------------------------------------------------------------

    /// A loop-shaped function: `entry → b1 → b2 → ... → bN → b1` with extra
    /// cycle edges, every block carrying phi-elimination-style copies. This
    /// mimics the fused BFS parent-loop MachIR that exposed the quadratic
    /// behavior.
    fn synthetic_loop_function(num_blocks: usize) -> MachFunction {
        let mut rng = XorShift::new(0xB16_B00B5);
        let mut blocks_insts = Vec::with_capacity(num_blocks);
        for i in 0..num_blocks {
            // A couple of computations.
            let mut insts = vec![preg_inst(
                trust_cg_ir::inst::AArch64Opcode::AddRR as u16,
                &[random_preg(&mut rng)],
                &[random_preg(&mut rng), random_preg(&mut rng)],
            )];
            insts.push(preg_inst(
                0x2000 + (i % 7) as u16,
                &random_pregs(&mut rng, 2),
                &random_pregs(&mut rng, 3),
            ));
            // Phi-elim-style copies, some coalescible.
            insts.push(preg_copy(random_preg(&mut rng), random_preg(&mut rng)));
            insts.push(preg_copy(random_preg(&mut rng), random_preg(&mut rng)));
            if i % 3 == 0 {
                let r = random_preg(&mut rng);
                insts.push(preg_copy(r, r)); // identity copy
            }
            if i % 11 == 0 {
                insts.push(MachInst {
                    opcode: 0xCA,
                    defs: Vec::new(),
                    uses: Vec::new(),
                    implicit_defs: vec![X0, X1, X2, X3, X8],
                    implicit_uses: vec![X0],
                    flags: InstFlags::IS_CALL.union(InstFlags::HAS_SIDE_EFFECTS),
                    tied_operands: vec![],
                });
            }
            blocks_insts.push(insts);
        }
        let mut func = make_function(blocks_insts);
        for i in 0..num_blocks {
            let next = if i + 1 < num_blocks {
                i + 1
            } else {
                1.min(num_blocks - 1)
            };
            func.blocks[i].succs.push(BlockId(next as u32));
            func.blocks[next].preds.push(BlockId(i as u32));
            // Side edge forming extra cycles.
            if i % 5 == 0 && num_blocks > 2 {
                let target = (i * 7 + 3) % num_blocks;
                func.blocks[i].succs.push(BlockId(target as u32));
                func.blocks[target].preds.push(BlockId(i as u32));
            }
        }
        func
    }

    fn run_synthetic_identity_and_speed(num_blocks: usize, min_copies: u32) {
        let func = synthetic_loop_function(num_blocks);

        let mut fast = func.clone();
        let fast_start = std::time::Instant::now();
        let fast_result = post_ra_coalesce(&mut fast);
        let fast_elapsed = fast_start.elapsed();

        let mut reference = func.clone();
        let ref_start = std::time::Instant::now();
        let ref_result = post_ra_coalesce_reference(&mut reference);
        let ref_elapsed = ref_start.elapsed();

        assert_eq!(fast_result, ref_result, "stats mismatch on synthetic loop");
        assert_funcs_identical(&fast, &reference, "synthetic loop function");
        assert!(
            fast_result.copies_removed > min_copies,
            "synthetic function must exercise substantial coalescing, got {}",
            fast_result.copies_removed
        );

        eprintln!(
            "post_ra_coalesce {num_blocks}-block synthetic: fast {fast_elapsed:?}, \
             reference {ref_elapsed:?} ({:.1}x), copies_removed {}",
            ref_elapsed.as_secs_f64() / fast_elapsed.as_secs_f64().max(1e-9),
            fast_result.copies_removed,
        );
        // Generous bound to avoid CI flakes; the real ratio is far larger
        // (measured 369x at 2000 blocks in release).
        assert!(
            fast_elapsed.as_secs_f64() * 5.0 < ref_elapsed.as_secs_f64(),
            "fast path not meaningfully faster: fast {fast_elapsed:?} vs reference {ref_elapsed:?}"
        );
    }

    #[test]
    fn test_large_function_identity_and_speed() {
        run_synthetic_identity_and_speed(300, 50);
    }

    /// The full-size reproduction of the TY fused-BFS shape. The reference
    /// path takes ~35s in release / ~10min in debug, so this runs only on
    /// demand: `TRUST_CG_RUN_MEASUREMENT_TESTS=1 cargo test --release
    /// test_huge_function`.
    /// Measured: fast 94ms vs reference 34.7s (369x) at 2000 blocks.
    #[test]
    fn test_huge_function_identity_and_speed_2000_blocks() {
        if !matches!(
            std::env::var("TRUST_CG_RUN_MEASUREMENT_TESTS").as_deref(),
            Ok("1")
        ) {
            eprintln!(
                "large-scale measurement campaign not requested; \
                 set TRUST_CG_RUN_MEASUREMENT_TESTS=1 to run"
            );
            return;
        }

        run_synthetic_identity_and_speed(2000, 100);
    }

    #[test]
    fn test_out_of_range_preg_falls_back_identically() {
        // x86 encodings live at 512..=559 (in range); fabricate an encoding
        // beyond the bitset to force the fallback and confirm it matches the
        // reference (trivially — it IS the reference).
        let big = PReg::new(PREG_SET_BITS + 5);
        let mut func = make_function(vec![vec![
            preg_inst(0x2000, &[big], &[]),
            preg_copy(X1, X0),
            preg_inst(0x2001, &[X2], &[X1]),
        ]]);
        let mut reference = func.clone();
        let fast_result = post_ra_coalesce(&mut func);
        let ref_result = post_ra_coalesce_reference(&mut reference);
        assert_eq!(fast_result, ref_result);
        assert_funcs_identical(&func, &reference, "out-of-range preg fallback");
    }
}
