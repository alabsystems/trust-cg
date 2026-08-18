// trust-cg-verify/post_ra_spill_slots.rs - TV-6 post-RA aarch64 spill-slot dataflow validation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! TV-6 (second slice): spill-SLOT reaching-STORE validation of the FINAL
//! post-register-allocation, post-frame-lowering AArch64 stream
//! (`[TCG-A64-SPILL-SLOT]`).
//!
//! # What this closes (gap vs the reaching-DEF slice)
//!
//! The companion [`crate::post_ra_reaching_def`] slice validates that every
//! physical *register* read has a reaching *definition* — but it is register-only
//! by construction (its own doc calls memory/spill-slot dataflow "DEFERRED to a
//! later slice", and `inst_gen_reads` deliberately models only the MemOp BASE
//! register, never the stack slot the load transfers). So a spill materialization
//! that reloads a stack slot which was **never stored** (a dropped store) or that
//! reloads the **wrong slot** (a store/reload offset mismatch) sails through the
//! register check: the reload's destination register is trivially "defined" (the
//! LDR defines it) and its base register (SP) is seeded, so the reaching-def net
//! sees nothing wrong while the loaded VALUE is garbage — a silent miscompile.
//!
//! Spill stores/reloads are minted by the materializers in
//! `trust-cg-codegen/src/pipeline.rs` (`make_spill_load`/`make_spill_store` ~:1967,
//! `materialize_spilled_register_offset_mem` ~:2036, `materialize_spilled_store_pair`
//! ~:2274). Each spilled vreg becomes `STR Xn,[slot]` / `LDR Xn,[slot]` against a
//! `StackSlot`, which `frame::eliminate_frame_indices` later resolves to a
//! constant-offset `MemOp { base, offset }`. This slice re-derives, from the final
//! resolved stream, that no reload reads a stack slot the function itself has not
//! already written on every path from entry.
//!
//! # Property (one clean, sound thing)
//!
//! For every reload `LDR Rt,[SP,#k]` from a **tracked spill slot** `[SP,#k]`, there
//! is a store `STR _,[SP,#k]` to that same slot on EVERY control-flow path from the
//! function entry to the reload. A reload with no reaching store on some path is a
//! post-RA bug: the value consumed is whatever the (uninitialized-this-activation)
//! stack held. This is a forward MUST reaching-STORE dataflow, structurally
//! identical to the reaching-DEF fixpoint but over stack-slot LOCATIONS (constant
//! SP offsets) instead of registers.
//!
//! # Why it is false-WARN free (WARN-net discipline)
//!
//! False WARNs would mean flagging a reload that is actually correct — i.e.
//! flagging a slot that was legitimately initialized OUTSIDE the tracked region
//! (by the caller, the prologue, or via an alias). Every such avenue is closed by
//! a conservative bail; when in doubt the analysis DECLINES the whole function and
//! reports nothing. The bails (each also enforced as a hard DECLINE below):
//!
//! * **Base must be exactly SP.** Only `MemOp { base == SP }` accesses are
//!   tracked. FP/X29-relative addressing is where the frame/incoming-arg/callee-
//!   saved area lives (caller/prologue-initialized and MIXED with spills); the
//!   presence of ANY `MemOp { base == X29 }` DECLINES the function (a framed
//!   function whose spills are FP-relative is out of scope for this SP-only
//!   slice). NOTE this X29-decline is NOT what keeps the slice sound on its own:
//!   since the deep-slot SP preference in `frame::resolve_slot_operand`
//!   (`trust-cg-codegen/src/frame.rs`, `FrameIndexEliminator`), a FRAMED function
//!   can resolve deep spill slots to `(SP, off)` with no X29 MemOp anywhere.
//!   Soundness for those functions rests entirely on the SP-invariance bail
//!   below: any frame deep enough to trigger the SP form has
//!   `sp_adjustment > 0`, so its prologue contains a `SUB SP` (and `MOV X29,SP`
//!   / `STP` writeback) that DECLINES the function before any SP MemOp can be
//!   mis-modeled as a frameless spill slot. Do not relax that bail without
//!   restoring a framed-function guard here.
//! * **SP must be invariant and un-escaped.** `[SP,#k]` only names a single fixed
//!   address if SP never changes and no SP-derived pointer ever enters a GPR (from
//!   which an untracked store could alias `[SP,#k]`). Any instruction that uses SP
//!   as anything other than the base of a plain scalar load/store — a prologue/
//!   epilogue `SUB/ADD SP,..`, `MOV X29,SP`, a frame-address `ADD Xd,SP,#imm`, a
//!   pre/post-index writeback on SP, a split `[Rt, Special(SP), Imm]` form, or SP
//!   in `implicit_defs` — DECLINES. Any `is_call` (which clobbers scratch and
//!   only occurs in framed non-leaf functions) DECLINES. This nukes every framed
//!   function fail-safe; only genuinely SP-invariant frameless functions proceed.
//! * **Only unambiguous constant-offset single-register loads/stores are modeled.**
//!   A tracked store is one of `StrRI/StrbRI/StrhRI/STRWui/STRXui/STRSui/STRDui`;
//!   a tracked reload is one of `LdrRI/LdrbRI/LdrhRI/LdrsbRI/LdrshRI`. Any OTHER
//!   instruction that touches SP-relative memory — a pair `STP/LDP` (two slots at
//!   once), a register-offset `LdrRO/StrRO`, an LSE atomic (reads AND writes the
//!   slot), or any writeback form — DECLINES rather than be mis-modeled.
//! * **Only body-managed slots are tracked.** The location universe is exactly the
//!   set of constant SP offsets the function itself STORES to. A reload of an SP
//!   offset the body never stores is UNtracked and never flagged — it cannot be a
//!   dropped-spill bug we can attribute, and treating it as one would risk a false
//!   WARN on any ABI/caller-initialized SP datum. (Cost: a spill whose store is
//!   dropped so completely that the offset appears NOWHERE as a store is not
//!   caught by this slice; the wrong-offset and store-on-only-some-paths shapes
//!   are.) More than 64 distinct tracked offsets → DECLINE (bitset capacity).
//! * **Anything unmodeled DECLINES.** A non-final stream (a surviving `VReg`,
//!   `StackSlot`, `FrameIndex`, or `IncomingArg`), an out-of-range CFG edge, or a
//!   non-converging fixpoint yields ZERO reports — the checker must never report
//!   on a stream it cannot soundly model. Predecessors are recomputed from the
//!   successor graph rather than trusted from `MachBlock::preds`, and every
//!   reachable block is analyzed independently of `block_order`; stale auxiliary
//!   CFG metadata therefore cannot hide a store-free path or reload.
//!
//! In correct codegen every reload of a body-managed spill slot is dominated by
//! its store (that is what the spill materializer guarantees), so a clean stream
//! produces ZERO reports. The report set can only be non-empty if a store is
//! genuinely missing on a path — the bug class.
//!
//! # Enforcement
//!
//! Ships **ENFORCE** ([`AARCH64_SPILL_SLOT_DEFAULT`], env-downgradable via
//! `TCG_AARCH64_POST_RA_SPILL_SLOTS` = `off`|`warn`|`enforce`) after a 0-false-WARN
//! soak of ~2841 a64 fns (differential corpus 2778 + real rustc->bridge->a64
//! 63/22-progs) — exactly how [`crate::post_ra_reaching_def`] and
//! [`crate::post_regalloc_recheck`] were ratcheted. A reload of an un-stored /
//! wrong-offset spill slot now FAILS the a64 compile CLOSED. Runs ALONGSIDE the
//! reaching-def net (its own gate/tag/telemetry); it does not modify that check.

use std::collections::HashMap;
use std::collections::VecDeque;
use std::sync::atomic::{AtomicU64, Ordering};

use trust_cg_ir::aarch64_regs::{SP, X29};
use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, MachOperand, SpecialReg};

pub use crate::post_regalloc_recheck::PostRegallocRecheckMode;

/// Maximum number of distinct tracked spill-slot offsets (bitset width). A
/// function with more distinct SP-store offsets than this DECLINES — fail-safe,
/// and mirrors the fixed 64-location bound of the reaching-def slice.
const MAX_TRACKED_SLOTS: usize = 64;

// ---------------------------------------------------------------------------
// Access model: classify each instruction's relationship to SP-relative memory
// ---------------------------------------------------------------------------

/// Opcodes that STORE a single scalar register at a constant `[base,#imm]`
/// offset — the only store forms whose SP-relative slot this slice tracks.
fn is_tracked_store_opcode(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        StrRI | StrbRI | StrhRI | STRWui | STRXui | STRSui | STRDui
    )
}

/// Opcodes that LOAD a single scalar register from a constant `[base,#imm]`
/// offset — the only reload forms this slice read-checks.
fn is_tracked_load_opcode(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(op, LdrRI | LdrbRI | LdrhRI | LdrsbRI | LdrshRI)
}

/// How one instruction relates to tracked SP-relative memory.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SlotAccess {
    /// No SP-relative memory access we care about.
    None,
    /// A tracked store to `[SP,#offset]` (a gen).
    Store(i64),
    /// A tracked reload from `[SP,#offset]` (a read to check).
    Load(i64),
    /// Touches SP-relative (or FP-relative) memory in a form we cannot soundly
    /// model — the whole function must DECLINE.
    Decline,
}

/// Classify `inst`'s SP-relative memory access. Any FP/X29-relative access, or
/// any SP-relative access through a non-plain-scalar form (pair / register-offset
/// / writeback / atomic), yields [`SlotAccess::Decline`].
fn classify_slot_access(inst: &MachInst) -> SlotAccess {
    let mut sp_offset: Option<i64> = None;
    for operand in &inst.operands {
        if let MachOperand::MemOp { base, offset } = operand {
            if *base == X29 {
                // FP-relative addressing => this is a frame-pointer frame whose
                // spills are FP-relative; out of scope for the SP-only slice.
                return SlotAccess::Decline;
            }
            if *base == SP {
                // A single plain MemOp per access is expected; a second SP MemOp
                // on one instruction is an unmodeled shape.
                if sp_offset.is_some() {
                    return SlotAccess::Decline;
                }
                sp_offset = Some(*offset);
            }
        }
    }
    let Some(off) = sp_offset else {
        return SlotAccess::None;
    };
    let op = inst.opcode;
    // A tracked store writes memory and only writes it (excludes LSE atomics,
    // which both read and write the slot).
    if is_tracked_store_opcode(op) && inst.writes_memory() && !inst.reads_memory() {
        return SlotAccess::Store(off);
    }
    if is_tracked_load_opcode(op) && inst.reads_memory() && !inst.writes_memory() {
        return SlotAccess::Load(off);
    }
    // SP-relative memory access through a form we do not model (pair, register-
    // offset, writeback, atomic, ...): fail safe.
    SlotAccess::Decline
}

/// Whether SP is used in a way that makes SP-relative slot identity unsound:
/// SP modified, SP escaping into a GPR (frame-address materialization), a split
/// `Special(SP)` addressing/ALU form, SP in `implicit_defs`, or a call. The ONLY
/// sound appearance of SP is as the `base` of a plain `MemOp` (a distinct operand
/// variant, so it never trips this check).
fn sp_used_unsafely(inst: &MachInst) -> bool {
    if inst.is_call() {
        return true;
    }
    if inst.implicit_defs.contains(&SP) {
        return true;
    }
    inst.operands.iter().any(|operand| match operand {
        // Split addressing / ALU operand form of SP (e.g. `SUB SP,SP,#imm`,
        // `MOV X29,SP`, `ADD Xd,SP,#imm`, `[Rt, Special(SP), Imm]`).
        MachOperand::Special(SpecialReg::SP) => true,
        // SP as a bare register operand (never a plain load/store base, which is
        // the MemOp variant) — an ALU/move source or def touching SP.
        MachOperand::PReg(p) if *p == SP => true,
        _ => false,
    })
}

/// A stream is in the final, fully-lowered form this validator models only if no
/// operand is a pre-regalloc `VReg` or a pre-frame-lowering placeholder
/// (`StackSlot`/`FrameIndex`/`IncomingArg`). Any of these means the analysis
/// assumptions (all frame access is a resolved constant-offset `MemOp`) do not
/// hold, so we DECLINE.
fn stream_is_final(func: &MachFunction) -> bool {
    // Inspect the block table itself, not `block_order`: an omitted reachable
    // block must not be able to evade final-form validation.
    for block in &func.blocks {
        for &inst_id in &block.insts {
            let Some(inst) = func.insts.get(inst_id.0 as usize) else {
                return false;
            };
            for operand in &inst.operands {
                if matches!(
                    operand,
                    MachOperand::VReg(_)
                        | MachOperand::StackSlot(_)
                        | MachOperand::FrameIndex(_)
                        | MachOperand::IncomingArg(_)
                ) {
                    return false;
                }
            }
        }
    }
    true
}

// ---------------------------------------------------------------------------
// Forward MUST reaching-store fixpoint
// ---------------------------------------------------------------------------

/// The stored-slot bitset on entry to block `b`: the entry block starts EMPTY (no
/// spill slot is stored before the body runs); every other block is the
/// INTERSECTION of its reachable predecessors' out-sets (a slot is stored only if
/// stored on ALL paths).
fn block_in(
    b: usize,
    entry_idx: usize,
    preds: &[Vec<usize>],
    stored_out: &[u64],
    reachable: &[bool],
) -> u64 {
    if b == entry_idx {
        return 0;
    }
    let mut acc = u64::MAX;
    let mut any = false;
    for &p in &preds[b] {
        if reachable[p] {
            acc &= stored_out[p];
            any = true;
        }
    }
    // A reachable non-entry block always has a reachable predecessor; the empty
    // fallback is defensive and can never over-approximate the stored set.
    if any { acc } else { 0 }
}

/// Run the analysis over `func`. Returns `Some(violations)` (possibly empty) for a
/// stream we could soundly model, or `None` to DECLINE (non-final stream, framed
/// / SP-escaping function, unmodeled SP form, malformed CFG, or non-convergence)
/// — declining reports nothing.
fn analyze(func: &MachFunction) -> Option<Vec<SpillSlotViolation>> {
    if !stream_is_final(func) {
        return None;
    }
    let nblocks = func.blocks.len();
    if nblocks == 0 {
        return Some(Vec::new());
    }
    let entry_idx = func.entry.0 as usize;
    if entry_idx >= nblocks {
        return None;
    }

    // 1. Validate the successor graph and independently derive predecessors.
    // `MachBlock::preds` is auxiliary allocator metadata and can be stale; a
    // missing predecessor there must never turn a MUST intersection into a
    // false proof that a slot is initialized on every path.
    let mut preds = vec![Vec::new(); nblocks];
    for (b, block) in func.blocks.iter().enumerate() {
        for &succ in &block.succs {
            let s = succ.0 as usize;
            if s >= nblocks {
                return None;
            }
            preds[s].push(b);
        }
    }

    // 2. Reachability from entry over the validated successor graph.
    let mut reachable = vec![false; nblocks];
    let mut queue = VecDeque::new();
    reachable[entry_idx] = true;
    queue.push_back(func.entry);
    while let Some(bid) = queue.pop_front() {
        let block = func.blocks.get(bid.0 as usize)?;
        for &s in &block.succs {
            let si = s.0 as usize;
            if !reachable[si] {
                reachable[si] = true;
                queue.push_back(s);
            }
        }
    }

    // 3. Safety + slot-collection pre-pass. Any unsafe SP use or unmodeled SP
    //    access DECLINES; every distinct tracked STORE offset is assigned a bit.
    let mut offset_bit: HashMap<i64, u32> = HashMap::new();
    for (b, &is_reachable) in reachable.iter().enumerate() {
        if !is_reachable {
            continue;
        }
        for &inst_id in &func.blocks[b].insts {
            let inst = func.insts.get(inst_id.0 as usize)?;
            if sp_used_unsafely(inst) {
                return None;
            }
            match classify_slot_access(inst) {
                SlotAccess::Decline => return None,
                SlotAccess::Store(off) => {
                    if !offset_bit.contains_key(&off) {
                        let next = offset_bit.len();
                        if next >= MAX_TRACKED_SLOTS {
                            return None;
                        }
                        offset_bit.insert(off, next as u32);
                    }
                }
                SlotAccess::Load(_) | SlotAccess::None => {}
            }
        }
    }
    // Nothing body-managed to track: analyzed, trivially clean.
    if offset_bit.is_empty() {
        return Some(Vec::new());
    }

    // 4. Per-block gen_bits = union of tracked-store bits.
    let bit_of = |off: i64| -> Option<u64> { offset_bit.get(&off).map(|&b| 1u64 << b) };
    let mut gen_bits = vec![0u64; nblocks];
    for b in 0..nblocks {
        if !reachable[b] {
            continue;
        }
        let mut g = 0u64;
        for &inst_id in &func.blocks[b].insts {
            let inst = &func.insts[inst_id.0 as usize];
            if let SlotAccess::Store(off) = classify_slot_access(inst)
                && let Some(m) = bit_of(off)
            {
                g |= m;
            }
        }
        gen_bits[b] = g;
    }

    // 5. Forward MUST fixpoint. Non-entry out-sets start at TOP (all stored) so a
    //    not-yet-computed back-edge predecessor never spuriously narrows a loop
    //    header; intersection can only clear bits, so it converges.
    let mut stored_out = vec![u64::MAX; nblocks];
    stored_out[entry_idx] = gen_bits[entry_idx];
    let max_iters = nblocks.saturating_mul(MAX_TRACKED_SLOTS).saturating_add(8);
    let mut iters = 0usize;
    loop {
        let mut changed = false;
        // Iterate the authoritative block table, not `block_order`: an omitted
        // reachable block must still participate in the fixed point.
        for b in 0..nblocks {
            if !reachable[b] {
                continue;
            }
            let in_b = block_in(b, entry_idx, &preds, &stored_out, &reachable);
            let new_out = in_b | gen_bits[b];
            if new_out != stored_out[b] {
                stored_out[b] = new_out;
                changed = true;
            }
        }
        iters += 1;
        if !changed {
            break;
        }
        if iters > max_iters {
            // Non-convergence (should be unreachable): decline, never flag.
            return None;
        }
    }

    // 6. Per-instruction reload check. As above, walk every reachable block in
    // the authoritative block table rather than trusting `block_order`.
    let mut violations = Vec::new();
    for b in 0..nblocks {
        if !reachable[b] {
            continue;
        }
        let bid = trust_cg_ir::BlockId(b as u32);
        let mut cur = block_in(b, entry_idx, &preds, &stored_out, &reachable);
        for (inst_pos, &inst_id) in func.blocks[b].insts.iter().enumerate() {
            let inst = &func.insts[inst_id.0 as usize];
            match classify_slot_access(inst) {
                SlotAccess::Load(off) => {
                    // Only body-managed (ever-stored) slots are tracked; a reload
                    // of an untracked offset is not attributable and not flagged.
                    if let Some(m) = bit_of(off)
                        && (cur & m) == 0
                    {
                        violations.push(SpillSlotViolation {
                                kind: SpillSlotViolationKind::ReloadWithoutReachingStore,
                                detail: format!(
                                    "block {} inst #{} ({:?}): reload from spill slot [SP,#{}] has no \
                                     reaching store on every path from entry (dropped/mismatched spill \
                                     store — the reloaded value is uninitialized this activation)",
                                    bid.0, inst_pos, inst.opcode, off
                                ),
                            });
                    }
                }
                SlotAccess::Store(off) => {
                    if let Some(m) = bit_of(off) {
                        cur |= m;
                    }
                }
                SlotAccess::None | SlotAccess::Decline => {}
            }
        }
    }
    Some(violations)
}

// ---------------------------------------------------------------------------
// Violations
// ---------------------------------------------------------------------------

/// Which spill-slot property broke (one kind in this slice).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpillSlotViolationKind {
    /// A reload reads a spill slot with no reaching store on some path.
    ReloadWithoutReachingStore,
}

impl SpillSlotViolationKind {
    /// Greppable tag for the diagnostic line.
    pub fn tag(self) -> &'static str {
        match self {
            Self::ReloadWithoutReachingStore => "reload-without-reaching-store",
        }
    }
}

/// A single spill-slot violation. In ENFORCE mode any one fails the compile.
#[derive(Debug, Clone)]
pub struct SpillSlotViolation {
    /// Which property broke.
    pub kind: SpillSlotViolationKind,
    /// Human-readable diagnostic (block / inst index / opcode / slot offset).
    pub detail: String,
}

// ---------------------------------------------------------------------------
// Mode + telemetry
// ---------------------------------------------------------------------------

/// Default mode for the aarch64 spill-slot net: ENFORCE, after its zero-hit
/// corpus soak, exactly as the reaching-def net and structural recheck were.
pub const AARCH64_SPILL_SLOT_DEFAULT: PostRegallocRecheckMode = PostRegallocRecheckMode::Enforce;

/// Resolve the active mode from `TCG_AARCH64_POST_RA_SPILL_SLOTS`
/// (`off`|`warn`|`enforce`, or `0`|`1`|`2`), defaulting to
/// [`AARCH64_SPILL_SLOT_DEFAULT`]. The environment knob remains as an explicit
/// diagnostic downgrade/disable escape hatch; absent it, violations fail closed.
pub fn spill_slot_mode() -> PostRegallocRecheckMode {
    match std::env::var("TCG_AARCH64_POST_RA_SPILL_SLOTS").as_deref() {
        Ok("off") | Ok("0") => PostRegallocRecheckMode::Off,
        Ok("enforce") | Ok("2") => PostRegallocRecheckMode::Enforce,
        Ok("warn") | Ok("1") => PostRegallocRecheckMode::Warn,
        _ => AARCH64_SPILL_SLOT_DEFAULT,
    }
}

/// Process-wide count of spill-slot violations observed (warn or enforce).
static VIOLATION_HITS: AtomicU64 = AtomicU64::new(0);
/// Streams the net could soundly MODEL (final, frameless, SP-invariant form).
static STREAMS_ANALYZED: AtomicU64 = AtomicU64::new(0);
/// Streams the net DECLINED (non-final / framed / SP-escaping / unmodeled).
static STREAMS_DECLINED: AtomicU64 = AtomicU64::new(0);

/// Total spill-slot violations observed by this process (soak telemetry).
pub fn spill_slot_hit_count() -> u64 {
    VIOLATION_HITS.load(Ordering::Relaxed)
}

/// (analyzed, declined) stream counts — how much of the corpus the net actually
/// modeled vs conservatively skipped. On a frame-pointer-default target most
/// functions DECLINE (their spills are FP-relative); the analyzed set is the
/// frameless / red-zone-leaf functions whose spills are SP-relative.
pub fn coverage_counts() -> (u64, u64) {
    (
        STREAMS_ANALYZED.load(Ordering::Relaxed),
        STREAMS_DECLINED.load(Ordering::Relaxed),
    )
}

fn record_violation(function_name: &str, detail: &str, mode: PostRegallocRecheckMode) {
    VIOLATION_HITS.fetch_add(1, Ordering::Relaxed);
    let tag = match mode {
        PostRegallocRecheckMode::Enforce => "[TCG-A64-SPILL-SLOT-FAIL]",
        _ => "[TCG-A64-SPILL-SLOT-WARN]",
    };
    eprintln!("{tag} arch=aarch64 fn={function_name}: {detail}");
}

// ---------------------------------------------------------------------------
// Public entry points
// ---------------------------------------------------------------------------

/// Pure entry point: the spill-slot violations in `func`, or an EMPTY list for a
/// clean stream OR a stream this validator declines to model. Side-effect free.
pub fn check(func: &MachFunction) -> Vec<SpillSlotViolation> {
    analyze(func).unwrap_or_default()
}

/// Driver: apply the resolved mode.
/// * `Off` -> `None` immediately.
/// * All violations are recorded (telemetry) regardless of mode.
/// * `Enforce` -> the FIRST violation is returned so the caller fails closed;
///   `Warn` -> `None` (telemetry only, no verdict change).
pub fn evaluate(func: &MachFunction, mode: PostRegallocRecheckMode) -> Option<SpillSlotViolation> {
    if mode == PostRegallocRecheckMode::Off {
        return None;
    }
    let debug = std::env::var_os("TCG_AARCH64_POST_RA_SPILL_SLOTS_DEBUG").is_some();
    let violations = match analyze(func) {
        Some(v) => {
            STREAMS_ANALYZED.fetch_add(1, Ordering::Relaxed);
            if debug {
                eprintln!(
                    "[A64-SS-DEBUG] fn={} outcome=analyzed viol={}",
                    func.name,
                    v.len()
                );
            }
            v
        }
        None => {
            STREAMS_DECLINED.fetch_add(1, Ordering::Relaxed);
            if debug {
                eprintln!("[A64-SS-DEBUG] fn={} outcome=declined", func.name);
            }
            return None;
        }
    };
    for v in &violations {
        record_violation(&func.name, &v.detail, mode);
    }
    if mode == PostRegallocRecheckMode::Enforce {
        violations.into_iter().next()
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::aarch64_regs::{SP, X0, X1, X9, X29};
    use trust_cg_ir::{InstId, PReg, Signature};

    fn store(base: PReg, offset: i64) -> MachInst {
        MachInst::new(
            AArch64Opcode::StrRI,
            vec![MachOperand::PReg(X0), MachOperand::MemOp { base, offset }],
        )
    }

    fn load(base: PReg, offset: i64) -> MachInst {
        MachInst::new(
            AArch64Opcode::LdrRI,
            vec![MachOperand::PReg(X9), MachOperand::MemOp { base, offset }],
        )
    }

    fn single_block(name: &str, insts: Vec<MachInst>) -> MachFunction {
        let mut f = MachFunction::new(name.to_string(), Signature::new(vec![], vec![]));
        let entry = f.entry;
        for inst in insts {
            let id = InstId(f.insts.len() as u32);
            f.insts.push(inst);
            f.append_inst(entry, id);
        }
        f
    }

    #[test]
    fn store_then_reload_passes() {
        // str x0,[sp,#-16] ; ldr x9,[sp,#-16] — slot stored before its reload.
        let f = single_block("good", vec![store(SP, -16), load(SP, -16)]);
        assert!(check(&f).is_empty());
        assert!(evaluate(&f, PostRegallocRecheckMode::Warn).is_none());
        assert!(evaluate(&f, PostRegallocRecheckMode::Enforce).is_none());
    }

    #[test]
    fn reload_without_reaching_store_refutes() {
        // REFUTATION: ldr x9,[sp,#-16] BEFORE str x0,[sp,#-16]. The store makes
        // -16 a tracked (body-managed) slot; the reload precedes it -> no reaching
        // store at the reload.
        let f = single_block("bad", vec![load(SP, -16), store(SP, -16)]);
        let vs = check(&f);
        assert_eq!(vs.len(), 1);
        assert_eq!(
            vs[0].kind,
            SpillSlotViolationKind::ReloadWithoutReachingStore
        );
        assert!(evaluate(&f, PostRegallocRecheckMode::Enforce).is_some());
        assert!(evaluate(&f, PostRegallocRecheckMode::Warn).is_none());
        assert!(evaluate(&f, PostRegallocRecheckMode::Off).is_none());
    }

    #[test]
    fn wrong_offset_reload_refutes() {
        // store to -16 (tracked), then reload from -8 which is ALSO stored later
        // (so -8 is tracked) but not before this reload -> refutes. Mirrors a
        // store/reload offset-mismatch materialization bug.
        let f = single_block(
            "wrong_off",
            vec![store(SP, -16), load(SP, -8), store(SP, -8)],
        );
        assert_eq!(check(&f).len(), 1);
    }

    #[test]
    fn reload_of_never_stored_slot_not_flagged() {
        // ldr x9,[sp,#-16] with NO store to -16 anywhere: -16 is untracked (not
        // body-managed) and is NOT flagged — the FP-safety boundary (could be an
        // ABI/caller datum; a fully-dropped store is a documented coverage gap).
        let f = single_block("untracked", vec![load(SP, -16)]);
        assert!(check(&f).is_empty());
    }

    /// Diamond b0 -> {b1, b2} -> b3. `store_in_b2` controls whether the b2 path
    /// stores [sp,#-16] before the join reloads it.
    fn diamond(store_in_b2: bool) -> MachFunction {
        let mut f = MachFunction::new("diamond".to_string(), Signature::new(vec![], vec![]));
        let b0 = f.entry;
        let b1 = f.create_block();
        let b2 = f.create_block();
        let b3 = f.create_block();
        let i1 = InstId(f.insts.len() as u32);
        f.insts.push(store(SP, -16));
        f.append_inst(b1, i1);
        if store_in_b2 {
            let i2 = InstId(f.insts.len() as u32);
            f.insts.push(store(SP, -16));
            f.append_inst(b2, i2);
        }
        let i3 = InstId(f.insts.len() as u32);
        f.insts.push(load(SP, -16));
        f.append_inst(b3, i3);
        f.add_edge(b0, b1);
        f.add_edge(b0, b2);
        f.add_edge(b1, b3);
        f.add_edge(b2, b3);
        f
    }

    #[test]
    fn diamond_store_on_one_path_refutes() {
        // [sp,#-16] stored on the b1 path only; along b0->b2->b3 it is unstored.
        let f = diamond(false);
        assert_eq!(check(&f).len(), 1);
    }

    #[test]
    fn diamond_store_on_all_paths_passes() {
        // stored on BOTH incoming paths: no violation (MUST analysis).
        let f = diamond(true);
        assert!(check(&f).is_empty());
    }

    #[test]
    fn stale_predecessors_cannot_hide_store_free_path() {
        // The executable successor graph is the same bad diamond as above, but
        // corrupt the join's auxiliary predecessor list so it mentions only the
        // storing arm. A checker that trusts `preds` falsely proves the reload
        // initialized; the independent successor-derived graph must still catch
        // the store-free b2 path.
        let mut f = diamond(false);
        let join = f.blocks[f.entry.0 as usize].succs[0];
        let join = f.blocks[join.0 as usize].succs[0];
        let storing_arm = f.blocks[f.entry.0 as usize].succs[0];
        f.blocks[join.0 as usize].preds = vec![storing_arm];
        assert_eq!(check(&f).len(), 1);
    }

    #[test]
    fn block_order_omission_cannot_hide_reload() {
        // `block_order` is layout metadata, not the authoritative CFG. Omitting
        // the reachable entry block must not suppress its reload-before-store.
        let mut f = single_block("omitted", vec![load(SP, -16), store(SP, -16)]);
        f.block_order.clear();
        assert_eq!(check(&f).len(), 1);
    }

    #[test]
    fn out_of_range_successor_declines() {
        // A malformed edge cannot be ignored while the rest of the stream is
        // certified. Exercise the internal result to distinguish decline from
        // a modeled-clean function.
        let mut f = single_block("bad_edge", vec![load(SP, -16), store(SP, -16)]);
        f.blocks[f.entry.0 as usize]
            .succs
            .push(trust_cg_ir::BlockId(u32::MAX));
        assert!(analyze(&f).is_none());
    }

    #[test]
    fn fp_base_reload_declines() {
        // Same reload-before-store shape but FP/X29-relative: framed function,
        // out of scope -> DECLINE (report nothing), never a false WARN.
        let f = single_block("fp_frame", vec![load(X29, -16), store(X29, -16)]);
        assert!(check(&f).is_empty());
        // Contrast: the identical SP-relative shape DOES refute.
        let f_sp = single_block("sp_frame", vec![load(SP, -16), store(SP, -16)]);
        assert_eq!(check(&f_sp).len(), 1);
    }

    #[test]
    fn sp_escape_declines() {
        // An `ADD x0, SP, #16` materializes an SP-derived pointer into a GPR: a
        // later untracked store could alias any slot -> DECLINE the whole function
        // even though the reload-before-store would otherwise refute.
        let add = MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::Special(SpecialReg::SP),
                MachOperand::Imm(16),
            ],
        );
        let f = single_block("sp_escape", vec![add, load(SP, -16), store(SP, -16)]);
        assert!(check(&f).is_empty());
    }

    #[test]
    fn unmodeled_pair_store_declines() {
        // A pair STP to [sp,#-16] writes two slots at once — an unmodeled form.
        // Its presence DECLINES rather than being mis-modeled.
        let stp = MachInst::new(
            AArch64Opcode::StpRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::MemOp {
                    base: SP,
                    offset: -16,
                },
            ],
        );
        let f = single_block("pair", vec![stp, load(SP, -16)]);
        assert!(check(&f).is_empty());
    }

    #[test]
    fn call_declines() {
        // A call only occurs in framed non-leaf functions; it clobbers scratch and
        // is a conservative memory barrier -> DECLINE.
        let call = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("f".to_string())],
        );
        let f = single_block("has_call", vec![call, load(SP, -16), store(SP, -16)]);
        assert!(check(&f).is_empty());
    }

    #[test]
    fn surviving_vreg_declines() {
        use trust_cg_ir::{RegClass, VReg};
        let inst = MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                MachOperand::MemOp {
                    base: SP,
                    offset: -16,
                },
            ],
        );
        let f = single_block("vreg", vec![inst, load(SP, -16)]);
        assert!(check(&f).is_empty());
    }

    #[test]
    fn mode_default_is_enforce() {
        assert_eq!(AARCH64_SPILL_SLOT_DEFAULT, PostRegallocRecheckMode::Enforce);
    }
}
