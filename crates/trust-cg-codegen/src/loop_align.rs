// trust-cg-codegen/loop_align.rs - Emission-time 32-byte alignment of
// innermost loop headers
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Static 32-byte alignment of innermost-loop-head blocks at emission.
//!
//! # Why
//!
//! Apple Silicon fetches instructions in aligned 32-byte lines. A short hot
//! loop whose body STRADDLES a 32-byte boundary costs an extra fetch line
//! every iteration; the same loop within one line does not. Because trust-cg
//! (before this pass) laid blocks out at whatever byte offset the preceding
//! code happened to end on, a 5-instruction inner loop landed on either side
//! of that boundary by lottery — measured at 2-20% swings on fetch-bound
//! scalar loops (the sieve diagnosis: identical opcode multisets, layout-only
//! deltas, 0.68x from a profile-guided reorder whose entire effect was moving
//! the clear-loop off a fetch boundary). clang plays the same card via loop
//! `.p2align 5` on AArch64. This pass captures that win statically.
//!
//! # What it does
//!
//! Immediately before branch resolution (the point where `block_order` and
//! every instruction are FINAL), walk the layout and, for every block that is
//! an INNERMOST loop header, insert up to 7 [`AArch64Opcode::AlignNop`]
//! instructions (full alignment — no max-skip forfeits; see MAX_PAD_BYTES) at
//! the very END of the layout-predecessor block so the header's first
//! instruction starts on a function-relative 32-byte boundary. The module
//! emitters then place any function containing an aligned header on a 32-byte
//! section boundary ([`trust_cg_ir::MachFunction::text_align_log2`]), making
//! the function-relative alignment absolute in the linked image.
//!
//! # Soundness argument (why NOP padding at a block seam preserves semantics)
//!
//! An [`AArch64Opcode::AlignNop`] is a REAL instruction in the arena and the
//! block instruction lists, so every downstream byte-offset derivation counts
//! it exactly once: branch resolution (`resolve_branches`), the encoder, the
//! EH `InstId -> byte` re-derivation, and the resolved-stream CFG
//! reconstruction all walk the same lists. There is no side table to drift.
//!
//! Execution-wise the padding is placed ONLY at the end of the block laid out
//! immediately before the loop header. Two cases:
//!
//! 1. The predecessor block falls through (its last instruction is not an
//!    unconditional control transfer): the NOPs execute once per fallthrough
//!    entry into the loop — architecturally no-ops, at most 3.
//! 2. The predecessor ends in a hard terminator (`B`/`Ret`/`Brk`/...): the
//!    NOPs are dead bytes, never executed.
//!
//! No branch ever lands ON the padding: branch targets are block starts,
//! which lie AFTER any padding by construction. The one pre-resolved
//! intra-block immediate shape in the final stream — the `B.cond +2; BRK`
//! guard skip — can target "one past the BRK"; if the BRK is the
//! predecessor's last instruction that target becomes the first inserted NOP,
//! which executes the NOP run and falls through into the header: the same
//! successor state as before, three no-ops later. (The CFG reconstructor's
//! `last_real_inst` fallthrough derivation explicitly skips trailing
//! `AlignNop`s so dead padding after a hard terminator does not fabricate a
//! fallthrough edge.)
//!
//! # Innermost-header detection (layout spans)
//!
//! At this point in the pipeline the CFG side tables may be stale, but the
//! final layout is authoritative. A block H is a BACKEDGE TARGET if some
//! branch in a block at layout position >= H's position targets H. Its SPAN
//! runs to the layout position of its last such source. H is INNERMOST if no
//! other backedge target's span nests strictly inside H's span. For the
//! natural contiguous loop layouts our layout passes produce this equals loop
//! innermost-ness; for scattered layouts it degrades to a heuristic — which
//! is fine, because alignment choice is PERF-ONLY and can never miscompile.
//!
//! # Seam gate (executed-NOP control)
//!
//! Padding at a fallthrough seam is executed code. When the seam lies INSIDE
//! an enclosing cycle — some backedge span contains both the predecessor and
//! the head — the NOP run executes once per iteration of that cycle, not once
//! per loop entry. A head is therefore GATED (left unpadded, riding the
//! placement lottery) when its seam is inside an enclosing cycle AND its own
//! cycle's layout span exceeds [`SEAM_GATE_MAX_SPAN_BYTES`] (fetch-line
//! alignment cannot pay on a huge body; the measured case is Queens'
//! fully-unrolled backtracking body, whose 8 retry-backedge heads put 3-6
//! NOPs each on the recursion-success path — -2.4%). Tight nested loops
//! (sieve/chomp/misr, spans well under the threshold) stay padded: one NOP
//! run per outer iteration buys trip-count-many aligned inner iterations.
//!
//! # Kill switches
//!
//! `TCG_NO_LOOP_HEAD_ALIGN=1` disables the pass entirely; the emitted objects
//! are then byte-identical to a build without this pass.
//! `TCG_LOOP_ALIGN_NO_SEAM_GATE=1` restores the ungated pad-every-
//! fallthrough-seam policy; `TCG_LOOP_ALIGN_SEAM_SPAN=<bytes>` overrides the
//! span threshold; `TCG_LOOP_ALIGN_MAX_SKIP=<bytes>` overrides the max-skip;
//! `TCG_LOOP_ALIGN_IN_CYCLE_PAD=<bytes>` overrides the in-cycle pad budget
//! (28 restores the pre-budget policy); `TCG_LOOP_ALIGN_NO_FORFEIT_PIN=1`
//! stops requesting 32-byte FUNCTION placement for a loop-bearing function
//! whose heads all forfeited their padding (see the end of
//! [`align_innermost_loop_heads`]).

use std::collections::BTreeMap;

use trust_cg_ir::{AArch64Opcode, BlockId, MachFunction, MachInst, MachOperand};

/// Alignment target in bytes: the Apple Silicon fetch-line size.
const LOOP_HEAD_ALIGN_BYTES: u32 = 32;

/// Maximum padding inserted per header: 28 bytes = FULL alignment (any
/// header at most one word past a boundary still pads), i.e. no max-skip
/// forfeits. Measured (interleaved min+med best-of-13, 10-program mover set)
/// against the earlier clang-style 12-byte skip: misr med -7%, Treesort
/// -6..-11%, chomp -2..-3%, sieve -1.5%, Puzzle -1%, vs only Quicksort
/// +2..3%, Towers +1.5%, dry +0.8% — net geomean positive on both stats.
/// The 12-byte policy left FORFEITED heads (misr: 11 of them, pads 16..28)
/// riding a lottery that every unrelated codegen change reshuffles; full
/// padding makes every fallthrough-seam header deterministic. The cost is at
/// most 7 executed NOPs per loop ENTRY on fallthrough seams (never per
/// iteration).
const MAX_PAD_BYTES: u32 = 28;

/// Effective max-skip: `TCG_LOOP_ALIGN_MAX_SKIP=<bytes>` overrides
/// [`MAX_PAD_BYTES`] for A/B experiments (e.g. 28 = full alignment of every
/// fallthrough-seam header; a header one word past a boundary needs 28 bytes).
/// Values are clamped to word multiples in [0, 28]. Cached per process.
fn max_pad_bytes() -> u32 {
    static MAX: std::sync::OnceLock<u32> = std::sync::OnceLock::new();
    *MAX.get_or_init(|| {
        std::env::var("TCG_LOOP_ALIGN_MAX_SKIP")
            .ok()
            .and_then(|v| v.parse::<u32>().ok())
            .map(|v| (v.min(28) / 4) * 4)
            .unwrap_or(MAX_PAD_BYTES)
    })
}

/// `log2(LOOP_HEAD_ALIGN_BYTES)` for [`MachFunction::text_align_log2`].
const LOOP_HEAD_ALIGN_LOG2: u8 = 5;

/// Seam gate span threshold: a head whose own cycle spans MORE than this many
/// layout bytes gets no padding when its seam lies inside an enclosing cycle
/// (see [`align_innermost_loop_heads`], "seam gate"). 32-byte alignment is a
/// fetch-line optimization: a loop occupying N fetch lines pays at most 1/N
/// extra lines per iteration from misalignment, so past a handful of lines
/// the head's line position is noise — while padding a seam INSIDE a hot
/// enclosing cycle costs executed NOPs every iteration of that cycle
/// (measured: -2.4% on amplified Stanford/Queens, whose fully-unrolled
/// backtracking body has 8 retry-backedge heads with ~900-byte spans and the
/// padding on the recursion-success fallthrough path). 256 bytes = 8 fetch
/// lines; every measured tight-loop win (sieve/chomp/misr) spans well under
/// this, every measured unrolled-body loss spans well over it.
const SEAM_GATE_MAX_SPAN_BYTES: u32 = 256;

/// Maximum padding admitted at a seam that lies INSIDE an enclosing cycle.
/// Those NOPs are executed once per pass through that cycle, so the pad size
/// is a recurring cost weighed against at most one saved fetch line per
/// iteration of the head's own loop. 8 bytes = at most 2 executed NOPs.
/// Measured on Stanford/Quicksort (pads of 28/28/20/16 at in-cycle seams,
/// 18 executed NOPs in the hot function): 1.078 min / 1.184 trimmed vs clang
/// with them, 0.870 / 0.824 without. Entry-only seams keep the full
/// [`MAX_PAD_BYTES`] budget — their NOPs run once per loop entry.
const IN_CYCLE_MAX_PAD_BYTES: u32 = 8;

/// `TCG_LOOP_ALIGN_IN_CYCLE_PAD=<bytes>` overrides
/// [`IN_CYCLE_MAX_PAD_BYTES`] for A/B experiments (28 restores the
/// pre-budget pad-anything-under-the-span-threshold policy). Cached.
fn in_cycle_max_pad_bytes() -> u32 {
    static V: std::sync::OnceLock<u32> = std::sync::OnceLock::new();
    *V.get_or_init(|| {
        std::env::var("TCG_LOOP_ALIGN_IN_CYCLE_PAD")
            .ok()
            .and_then(|v| v.parse::<u32>().ok())
            .map(|v| (v.min(28) / 4) * 4)
            .unwrap_or(IN_CYCLE_MAX_PAD_BYTES)
    })
}

/// Effective seam-gate span threshold: `TCG_LOOP_ALIGN_SEAM_SPAN=<bytes>`
/// overrides [`SEAM_GATE_MAX_SPAN_BYTES`] for A/B experiments. Cached per
/// process.
fn seam_gate_max_span_bytes() -> u32 {
    static MAX: std::sync::OnceLock<u32> = std::sync::OnceLock::new();
    *MAX.get_or_init(|| {
        std::env::var("TCG_LOOP_ALIGN_SEAM_SPAN")
            .ok()
            .and_then(|v| v.parse::<u32>().ok())
            .unwrap_or(SEAM_GATE_MAX_SPAN_BYTES)
    })
}

/// Seam-gate kill switch: `TCG_LOOP_ALIGN_NO_SEAM_GATE=1` restores the
/// ungated policy (pad every fallthrough-seam head) for A/B measurement.
/// Cached per process.
fn seam_gate_disabled() -> bool {
    static DISABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *DISABLED.get_or_init(|| std::env::var_os("TCG_LOOP_ALIGN_NO_SEAM_GATE").is_some())
}

/// Kill switch: `TCG_NO_LOOP_HEAD_ALIGN=1` disables loop-head alignment.
/// Cached per process (matches every other TCG_* emission switch).
fn loop_head_align_disabled() -> bool {
    static DISABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *DISABLED.get_or_init(|| std::env::var_os("TCG_NO_LOOP_HEAD_ALIGN").is_some())
}

/// EXPERIMENT KNOB: `TCG_LOOP_ALIGN_NO_FUNC_PLACEMENT=1` keeps loop-head NOP
/// padding but stops raising [`MachFunction::text_align_log2`], so the function
/// itself is NOT pinned to a 32-byte section boundary.
///
/// This exists to DECOMPOSE the pass's two independent effects, which every
/// prior measurement conflated because the single `TCG_NO_LOOP_HEAD_ALIGN`
/// switch turns off both at once:
///   (a) intra-function padding, which costs executed NOPs, and
///   (b) inter-function PLACEMENT, which costs nothing to execute but decides
///       where every loop in the function lands modulo 32.
///
/// The witness that forced the split (n=41, three arms): Shootout/sieve emits 4
/// pad NOPs and runs 8.3% SLOWER than with the pass off — but a build that
/// refuses all four pads (0 NOPs, i.e. the SAME padding decision as pass-off) is
/// still 0.9% slower than pass-off. Four NOPs cannot explain a 9-point gap, so
/// the effect had to be (b).
///
/// DECOMPOSITION (n=31, arms base / nopad / noplace, ratios vs base, min/med):
///
/// | program    | nopad (both off) | noplace (padding kept) | attribution     |
/// |------------|------------------|------------------------|-----------------|
/// | sieve      | 0.9182 / 0.9130  | 0.9093 / 0.9036        | ~all PLACEMENT  |
/// | Treesort   | 1.0973 / 1.0493  | 1.2107 / 1.1291        | ~all PLACEMENT  |
/// | Quicksort  | 0.8622 / 0.8203  | 1.0547 / 1.0692        | ~all PADDING    |
/// | queens     | 0.9685 / 0.9685  | 0.9813 / 0.9808        | ~60% placement  |
/// | Bubblesort | 0.9766 / 1.0006  | 0.9860 / 1.0057        | ~60% placement  |
///
/// Read the signs: placement COSTS sieve 9% and queens 3%, and BUYS Treesort
/// 21%; padding costs Quicksort 14%. Both mechanisms are real, both are large,
/// and which one wins is per-program with no static predictor — over the full
/// 65-program corpus the whole pass is a wash (geomean min 1.0008 / med 1.0018),
/// so it is a high-variance lottery with ~zero expected value rather than a
/// consistent win or a consistent loss.
///
/// Consequences for anyone touching this file:
///  * Do NOT read a per-program alignment delta as evidence about padding
///    policy — measure with this knob first to learn which half moved.
///  * Any code-size change anywhere in the compiler reshuffles this lottery,
///    which is why unrelated levers keep showing +/-1-2% per-program swings that
///    invert under `TCG_NO_LOOP_HEAD_ALIGN=1`. Always run that control before
///    attributing a regression to the transform under test.
///  * A principled fix needs per-function execution frequency (the PGO arc),
///    not another static heuristic. A cost-model attempt built on the
///    padding-only reading — cumulative per-cycle pad budget, do-no-harm
///    displacement check, self-recursive entry tier — was measured and
///    FALSIFIED (worse on sieve/Quicksort/queens/misr, better only on
///    Treesort); it is not in the tree.
///
/// Unset, this knob changes nothing: verified byte-identical objects against the
/// pre-knob compiler across all 65 importable SingleSource programs.
fn func_placement_disabled() -> bool {
    static DISABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *DISABLED.get_or_init(|| std::env::var_os("TCG_LOOP_ALIGN_NO_FUNC_PLACEMENT").is_some())
}

/// Real-cycle filter kill switch: `TCG_LOOP_ALIGN_NO_CYCLE_CHECK=1` restores
/// the legacy "any layout-backward branch is a backedge" span derivation
/// (which also padded the REJOIN targets of cold-sunk guard blocks — see
/// [`backedge_spans`]). Cached per process.
fn cycle_check_disabled() -> bool {
    static DISABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *DISABLED.get_or_init(|| std::env::var_os("TCG_LOOP_ALIGN_NO_CYCLE_CHECK").is_some())
}

/// Align innermost loop headers to 32 bytes by inserting `AlignNop` padding
/// at layout seams. Must run when `block_order` and the instruction stream
/// are FINAL, immediately before branch resolution — any instruction
/// inserted or removed after this pass invalidates the computed alignment
/// (though never correctness: `AlignNop`s are ordinary instructions to every
/// later phase).
///
/// Returns `true` if at least one innermost header is function-relative
/// 32-byte aligned on exit (padding inserted, or already on a boundary), in
/// which case `func.text_align_log2` has been raised so the object emitters
/// place the function itself on a 32-byte boundary.
pub fn align_innermost_loop_heads(func: &mut MachFunction) -> bool {
    if loop_head_align_disabled() {
        return false;
    }
    // Single-block functions have no layout seam to pad (the entry block
    // starts at function offset 0 and is aligned by function placement).
    if func.block_order.len() < 2 {
        return false;
    }

    let (spans, had_backward) = backedge_spans(func);
    if spans.is_empty() {
        // The real-cycle filter dropped EVERY span (a no-real-cycle function
        // whose backward branches are all cold-guard rejoins). The executed
        // NOP pads go away, but keep the legacy 32-byte FUNCTION placement:
        // hot self-RECURSIVE functions (Stanford/Treesort `Insert`/
        // `Checktree`) re-enter at the function entry on every call, and
        // un-pinning that entry was measured to cost what the pad removal
        // saved. Placement costs only dead inter-function bytes.
        if had_backward {
            if !func_placement_disabled() {
                func.text_align_log2 = func.text_align_log2.max(LOOP_HEAD_ALIGN_LOG2);
            }
            return true;
        }
        return false;
    }

    // Pre-padding byte offset of each layout position (padding never changes
    // a cycle's intrinsic byte length, so span sizes are computed on the
    // unpadded layout; boundary alignment below uses the running padded
    // `offset` instead).
    let mut pre_off: Vec<u32> = Vec::with_capacity(func.block_order.len() + 1);
    {
        let mut off = 0u32;
        for &bid in &func.block_order {
            pre_off.push(off);
            for &iid in &func.blocks[bid.0 as usize].insts {
                if !func.insts[iid.0 as usize].is_pseudo() {
                    off += 4;
                }
            }
        }
        pre_off.push(off);
    }

    // Walk the layout accumulating byte offsets (non-pseudo instructions are
    // exactly 4 bytes each — the same rule as `resolve_branches` and the
    // encoder), inserting padding as we go so later offsets include earlier
    // padding. Single forward pass: padding before block i only changes
    // offsets of blocks >= i.
    let mut any_aligned = false;
    let mut offset: u32 = 0;
    for layout_idx in 0..func.block_order.len() {
        let block_id = func.block_order[layout_idx];

        // The entry block is never padded: it starts at function offset 0,
        // which function placement itself aligns.
        if layout_idx > 0 && spans.contains_key(&layout_idx) {
            let pad =
                (LOOP_HEAD_ALIGN_BYTES - (offset % LOOP_HEAD_ALIGN_BYTES)) % LOOP_HEAD_ALIGN_BYTES;
            if pad == 0 {
                // Already on a boundary — request function placement so the
                // function-relative boundary is absolute.
                any_aligned = true;
            } else if pad <= max_pad_bytes() {
                debug_assert_eq!(pad % 4, 0, "AArch64 offsets are word-multiples");
                let prev_block = func.block_order[layout_idx - 1];
                // FAIL-CLOSED seam gate: pad ONLY when the layout-predecessor
                // genuinely FALLS THROUGH into the header (its last real
                // instruction is not a terminator). Padding appended after a
                // hard terminator (`B`/`Ret`/`BCond`/...) would be
                // architecturally dead bytes, but the post-RA structural
                // recheck rightly refuses `code-after-terminator` — that
                // invariant catches real misplaced-code bugs and must NOT be
                // weakened for padding's sake (51 torture programs fail
                // closed without this gate). The fallthrough seam is exactly
                // the shape the sieve win uses; terminator-ending seams
                // forfeit alignment (the lottery persists there — a
                // dedicated padding-block design could recover them later).
                let prev_last = func.blocks[prev_block.0 as usize]
                    .insts
                    .iter()
                    .rev()
                    .map(|&id| &func.insts[id.0 as usize])
                    .find(|inst| !inst.is_pseudo());
                // A seam falls through when the predecessor's last real
                // instruction either is not a terminator at all, or is a
                // CONDITIONAL branch (`BCond`/`Bcc`/`CBZ`/`CBNZ`/`TBZ`/
                // `TBNZ`) — architecturally the not-taken path continues into
                // the padding, then the header: 1-3 executed NOPs, harmless.
                // Only an UNCONDITIONAL transfer (`B`/`Br`/`Ret`/`TailCall`/
                // trap) makes appended padding dead code, which the post-RA
                // structural recheck rightly refuses.
                let prev_falls_through = prev_last.is_some_and(|inst| {
                    use AArch64Opcode as O;
                    !inst.is_terminator()
                        || matches!(
                            inst.opcode,
                            O::BCond | O::Bcc | O::Cbz | O::Cbnz | O::Tbz | O::Tbnz
                        )
                });
                // SEAM GATE (measured; see SEAM_GATE_MAX_SPAN_BYTES): padding
                // a fallthrough seam costs executed NOPs every time control
                // crosses it. When the seam lies INSIDE an enclosing cycle
                // (some span [t, e] contains both the predecessor and the
                // head), that cost recurs per iteration of that cycle — per
                // pass through a hot unrolled body, not per loop entry. That
                // recurring cost is only worth paying when the head's OWN
                // cycle is tight enough for fetch-line alignment to matter
                // (span <= threshold): a tight nested loop repays one NOP run
                // per outer iteration with trip-count-many aligned fetches
                // (the sieve/chomp shape); a huge-span head (Queens' unrolled
                // retry backedges) gains nothing and bleeds NOPs on the hot
                // path. Entry-only seams (no enclosing cycle) stay padded
                // unconditionally: at most one NOP run per function entry.
                let &(_, span_end) = &spans[&layout_idx];
                let head_span_bytes = pre_off[span_end + 1] - pre_off[layout_idx];
                let seam_in_cycle = spans
                    .range(..layout_idx)
                    .any(|(_, &(_, e))| e >= layout_idx);
                // IN-CYCLE PAD BUDGET (measured on Stanford/Quicksort): the
                // span test alone is not a cost model. A seam inside a cycle
                // pays `pad/4` NOPs on EVERY pass through that cycle, while
                // the alignment can save at most one fetch line per iteration
                // of the head's own loop — so the pad SIZE, not just the
                // span, decides profitability. Quicksort's `Quick` was taking
                // pad=28 (7 executed NOPs per enclosing iteration) at spans of
                // 128-152 bytes, and one head paid 28 bytes of padding to
                // align a 24-BYTE loop — more padding than loop. Measured
                // cost: 1.078/1.184 vs clang with padding, 0.870/0.824 with
                // the pass off (tcg BEATS clang by 13-18% unpadded) — a 24%
                // swing from this one policy. Entry-only seams are unaffected
                // (their NOPs run once per loop entry, not per iteration), so
                // the sieve/Treesort wins are preserved.
                let seam_gated = !seam_gate_disabled()
                    && seam_in_cycle
                    && (head_span_bytes > seam_gate_max_span_bytes()
                        || pad > in_cycle_max_pad_bytes());
                if std::env::var_os("TCG_LOOP_ALIGN_TRACE").is_some() {
                    eprintln!(
                        "[loop-align] fn={} head={:?} prev={:?} prev_last={:?} falls_through={} pad={} span_bytes={} seam_in_cycle={} seam_gated={}",
                        func.name,
                        block_id,
                        prev_block,
                        prev_last.map(|i| i.opcode),
                        prev_falls_through,
                        pad,
                        head_span_bytes,
                        seam_in_cycle,
                        seam_gated
                    );
                }
                if prev_falls_through && !seam_gated {
                    for _ in 0..(pad / 4) {
                        let nop_id = func.push_inst(MachInst::new(AArch64Opcode::AlignNop, vec![]));
                        func.blocks[prev_block.0 as usize].insts.push(nop_id);
                    }
                    offset += pad;
                    any_aligned = true;
                }
            } else if std::env::var_os("TCG_LOOP_ALIGN_TRACE").is_some() {
                // pad > max-skip: leave this header to the lottery (same as
                // clang's max-skip); it neither requests nor blocks alignment
                // of the other headers. Traced so forfeits are visible.
                eprintln!(
                    "[loop-align] fn={} head={:?} FORFEIT pad={} > max_skip={}",
                    func.name,
                    block_id,
                    pad,
                    max_pad_bytes()
                );
            }
        }

        let block = &func.blocks[block_id.0 as usize];
        for &inst_id in &block.insts {
            if !func.insts[inst_id.0 as usize].is_pseudo() {
                offset += 4;
            }
        }
    }

    if any_aligned {
        if !func_placement_disabled() {
            func.text_align_log2 = func.text_align_log2.max(LOOP_HEAD_ALIGN_LOG2);
        }
        return true;
    }

    // EVERY head forfeited (pad > max-skip, seam-gated, or a hard-terminator
    // seam) — but the function still has real cycles, so it still HAS loop
    // heads whose fetch-line offsets matter. Pin the function to 32 bytes
    // anyway: without the pin those offsets are decided by the accumulated
    // size of every function emitted before this one, so any unrelated codegen
    // change reshuffles a hot loop across the fetch line — the same lottery
    // MAX_PAD_BYTES was raised to 28 to eliminate for the heads it CAN pad,
    // and the same reason the empty-span branch above keeps the placement for
    // recursive entries. Pinning costs only dead inter-function bytes and
    // changes no executed instruction.
    //
    // Measured on Stanford/Treesort `Insert`. Its two-armed descent loop pads
    // nothing (the header needs 24 bytes at an in-cycle seam = gated; the
    // arm head sits behind the entry block's unconditional `b`, a
    // non-fallthrough seam). Before this, the function was pinned only by
    // ACCIDENT — the layout happened to put the epilogue block on a paddable
    // 8-byte seam — so the descent loop's line offset moved whenever the
    // layout changed, worth up to 18% on the amplified benchmark.
    //
    // Kill switch: `TCG_LOOP_ALIGN_NO_FORFEIT_PIN=1` restores the
    // pin-only-when-something-was-padded policy.
    if had_backward && !forfeit_pin_disabled() {
        if !func_placement_disabled() {
            func.text_align_log2 = func.text_align_log2.max(LOOP_HEAD_ALIGN_LOG2);
        }
    }
    false
}

/// Forfeited-head function-placement pin kill switch:
/// `TCG_LOOP_ALIGN_NO_FORFEIT_PIN=1` stops [`align_innermost_loop_heads`] from
/// requesting 32-byte function placement for a loop-bearing function in which
/// every head forfeited its padding. Cached per process.
fn forfeit_pin_disabled() -> bool {
    static DISABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *DISABLED.get_or_init(|| std::env::var_os("TCG_LOOP_ALIGN_NO_FORFEIT_PIN").is_some())
}

/// Compute the layout SPANS of ALL backedge-target blocks (loop heads) from
/// the final layout: a map from the target's layout position to
/// `(target block, layout position of its furthest backedge source)`.
///
/// A layout-backward branch is only a BACKEDGE when it closes a REAL cycle:
/// the target must be able to reach the branching block again through the
/// CFG. The legacy derivation (restorable via
/// `TCG_LOOP_ALIGN_NO_CYCLE_CHECK=1`) treated EVERY layout-backward branch as
/// a backedge — which misclassified the REJOIN branches of cold-sunk error
/// guards (layout.rs `sink_cold_guards_to_end` places the guard at the end;
/// its `B rejoin` then points layout-backward into straight-line code) and
/// padded the rejoin blocks as "loop heads": 4-NOP islands EXECUTED on the
/// hot fall-through path of loop-free functions (Stanford/Towers `Move`: two
/// such islands = 8 executed NOPs per call, one of the three measured layout
/// defects behind its 1.26x residual). Cycle membership is decided by BFS
/// reachability target -> source over branch `Block` operands plus layout
/// fall-throughs; a block ending in an INDIRECT branch (`Br`, unknown
/// targets) conservatively reaches everything, reproducing the legacy
/// verdict there. Alignment choice is PERF-ONLY either way (see module docs)
/// — this filter only ever DROPS pad candidates, never adds them.
///
/// The filter is applied PER FUNCTION, all-or-nothing: only a function with
/// NO real cycle at all drops its (entirely fake) spans; a function carrying
/// any real loop keeps the full legacy span set byte-identically — see the
/// measured rationale at the policy site below.
///
/// See the module docs for the span definition. Deterministic: a `BTreeMap`
/// keyed by the target's layout position. The second return is whether ANY
/// layout-backward branch existed pre-filter (so the caller can keep the
/// function-placement request when the filter dropped every span).
fn backedge_spans(func: &MachFunction) -> (BTreeMap<usize, (BlockId, usize)>, bool) {
    // layout position of every laid-out block
    let mut layout_pos: BTreeMap<BlockId, usize> = BTreeMap::new();
    for (idx, &bid) in func.block_order.iter().enumerate() {
        layout_pos.insert(bid, idx);
    }

    // Backward (target, source) pairs, grouped per target layout position.
    let mut backward: BTreeMap<usize, (BlockId, Vec<usize>)> = BTreeMap::new();
    for (&bid, &pos) in &layout_pos {
        let block = &func.blocks[bid.0 as usize];
        for &inst_id in &block.insts {
            let inst = &func.insts[inst_id.0 as usize];
            if inst.is_pseudo() || !inst.is_branch() {
                continue;
            }
            for op in &inst.operands {
                let MachOperand::Block(target) = op else {
                    continue;
                };
                let Some(&target_pos) = layout_pos.get(target) else {
                    continue;
                };
                if target_pos <= pos {
                    backward
                        .entry(target_pos)
                        .or_insert((*target, Vec::new()))
                        .1
                        .push(pos);
                }
            }
        }
    }

    // Legacy spans: every backward pair, furthest source.
    let had_backward = !backward.is_empty();
    let legacy = |backward: BTreeMap<usize, (BlockId, Vec<usize>)>| {
        let mut spans: BTreeMap<usize, (BlockId, usize)> = BTreeMap::new();
        for (target_pos, (target, sources)) in backward {
            let max_src = sources.iter().copied().max().expect("nonempty sources");
            spans.insert(target_pos, (target, max_src));
        }
        spans
    };
    if cycle_check_disabled() {
        return (legacy(backward), had_backward);
    }
    // Does ANY backward branch close a real cycle (target reaches its source
    // through the CFG)? `None` from the BFS (indirect branch met) counts as
    // yes — unknown targets, conservative legacy verdict.
    let succs = layout_successors(func, &layout_pos);
    let has_real_cycle = backward.iter().any(|(&target_pos, (_, sources))| {
        let reach = reachable_from(target_pos, &succs);
        sources
            .iter()
            .any(|&s| reach.as_ref().is_none_or(|r| r.contains(&s)))
    });
    // CONSERVATIVE per-function policy (measured): only a function with NO
    // real cycle at all — where every "backedge target" is a rejoin of a
    // cold-sunk guard or similar forward-CFG shape and every pad is pure
    // hot-path waste — drops its padding (⇒ no spans, no alignment request).
    // A function carrying any real loop keeps the legacy spans BYTE-IDENTICAL,
    // fake heads included: those accidental pads participate in the alignment
    // lottery of its real loop bodies, and removing them was measured to shift
    // hot rejoin blocks off fetch boundaries (amplified Stanford/Treesort
    // `Insert`/`Trees`/`Checktree`: +2% min / +5% med). Until padding can be
    // placed as DEAD bytes after hard terminators (the padding-block design in
    // the seam-gate note), the lottery there is left untouched.
    if has_real_cycle {
        return (legacy(backward), had_backward);
    }
    let spans = BTreeMap::new();

    // ALL REAL-CYCLE backedge targets, not just innermost. An innermost-only policy was
    // measured to REGRESS misr 1.04/1.12 (min/med best-of-21): aligning a
    // subset shifts every unselected loop head by the inserted padding —
    // reshuffling the placement lottery for exactly the loops left out
    // (misr's `simulate` has ~12 heads; the 4 selected ones landed mod32=0
    // while the hot unselected ones moved to mod32=8..28). Aligning every
    // backedge target (clang's `.p2align 5` practice, still bounded by the
    // max-skip and the fallthrough seam gate) makes every loop head's
    // placement deterministic instead of lottery-dependent. (The SEAM GATE
    // in the caller is not such a subset policy: a gated head is one whose
    // alignment is measured to not matter, so leaving it to the lottery is
    // harmless, and every non-gated head is still explicitly padded to its
    // boundary — deterministic regardless of how many heads were gated
    // before it.)
    (spans, had_backward)
}

/// Layout-position successor graph, `succs[i]` = the layout positions control
/// can transfer to from the block at layout position `i`: every branch
/// instruction's `Block` operands (covers `B`/conditionals/jump-table block
/// lists) plus the layout-next position when the block's last real
/// instruction can fall through (no real instruction, a non-terminator, or a
/// CONDITIONAL branch — the same fall-through rule as the seam gate). `None`
/// for a block whose last real instruction is an INDIRECT `Br`: its targets
/// are data-driven and unknown here, so reachability through it must be
/// treated as universal (see [`reachable_from`]).
#[allow(clippy::type_complexity)]
fn layout_successors(
    func: &MachFunction,
    layout_pos: &BTreeMap<BlockId, usize>,
) -> Vec<Option<Vec<usize>>> {
    let n = func.block_order.len();
    let mut succs: Vec<Option<Vec<usize>>> = vec![Some(Vec::new()); n];
    for (idx, &bid) in func.block_order.iter().enumerate() {
        let block = &func.blocks[bid.0 as usize];
        let mut out: Vec<usize> = Vec::new();
        let mut last_real: Option<&MachInst> = None;
        for &inst_id in &block.insts {
            let inst = &func.insts[inst_id.0 as usize];
            if inst.is_pseudo() {
                continue;
            }
            last_real = Some(inst);
            if inst.is_branch() {
                for op in &inst.operands {
                    if let MachOperand::Block(target) = op
                        && let Some(&tpos) = layout_pos.get(target)
                    {
                        out.push(tpos);
                    }
                }
            }
        }
        let falls_through = match last_real {
            None => true,
            Some(inst) => {
                if inst.opcode == AArch64Opcode::Br {
                    // Indirect branch: unknown targets — mark and move on.
                    succs[idx] = None;
                    continue;
                }
                !inst.is_terminator() || inst.opcode.is_conditional_branch()
            }
        };
        if falls_through && idx + 1 < n {
            out.push(idx + 1);
        }
        out.sort_unstable();
        out.dedup();
        succs[idx] = Some(out);
    }
    succs
}

/// Layout positions reachable from `start` (inclusive) by BFS over
/// [`layout_successors`], or `None` when the walk touches an unknown-target
/// (indirect-branch) block — the caller must then treat every position as
/// reachable, reproducing the legacy any-backward-branch verdict.
fn reachable_from(
    start: usize,
    succs: &[Option<Vec<usize>>],
) -> Option<std::collections::BTreeSet<usize>> {
    let mut seen: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();
    let mut work = vec![start];
    while let Some(p) = work.pop() {
        if !seen.insert(p) {
            continue;
        }
        let out = succs.get(p)?.as_ref()?;
        for &s in out {
            if !seen.contains(&s) {
                work.push(s);
            }
        }
    }
    Some(seen)
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::{PReg, Signature};

    fn preg(i: u16) -> MachOperand {
        MachOperand::PReg(PReg::new(i))
    }

    /// Build: entry (n0 insts) -> body block (loop head, self-branch) with a
    /// trailing exit block. Returns (func, head block id).
    fn loop_func(entry_insts: usize) -> (MachFunction, BlockId) {
        let sig = Signature::new(vec![], vec![]);
        let mut f = MachFunction::new("t".to_string(), sig);
        let entry = f.entry;
        for _ in 0..entry_insts {
            let id = f.push_inst(MachInst::new(
                AArch64Opcode::AddRI,
                vec![preg(0), preg(0), MachOperand::Imm(1)],
            ));
            f.append_inst(entry, id);
        }
        let head = f.create_block();
        let add = f.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![preg(0), preg(0), MachOperand::Imm(1)],
        ));
        f.append_inst(head, add);
        let back = f.push_inst(MachInst::new(
            AArch64Opcode::Cbnz,
            vec![preg(0), MachOperand::Block(head)],
        ));
        f.append_inst(head, back);
        let exit = f.create_block();
        let ret = f.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        f.append_inst(exit, ret);
        (f, head)
    }

    fn head_offset(f: &MachFunction, head: BlockId) -> u32 {
        let mut off = 0u32;
        for &bid in &f.block_order {
            if bid == head {
                return off;
            }
            for &iid in &f.blocks[bid.0 as usize].insts {
                if !f.insts[iid.0 as usize].is_pseudo() {
                    off += 4;
                }
            }
        }
        panic!("head not laid out");
    }

    fn align_nop_count(f: &MachFunction) -> usize {
        f.insts
            .iter()
            .filter(|i| i.opcode == AArch64Opcode::AlignNop)
            .count()
    }

    #[test]
    fn pads_unaligned_innermost_head_to_32() {
        // 6 entry insts = head at 24; pad 8 (2 nops) -> 32.
        let (mut f, head) = loop_func(6);
        assert!(align_innermost_loop_heads(&mut f));
        assert_eq!(align_nop_count(&f), 2);
        assert_eq!(head_offset(&f, head), 32);
        assert_eq!(head_offset(&f, head) % 32, 0);
        assert_eq!(f.text_align_log2, 5);
        // Padding lives at the END of the entry (previous) block.
        let entry_insts = &f.blocks[f.entry.0 as usize].insts;
        let last = f.insts[entry_insts.last().unwrap().0 as usize].opcode;
        assert_eq!(last, AArch64Opcode::AlignNop);
    }

    #[test]
    fn skips_when_padding_exceeds_max_skip() {
        // The full-alignment default (MAX_PAD_BYTES = 28) never forfeits:
        // pad is always in {0,4,..,28}. The forfeit branch stays for the
        // TCG_LOOP_ALIGN_MAX_SKIP A/B override; with the default, a head at
        // 16 pads 16 bytes (4 nops) instead of riding the lottery.
        let (mut f, head) = loop_func(4);
        assert!(align_innermost_loop_heads(&mut f));
        assert_eq!(align_nop_count(&f), 4);
        assert_eq!(head_offset(&f, head), 32);
        assert_eq!(f.text_align_log2, 5);
    }

    #[test]
    fn requests_placement_for_naturally_aligned_head() {
        // 8 entry insts = head at 32 already; no NOPs, but the function must
        // still request 32-byte placement to make that boundary absolute.
        let (mut f, head) = loop_func(8);
        assert!(align_innermost_loop_heads(&mut f));
        assert_eq!(align_nop_count(&f), 0);
        assert_eq!(head_offset(&f, head), 32);
        assert_eq!(f.text_align_log2, 5);
    }

    #[test]
    fn all_heads_padded_nested_loops() {
        // entry(5) -> outer_head -> inner_head(self loop) -> latch(-> outer) -> exit
        let sig = Signature::new(vec![], vec![]);
        let mut f = MachFunction::new("nest".to_string(), sig);
        let entry = f.entry;
        for _ in 0..5 {
            let id = f.push_inst(MachInst::new(
                AArch64Opcode::AddRI,
                vec![preg(0), preg(0), MachOperand::Imm(1)],
            ));
            f.append_inst(entry, id);
        }
        let outer = f.create_block();
        let a = f.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![preg(1), preg(1), MachOperand::Imm(1)],
        ));
        f.append_inst(outer, a);
        let inner = f.create_block();
        let b = f.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![preg(2), preg(2), MachOperand::Imm(1)],
        ));
        f.append_inst(inner, b);
        let back_inner = f.push_inst(MachInst::new(
            AArch64Opcode::Cbnz,
            vec![preg(2), MachOperand::Block(inner)],
        ));
        f.append_inst(inner, back_inner);
        let latch = f.create_block();
        let back_outer = f.push_inst(MachInst::new(
            AArch64Opcode::Cbnz,
            vec![preg(1), MachOperand::Block(outer)],
        ));
        f.append_inst(latch, back_outer);
        let exit = f.create_block();
        let ret = f.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        f.append_inst(exit, ret);

        // ALL-heads policy (measured: innermost-only regressed misr by
        // shifting the unselected heads — see backedge_targets): both the
        // outer and the inner header are alignment candidates.
        let mut heads: Vec<BlockId> = backedge_spans(&f).0.values().map(|&(bid, _)| bid).collect();
        heads.sort_by_key(|b| b.0);
        assert_eq!(
            heads,
            vec![outer, inner],
            "every backedge target is a candidate"
        );

        // outer starts at 20 (5 entry insts): pad 12B (3 nops). Its seam is
        // the ENTRY block — not inside any cycle — so the full MAX_PAD_BYTES
        // budget applies and outer aligns to 32.
        // inner then starts at 36 (32 + 1 outer inst @4) and needs pad 28,
        // but its seam (end of `outer`) lies INSIDE outer's own cycle, so the
        // NOPs would execute once per outer iteration. 28 > IN_CYCLE_MAX_PAD
        // (8), so inner is GATED and rides the placement lottery instead —
        // the measured Quicksort policy (28-byte in-cycle pads cost 24%).
        assert!(align_innermost_loop_heads(&mut f));
        assert_eq!(head_offset(&f, outer), 32);
        assert_eq!(
            head_offset(&f, inner),
            36,
            "in-cycle pad over budget is gated"
        );
        let entry_insts = &f.blocks[entry.0 as usize].insts;
        assert_eq!(
            f.insts[entry_insts.last().unwrap().0 as usize].opcode,
            AArch64Opcode::AlignNop
        );
        assert_eq!(align_nop_count(&f), 3);
    }

    #[test]
    fn seam_gate_skips_big_span_head_inside_enclosing_cycle() {
        // entry(5) -> outer head A -> P (falls through, Cbz) -> H (70 insts,
        // big span) -> T1 (Cbnz backedge to H) -> T2 (Cbnz backedge to A) ->
        // exit. The P->H seam lies inside A's cycle and H's own span is
        // 70*4 + 4 = 284 bytes > SEAM_GATE_MAX_SPAN_BYTES (256): the NOPs
        // would execute once per A-iteration for a head alignment that cannot
        // pay — H must be seam-GATED (left unpadded). A itself (entry-only
        // seam) still pads.
        let sig = Signature::new(vec![], vec![]);
        let mut f = MachFunction::new("g".to_string(), sig);
        let entry = f.entry;
        for _ in 0..5 {
            let id = f.push_inst(MachInst::new(
                AArch64Opcode::AddRI,
                vec![preg(0), preg(0), MachOperand::Imm(1)],
            ));
            f.append_inst(entry, id);
        }
        let outer = f.create_block();
        let a = f.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![preg(1), preg(1), MachOperand::Imm(1)],
        ));
        f.append_inst(outer, a);
        let p = f.create_block();
        let p0 = f.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![preg(2), preg(2), MachOperand::Imm(1)],
        ));
        f.append_inst(p, p0);
        let h = f.create_block();
        let p1 = f.push_inst(MachInst::new(
            AArch64Opcode::Cbz,
            vec![preg(2), MachOperand::Block(h)],
        ));
        f.append_inst(p, p1);
        for _ in 0..70 {
            let id = f.push_inst(MachInst::new(
                AArch64Opcode::AddRI,
                vec![preg(3), preg(3), MachOperand::Imm(1)],
            ));
            f.append_inst(h, id);
        }
        let t1 = f.create_block();
        let back_h = f.push_inst(MachInst::new(
            AArch64Opcode::Cbnz,
            vec![preg(3), MachOperand::Block(h)],
        ));
        f.append_inst(t1, back_h);
        let t2 = f.create_block();
        let back_a = f.push_inst(MachInst::new(
            AArch64Opcode::Cbnz,
            vec![preg(1), MachOperand::Block(outer)],
        ));
        f.append_inst(t2, back_a);
        let exit = f.create_block();
        let ret = f.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        f.append_inst(exit, ret);

        assert!(align_innermost_loop_heads(&mut f));
        // A: entry seam (no enclosing cycle), 20 -> pad 12 -> 32.
        assert_eq!(head_offset(&f, outer), 32);
        // H: seam-gated — P's block got no padding, H rides the lottery
        // (offset 44 here, deliberately unaligned).
        let p_insts = &f.blocks[p.0 as usize].insts;
        assert_ne!(
            f.insts[p_insts.last().unwrap().0 as usize].opcode,
            AArch64Opcode::AlignNop,
            "seam-gated head must not receive padding"
        );
        assert_eq!(head_offset(&f, h), 44);
        assert_eq!(align_nop_count(&f), 3);
    }

    #[test]
    fn entry_self_loop_is_never_padded() {
        let sig = Signature::new(vec![], vec![]);
        let mut f = MachFunction::new("e".to_string(), sig);
        let entry = f.entry;
        let back = f.push_inst(MachInst::new(
            AArch64Opcode::Cbnz,
            vec![preg(0), MachOperand::Block(entry)],
        ));
        f.append_inst(entry, back);
        let exit = f.create_block();
        let ret = f.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        f.append_inst(exit, ret);
        // Entry head: offset 0 is aligned by function placement; the pass
        // must not insert padding, and (offset 0 % 32 == 0 case falls under
        // layout_idx == 0, excluded) must not request placement either.
        assert!(!align_innermost_loop_heads(&mut f));
        assert_eq!(align_nop_count(&f), 0);
    }
}
