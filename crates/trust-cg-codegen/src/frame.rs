// trust-cg-codegen - Frame lowering for AArch64 macOS
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: ~/llvm-project-ref/llvm/lib/Target/AArch64/AArch64FrameLowering.cpp
// Reference: ~/llvm-project-ref/llvm/lib/Target/AArch64/AArch64PrologueEpilogue.cpp
// Reference: ~/llvm-project-ref/llvm/lib/Target/AArch64/MCTargetDesc/AArch64AsmBackend.cpp
//            (generateCompactUnwindEncoding, line 576)

//! AArch64 frame lowering for Apple/Darwin targets.
//!
//! Implements prologue/epilogue generation, frame index elimination,
//! and Darwin compact unwind encoding for the AArch64 macOS ABI.
//!
//! # Frame layout (high address to low)
//!
//! ```text
//! ┌──────────────────────┐  ← caller SP
//! │  incoming arguments   │
//! ├──────────────────────┤
//! │  X29 (FP) / X30 (LR) │  ← FP points here (X29 saved value)
//! ├──────────────────────┤
//! │  callee-saved GPR     │  pairs: X19/X20, X21/X22, ...
//! │  callee-saved FPR     │  pairs: D8/D9, D10/D11, ...
//! ├──────────────────────┤
//! │  spill slots          │  from register allocator
//! │  local variables      │  alloca / aggregates
//! ├──────────────────────┤
//! │  outgoing arg area    │  for stack-passed call arguments
//! └──────────────────────┘  ← SP (16-byte aligned)
//! ```
//!
//! # Key invariants
//!
//! - Apple AArch64 frames normally use a valid frame pointer (X29).
//! - X29/X30 are saved as the first pair when a frame pointer is used.
//! - Trivial leaf functions with no stack, no calls, and no callee-saved
//!   registers may use a zero-byte frameless layout.
//! - Stack pointer must be 16-byte aligned at all times.
//! - Callee-saved registers are saved in pairs (STP/LDP) for compact
//!   unwind compatibility.
//! - Red zone (128 bytes below SP) is disabled by default.

mod eh_identity;
mod instruction_view;
mod zero_storage;

#[path = "../../../formal/lean/Trust/A64/FrameLayoutBits.lean"]
clean mod frame_layout_bits;

use instruction_view::FrameInstructions;

use std::collections::BTreeMap;
use std::ops::Index;

use trust_cg_ir::function::{
    EhCallSiteBindings, EhCallSiteEntry, MachBlock, MachFunction, StackSlot,
};
use trust_cg_ir::inst::{AArch64Opcode, MachInst};
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::regs::{
    PReg, RegClass, SP, SpecialReg, V8, V9, V10, V11, V12, V13, V14, V15, W0, X0, X19, X20, X21,
    X22, X23, X24, X25, X26, X27, X28, X29, X30, XZR, gpr32_to_gpr64, hw_encoding, preg_class,
};
use trust_cg_ir::types::{BlockId, InstId};

// ---------------------------------------------------------------------------
// Constants — Darwin compact unwind encoding (ARM64)
// ---------------------------------------------------------------------------
// Reference: AArch64AsmBackend.cpp line 517

/// Standard frame-pointer-based unwind mode.
pub const UNWIND_ARM64_MODE_FRAME: u32 = 0x04000000;
/// Frameless leaf function unwind mode.
pub const UNWIND_ARM64_MODE_FRAMELESS: u32 = 0x02000000;
/// Fallback to full DWARF FDE.
pub const UNWIND_ARM64_MODE_DWARF: u32 = 0x03000000;

/// Compact-unwind "has language-specific data area" flag.
///
/// When set in a `__compact_unwind` entry's encoding, it tells the static
/// linker (and, after `__unwind_info` synthesis, the runtime unwinder) that
/// this function carries an LSDA pointer in the entry's `lsda` field. The
/// personality routine is only consulted for entries with this bit set; an
/// entry whose `lsda` field is relocated but whose encoding omits this bit is
/// treated by `ld` as having no LSDA, so the personality is never invoked and
/// exceptions unwind straight past any landing pad. Matches LLVM's
/// `UNWIND_HAS_LSDA` (see libunwind's `compact_unwind_encoding.h`).
pub const UNWIND_HAS_LSDA: u32 = 0x40000000;

/// Compact unwind register-pair flags for GPRs.
pub const UNWIND_ARM64_FRAME_X19_X20_PAIR: u32 = 0x00000001;
pub const UNWIND_ARM64_FRAME_X21_X22_PAIR: u32 = 0x00000002;
pub const UNWIND_ARM64_FRAME_X23_X24_PAIR: u32 = 0x00000004;
pub const UNWIND_ARM64_FRAME_X25_X26_PAIR: u32 = 0x00000008;
pub const UNWIND_ARM64_FRAME_X27_X28_PAIR: u32 = 0x00000010;

/// Compact unwind register-pair flags for FPRs (D-regs = lower 64 bits of V-regs).
pub const UNWIND_ARM64_FRAME_D8_D9_PAIR: u32 = 0x00000100;
pub const UNWIND_ARM64_FRAME_D10_D11_PAIR: u32 = 0x00000200;
pub const UNWIND_ARM64_FRAME_D12_D13_PAIR: u32 = 0x00000400;
pub const UNWIND_ARM64_FRAME_D14_D15_PAIR: u32 = 0x00000800;

/// Maximum leaf-function frame size eligible for red zone optimization.
/// Apple AArch64 red zone is 128 bytes.
pub const RED_ZONE_SIZE: u32 = 128;

/// AArch64 stack alignment requirement (Apple/Darwin).
pub const STACK_ALIGNMENT: u32 = 16;

const AARCH64_ADD_SUB_IMM12_MAX: u32 = 4095;
pub(crate) const AARCH64_SP_ADJUST_CHUNK: u32 =
    (AARCH64_ADD_SUB_IMM12_MAX / STACK_ALIGNMENT) * STACK_ALIGNMENT;

/// C-level symbol for the process stack guard word. The Mach-O writer adds
/// the leading underscore (`___stack_chk_guard`); ELF uses the name as is.
/// Either way it is read through a GOT slot (see
/// [`crate::pipeline::StackProtectorTargetAbi`]).
pub const STACK_CHK_GUARD_SYMBOL: &str = trust_cg_lower::RuntimeSymbol::StackChkGuard.name();
/// C-level symbol for the stack-check failure routine, called on mismatch.
pub const STACK_CHK_FAIL_SYMBOL: &str = trust_cg_lower::RuntimeSymbol::StackChkFail.name();

// ---------------------------------------------------------------------------
// Stack probing (stack-clash protection)
// ---------------------------------------------------------------------------
//
// Moving SP past the guard region below a thread stack without touching it
// lets a later access land in whatever mapping lies below the guard, which
// silently corrupts it instead of faulting. AArch64 frame lowering therefore
// follows LLVM's `probe-stack=inline-asm` scheme, rustc's default on every
// aarch64 target:
//
// * every nonzero frame begins with the callee-saved pre-index store
//   (`stp ..., [sp, #-csa]!`), which touches the new SP;
// * a static SP adjustment is allocated in `STACK_PROBE_INTERVAL` steps, each
//   followed by `str xzr, [sp]` before the next decrement. Up to
//   `STACK_PROBE_MAX_UNROLL` steps are emitted inline; more use a counted loop
//   in its own block, after the frame pointer is established so the FP-based
//   CFA stays valid in every iteration;
// * the residual below one interval is probed when it exceeds
//   `STACK_PROBE_MAX_UNPROBED`, or when a runtime-sized allocation may follow;
// * a runtime-sized allocation walks SP down one interval at a time, probing
//   each step, then sets SP to the target and probes it.
//
// Resulting invariant: consecutive stack touches made by one frame are at most
// `STACK_PROBE_INTERVAL` bytes apart, and at most `STACK_PROBE_MAX_UNPROBED`
// bytes above SP are untouched at any call, so a guard region of at least
// `STACK_PROBE_INTERVAL` bytes cannot be stepped over. It relies on callers
// keeping the same bound (trust-cg and LLVM inline-probing callers do); it
// is tested, not proved. Deallocation needs no probes.

/// Largest SP decrement between two stack touches. This is LLVM's AArch64
/// `stack-probe-size` default; 4 KiB is the smallest guard region the scheme
/// defends (4 KiB Linux pages), so 16 KiB Darwin and Linux pages are covered.
pub const STACK_PROBE_INTERVAL: u32 = 4096;

/// Most bytes a static allocation may leave untouched above SP
/// (LLVM `AArch64::StackProbeMaxUnprobedStack`).
pub const STACK_PROBE_MAX_UNPROBED: u32 = 1024;

/// Most interval steps emitted inline before a probe loop is used
/// (LLVM `AArch64::StackProbeMaxLoopUnroll`).
pub const STACK_PROBE_MAX_UNROLL: u32 = 4;

/// Loop counter for the static probe loop. IP0 is never allocated and never
/// carries an argument, so it is free at function entry.
const STACK_PROBE_COUNTER: PReg = X16;

/// AArch64 condition codes used by the probe loops.
const COND_NE: i64 = 0b0001;
const COND_LS: i64 = 0b1001;

/// How one static SP adjustment is allocated and probed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StaticStackProbePlan {
    /// Whole `STACK_PROBE_INTERVAL` steps, each followed by a probe.
    pub steps: u32,
    /// Whether the steps run as a loop (more than `STACK_PROBE_MAX_UNROLL`).
    pub looped: bool,
    /// Bytes allocated after the steps; always below one interval.
    pub residual: u32,
    /// Whether a probe follows the residual allocation.
    pub residual_probe: bool,
}

impl StaticStackProbePlan {
    /// Plan an SP adjustment of `adjustment` bytes. `runtime_allocation_follows`
    /// forces a final probe so a later runtime-sized allocation starts at a
    /// touched SP.
    pub fn for_adjustment(adjustment: u32, runtime_allocation_follows: bool) -> Self {
        let steps = adjustment / STACK_PROBE_INTERVAL;
        let residual = adjustment % STACK_PROBE_INTERVAL;
        Self {
            steps,
            looped: steps > STACK_PROBE_MAX_UNROLL,
            residual,
            residual_probe: residual > STACK_PROBE_MAX_UNPROBED
                || (runtime_allocation_follows && residual > 0),
        }
    }

    /// Plan the local-area adjustment emitted by [`emit_prologue`].
    pub fn for_layout(layout: &FrameLayout) -> Self {
        if prologue_is_red_zone_minimal(layout) {
            return Self::for_adjustment(0, false);
        }
        Self::for_adjustment(layout.sp_adjustment(), layout.has_dynamic_alloc)
    }

    /// Number of `str xzr, [sp]` probes executed by the allocation.
    pub fn probe_count(&self) -> u32 {
        self.steps + u32::from(self.residual_probe)
    }
}

/// One straight-line element of a static SP allocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SpAllocationStep {
    /// `sub sp, sp, #bytes` (one encodable immediate chunk).
    Sub(u32),
    /// `str xzr, [sp]`.
    Probe,
}

/// Fully unrolled static allocation of [`emit_prologue`]'s local area, one
/// entry per emitted instruction. DWARF CFI for SP-based frames mirrors it.
pub(crate) fn straight_line_sp_allocation(layout: &FrameLayout) -> Vec<SpAllocationStep> {
    let plan = StaticStackProbePlan::for_layout(layout);
    let mut steps = Vec::new();
    for _ in 0..plan.steps {
        push_sp_allocation_chunks(&mut steps, STACK_PROBE_INTERVAL);
        steps.push(SpAllocationStep::Probe);
    }
    push_sp_allocation_chunks(&mut steps, plan.residual);
    if plan.residual_probe {
        steps.push(SpAllocationStep::Probe);
    }
    steps
}

fn push_sp_allocation_chunks(steps: &mut Vec<SpAllocationStep>, mut bytes: u32) {
    while bytes > 0 {
        let chunk = bytes.min(AARCH64_SP_ADJUST_CHUNK);
        steps.push(SpAllocationStep::Sub(chunk));
        bytes -= chunk;
    }
}

fn prologue_is_red_zone_minimal(layout: &FrameLayout) -> bool {
    layout.uses_red_zone && layout.sp_adjustment() == 0 && layout.callee_saved_pairs.len() <= 1
}

/// `STR XZR, [SP]`: touch the page SP now points into.
fn make_stack_probe() -> MachInst {
    MachInst::new(
        AArch64Opcode::StrRI,
        vec![
            MachOperand::PReg(XZR),
            MachOperand::Special(SpecialReg::SP),
            MachOperand::Imm(0),
        ],
    )
}

/// Whether `inst` is the stack probe emitted by frame lowering.
pub fn is_stack_probe(inst: &MachInst) -> bool {
    inst.opcode == AArch64Opcode::StrRI
        && inst.operands
            == [
                MachOperand::PReg(XZR),
                MachOperand::Special(SpecialReg::SP),
                MachOperand::Imm(0),
            ]
}

// ---------------------------------------------------------------------------
// CalleeSavedPair — a pair of registers saved/restored together
// ---------------------------------------------------------------------------

/// A pair of callee-saved registers stored together via STP/LDP.
///
/// AArch64 convention saves registers in pairs to maintain 16-byte
/// alignment and enable compact unwind encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CalleeSavedPair {
    /// First register in the pair (lower-numbered).
    pub reg1: PReg,
    /// Second register in the pair (higher-numbered).
    pub reg2: PReg,
    /// Legacy FP-relative ordering metadata for the saved pair.
    ///
    /// The prologue/epilogue do not consume this as the actual STP/LDP
    /// displacement. The Apple-canonical emitter puts FP/LR at the TOP of
    /// the callee-saved area and establishes FP there; extra pairs are below
    /// FP, with reversed register storage order. This field retains historical
    /// pair-order values, not actual byte addresses. Use the emitted operands
    /// and their checked word bindings for save-slot/frame proofs.
    pub fp_offset: i32,
    /// Whether this is an FPR pair (D-registers) vs GPR pair (X-registers).
    pub is_fpr: bool,
}

// ---------------------------------------------------------------------------
// FrameLayout — complete stack frame description
// ---------------------------------------------------------------------------

/// Complete description of a function's stack frame layout.
///
/// Computed after register allocation, before prologue/epilogue insertion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrameLayout {
    /// Callee-saved register pairs to save/restore (in save order).
    /// The first pair is always X29/X30 (FP/LR) when `uses_frame_pointer` is true.
    pub callee_saved_pairs: Vec<CalleeSavedPair>,

    /// Total size of the callee-saved register area (bytes).
    pub callee_saved_area_size: u32,

    /// Reserved area for ALL stack slots, including spills and addressable
    /// locals, with downward-placement alignment padding. This does not imply
    /// that the bytes are private or inaccessible to a callee.
    pub spill_area_size: u32,

    /// Separate local-area contribution. Current computation combines locals
    /// into `spill_area_size` and sets this to zero; zero is not evidence that
    /// the source has no local allocations or address-taken stack slots.
    pub local_area_size: u32,

    /// Size of outgoing argument area (max across all calls), in bytes.
    pub outgoing_arg_area_size: u32,

    /// Total frame size (callee-saved + spills + locals + outgoing args),
    /// rounded up to 16-byte alignment.
    pub total_frame_size: u32,

    /// Whether this function uses a frame pointer.
    ///
    /// Apple AArch64 frames normally use X29, but Trust Codegen permits a zero-byte
    /// frameless layout for trivial leaf functions.
    pub uses_frame_pointer: bool,

    /// Whether this function is a leaf (no calls).
    pub is_leaf: bool,

    /// Whether the red zone optimization is applied (leaf + small frame).
    pub uses_red_zone: bool,

    /// Offset from FP to the start of the spill/local area.
    /// On AArch64: FP points at the saved FP/LR pair after the callee-saved
    /// area has already been allocated. Extra saved pairs lie below FP, and
    /// spill/local placement starts below the whole saved area, at
    /// `FP - (callee_saved_area_size - 16)`.
    pub fp_to_spill_offset: i32,

    /// Whether this function uses runtime-sized stack allocation.
    ///
    /// Dynamic allocation means the stack pointer may move by an amount unknown
    /// at compile time. Trust Codegen currently conservatively encodes these frames with
    /// `UNWIND_ARM64_MODE_DWARF` and emits DWARF CFI fallback.
    pub has_dynamic_alloc: bool,
}

impl FrameLayout {
    /// Size of the SP adjustment needed after callee-save pushes.
    /// This is locals + spills + outgoing args.
    #[inline]
    pub fn sp_adjustment(&self) -> u32 {
        self.total_frame_size - self.callee_saved_area_size
    }
}

// ---------------------------------------------------------------------------
// Frame layout computation
// ---------------------------------------------------------------------------

/// Results of a single-pass scan over all instructions.
///
/// Replaces the previous three separate passes (`scan_callee_saved_gprs`,
/// `scan_callee_saved_fprs`, `has_calls`) with one pass for better cache
/// utilization on large functions.
struct ScanResult {
    /// Bitmask of callee-saved GPRs used (bit N = X(19+N)).
    gpr_used: u16,
    /// Bitmask of callee-saved FPRs used (bit N = V(8+N)).
    fpr_used: u8,
    /// Whether the function contains any call instructions.
    has_calls: bool,
}

/// Scan all instructions in a single pass to determine:
/// - Which callee-saved GPRs (X19-X28, including W aliases) are used
/// - Which callee-saved FPRs (V8-V15, including D/S aliases) are used
/// - Whether the function contains any call instructions
///
/// This merged scan replaces three separate iteration passes for better
/// cache locality and reduced overhead on functions with many instructions.
#[inline]
fn callee_saved_gpr_index(preg: PReg) -> Option<u16> {
    match preg.encoding() {
        r @ 19..=28 => Some(r - 19),
        r @ 51..=60 => Some(r - 51),
        _ => None,
    }
}

#[inline]
fn callee_saved_fpr_index(preg: PReg) -> Option<u8> {
    match preg.encoding() {
        r @ 72..=79 => Some((r - 72) as u8),
        r @ 104..=111 => Some((r - 104) as u8),
        r @ 136..=143 => Some((r - 136) as u8),
        // H8-H15 (enc 173-180) are the low 16 bits of V8-V15 (the same physical
        // registers as D8-D15 / S8-S15). They are allocatable for `Fpr16` and
        // hinted as callee-saved, but used to fall through to `None` here — so an
        // F16 value live across a call never set the `fpr_used` bit and the
        // prologue D8-D15 STP/LDP save was never emitted, silently clobbering it.
        // Map them to bit indices 0..7 (H8->0 .. H15->7), identical to the V/D/S
        // arms, so the EXISTING D8-D15 STP/LDP save fires — saving the low 64
        // bits of V8-V15 fully preserves the H alias (the low 16 bits).
        r @ 173..=180 => Some((r - 173) as u8),
        _ => None,
    }
}

#[inline]
fn mark_callee_saved_reg(preg: PReg, gpr_used: &mut u16, fpr_used: &mut u8) {
    if let Some(idx) = callee_saved_gpr_index(preg) {
        *gpr_used |= 1 << idx;
    } else if let Some(idx) = callee_saved_fpr_index(preg) {
        *fpr_used |= 1 << idx;
    }
}

#[inline]
#[cfg(test)]
fn scan_function(func: &MachFunction) -> ScanResult {
    scan_instructions(&FrameInstructions::all(func))
}

fn scan_instructions(instructions: &FrameInstructions<'_>) -> ScanResult {
    let mut gpr_used = 0u16;
    let mut fpr_used = 0u8;
    let mut has_calls = false;

    for inst in instructions.iter() {
        // Check for call instructions.
        // A direct tail call consumes call arguments and clobbers caller-saved
        // registers, but it never returns and does not write LR. It therefore
        // remains a leaf for frame-layout purposes.
        if !has_calls && inst.is_call() && inst.opcode != AArch64Opcode::TailCall {
            has_calls = true;
        }

        // Scan explicit operands for callee-saved register uses.
        for op in &inst.operands {
            if let MachOperand::PReg(preg) = op {
                mark_callee_saved_reg(*preg, &mut gpr_used, &mut fpr_used);
            }
        }

        // Check implicit defs/uses.
        for preg in inst.implicit_defs.iter().chain(inst.implicit_uses.iter()) {
            mark_callee_saved_reg(*preg, &mut gpr_used, &mut fpr_used);
        }
    }

    ScanResult {
        gpr_used,
        fpr_used,
        has_calls,
    }
}

/// The single source of truth for the ORDER in which stack slots are laid out.
///
/// Slots grow DOWNWARD, so the slot yielded FIRST gets the HIGHEST address.
///
/// # Why this is shared
///
/// Two functions walk the slot list with the identical downward algorithm
/// (`offset -= size; offset &= !(align - 1)`): [`compute_stack_slot_area`],
/// which computes the frame SIZE to reserve, and [`stack_slot_frame_offsets`],
/// which computes each slot's ADDRESS. They agree only because they visit the
/// slots in the same order. Reordering one without the other places the deepest
/// slots past the reserved area and into the outgoing-argument region, where a
/// callee's stores destroy them (this exact desynchronization produced five
/// gcc-c-torture miscompiles when the protector hoist was first attempted).
/// Routing both through this helper makes them agree BY CONSTRUCTION.
///
/// # Why the protector slot goes first
///
/// The stack-protector canary only detects an overflow that must CROSS it to
/// reach the return address. Allocated in program order it lands last, hence
/// DEEPEST — below every local buffer — so an upward overflow reaches the saved
/// FP/LR without ever touching it and the protector cannot fire for the threat
/// model it exists for. Emitting it first puts it adjacent to the frame record,
/// above every other local, matching clang.
///
/// The canary slot carries 16-byte alignment (see [`ensure_stack_protector_slot`]),
/// so it consumes one full stack granule: because both walkers round each slot's
/// base DOWN to that slot's own alignment, every slot beneath the canary keeps
/// the alignment it would have had without it, with no separate padding logic.
///
/// Out-of-range metadata uses plain order in both read-only layout walkers.
/// That alone is not fail-closed guard admission: preparation and prologue
/// insertion reject malformed required guard storage before changing code.
fn stack_slot_layout_order(func: &MachFunction) -> impl Iterator<Item = usize> + '_ {
    let slot_count = func.stack_slots.len();
    let protector = func
        .stack_protector_slot
        .map(|slot| slot.0 as usize)
        .filter(|idx| *idx < slot_count);
    protector
        .into_iter()
        .chain((0..slot_count).filter(move |idx| Some(*idx) != protector))
}

/// Compute the total size of all stack slots (spills + locals), respecting alignment.
///
/// This MUST mirror the DOWNWARD allocation performed by
/// [`stack_slot_frame_offsets`]: each slot's base is placed by subtracting its
/// size then rounding the base DOWN to the slot's alignment. Anchored at 0, the
/// reserved area is the distance from 0 to the lowest slot base.
///
/// A naive upward-packing sum (align each base UP from the bottom) UNDER-counts
/// the alignment padding that the downward allocator introduces: a 16-aligned
/// N-byte slot rounds its base down by up to 15 bytes, so the true extent can
/// exceed the upward sum. Under-reserving here left the lowest slot BELOW the
/// reserved area / SP, where a callee's prologue clobbered it — which corrupted
/// the stack-protector canary (whose 8-byte slot is allocated last, hence
/// lowest). Regression: gcc-c-torture pr65369 / any `sspreq` function with an
/// address-taken local array plus a call. `fp_to_spill_offset` is always
/// 16-aligned, so anchoring at 0 reproduces the exact padding for the common
/// align<=16 slots; over-aligned slots get a conservative slack (the real anchor
/// is only guaranteed 16-aligned).
#[inline]
fn compute_stack_slot_area(func: &MachFunction) -> Result<u32, crate::lower::LowerError> {
    let (extent, max_align) = checked_stack_slot_extent(func, 0)?;
    // Preserve the existing slack for an anchor guaranteed only 16-byte alignment.
    extent
        .checked_add(max_align - STACK_ALIGNMENT)
        .ok_or_else(|| frame_layout_overflow("over-aligned stack-slot area"))
}

fn frame_layout_overflow(detail: &str) -> crate::lower::LowerError {
    crate::lower::LowerError::FrameLowering(format!("frame layout overflow: {detail}"))
}

fn checked_frame_align(value: u32) -> Result<u32, crate::lower::LowerError> {
    const MASK: u32 = trust_cg_a64_frame_alignment_mask(STACK_ALIGNMENT);
    value
        .checked_add(STACK_ALIGNMENT - 1)
        .map(|value| trust_cg_a64_frame_apply_mask(value, MASK))
        .ok_or_else(|| frame_layout_overflow("16-byte alignment"))
}

/// Validate the exact downward placement used by stack_slot_frame_offsets.
/// Its public offset domain is i32, including the real CSA-dependent anchor.
/// Validate the operands of its existing i32 casts as well as the result:
/// size/align=2^31 is not interchangeable with a positive signed operand.
fn checked_stack_slot_extent(
    func: &MachFunction,
    anchor: i32,
) -> Result<(u32, u32), crate::lower::LowerError> {
    let mut offset = i64::from(anchor);
    let mut max_align: u32 = STACK_ALIGNMENT;
    for idx in stack_slot_layout_order(func) {
        let slot = &func.stack_slots[idx];
        if !slot.align.is_power_of_two() {
            return Err(crate::lower::LowerError::FrameLowering(format!(
                "frame layout invalid alignment {} for stack slot {idx}",
                slot.align
            )));
        }
        if slot.is_runtime_sized() {
            continue;
        }
        if i32::try_from(slot.size).is_err() || i32::try_from(slot.align).is_err() {
            return Err(frame_layout_overflow(
                "fixed stack-slot size/alignment exceeds signed FP domain",
            ));
        }
        offset = offset
            .checked_sub(i64::from(slot.size))
            .ok_or_else(|| frame_layout_overflow("downward stack-slot subtraction"))?;
        offset &= !(i64::from(slot.align) - 1);
        i32::try_from(offset)
            .map_err(|_| frame_layout_overflow("CSA-anchored stack-slot offset exceeds i32"))?;
        max_align = max_align.max(slot.align);
    }
    let extent = i64::from(anchor)
        .checked_sub(offset)
        .and_then(|value| u32::try_from(value).ok())
        .ok_or_else(|| frame_layout_overflow("stack-slot extent"))?;
    Ok((extent, max_align))
}

/// Returns true when any stack slot requires runtime sizing.
#[inline]
pub fn function_has_runtime_stack_slots(func: &MachFunction) -> bool {
    func.stack_slots.iter().any(|slot| slot.is_runtime_sized())
}

#[inline]
fn is_dynamic_stack_alloc_pseudo(inst: &MachInst) -> bool {
    inst.opcode == AArch64Opcode::StackAlloc && inst.operands.len() >= 2
}

/// Returns true when the function contains an explicit runtime SP allocation pseudo.
#[inline]
pub fn function_has_dynamic_stack_alloc_pseudos(func: &MachFunction) -> bool {
    func.insts.iter().any(is_dynamic_stack_alloc_pseudo)
}

#[inline]
fn instructions_have_frame_pointer_dependencies(instructions: &FrameInstructions<'_>) -> bool {
    instructions.iter().any(|inst| {
        inst.implicit_defs.contains(&X29)
            || inst.implicit_uses.contains(&X29)
            || inst.operands.iter().any(|operand| match operand {
                MachOperand::StackSlot(_)
                | MachOperand::FrameIndex(_)
                | MachOperand::IncomingArg(_) => true,
                MachOperand::PReg(preg) => *preg == X29,
                MachOperand::MemOp { base, .. } => *base == X29,
                _ => false,
            })
    })
}

/// Reserve the fixed frame slot that holds the entry stack guard value.
///
/// The guard value is 8 bytes but the slot is declared 16-byte aligned. That is
/// load-bearing, not cosmetic: [`stack_slot_layout_order`] hoists this slot to
/// the TOP of the local area (adjacent to the saved FP/LR), and both frame
/// walkers round each slot's base DOWN to its own alignment. A 16-aligned
/// canary therefore consumes exactly one stack granule and leaves every slot
/// beneath it on the alignment it would have had otherwise — no separate
/// padding logic, which is what desynchronized the two walkers in the earlier
/// attempt at this fix. `compute_stack_slot_area`'s `max_align - STACK_ALIGNMENT`
/// slack term also stays 0, since 16 == `STACK_ALIGNMENT`.
///
/// Note this only changes the slot's LAYOUT position; the slot ID is still
/// handed out in allocation order by `try_alloc_stack_slot`.
pub fn ensure_stack_protector_slot(
    func: &mut MachFunction,
) -> Result<(), crate::lower::LowerError> {
    if !func.stack_protector.is_enabled() {
        return Ok(());
    }
    if func.stack_protector_slot.is_some() {
        checked_stack_protector_slot(func)?;
        return Ok(());
    }
    let slot = func
        .try_alloc_stack_slot(StackSlot::new(8, STACK_ALIGNMENT))
        .ok_or_else(|| {
            crate::lower::LowerError::FrameLowering(
                "stack guard slot ID domain exhausted".to_string(),
            )
        })?;
    func.stack_protector_slot = Some(slot);
    Ok(())
}

/// The protector owns a fixed eight-byte value in one aligned stack granule.
/// An arbitrary existing local or dynamic allocation is not equivalent guard
/// storage. Public IR metadata must satisfy the same shape as preparation.
fn checked_stack_protector_slot(func: &MachFunction) -> Result<usize, crate::lower::LowerError> {
    let error = |detail: &str| {
        crate::lower::LowerError::FrameLowering(format!(
            "invalid stack guard reservation: {detail}"
        ))
    };
    let id = func
        .stack_protector_slot
        .ok_or_else(|| error("missing slot"))?;
    let index = id.0 as usize;
    let slot = func
        .stack_slots
        .get(index)
        .ok_or_else(|| error("slot ID is outside the arena"))?;
    if slot.is_runtime_sized() || slot.size != 8 || slot.align != STACK_ALIGNMENT {
        return Err(error("expected a fixed 8-byte, 16-aligned slot"));
    }
    Ok(index)
}

/// Compute the maximum outgoing stack-argument area needed by any call site.
///
/// ISel emits outgoing stack arguments as `STR{,B,H}` / `STP` with a base of
/// `PReg(SP)` (or `Special(SP)`) and a non-negative immediate offset. This
/// helper scans every instruction and returns the high-water mark of
/// `offset + access_size` across valid such stores, including volatile scalar
/// aliases and the full S/D/Q transfer width. Writeback pairs are not outgoing
/// argument stores. Malformed or unrepresentable intents get no area credit;
/// their eventual encoder admission is still required.
///
/// This runs BEFORE [`eliminate_frame_indices`], so spill stores are still
/// encoded as `FrameIndex`/`StackSlot` operands and do not use `PReg(SP)`
/// bases directly — meaning this scan only matches genuine outgoing-arg
/// stores emitted by ISel, never spill stores.
///
/// The result is rounded up to 16 bytes (AArch64 stack alignment requirement)
/// so the caller can safely subtract it from SP on entry without misaligning
/// the stack.
pub fn compute_max_outgoing_arg_size(func: &MachFunction) -> u32 {
    instructions_max_outgoing_arg_size(&FrameInstructions::all(func))
}

fn instructions_max_outgoing_arg_size(instructions: &FrameInstructions<'_>) -> u32 {
    use AArch64Opcode::*;

    let mut max_end = 0u32;
    for inst in instructions.iter() {
        let (base_idx, offset, access_size) = match inst.opcode {
            StpRI => {
                let Ok(pair) = crate::aarch64::encode::pair_memory_descriptor(inst) else {
                    continue;
                };
                (2, pair.offset, 2 * i64::from(pair.element_bytes))
            }
            StrRI | StrbRI | StrhRI | VolatileStrRI | VolatileStrbRI | VolatileStrhRI => {
                // Resolved scalar producers admit an omitted zero offset or
                // one actual immediate. SP is checked below; unresolved spill
                // slots and MemOp operands are not outgoing-argument shapes.
                if !matches!(inst.operands.len(), 2 | 3) {
                    continue;
                }
                let offset = match inst.operands.get(2) {
                    None => 0,
                    Some(MachOperand::Imm(offset)) => *offset,
                    _ => continue,
                };
                let Some(size) = crate::aarch64::encode::scalar_ri_mem_scale(inst) else {
                    continue;
                };
                (1, offset, size)
            }
            _ => continue,
        };

        // Base must be SP (either PReg(SP) or Special(SP)).
        let base_is_sp = match &inst.operands[base_idx] {
            MachOperand::PReg(p) if *p == SP => true,
            MachOperand::Special(SpecialReg::SP) => true,
            _ => false,
        };
        if !base_is_sp {
            continue;
        }

        if offset < 0 {
            continue;
        }
        // A pair descriptor has bounded imm7; scalar producers may await
        // large-offset legalization. Neither may overflow or narrow-wrap the
        // u32 frame-size domain, including its final 16-byte rounding.
        let Some(rounded_end) = offset
            .checked_add(access_size)
            .and_then(|end| end.checked_add(15))
            .and_then(|end| u32::try_from(end).ok())
            .map(|end| end & !15)
        else {
            continue;
        };
        if rounded_end > max_end {
            max_end = rounded_end;
        }
    }

    max_end
}

/// Compute the complete frame layout for a function.
///
/// This is called after register allocation, when physical register
/// assignments are known and spill slots have been allocated.
///
/// # Arguments
/// * `func` — The machine function (post-regalloc).
/// * `outgoing_arg_size` — Maximum outgoing argument area across all call sites.
/// * `enable_red_zone` — Whether to consider red zone optimization for leaf functions.
///
/// # Panics
/// Compatibility entrypoint for representable, well-aligned layouts. Panics
/// on invalid alignment or frame/FP-offset overflow; compiler Result paths
/// must use [`try_compute_frame_layout`] instead.
pub fn compute_frame_layout(
    func: &MachFunction,
    outgoing_arg_size: u32,
    enable_red_zone: bool,
) -> FrameLayout {
    try_compute_frame_layout(func, outgoing_arg_size, enable_red_zone)
        .expect("compute_frame_layout requires a representable frame")
}

/// Compute the complete frame layout for a function with runtime-sized stack allocation.
///
/// Like [`compute_frame_layout`] but explicitly marks the frame as having
/// runtime-sized stack allocation. Trust Codegen currently routes these layouts
/// through DWARF CFI fallback for unwind encoding.
///
/// # Panics
/// Same compatibility precondition as [`compute_frame_layout`]. Fallible
/// consumers must use [`try_compute_frame_layout_dynamic`].
pub fn compute_frame_layout_dynamic(
    func: &MachFunction,
    outgoing_arg_size: u32,
    enable_red_zone: bool,
) -> FrameLayout {
    try_compute_frame_layout_dynamic(func, outgoing_arg_size, enable_red_zone)
        .expect("compute_frame_layout_dynamic requires a representable frame")
}

/// Compute a layout without wrapping or panicking on frame arithmetic.
pub fn try_compute_frame_layout(
    func: &MachFunction,
    outgoing_arg_size: u32,
    enable_red_zone: bool,
) -> Result<FrameLayout, crate::lower::LowerError> {
    try_compute_frame_layout_inner(
        FrameInstructions::all(func),
        outgoing_arg_size,
        enable_red_zone,
        false,
        LeafFramePolicy::Keep,
    )
}

/// Checked layout with runtime-sized stack allocation explicitly enabled.
pub fn try_compute_frame_layout_dynamic(
    func: &MachFunction,
    outgoing_arg_size: u32,
    enable_red_zone: bool,
) -> Result<FrameLayout, crate::lower::LowerError> {
    try_compute_frame_layout_inner(
        FrameInstructions::all(func),
        outgoing_arg_size,
        enable_red_zone,
        true,
        LeafFramePolicy::Keep,
    )
}

/// Frame-record policy, independent of whether the target has a red zone.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LeafFramePolicy {
    /// Preserve the existing target/red-zone layout behavior.
    Keep,
    /// Also omit the frame for audited leaves requiring no stack storage.
    /// ADD/SUB/immediate-LSL bodies and constant/copy returns keep the
    /// sixteen-byte FP/LR envelope through which the verifier's source-bound
    /// frame owner binds their complete body.
    OmitZeroStorage,
    /// Apply the ordinary zero-storage audit without keeping an envelope for
    /// the frame-bound proof owner. The caller's source is either outside that
    /// owner's domain or has independently checked frameless return/control
    /// binding. This selects layout only and grants no instruction proof.
    OmitZeroStorageWithoutFrameOwner,
}

/// Checked layout with an explicit leaf-frame policy. Runtime allocations are
/// detected from both stack-slot declarations and machine instructions.
pub fn try_compute_frame_layout_with_leaf_policy(
    func: &MachFunction,
    outgoing_arg_size: u32,
    enable_red_zone: bool,
    leaf_policy: LeafFramePolicy,
) -> Result<FrameLayout, crate::lower::LowerError> {
    try_compute_frame_layout_inner(
        FrameInstructions::all(func),
        outgoing_arg_size,
        enable_red_zone,
        false,
        leaf_policy,
    )
}

/// Production frame effects come from exactly the validated emitted layout.
/// Public compatibility queries retain their whole-arena input contract.
pub(crate) fn try_compute_emitted_frame_layout(
    func: &MachFunction,
    enable_red_zone: bool,
    leaf_policy: LeafFramePolicy,
) -> Result<FrameLayout, crate::lower::LowerError> {
    let instructions = FrameInstructions::emitted(func)?;
    let outgoing_arg_size = instructions_max_outgoing_arg_size(&instructions);
    try_compute_frame_layout_inner(
        instructions,
        outgoing_arg_size,
        enable_red_zone,
        false,
        leaf_policy,
    )
}

fn try_compute_frame_layout_inner(
    instructions: FrameInstructions<'_>,
    outgoing_arg_size: u32,
    enable_red_zone: bool,
    has_dynamic_alloc: bool,
    leaf_policy: LeafFramePolicy,
) -> Result<FrameLayout, crate::lower::LowerError> {
    let func = instructions.function();
    let has_dynamic_alloc = has_dynamic_alloc
        || function_has_runtime_stack_slots(func)
        || instructions.iter().any(is_dynamic_stack_alloc_pseudo);

    // Single-pass scan replaces three separate iterations.
    let scan = scan_instructions(&instructions);
    let is_leaf = !scan.has_calls;

    // Callee-saved register usage from merged scan.
    let gpr_used = scan.gpr_used;
    let fpr_used = scan.fpr_used;

    let has_frame_pointer_dependencies =
        instructions_have_frame_pointer_dependencies(&instructions);
    let has_stack_protector_frame_dependency =
        func.stack_protector.is_enabled() || func.stack_protector_slot.is_some();
    let raw_stack_slot_area = compute_stack_slot_area(func)?;

    // Outgoing argument area (only non-leaf functions need this).
    let outgoing_arg_area_size = if is_leaf {
        0
    } else {
        checked_frame_align(outgoing_arg_size)?
    };

    let omit_zero_storage = match leaf_policy {
        LeafFramePolicy::Keep => false,
        LeafFramePolicy::OmitZeroStorage => {
            outgoing_arg_size == 0
                && zero_storage::eligible(&instructions, zero_storage::OwnerEnvelopes::Keep)
        }
        LeafFramePolicy::OmitZeroStorageWithoutFrameOwner => {
            outgoing_arg_size == 0
                && zero_storage::eligible(&instructions, zero_storage::OwnerEnvelopes::Independent)
        }
    };
    let can_use_zero_frame = (enable_red_zone || omit_zero_storage)
        && is_leaf
        && !has_dynamic_alloc
        && outgoing_arg_area_size == 0
        && gpr_used == 0
        && fpr_used == 0
        && !has_stack_protector_frame_dependency
        && !has_frame_pointer_dependencies;

    let uses_frame_pointer = !can_use_zero_frame;
    let stack_slot_area = if can_use_zero_frame {
        0
    } else {
        raw_stack_slot_area
    };

    // Build callee-saved pairs. FP/LR is first when a frame pointer is used.
    // Pre-allocate for max 10 pairs (1 FP/LR + 5 GPR + 4 FPR).
    let mut pairs = Vec::with_capacity(10);
    let mut csa_offset: i32 = -16; // FP/LR pair is at [FP, #0] but stored with offset -16 from old SP

    if uses_frame_pointer {
        pairs.push(CalleeSavedPair {
            reg1: X29,
            reg2: X30,
            fp_offset: 0, // FP points exactly at saved FP/LR
            is_fpr: false,
        });
    }

    // GPR pairs: X19/X20, X21/X22, X23/X24, X25/X26, X27/X28
    let gpr_pair_regs: [(PReg, PReg, u16); 5] = [
        (X19, X20, 0b0000_0000_0011), // bits 0,1
        (X21, X22, 0b0000_0000_1100), // bits 2,3
        (X23, X24, 0b0000_0011_0000), // bits 4,5
        (X25, X26, 0b0000_1100_0000), // bits 6,7
        (X27, X28, 0b0011_0000_0000), // bits 8,9
    ];

    for (reg1, reg2, mask) in &gpr_pair_regs {
        if gpr_used & mask != 0 {
            csa_offset -= 16;
            pairs.push(CalleeSavedPair {
                reg1: *reg1,
                reg2: *reg2,
                fp_offset: csa_offset,
                is_fpr: false,
            });
        }
    }

    // FPR pairs: D8/D9, D10/D11, D12/D13, D14/D15
    // (V8-V15 in our encoding, but we save the lower 64 bits = D-regs)
    let fpr_pair_regs: [(PReg, PReg, u8); 4] = [
        (V8, V9, 0b0000_0011),   // bits 0,1
        (V10, V11, 0b0000_1100), // bits 2,3
        (V12, V13, 0b0011_0000), // bits 4,5
        (V14, V15, 0b1100_0000), // bits 6,7
    ];

    for (reg1, reg2, mask) in &fpr_pair_regs {
        if fpr_used & mask != 0 {
            csa_offset -= 16;
            pairs.push(CalleeSavedPair {
                reg1: *reg1,
                reg2: *reg2,
                fp_offset: csa_offset,
                is_fpr: true,
            });
        }
    }

    // Callee-saved area = 16 bytes per pair (always 16-byte aligned by construction).
    let callee_saved_area_size = (pairs.len() as u32) * 16;

    // Total frame = callee-saved + stack slots + outgoing args, aligned to 16.
    let raw_total = callee_saved_area_size
        .checked_add(stack_slot_area)
        .and_then(|total| total.checked_add(outgoing_arg_area_size))
        .ok_or_else(|| frame_layout_overflow("saved registers + slots + outgoing arguments"))?;
    let total_frame_size = checked_frame_align(raw_total)?;

    // Red zone: leaf function with no stack slots and total frame <= 128 bytes.
    let uses_red_zone = enable_red_zone
        && is_leaf
        && !has_dynamic_alloc
        && stack_slot_area == 0
        && outgoing_arg_area_size == 0
        && total_frame_size <= RED_ZONE_SIZE;

    // With the Apple-canonical FRAME layout, FP points at the saved FP/LR pair
    // at the TOP of the callee-saved area; any extra callee-saved pairs occupy
    // the `csa - 16` bytes BELOW FP, and locals/spills grow downward from there.
    // The spill area therefore starts at `FP - (csa - 16)`. (For FP/LR-only
    // frames, csa == 16 and this is 0 — unchanged from the historical model.)
    let fp_to_spill_offset = -((callee_saved_area_size as i32) - 16);
    // A zero-based extent alone does not prove that every actual FP-relative
    // slot survives the additional saved-register displacement in i32.
    checked_stack_slot_extent(func, fp_to_spill_offset)?;

    Ok(FrameLayout {
        callee_saved_pairs: pairs,
        callee_saved_area_size,
        spill_area_size: stack_slot_area,
        local_area_size: 0, // Currently combined with spill_area_size
        outgoing_arg_area_size,
        total_frame_size,
        uses_frame_pointer,
        is_leaf,
        uses_red_zone,
        fp_to_spill_offset,
        has_dynamic_alloc,
    })
}

// ---------------------------------------------------------------------------
// Prologue emission
// ---------------------------------------------------------------------------

/// Generate prologue instructions for the function.
///
/// # Prologue sequence (standard frame-pointer frame)
///
/// ```asm
/// ; Save FP/LR (pre-index decrement)
/// stp  x29, x30, [sp, #-CSA_SIZE]!    ; allocate callee-saved area
/// mov  x29, sp                         ; establish frame pointer
///
/// ; Save callee-saved GPR/FPR pairs (positive offsets from SP)
/// stp  x19, x20, [sp, #16]
/// stp  x21, x22, [sp, #32]
/// ...
/// stp  d8,  d9,  [sp, #N]
/// ...
///
/// ; Allocate local + spill + outgoing arg space, probing every
/// ; STACK_PROBE_INTERVAL bytes (see "Stack probing" above)
/// sub  sp, sp, #(total_frame - callee_saved_area)
/// ```
///
/// Returns the straight-line instructions in order. A frame whose plan needs
/// a probe loop is returned here with every probe step unrolled; frame
/// insertion emits the equivalent counted loop in its own block instead.
pub fn emit_prologue(layout: &FrameLayout) -> Vec<MachInst> {
    let parts = emit_prologue_parts(layout, true);
    debug_assert!(parts.probe_loop.is_none());
    let mut insts = parts.head;
    insts.extend(parts.tail);
    insts
}

/// Prologue instructions around an optional static probe loop.
struct PrologueParts {
    /// Callee-saved stores, frame-pointer setup, unrolled probe steps and,
    /// for a looped plan, the loop-counter setup.
    head: Vec<MachInst>,
    /// How many leading `head` instructions are the callee-saved stores and
    /// the frame-pointer setup: the point where a U10 stack-limit check goes,
    /// before any probe, counter or SP adjustment.
    csa_len: usize,
    /// One loop iteration: allocate one interval, probe it and decrement the
    /// counter. Frame insertion appends the backward `B.NE` to its block.
    probe_loop: Option<Vec<MachInst>>,
    /// Residual allocation and its probe.
    tail: Vec<MachInst>,
}

fn emit_prologue_parts(layout: &FrameLayout, unroll_all: bool) -> PrologueParts {
    // Worst case without probes: CSA stores + FP setup + one SUB SP.
    let capacity = layout.callee_saved_pairs.len() + 2;
    let mut head = Vec::with_capacity(capacity);

    if prologue_is_red_zone_minimal(layout) {
        // Red zone: minimal prologue for trivial leaf functions.
        // Still save FP/LR if frame pointer is used (Apple requires it).
        if layout.uses_frame_pointer && !layout.callee_saved_pairs.is_empty() {
            // STP X29, X30, [SP, #-16]!
            head.push(make_stp_pre_index(X29, X30, -16_i64));
            // MOV X29, SP
            head.push(make_mov_sp_to_fp());
        }
        return PrologueParts {
            csa_len: head.len(),
            head,
            probe_loop: None,
            tail: Vec::new(),
        };
    }

    if !layout.callee_saved_pairs.is_empty() {
        emit_callee_saved_prologue(layout, &mut head);
    }
    let csa_len = head.len();

    // Allocate locals + spills + outgoing args.
    let plan = StaticStackProbePlan::for_layout(layout);
    let probe_step = |insts: &mut Vec<MachInst>| {
        push_sub_sp_imm(insts, STACK_PROBE_INTERVAL);
        insts.push(make_stack_probe());
    };
    let probe_loop = if plan.looped && !unroll_all {
        emit_materialize_u64(STACK_PROBE_COUNTER, u64::from(plan.steps), &mut head);
        let mut body = Vec::with_capacity(4);
        probe_step(&mut body);
        body.push(MachInst::new(
            AArch64Opcode::SubsRI,
            vec![
                MachOperand::PReg(STACK_PROBE_COUNTER),
                MachOperand::PReg(STACK_PROBE_COUNTER),
                MachOperand::Imm(1),
            ],
        ));
        Some(body)
    } else {
        for _ in 0..plan.steps {
            probe_step(&mut head);
        }
        None
    };
    let mut tail = Vec::with_capacity(2);
    push_sub_sp_imm(&mut tail, plan.residual);
    if plan.residual_probe {
        tail.push(make_stack_probe());
    }
    PrologueParts {
        head,
        csa_len,
        probe_loop,
        tail,
    }
}

/// Emit the callee-saved stores and frame-pointer setup of a frame with at
/// least one saved pair.
fn emit_callee_saved_prologue(layout: &FrameLayout, insts: &mut Vec<MachInst>) {
    // Apple-canonical `UNWIND_ARM64_MODE_FRAME` layout. The compact unwinder
    // (libunwind `stepWithCompactEncodingFrame`) and the C++ personality assume
    // FP/LR sit at the TOP of the callee-saved area (`[FP]`/`[FP+8]`) with the
    // extra callee-saved GPR/FPR pairs in a contiguous range RIGHT BELOW FP, in
    // register-number order so that X19 is at `[FP-8]`, X20 at `[FP-16]`, X21 at
    // `[FP-24]`, ... (see Apple's `compact_unwind_encoding.h`). Emit exactly that
    // shape so a mid-function re-entry into the unwinder (a cleanup landing pad's
    // `_Unwind_Resume`) restores the callee-saved registers from the correct
    // slots instead of reading garbage from below the frame.
    //
    //   stp <bottom extra pair, reversed>, [sp, #-csa]!   ; allocate CSA
    //   stp <next extra pair,   reversed>, [sp, #16]
    //   ...
    //   stp x19? -> stp x20, x19, [sp, #csa-32]
    //   stp x29, x30, [sp, #csa-16]                       ; FP/LR at the top
    //   add x29, sp, #csa-16                              ; FP -> FP/LR slot
    //
    // `STP Xn, Xm, [base, #off]` stores Xn at `[base+off]` and Xm at `[base+off+8]`,
    // so to land the lower-numbered register at the HIGHER address (closer to FP)
    // each pair is stored with its registers reversed (e.g. `stp x20, x19`).
    let csa = layout.callee_saved_area_size as i64;
    let num_pairs = layout.callee_saved_pairs.len();
    let num_extra = num_pairs - 1; // pairs[0] = FP/LR

    // Emit the extra callee-saved pairs from the BOTTOM of the CSA upward, so the
    // pre-index store (which allocates the whole CSA) comes first. Iterate the
    // pairs vec in reverse (highest register number = lowest address first).
    // pairs[1] (e.g. X19/X20) is closest to FP; higher-indexed pairs sit lower.
    for i in (1..num_pairs).rev() {
        let pair = &layout.callee_saved_pairs[i];
        let (reg1, reg2) = storage_regs_for_callee_saved_pair(pair);
        let sp_offset = ((num_extra - i) as i64) * 16;
        if sp_offset == 0 {
            // Bottom-most extra pair: pre-index to allocate the CSA.
            insts.push(make_stp_pre_index(reg2, reg1, -csa));
        } else {
            insts.push(make_stp_offset(reg2, reg1, sp_offset));
        }
    }

    // FP/LR at the TOP of the callee-saved area.
    if num_extra == 0 {
        // No extra pairs: the FP/LR store itself allocates the CSA (csa == 16).
        insts.push(make_stp_pre_index(X29, X30, -csa));
    } else {
        insts.push(make_stp_offset(X29, X30, csa - 16));
    }

    // Establish frame pointer pointing at the saved FP/LR pair.
    if layout.uses_frame_pointer {
        insts.push(make_add_fp_sp_imm(csa - 16));
    }
}

// ---------------------------------------------------------------------------
// Epilogue emission
// ---------------------------------------------------------------------------

/// Generate epilogue instructions for the function.
///
/// # Epilogue sequence
///
/// ```asm
/// ; Deallocate local + spill + outgoing arg space
/// add  sp, sp, #(total_frame - callee_saved_area)
///
/// ; Restore callee-saved pairs (reverse order of save, positive offsets)
/// ldp  d8,  d9,  [sp, #N]
/// ...
/// ldp  x21, x22, [sp, #32]
/// ldp  x19, x20, [sp, #16]
///
/// ; Restore FP/LR (post-index increment)
/// ldp  x29, x30, [sp], #CSA_SIZE
///
/// ret
/// ```
///
/// Returns the generated instructions in order.
pub fn emit_epilogue(layout: &FrameLayout) -> Vec<MachInst> {
    // Pre-allocate: worst case is 1 (ADD SP) + N-1 (LDP pairs) + 1 (LDP post-index) + 1 (RET)
    let capacity = layout.callee_saved_pairs.len() + 2;
    let mut insts = Vec::with_capacity(capacity);

    if layout.uses_red_zone && layout.sp_adjustment() == 0 && layout.callee_saved_pairs.len() <= 1 {
        // Red zone: minimal epilogue.
        if layout.uses_frame_pointer && !layout.callee_saved_pairs.is_empty() {
            // LDP X29, X30, [SP], #16
            insts.push(make_ldp_post_index(X29, X30, 16));
        }
        insts.push(make_ret());
        return insts;
    }

    // A frameless leaf has no FP/LR pair to restore. This also mirrors the
    // prologue for fixed SP-only layouts, without relying on red-zone support.
    if layout.callee_saved_pairs.is_empty() {
        if layout.sp_adjustment() > 0 {
            push_add_sp_imm(&mut insts, layout.sp_adjustment());
        }
        insts.push(make_ret());
        return insts;
    }

    // Deallocate locals + spills + outgoing args. Runtime-sized allocations
    // leave SP at an unknown depth, so restore SP from FP first. With the
    // Apple-canonical layout FP points at the saved FP/LR pair (top of the CSA),
    // so `MOV SP, FP` lands SP at the FP/LR slot; we then peel FP/LR with a
    // post-index `LDP X29,X30,[sp],#16` and restore the extra pairs from the
    // remaining (now-below-SP) area via FP-relative loads. For the common fixed
    // frame we mirror the prologue exactly in reverse.
    let csa = layout.callee_saved_area_size as i64;
    let num_extra = layout.callee_saved_pairs.len() - 1; // pairs[0] = FP/LR
    let sp_adj = layout.sp_adjustment();

    if layout.has_dynamic_alloc && layout.uses_frame_pointer {
        // SP -> FP (= the FP/LR slot, top of CSA). Extra pairs are just below.
        insts.push(make_mov_fp_to_sp());
        // Restore the extra callee-saved pairs from FP-relative slots (they sit
        // below FP at [FP-8]/[FP-16]/...). `LDP Xn,Xm,[x29,#-off]` mirrors the
        // reversed-register prologue stores.
        for (i, pair) in layout.callee_saved_pairs.iter().enumerate().skip(1) {
            let (reg1, reg2) = storage_regs_for_callee_saved_pair(pair);
            // pairs[1] (X19/X20) sits closest to FP: its base (the lower-numbered
            // register, e.g. X20) is at [FP-16] and X19 at [FP-8]. pairs[2] is at
            // [FP-32]/[FP-24], etc. So pair i's base offset from FP is -(i * 16).
            let fp_rel = -((i as i64) * 16);
            insts.push(make_ldp_base_offset(reg2, reg1, X29, fp_rel));
        }
        // Peel FP/LR (post-index by 16) to leave SP at the caller's SP.
        insts.push(make_ldp_post_index(X29, X30, 16));
        insts.push(make_ret());
        return insts;
    }

    if sp_adj > 0 {
        push_add_sp_imm(&mut insts, sp_adj);
    }

    // Restore FP/LR from the top of the callee-saved area.
    if num_extra == 0 {
        // FP/LR is the whole CSA: post-index restore deallocates it.
        if !layout.callee_saved_pairs.is_empty() {
            insts.push(make_ldp_post_index(X29, X30, csa));
        }
    } else {
        insts.push(make_ldp_offset(X29, X30, csa - 16));
        // Restore the extra callee-saved pairs, mirroring the prologue stores.
        // The bottom-most pair (sp_offset == 0) uses post-index to deallocate
        // the whole CSA.
        for (i, pair) in layout.callee_saved_pairs.iter().enumerate().skip(1) {
            let (reg1, reg2) = storage_regs_for_callee_saved_pair(pair);
            let sp_offset = ((num_extra - i) as i64) * 16;
            if sp_offset == 0 {
                insts.push(make_ldp_post_index(reg2, reg1, csa));
            } else {
                insts.push(make_ldp_offset(reg2, reg1, sp_offset));
            }
        }
    }

    // Return.
    insts.push(make_ret());

    insts
}

fn emit_epilogue_before_tail_branch(layout: &FrameLayout) -> Vec<MachInst> {
    let mut insts = emit_epilogue(layout);
    if insts
        .last()
        .is_some_and(|inst| inst.opcode == AArch64Opcode::Ret)
    {
        insts.pop();
    }
    insts
}

fn stack_protector_frame_offset(
    func: &MachFunction,
    layout: &FrameLayout,
) -> Result<Option<i32>, crate::lower::LowerError> {
    if !func.stack_protector.is_enabled() {
        return Ok(None);
    }
    let slot = checked_stack_protector_slot(func)?;
    if !layout.uses_frame_pointer {
        return Err(crate::lower::LowerError::FrameLowering(
            "stack protector guard slot requires a frame pointer".to_string(),
        ));
    }
    let offset = stack_slot_frame_offsets(func, layout)
        .get(slot)
        .copied()
        .flatten()
        .ok_or_else(|| {
            crate::lower::LowerError::FrameLowering(
                "stack guard has no fixed frame offset".to_string(),
            )
        })?;
    Ok(Some(offset))
}

fn stack_chk_guard_address_sequence(dst: PReg) -> [MachInst; 2] {
    [
        MachInst::new(
            AArch64Opcode::Adrp,
            vec![
                MachOperand::PReg(dst),
                MachOperand::Symbol(STACK_CHK_GUARD_SYMBOL.to_string()),
            ],
        ),
        MachInst::new(
            AArch64Opcode::LdrGot,
            vec![
                MachOperand::PReg(dst),
                MachOperand::PReg(dst),
                MachOperand::Symbol(STACK_CHK_GUARD_SYMBOL.to_string()),
            ],
        ),
    ]
}

fn emit_stack_protector_prologue(slot_offset: i32) -> Vec<MachInst> {
    let mut insts = Vec::with_capacity(4);
    insts.extend(stack_chk_guard_address_sequence(X16));
    insts.push(MachInst::new(
        AArch64Opcode::LdrRI,
        vec![
            MachOperand::PReg(X16),
            MachOperand::PReg(X16),
            MachOperand::Imm(0),
        ],
    ));
    insts.push(MachInst::new(
        AArch64Opcode::StrRI,
        vec![
            MachOperand::PReg(X16),
            MachOperand::MemOp {
                base: X29,
                offset: i64::from(slot_offset),
            },
        ],
    ));
    insts
}

fn emit_stack_protector_check(slot_offset: i32, fail_block: BlockId) -> Vec<MachInst> {
    let mut insts = Vec::with_capacity(6);
    insts.extend(stack_chk_guard_address_sequence(X16));
    insts.push(MachInst::new(
        AArch64Opcode::LdrRI,
        vec![
            MachOperand::PReg(X16),
            MachOperand::PReg(X16),
            MachOperand::Imm(0),
        ],
    ));
    insts.push(MachInst::new(
        AArch64Opcode::LdrRI,
        vec![
            MachOperand::PReg(X17),
            MachOperand::MemOp {
                base: X29,
                offset: i64::from(slot_offset),
            },
        ],
    ));
    insts.push(MachInst::new(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(X17), MachOperand::PReg(X16)],
    ));
    insts.push(MachInst::new(
        AArch64Opcode::BCond,
        vec![MachOperand::Imm(1), MachOperand::Block(fail_block)],
    ));
    insts
}

// ---------------------------------------------------------------------------
// U10 prologue stack-limit check (docs/u10-prologue-stack-limit.md §3-§4)
// ---------------------------------------------------------------------------

/// AArch64 condition `LO` (unsigned lower, `CC`).
const COND_LO: i64 = 0b0011;

/// A stack-limit check frame insertion will emit.
struct StackLimitFramePlan {
    limit: trust_cg_ir::MachStackLimit,
    /// `F`: the SP adjustment after the callee-saved area.
    sp_adj: u32,
}

/// Admit `func`'s stack-limit request against its layout, before any edit.
///
/// `None` when nothing is requested, or when the frame is zero (`total ==
/// 0`): such a function writes no stack, so the check is elided and the
/// verifier certifies the elision. A frame needs the callee-saved prologue
/// the check follows (every nonzero frame has its FP record); a runtime-sized
/// allocation is refused in v1, because its SP decrements happen after the
/// check with sizes the check cannot cover.
fn stack_limit_frame_plan(
    func: &MachFunction,
    layout: &FrameLayout,
) -> Result<Option<StackLimitFramePlan>, crate::lower::LowerError> {
    let Some(limit) = &func.stack_limit else {
        return Ok(None);
    };
    if layout.total_frame_size == 0 {
        return Ok(None);
    }
    if layout.has_dynamic_alloc {
        return Err(frame_insertion_error(
            "[TCG-A64-STACK-LIMIT] a runtime-sized stack allocation cannot be covered by the \
             prologue stack-limit check in v1",
        ));
    }
    if !layout.uses_frame_pointer || layout.callee_saved_pairs.is_empty() {
        return Err(frame_insertion_error(
            "[TCG-A64-STACK-LIMIT] a nonzero frame without a frame record has no place for the \
             prologue stack-limit check",
        ));
    }
    Ok(Some(StackLimitFramePlan {
        limit: limit.clone(),
        sp_adj: layout.sp_adjustment(),
    }))
}

/// The check that follows the callee-saved prologue. With `P` = SP there
/// (`S − csa`) and `F = sp_adj`, it branches to `overflow` exactly when
/// `P − F <ℤ L` (`(P <u L) ∨ (P − L <u F)`):
///
/// ```text
///   ldr  x17, [x<k>, #off]   // Pointee; Value reads x<k> directly
///   subs x16, sp, x17        // extended register: P − L, C clear iff P <u L
///   b.lo overflow
///   cmp  x16, #F             // F > 4095: movz/movk x17, #F; cmp x16, x17
///   b.lo overflow
/// ```
///
/// With `F == 0` it is `subs xzr, sp, x17` (`cmp sp, x17`) and one `b.lo`.
/// X16 and X17 are IP0/IP1: never allocated, never an argument, dead at
/// entry (the protector and the probes use them the same way).
fn emit_stack_limit_check(
    limit: &trust_cg_ir::MachStackLimit,
    sp_adj: u32,
    overflow: BlockId,
) -> Vec<MachInst> {
    use trust_cg_ir::StackLimitSource;
    let mut insts = Vec::with_capacity(7);
    let source = match limit.request.source {
        StackLimitSource::Value => limit.limit_reg,
        StackLimitSource::Pointee { offset } => {
            insts.push(MachInst::new(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::PReg(X17),
                    MachOperand::PReg(limit.limit_reg),
                    MachOperand::Imm(i64::from(offset)),
                ],
            ));
            X17
        }
    };
    let branch = || {
        MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Imm(COND_LO), MachOperand::Block(overflow)],
        )
    };
    let difference = if sp_adj == 0 {
        MachOperand::Special(SpecialReg::XZR)
    } else {
        MachOperand::PReg(X16)
    };
    insts.push(MachInst::new(
        AArch64Opcode::SubsRR,
        vec![
            difference,
            MachOperand::Special(SpecialReg::SP),
            MachOperand::PReg(source),
        ],
    ));
    insts.push(branch());
    if sp_adj != 0 {
        if sp_adj <= AARCH64_ADD_SUB_IMM12_MAX {
            insts.push(MachInst::new(
                AArch64Opcode::CmpRI,
                vec![MachOperand::PReg(X16), MachOperand::Imm(i64::from(sp_adj))],
            ));
        } else {
            emit_materialize_u64(X17, u64::from(sp_adj), &mut insts);
            insts.push(MachInst::new(
                AArch64Opcode::CmpRR,
                vec![MachOperand::PReg(X16), MachOperand::PReg(X17)],
            ));
        }
        insts.push(branch());
    }
    insts
}

/// The overflow block's code. `Trap`: `brk #0x534c` with the frame intact.
/// `Handler`: the callee-saved restore of a frame whose SP adjustment was
/// never made (the epilogue without its `add sp`), then a tail call of the
/// handler that keeps the requester's argument registers as implicit uses.
fn emit_stack_limit_overflow(
    limit: &trust_cg_ir::MachStackLimit,
    layout: &FrameLayout,
) -> Vec<MachInst> {
    use trust_cg_ir::StackLimitOverflow;
    match &limit.request.overflow {
        StackLimitOverflow::Trap => vec![MachInst::new(
            AArch64Opcode::Brk,
            vec![MachOperand::Imm(i64::from(
                trust_cg_ir::STACK_LIMIT_TRAP_IMM,
            ))],
        )],
        StackLimitOverflow::Handler { symbol } => {
            let csa_only = FrameLayout {
                total_frame_size: layout.callee_saved_area_size,
                spill_area_size: 0,
                local_area_size: 0,
                outgoing_arg_area_size: 0,
                has_dynamic_alloc: false,
                ..layout.clone()
            };
            let mut insts = emit_epilogue_before_tail_branch(&csa_only);
            let mut tail = MachInst::new(
                AArch64Opcode::TailCall,
                vec![MachOperand::Symbol(symbol.clone())],
            );
            tail.implicit_uses = trust_cg_ir::inst::intern_pregs(&limit.arg_regs);
            insts.push(tail);
            insts
        }
    }
}

fn append_stack_chk_fail_block(
    plan: &mut FrameInsertionPlan,
) -> Result<BlockId, crate::lower::LowerError> {
    let fail_block = plan.create_block()?;
    let call = plan.push_inst(MachInst::new(
        AArch64Opcode::Bl,
        vec![MachOperand::Symbol(STACK_CHK_FAIL_SYMBOL.to_string())],
    ))?;
    let trap = plan.push_inst(MachInst::new(AArch64Opcode::Brk, vec![]))?;
    plan.blocks[fail_block.0 as usize].insts.push(call);
    plan.blocks[fail_block.0 as usize].insts.push(trap);
    Ok(fail_block)
}

/// Stage frame insertion without cloning the instruction arena or mutating its
/// owner. Existing IDs are retained; only edited instructions and new code are
/// owned by the plan. All recoverable errors occur before `commit` publishes it.
struct FrameInsertionPlan {
    original_inst_count: usize,
    added_insts: Vec<MachInst>,
    edited_insts: BTreeMap<usize, MachInst>,
    blocks: Vec<MachBlock>,
    block_order: Vec<BlockId>,
    entry: BlockId,
    /// EH call sites, retargeted when a probe loop splits a protected block.
    eh_call_sites: Vec<EhCallSiteEntry>,
    eh_call_site_bindings: EhCallSiteBindings,
    /// The U10 overflow block, when a stack-limit check was emitted.
    stack_limit_overflow_block: Option<BlockId>,
}

fn frame_insertion_error(detail: impl Into<String>) -> crate::lower::LowerError {
    crate::lower::LowerError::FrameLowering(detail.into())
}

fn checked_frame_insertion_id(
    base: usize,
    added: usize,
    arena: &'static str,
) -> Result<u32, crate::lower::LowerError> {
    base.checked_add(added)
        .and_then(|index| u32::try_from(index).ok())
        .ok_or_else(|| {
            frame_insertion_error(format!("frame insertion {arena} ID domain exhausted"))
        })
}

impl FrameInsertionPlan {
    fn new(func: &MachFunction) -> Result<Self, crate::lower::LowerError> {
        // Public frame entrypoints must also be safe without the outer compiler
        // validator. Validate references before any helper indexes the arenas.
        let block_count = func.blocks.len();
        if func.entry.0 as usize >= block_count
            || func
                .block_order
                .iter()
                .any(|id| id.0 as usize >= block_count)
            || func.blocks.iter().any(|block| {
                block
                    .insts
                    .iter()
                    .any(|id| id.0 as usize >= func.insts.len())
                    || block
                        .preds
                        .iter()
                        .chain(&block.succs)
                        .any(|id| id.0 as usize >= block_count)
            })
        {
            return Err(frame_insertion_error(
                "frame insertion received an invalid arena reference",
            ));
        }
        crate::pipeline::validate_exact_aarch64_eh_call_identity(func)
            .map_err(|error| frame_insertion_error(error.to_string()))?;
        Ok(Self {
            original_inst_count: func.insts.len(),
            added_insts: Vec::new(),
            edited_insts: BTreeMap::new(),
            blocks: func.blocks.clone(),
            block_order: func.block_order.clone(),
            entry: func.entry,
            eh_call_sites: func.eh_metadata.call_sites.clone(),
            eh_call_site_bindings: func.eh_metadata.call_site_bindings.clone(),
            stack_limit_overflow_block: None,
        })
    }

    fn push_inst(&mut self, inst: MachInst) -> Result<InstId, crate::lower::LowerError> {
        let id = checked_frame_insertion_id(
            self.original_inst_count,
            self.added_insts.len(),
            "instruction",
        )?;
        self.added_insts.push(inst);
        Ok(InstId(id))
    }

    fn create_block(&mut self) -> Result<BlockId, crate::lower::LowerError> {
        let id = BlockId(checked_frame_insertion_id(self.blocks.len(), 0, "block")?);
        self.blocks.push(MachBlock::new());
        self.block_order.push(id);
        Ok(id)
    }

    /// Create an empty block laid out directly after `anchor`, at `anchor`'s
    /// loop depth plus `extra_depth`. A block created after an anchor that is
    /// absent from the layout (unreachable, never encoded) stays out of it too.
    fn create_block_after(
        &mut self,
        anchor: BlockId,
        extra_depth: u32,
    ) -> Result<BlockId, crate::lower::LowerError> {
        let id = BlockId(checked_frame_insertion_id(self.blocks.len(), 0, "block")?);
        let mut block = MachBlock::new();
        block.loop_depth = self.blocks[anchor.0 as usize]
            .loop_depth
            .saturating_add(extra_depth);
        self.blocks.push(block);
        if let Some(position) = self.block_order.iter().position(|&block| block == anchor) {
            self.block_order.insert(position + 1, id);
        }
        Ok(id)
    }

    /// Move `block`'s instructions from index `at` onward into a new block laid
    /// out directly after `block`, and divide its successor edges between the
    /// halves. A successor that an instruction staying in `block` names (a
    /// mid-block conditional branch, such as a run-time witness branching to a
    /// trap block, or a jump table) keeps its edge from `block`. Every other
    /// successor moves to the new block, and so does a head-named one that the
    /// moved instructions also name, that is `block`'s layout successor while
    /// the moved instructions do not end in a hard terminator (the fall-through
    /// the tail inherits), that is an entry of a jump table the head's `ADR`
    /// names (its `BR` may follow the split point), or that is a landing pad
    /// of one of `block`'s call sites. The new block starts without predecessors; the
    /// caller wires the path into it. An EH call site naming `block` moves
    /// with its protected call; a split that would separate the call from its
    /// landing-pad edge fails.
    fn split_block_tail(
        &mut self,
        func: &MachFunction,
        block: BlockId,
        at: usize,
    ) -> Result<BlockId, crate::lower::LowerError> {
        let layout_next = self
            .block_order
            .iter()
            .position(|&candidate| candidate == block)
            .and_then(|position| self.block_order.get(position + 1))
            .copied();
        let tail = self.create_block_after(block, 0)?;
        let index = block.0 as usize;
        let moved = self.blocks[index].insts.split_off(at);
        let succs = std::mem::take(&mut self.blocks[index].succs);
        let (head_targets, tail_targets, tail_falls_through) = {
            let view = self.view(func);
            let last = moved
                .iter()
                .map(|id| &view.insts[id.0 as usize])
                .rfind(|inst| !inst.is_pseudo());
            let hard_terminator = last.is_some_and(|inst| {
                inst.is_unconditional_branch()
                    || inst.is_return()
                    || inst.opcode == AArch64Opcode::Brk
                    || (inst.is_terminator() && !inst.is_conditional_branch())
            });
            (
                named_block_targets(func, &view.insts, &self.blocks[index].insts),
                named_block_targets(func, &view.insts, &moved),
                !hard_terminator,
            )
        };
        let eh_partition = {
            let view = self.view(func);
            eh_identity::partition(
                &view.insts,
                &self.eh_call_sites,
                &self.eh_call_site_bindings,
                block,
                &self.blocks[index].insts,
                &moved,
            )?
        };
        let mut head_succs = Vec::new();
        let mut tail_succs = Vec::with_capacity(succs.len());
        for &succ in &succs {
            let head_named = head_targets.0.contains(&succ) || head_targets.1.contains(&succ);
            let to_head = head_named || eh_partition.head_pads.contains(&succ);
            let to_tail = (!head_named && !eh_partition.head_pads.contains(&succ))
                || tail_targets.0.contains(&succ)
                || tail_targets.1.contains(&succ)
                || head_targets.1.contains(&succ)
                || (tail_falls_through && layout_next == Some(succ))
                || eh_partition.tail_pads.contains(&succ);
            if to_head && !head_succs.contains(&succ) {
                head_succs.push(succ);
            }
            if to_tail && !tail_succs.contains(&succ) {
                tail_succs.push(succ);
            }
        }
        for &succ in &succs {
            let preds = &mut self.blocks[succ.0 as usize].preds;
            let in_head = head_succs.contains(&succ);
            let in_tail = tail_succs.contains(&succ);
            if in_head && in_tail {
                if !preds.contains(&tail) {
                    preds.push(tail);
                }
            } else if in_tail {
                for pred in preds.iter_mut() {
                    if *pred == block {
                        *pred = tail;
                    }
                }
            }
        }
        self.blocks[index].succs = head_succs;
        eh_partition.retarget(
            &mut self.eh_call_sites,
            &mut self.eh_call_site_bindings,
            tail,
        );
        self.blocks[tail.0 as usize].insts = moved;
        self.blocks[tail.0 as usize].succs = tail_succs;
        Ok(tail)
    }

    fn add_edge(&mut self, from: BlockId, to: BlockId) {
        self.blocks[from.0 as usize].succs.push(to);
        self.blocks[to.0 as usize].preds.push(from);
    }

    fn view<'a>(&'a self, source: &'a MachFunction) -> FrameFunctionView<'a> {
        FrameFunctionView {
            source,
            blocks: &self.blocks,
            insts: FrameInstructionView {
                source: &source.insts,
                plan: Some(self),
            },
        }
    }

    fn commit(self, func: &mut MachFunction) -> Result<(), crate::lower::LowerError> {
        // The caller exclusively owns the function throughout planning. Reserve
        // the only growing destination before publishing any edits or CFG state.
        func.insts
            .try_reserve(self.added_insts.len())
            .map_err(|error| {
                frame_insertion_error(format!(
                    "frame insertion instruction allocation failed: {error}"
                ))
            })?;
        func.insts.extend(self.added_insts);
        for (index, inst) in self.edited_insts {
            func.insts[index] = inst;
        }
        func.blocks = self.blocks;
        func.block_order = self.block_order;
        func.entry = self.entry;
        func.eh_metadata.call_sites = self.eh_call_sites;
        func.eh_metadata.call_site_bindings = self.eh_call_site_bindings;
        func.stack_limit_overflow_block = self.stack_limit_overflow_block;
        Ok(())
    }
}

/// The shrink-wrap and return-copy analyses see staged edits in their original
/// order, without a full-function clone or speculative mutation of the input.
struct FrameFunctionView<'a> {
    source: &'a MachFunction,
    blocks: &'a [MachBlock],
    insts: FrameInstructionView<'a>,
}

impl<'a> FrameFunctionView<'a> {
    #[cfg(test)]
    fn original(source: &'a MachFunction) -> Self {
        Self {
            source,
            blocks: &source.blocks,
            insts: FrameInstructionView {
                source: &source.insts,
                plan: None,
            },
        }
    }
}

struct FrameInstructionView<'a> {
    source: &'a [MachInst],
    plan: Option<&'a FrameInsertionPlan>,
}

impl Index<usize> for FrameInstructionView<'_> {
    type Output = MachInst;
    fn index(&self, index: usize) -> &Self::Output {
        if let Some(plan) = self.plan {
            if index >= self.source.len() {
                return &plan.added_insts[index - self.source.len()];
            }
            if let Some(inst) = plan.edited_insts.get(&index) {
                return inst;
            }
        }
        &self.source[index]
    }
}

/// Blocks the instructions `ids` name: `(Block operands, entries of every
/// referenced jump table)`.
fn named_block_targets(
    func: &MachFunction,
    insts: &FrameInstructionView<'_>,
    ids: &[InstId],
) -> (Vec<BlockId>, Vec<BlockId>) {
    let mut branches = Vec::new();
    let mut tables = Vec::new();
    for &id in ids {
        for operand in &insts[id.0 as usize].operands {
            match operand {
                MachOperand::Block(target) => branches.push(*target),
                MachOperand::JumpTableIndex(table) => {
                    if let Some(table) = func.jump_tables.get(*table as usize) {
                        tables.extend(table.targets.iter().copied());
                    }
                }
                _ => {}
            }
        }
    }
    (branches, tables)
}

impl FrameInstructionView<'_> {
    fn iter(&self) -> impl Iterator<Item = &MachInst> {
        let count = self.source.len() + self.plan.map_or(0, |plan| plan.added_insts.len());
        (0..count).map(|index| &self[index])
    }
}

// ---------------------------------------------------------------------------
// Frame index elimination
// ---------------------------------------------------------------------------

/// Resolve all frame-related operands in the function to concrete
/// SP+offset or FP+offset memory operands.
///
/// After this pass, no `FrameIndex` or `StackSlot` operands should remain in
/// the function.
///
/// # Addressing strategy
///
/// When a frame pointer is available (always on Apple AArch64):
/// - Spill slots use FP-relative addressing (stable across SP changes).
/// - Outgoing args use SP-relative addressing.
///
/// Frame index encoding: `FrameIdx(i)` where `i` is the stack slot index.
/// The concrete offset is computed from the frame layout.
pub fn eliminate_frame_indices(
    func: &mut MachFunction,
    layout: &FrameLayout,
) -> Result<(), FrameIndexEliminationError> {
    // IncomingArg offsets resolve to `[FP, #16 + offset]`.
    //
    // With the Apple-canonical FRAME layout the callee's FP points at the saved
    // FP/LR pair, which sits at the TOP of the callee-saved area: the saved
    // caller-FP is at `[FP]`, the saved LR at `[FP+8]`, and the caller's SP
    // (= the CFA) is at `FP + 16`. Incoming stack arguments live directly above
    // the CFA, so they are at `[FP + 16 + arg_offset]` — independent of how many
    // extra callee-saved pairs the frame holds (those occupy the slots BELOW
    // FP now, not above it).
    const FP_TO_CFA: i64 = 16; // saved caller-FP (8) + saved LR (8)

    // IncomingArg is not a stack slot and is handled as a plain immediate
    // offset by call-lowering code, so keep this rewrite separate from the
    // stack-slot eliminator below.
    for inst in &mut func.insts {
        for operand in &mut inst.operands {
            if let MachOperand::IncomingArg(arg_offset) = operand {
                let fp_offset = FP_TO_CFA.checked_add(*arg_offset).ok_or(
                    FrameIndexEliminationError::IncomingArgumentOffsetOverflow {
                        offset: *arg_offset,
                    },
                )?;
                *operand = MachOperand::Imm(fp_offset);
            }
        }
    }

    let eliminator = FrameIndexEliminator::new(layout, func);
    eliminator.run(func)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Pre-encode offset legalization (final safety net)
// ---------------------------------------------------------------------------

use trust_cg_opt::effects::{OperandRole, aarch64_operand_roles};

/// Locate the single addressing operand of a scalar register+immediate
/// load/store and return `(operand_index, base, byte_offset, is_split_form)`.
///
/// Canonical RI opcodes accept only these complete resolved shapes:
///   * resolved MemOp form:  `[Rt, MemOp { base, offset }]`  (post frame lowering)
///   * split base+imm form:  `[Rt, base(PReg|SP), Imm(offset)]`  (non-frame ISel)
///   * zero-offset form:    `[Rt, base(PReg|SP)]`
///
/// Their base must be X0..X30 or SP. Malformed and unresolved forms remain
/// untouched, so legalization cannot erase extra operands before encoding.
/// Legacy typed-store aliases retain their existing addressing accessor below.
fn scalar_mem_addressing(inst: &MachInst) -> Option<(usize, PReg, i64, bool)> {
    if matches!(
        inst.opcode,
        AArch64Opcode::LdrRI
            | AArch64Opcode::StrRI
            | AArch64Opcode::LdrbRI
            | AArch64Opcode::LdrhRI
            | AArch64Opcode::LdrsbRI
            | AArch64Opcode::LdrshRI
            | AArch64Opcode::StrbRI
            | AArch64Opcode::StrhRI
            | AArch64Opcode::VolatileLdrRI
            | AArch64Opcode::VolatileStrRI
            | AArch64Opcode::VolatileLdrbRI
            | AArch64Opcode::VolatileLdrhRI
            | AArch64Opcode::VolatileStrbRI
            | AArch64Opcode::VolatileStrhRI
    ) {
        let (base_operand, offset) = match inst.operands.as_slice() {
            [_, MachOperand::MemOp { base, offset }] if base.encoding() <= 31 => {
                return Some((1, *base, *offset, false));
            }
            [_, base] => (base, 0),
            [_, base, MachOperand::Imm(offset)] => (base, *offset),
            _ => return None,
        };
        let base = match base_operand {
            MachOperand::PReg(base) if base.encoding() <= 31 => *base,
            MachOperand::Special(SpecialReg::SP) => SP,
            _ => return None,
        };
        return Some((1, base, offset, true));
    }
    // Prefer an explicit MemOp anywhere in the operand list.
    for (idx, op) in inst.operands.iter().enumerate() {
        if let MachOperand::MemOp { base, offset } = op {
            return Some((idx, *base, *offset, false));
        }
    }
    // Fall back to the 3-operand `[Rt, base, Imm]` split form.
    if inst.operands.len() >= 3 {
        let base = match inst.operands.get(1) {
            Some(MachOperand::PReg(p)) => *p,
            Some(MachOperand::Special(SpecialReg::SP)) => SP,
            _ => return None,
        };
        if let Some(MachOperand::Imm(offset)) = inst.operands.get(2) {
            return Some((1, base, *offset, true));
        }
    }
    None
}

/// Whether `inst` is a scalar register+immediate load/store whose resolved
/// base+offset falls outside BOTH encodable AArch64 immediate ranges (and so
/// would fail closed at encode).
fn scalar_mem_offset_out_of_range(inst: &MachInst) -> bool {
    let Some(scale) = crate::aarch64::encode::scalar_ri_mem_scale(inst) else {
        return false;
    };
    let Some((_, _, offset, _)) = scalar_mem_addressing(inst) else {
        return false;
    };
    !crate::aarch64::encode::scalar_ri_offset_encodable(offset, scale)
}

/// Whether `inst` reads and/or writes a register aliasing `reg`, considering
/// explicit operands (via their AArch64 def/use roles), MemOp bases (always
/// read), and implicit def/use sets (e.g. a call clobbering the IP scratch).
fn scratch_read_written(inst: &MachInst, reg: PReg) -> (bool, bool) {
    let roles = aarch64_operand_roles(inst.opcode, inst.operands.len());
    let mut read = false;
    let mut written = false;
    for (i, op) in inst.operands.iter().enumerate() {
        let role = roles.get(i).copied().unwrap_or(OperandRole::Use);
        match op {
            MachOperand::PReg(r) if regs_overlap(*r, reg) => {
                read |= role.is_use();
                written |= role.is_def();
            }
            // A MemOp base is always read (to form the effective address).
            MachOperand::MemOp { base, .. } if regs_overlap(*base, reg) => {
                read = true;
            }
            _ => {}
        }
    }
    for r in inst.implicit_uses.iter() {
        if regs_overlap(*r, reg) {
            read = true;
        }
    }
    for r in inst.implicit_defs.iter() {
        if regs_overlap(*r, reg) {
            written = true;
        }
    }
    (read, written)
}

/// Whether the IP scratch register `reg` still holds a value that is LIVE at
/// this program point — i.e. some later instruction in the same block reads it
/// before any instruction redefines it.
///
/// The large-offset frame-slot materialization clobbers `reg` (it computes the
/// effective address there). That is sound only when `reg` is dead: X16/X17
/// (IP0/IP1) are the reserved scratch pool and are meant to never carry a value
/// across an instruction boundary. This scan proves that invariant for the
/// candidate scratch, so that a materialization step which *would* overwrite a
/// still-live value fails closed (a named compile error) instead of silently
/// miscompiling — the pr28982b loop-carried-pointer class, where a paired
/// spill materialization left a live pointer in X17 across the first store.
///
/// `remaining` is the block's instruction list AFTER the instruction being
/// rewritten, and `live_out_of_block` is the answer when the scan falls off the
/// end of that list. The IP scratch pool USED to be assumed dead at every block
/// boundary ("X16/X17 never carry a value across a block"); post-RA cross-block
/// spill-reload elision (`elide_redundant_spill_slot_reloads`) can now leave a
/// reloaded slot value live in X16/X17 across a branch, so the seed comes from
/// whole-function liveness ([`ip_scratch_block_live_out`]) instead of `false`.
/// A call still kills (caller-clobbered), and a redefinition without an
/// intervening read still proves the register dead here.
fn scratch_live_after(
    func: &MachFunction,
    remaining: &[InstId],
    reg: PReg,
    live_out_of_block: bool,
) -> bool {
    for &inst_id in remaining {
        charge_scratch_scan(1);
        let Some(inst) = func.insts.get(inst_id.0 as usize) else {
            continue;
        };
        let (read, written) = scratch_read_written(inst, reg);
        if read {
            return true;
        }
        if written {
            return false;
        }
        if inst.flags.is_call() {
            return false;
        }
    }
    live_out_of_block
}

#[cfg(test)]
thread_local! {
    static SCRATCH_SCAN_UNITS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Count `units` instructions examined by an IP-scratch liveness scan on this
/// thread. Unit tests bound how that count grows with block size (ledger row
/// L14-P6); outside `cfg(test)` this compiles to nothing.
#[inline(always)]
fn charge_scratch_scan(units: usize) {
    #[cfg(test)]
    SCRATCH_SCAN_UNITS.with(|total| total.set(total.get().saturating_add(units as u64)));
    #[cfg(not(test))]
    let _ = units;
}

/// [`scratch_live_after`] for every position of one block, computed once per
/// scratch register and then answered in constant time.
///
/// Frame-index elimination asks, for each access whose frame offset needs an
/// IP scratch, whether that scratch is live after the access. Answered by the
/// forward scan alone, a block of `n` such accesses (a frame larger than the
/// immediate range, e.g. a large stack array) costs `O(n^2)`: each scan runs
/// to the next read, write or call of the scratch, which is usually the block
/// end. This table is the same scan run backward once: `answers[k]` is
/// `scratch_live_after(func, &block_insts[k..], reg, live_out)`.
///
/// It is built on the first query in the block, from the instructions as they
/// are then. That equals the lazy scan at every later query because the
/// elimination loop rewrites only the instruction at the current position
/// (and appends new arena instructions): the instructions after a queried
/// position are still untouched when it is queried. A block that lists one
/// instruction id twice would break that, so such a block keeps the scan.
struct ScratchLiveness<'a> {
    block_insts: &'a [InstId],
    live_out: (bool, bool),
    unique_ids: Option<bool>,
    x16: Option<Vec<bool>>,
    x17: Option<Vec<bool>>,
}

impl<'a> ScratchLiveness<'a> {
    fn new(block_insts: &'a [InstId], live_out: (bool, bool)) -> Self {
        Self {
            block_insts,
            live_out,
            unique_ids: None,
            x16: None,
            x17: None,
        }
    }

    /// `scratch_live_after(func, &block_insts[pos + 1..], reg, live_out)`,
    /// where `live_out` is the block's live-out flag of `reg`.
    fn live_after(&mut self, func: &MachFunction, pos: usize, reg: PReg) -> bool {
        let remaining = self.block_insts.get(pos + 1..).unwrap_or(&[]);
        let (table, live_out) = if reg == X16 {
            (&mut self.x16, self.live_out.0)
        } else if reg == X17 {
            (&mut self.x17, self.live_out.1)
        } else {
            return scratch_live_after(func, remaining, reg, self.live_out.1);
        };
        let block_insts = self.block_insts;
        let unique_ids = *self.unique_ids.get_or_insert_with(|| {
            let mut seen = std::collections::HashSet::with_capacity(block_insts.len());
            block_insts.iter().all(|id| seen.insert(*id))
        });
        if !unique_ids {
            return scratch_live_after(func, remaining, reg, live_out);
        }
        let answers = table.get_or_insert_with(|| {
            charge_scratch_scan(block_insts.len());
            let mut answers = vec![live_out; block_insts.len() + 1];
            for (k, id) in block_insts.iter().enumerate().rev() {
                let after = answers[k + 1];
                answers[k] = match func.insts.get(id.0 as usize) {
                    None => after,
                    Some(inst) => {
                        let (read, written) = scratch_read_written(inst, reg);
                        if read {
                            true
                        } else if written || inst.flags.is_call() {
                            false
                        } else {
                            after
                        }
                    }
                };
            }
            answers
        });
        answers.get(pos + 1).copied().unwrap_or(live_out)
    }
}

/// Whole-function backward liveness of the IP scratch registers `(X16, X17)`,
/// as a per-block-index pair of live-OUT flags.
///
/// Frame lowering borrows X16/X17 to materialize out-of-range frame addresses,
/// which CLOBBERS them; every borrow is guarded by a liveness check that must
/// fail closed rather than overwrite a live value (the pr28982b class). That
/// check was block-local, which was exactly right while no pass could leave an
/// IP value live across a branch. Post-RA spill-reload CSE can, so this
/// computes the real answer: `live_out[B] = union of live_in[succ]`,
/// `live_in[B] = upward-exposed use in B, or (live_out[B] and B does not
/// definitely kill first)`. A call kills (caller-clobbered).
///
/// Successors come from [`crate::pipeline::derive_ir_cfg_edges_from_branch_operands`],
/// the same canonical authority the post-RA CFG validator checks against; that
/// derivation resolves a dense switch's indirect `Br` through the
/// `JumpTableIndex` operand in the SAME block. A block that branches indirectly
/// with no such operand (a computed goto) has an unknowable successor set and is
/// seeded LIVE in both registers, as is any block with an out-of-range edge — an
/// underivable edge may only make the guard stricter, never looser. Blocks
/// absent from `block_order` are never emitted, so their live-out is vacuously
/// false.
fn ip_scratch_block_live_out(func: &MachFunction) -> Vec<(bool, bool)> {
    let n = func.blocks.len();
    let mut succs: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut opaque_succs = vec![false; n];
    for &block_id in &func.block_order {
        let idx = block_id.0 as usize;
        if idx >= n {
            continue;
        }
        // An indirect `Br` reaches its targets through a jump table whose
        // `Adr ..., JumpTableIndex(i)` operand the CFG derivation reads from
        // this same block; without such an operand (a computed goto) the
        // successor set is unknowable and the block is treated as opaque.
        let inst_at = |id: InstId| func.insts.get(id.0 as usize);
        let has_indirect_br = func.blocks[idx]
            .insts
            .iter()
            .filter_map(|&id| inst_at(id))
            .any(|inst| inst.opcode == AArch64Opcode::Br);
        let has_jump_table = func.blocks[idx]
            .insts
            .iter()
            .filter_map(|&id| inst_at(id))
            .any(|inst| {
                inst.operands
                    .iter()
                    .any(|op| op.as_jump_table_index().is_some())
            });
        opaque_succs[idx] = has_indirect_br && !has_jump_table;
    }
    for (from, to) in crate::pipeline::derive_ir_cfg_edges_from_branch_operands(func) {
        let (from, to) = (from.0 as usize, to.0 as usize);
        if from < n && to < n {
            succs[from].push(to);
        } else if from < n {
            opaque_succs[from] = true;
        }
    }

    // Per block: (upward-exposed use, definitely killed before any use).
    let mut gen_kill: Vec<((bool, bool), (bool, bool))> = vec![((false, false), (false, false)); n];
    for (idx, block) in func.blocks.iter().enumerate() {
        let (mut use16, mut kill16) = (false, false);
        let (mut use17, mut kill17) = (false, false);
        for &inst_id in &block.insts {
            let Some(inst) = func.insts.get(inst_id.0 as usize) else {
                continue;
            };
            let (r16, w16) = scratch_read_written(inst, X16);
            let (r17, w17) = scratch_read_written(inst, X17);
            let call = inst.flags.is_call();
            if !use16 && !kill16 {
                if r16 {
                    use16 = true;
                } else if w16 || call {
                    kill16 = true;
                }
            }
            if !use17 && !kill17 {
                if r17 {
                    use17 = true;
                } else if w17 || call {
                    kill17 = true;
                }
            }
        }
        gen_kill[idx] = ((use16, use17), (kill16, kill17));
    }

    // A block whose successors are not derivable keeps both registers live-out:
    // strictly conservative for the guard this feeds.
    let mut live_in: Vec<(bool, bool)> = vec![(false, false); n];
    let mut live_out: Vec<(bool, bool)> = vec![(false, false); n];
    // Liveness only ever grows here, so iterating to stability terminates in at
    // most `n` sweeps; the extra sweep detects the fixpoint.
    for _ in 0..=n {
        let mut changed = false;
        for idx in (0..n).rev() {
            let mut out = if opaque_succs[idx] {
                (true, true)
            } else {
                (false, false)
            };
            for &s in &succs[idx] {
                out.0 |= live_in[s].0;
                out.1 |= live_in[s].1;
            }
            let ((use16, use17), (kill16, kill17)) = gen_kill[idx];
            let new_in = (use16 || (out.0 && !kill16), use17 || (out.1 && !kill17));
            if out != live_out[idx] || new_in != live_in[idx] {
                live_out[idx] = out;
                live_in[idx] = new_in;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    live_out
}

/// The GPR destination of a single-register RI *load* (operand 0, a pure Def),
/// as its 64-bit view — or `None` when it cannot host address arithmetic.
/// Only a writable GPR can hold the address: ZR discards it, and SP must not be
/// repurposed. Reusing a writable destination distinct from the address base is
/// sound because the load overwrites it anyway, so its prior value is dead.
fn load_dest_gpr(inst: &MachInst) -> Option<PReg> {
    let is_load = matches!(
        inst.opcode,
        AArch64Opcode::LdrRI
            | AArch64Opcode::LdrbRI
            | AArch64Opcode::LdrhRI
            | AArch64Opcode::LdrsbRI
            | AArch64Opcode::LdrshRI
            | AArch64Opcode::VolatileLdrRI
            | AArch64Opcode::VolatileLdrbRI
            | AArch64Opcode::VolatileLdrhRI
    );
    if !is_load {
        return None;
    }
    let dest = match inst.operands.first() {
        Some(MachOperand::PReg(p)) => match preg_class(*p) {
            RegClass::Gpr64 => Some(*p),
            RegClass::Gpr32 => gpr32_to_gpr64(*p),
            _ => None,
        },
        _ => None,
    }?;
    (dest != SP && dest != XZR).then_some(dest)
}

/// Choose a scratch register to hold the materialized effective address, or
/// `None` (fail closed) if no register can be repurposed without clobbering a
/// live value.
///
/// `live_out16`/`live_out17` are the block-local live-out flags of X16/X17 at
/// this instruction (X16/X17 are reserved scratch, so their live ranges never
/// leave a block; the frame prologue/epilogue and spill sequences DO carry live
/// values in them across a handful of instructions — e.g. the stack-protector
/// guard in X16 spanning the canary-check load — which is exactly what these
/// flags guard against).
fn choose_legalization_scratch(
    inst: &MachInst,
    base: PReg,
    live_out16: bool,
    live_out17: bool,
) -> Option<PReg> {
    // Preferred: a GPR load destination distinct from the base — always safe.
    if let Some(dest) = load_dest_gpr(inst)
        && !regs_overlap(dest, base)
    {
        return Some(dest);
    }
    // Otherwise X16/X17: it must NOT be a register this instruction reads (its
    // transfer value or base), and it must be DEAD after the instruction (no
    // later use of its current value) so clobbering it is a no-op.
    for (cand, live_out) in [(X16, live_out16), (X17, live_out17)] {
        let (reads, _writes) = scratch_read_written(inst, cand);
        if reads || live_out {
            continue;
        }
        return Some(cand);
    }
    None
}

/// Convert a normalized base `PReg` back to the operand form the encoder expects
/// (SP must be `Special(SP)`, never `PReg(31)`, in add/sub Rn position).
#[inline]
fn addr_base_operand(base: PReg) -> MachOperand {
    if base == SP {
        MachOperand::Special(SpecialReg::SP)
    } else {
        MachOperand::PReg(base)
    }
}

/// Emit the arithmetic that computes the effective address `base + offset` into
/// `scratch`, appending the resulting instruction(s) to `out`. The value left in
/// `scratch` is *exactly* `base + offset` in every branch, so a subsequent
/// `[scratch, #0]` access transfers the same bytes to/from the same address.
///
/// - `|offset| <= 4095`: the single `ADD/SUB xScratch, base, #imm12` form. This
///   is the cheap path (one instruction) and is SP-safe — the add/sub *immediate*
///   form accepts SP as `Rn`.
/// - `|offset| > 4095`: materialize `|offset|` via `MOVZ`(+`MOVK`) into `scratch`
///   and fold the base in as a shifted register (`ADD/SUB xScratch, base,
///   xScratch`). The shifted-register form CANNOT take SP as `Rn`.
///
/// Fails closed (returns `Err`, never wrong code) when the large-magnitude path
/// is required with an `SP` base (would need a second scratch to add to SP) or
/// when `|offset|` exceeds the 32-bit `MOVZ`/`MOVK` materialization window.
///
/// Shared by [`legalize_one_mem_offset`] (the pre-encode safety net) and
/// `FrameIndexEliminator::materialize_and_rewrite` so both large-offset paths
/// agree on the single-instruction fast path and the fail-closed contract.
fn emit_effective_address_into_scratch(
    func: &mut MachFunction,
    scratch: PReg,
    base: PReg,
    offset: i64,
    out: &mut Vec<InstId>,
) -> Result<(), String> {
    let abs = offset.unsigned_abs();
    let base_operand = addr_base_operand(base);

    if abs <= AARCH64_ADD_SUB_IMM12_MAX as u64 {
        // Single ADD/SUB immediate — one fewer instruction than MOVZ + reg-form,
        // and SP-safe (the immediate form accepts SP as Rn).
        let opcode = if offset >= 0 {
            AArch64Opcode::AddRI
        } else {
            AArch64Opcode::SubRI
        };
        out.push(func.push_inst(MachInst::new(
            opcode,
            vec![
                MachOperand::PReg(scratch),
                base_operand,
                MachOperand::Imm(abs as i64),
            ],
        )));
        return Ok(());
    }

    // Large magnitude: materialize |offset| in the scratch, then ADD/SUB the base
    // as a shifted register. That register form cannot take SP as Rn, and the
    // MOVZ/MOVK window is 32 bits; outside those bounds we FAIL CLOSED.
    if base == SP {
        return Err(format!(
            "frame-address materialization: SP-relative offset {offset} exceeds the ±4095 \
             immediate range and the shifted-register add/sub form cannot take SP as Rn without a \
             second scratch — kept fail-closed"
        ));
    }
    if abs > 0xFFFF_FFFF {
        return Err(format!(
            "frame-address materialization: offset magnitude {abs} exceeds the 32-bit MOVZ/MOVK \
             materialization window — kept fail-closed"
        ));
    }

    let lo16 = (abs & 0xFFFF) as i64;
    out.push(func.push_inst(MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(scratch), MachOperand::Imm(lo16)],
    )));
    if abs > 0xFFFF {
        let hi16 = ((abs >> 16) & 0xFFFF) as i64;
        out.push(func.push_inst(MachInst::new(
            AArch64Opcode::Movk,
            vec![
                MachOperand::PReg(scratch),
                MachOperand::Imm(hi16),
                MachOperand::Imm(16),
            ],
        )));
    }
    let opcode = if offset >= 0 {
        AArch64Opcode::AddRR
    } else {
        AArch64Opcode::SubRR
    };
    out.push(func.push_inst(MachInst::new(
        opcode,
        vec![
            MachOperand::PReg(scratch),
            base_operand,
            MachOperand::PReg(scratch),
        ],
    )));
    Ok(())
}

/// Final safety-net pass: legalize any scalar register+immediate load/store
/// whose fully-resolved base+offset is outside BOTH the unsigned-scaled and
/// unscaled AArch64 immediate ranges.
///
/// # Why this exists (and why here)
///
/// `eliminate_frame_indices` already materializes *frame* slots whose FP-/SP-
/// relative offset is large, but only for operands still carried as
/// `FrameIndex`/`StackSlot` when it runs. Offsets can reach the encoder as an
/// already-resolved `MemOp` by other routes (e.g. spill stores whose slot
/// offset lands out of range), leaving `str x16, [x29, #-384]` to fail closed at
/// encode. This pass is the exhaustive net: it operates on the *encoder's own*
/// notion of encodability (`scalar_ri_offset_encodable`) over the final operand
/// shapes, so nothing out of range can slip through regardless of provenance.
///
/// It MUST run after all frame finalization (offsets final) and before branch
/// resolution (so the instructions it inserts are counted in PC-relative
/// offsets) — i.e. at the tail of `run_frame_lowering`.
///
/// # Legalization
///
/// For an out-of-range access `op Rt, [base, #off]` it computes the effective
/// address `base + off` into a free scratch (X16/X17) and rewrites the access to
/// `op Rt, [scratch, #0]` — same opcode, same width, so the exact same bytes are
/// transferred to/from the exact same address:
///
/// ```asm
/// ; |off| <= 4095  (covers every realistic frame; the failing repros)
/// sub  xS, base, #|off|          ; or add for off >= 0
/// op   Rt, [xS, #0]
///
/// ; |off| > 4095   (very large frames; base must not be SP)
/// movz xS, #(|off| & 0xffff)
/// movk xS, #(|off| >> 16), lsl #16   ; if |off| > 0xffff
/// sub  xS, base, xS              ; or add for off >= 0
/// op   Rt, [xS, #0]
/// ```
///
/// # Scratch safety (fail-closed)
///
/// X16/X17 are reserved (never register-allocated), so regalloc never parks a
/// value in them — but the hand-emitted frame prologue/epilogue and spill
/// sequences DO use them as short-lived carriers (e.g. the stack-protector guard
/// sits in X16 across the canary-check `ldr x17, [x29, #-off]`). A block-local
/// backward liveness of X16/X17 makes the choice sound: the scratch is picked to
/// (a) not be an input the access reads, and (b) be dead after the access. For a
/// GPR-destination load the destination itself is preferred (dead by definition).
/// If nothing is free — or the `> 4095` path is needed with an `SP` base (which
/// would need a second scratch) — the pass FAILS CLOSED, never clobbering a live
/// register.
pub fn legalize_large_mem_offsets(func: &mut MachFunction) -> Result<(), String> {
    let num_blocks = func.blocks.len();
    // Whole-function live-out of X16/X17 per block: post-RA spill-reload CSE can
    // leave a reloaded slot value in an IP register across a branch, so the
    // block-local scan below must be seeded with the real cross-block answer
    // instead of `false` (see `ip_scratch_block_live_out`).
    let block_live_out = ip_scratch_block_live_out(func);
    for block_idx in 0..num_blocks {
        // Byte-identity guard: touch a block only if it actually contains an
        // out-of-range access, so in-range functions are left bit-for-bit intact.
        let needs = func.blocks[block_idx]
            .insts
            .iter()
            .any(|&id| scalar_mem_offset_out_of_range(&func.insts[id.0 as usize]));
        if !needs {
            continue;
        }

        let block_insts = std::mem::take(&mut func.blocks[block_idx].insts);

        // Backward liveness of X16/X17 through this block, seeded with the
        // block's whole-function live-out. The resulting per-instruction
        // live-out flags tell the scratch chooser which of X16/X17 holds a
        // value that outlives the access.
        let n = block_insts.len();
        let mut live_out: Vec<(bool, bool)> = vec![(false, false); n];
        let (mut cur16, mut cur17) = block_live_out
            .get(block_idx)
            .copied()
            .unwrap_or((true, true));
        for i in (0..n).rev() {
            live_out[i] = (cur16, cur17);
            let inst = &func.insts[block_insts[i].0 as usize];
            let (r16, w16) = scratch_read_written(inst, X16);
            let (r17, w17) = scratch_read_written(inst, X17);
            cur16 = if r16 {
                true
            } else if w16 {
                false
            } else {
                cur16
            };
            cur17 = if r17 {
                true
            } else if w17 {
                false
            } else {
                cur17
            };
        }

        let mut new_insts = Vec::with_capacity(block_insts.len() + 4);
        for (i, &inst_id) in block_insts.iter().enumerate() {
            if !scalar_mem_offset_out_of_range(&func.insts[inst_id.0 as usize]) {
                new_insts.push(inst_id);
                continue;
            }
            let (lo16, lo17) = live_out[i];
            legalize_one_mem_offset(func, inst_id, lo16, lo17, &mut new_insts)?;
        }
        func.blocks[block_idx].insts = new_insts;
    }
    Ok(())
}

/// Legalize one out-of-range scalar load/store, appending the materialization
/// instructions followed by the rewritten access to `out`. `live_out16`/
/// `live_out17` are the block-local live-out flags of X16/X17 at this access.
fn legalize_one_mem_offset(
    func: &mut MachFunction,
    inst_id: InstId,
    live_out16: bool,
    live_out17: bool,
    out: &mut Vec<InstId>,
) -> Result<(), String> {
    // Snapshot everything we need before any `push_inst` (which may reallocate
    // the instruction arena and invalidate borrows).
    let (mem_idx, base, offset, is_split) = {
        let inst = &func.insts[inst_id.0 as usize];
        scalar_mem_addressing(inst).ok_or_else(|| {
            format!(
                "offset legalization: no addressing operand in {:?}",
                inst.opcode
            )
        })?
    };

    // Choose a scratch that clobbers no live value (see `choose_legalization_scratch`).
    let scratch = {
        let inst = &func.insts[inst_id.0 as usize];
        choose_legalization_scratch(inst, base, live_out16, live_out17).ok_or_else(|| {
            format!(
                "offset legalization ran out of free scratch registers for {:?} at [{}, #{}] \
                 (X16/X17 both live or in use) — kept fail-closed to avoid clobbering a live \
                 register",
                inst.opcode,
                base_reg_name(base),
                offset
            )
        })?
    };

    // Compute `base + offset` into the scratch. The single ADD/SUB #imm12 form
    // handles the common (small-magnitude) case in one instruction; larger
    // magnitudes materialize via MOVZ/MOVK + reg-form. Shared with the frame
    // eliminator so both large-offset paths agree.
    emit_effective_address_into_scratch(func, scratch, base, offset, out)?;

    // Rewrite the access to use [scratch, #0]. The effective address is
    // unchanged (scratch == base + off), so the transferred bytes are identical.
    let inst = &mut func.insts[inst_id.0 as usize];
    inst.operands[mem_idx] = MachOperand::MemOp {
        base: scratch,
        offset: 0,
    };
    if is_split {
        // Collapse `[Rt, base, Imm]` to `[Rt, MemOp]` (mem_idx == 1 here).
        inst.operands.truncate(2);
    }
    out.push(inst_id);
    Ok(())
}

/// Human-readable base register name for diagnostics.
fn base_reg_name(base: PReg) -> String {
    if base == SP {
        "sp".to_string()
    } else {
        format!("x{}", hw_encoding(base))
    }
}

/// Compute the FP-relative offset for each fixed-size stack slot.
///
/// Returns a vector indexed by stack slot index. Fixed-size slots contain the
/// signed offset from FP to the start of that slot; runtime-sized slots return
/// `None` because they do not have a single static frame offset.
pub fn stack_slot_frame_offsets(func: &MachFunction, layout: &FrameLayout) -> Vec<Option<i32>> {
    // Indexed by slot ID; visited in [`stack_slot_layout_order`], which is the
    // same order [`compute_stack_slot_area`] uses to size the reserved area.
    let mut offsets = vec![None; func.stack_slots.len()];
    // Spill/local area starts immediately below FP. The callee-saved area is
    // above FP-relative locals because FP is established after the initial
    // callee-save pre-index allocation.
    // We lay out slots growing downward from there.
    let mut current_offset = layout.fp_to_spill_offset;

    for idx in stack_slot_layout_order(func) {
        let slot = &func.stack_slots[idx];
        if slot.is_runtime_sized() {
            // Runtime-sized slots have no single static offset; they keep None.
            continue;
        }
        // Grow downward: subtract size, then align.
        current_offset -= slot.size as i32;
        // Align the offset (make it more negative if needed).
        let align = slot.align as i32;
        if align > 0 {
            // Round down to alignment boundary (for negative offsets).
            let mask = trust_cg_a64_frame_alignment_mask(align as u32);
            current_offset = trust_cg_a64_frame_apply_mask(current_offset as u32, mask) as i32;
        }
        offsets[idx] = Some(current_offset);
    }

    offsets
}

/// Compute the FP-relative offset for each stack slot.
///
/// Returns a vector indexed by stack slot index, where each value is the
/// signed offset from FP to the start of that slot. Runtime-sized slots keep
/// the current fixed cursor for the eliminator's legacy panic path; callers
/// that need read-only fixed-slot metadata should use
/// [`stack_slot_frame_offsets`].
fn compute_slot_offsets(func: &MachFunction, layout: &FrameLayout) -> Vec<i32> {
    stack_slot_frame_offsets(func, layout)
        .into_iter()
        .map(|offset| offset.unwrap_or(layout.fp_to_spill_offset))
        .collect()
}

// ---------------------------------------------------------------------------
// Frame index elimination — enhanced pass
// ---------------------------------------------------------------------------

/// AArch64 LDR/STR unsigned immediate offset upper bound (conservative).
/// The real limit depends on access size (4095 * scale), but we use the
/// unscaled upper bound for simplicity.
const AARCH64_MAX_IMM_OFFSET: i64 = 4095;

/// AArch64 LDR/STR signed immediate offset lower bound (LDUR/STUR range).
const AARCH64_MIN_IMM_OFFSET: i64 = -256;

/// AArch64 scratch registers for memory-offset materialization.
/// X16/IP0 and X17/IP1 are ABI scratch registers and are not allocated by
/// register allocation.
use trust_cg_ir::regs::{X16, X17, regs_overlap};

/// Check whether an offset exceeds the AArch64 immediate encoding range
/// for load/store instructions.
///
/// Conservative range: -256 <= offset <= 4095.
/// Offsets outside this range require materialization in a scratch register.
#[inline]
pub fn is_large_offset(offset: i64) -> bool {
    !(AARCH64_MIN_IMM_OFFSET..=AARCH64_MAX_IMM_OFFSET).contains(&offset)
}

/// Statistics from a frame index elimination pass.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct EliminationStats {
    /// Number of FrameIndex/StackSlot operands replaced.
    pub eliminated_count: u32,
    /// Number of large offsets that required scratch register materialization.
    pub large_offset_count: u32,
}

/// Enhanced frame index elimination pass.
///
/// Resolves all `FrameIndex` and `StackSlot` operands in a function to
/// concrete memory operands (FP+offset or SP+offset), handling large
/// offsets that exceed AArch64 immediate encoding range.
///
/// # Large offset handling
///
/// When an offset exceeds the encodable immediate range (-256..4095),
/// the eliminator inserts instructions to materialize the offset in X16 (IP0):
///
/// ```asm
/// movz  x16, #offset_lo             ; lower 16 bits
/// movk  x16, #offset_hi, lsl #16    ; upper 16 bits (if needed)
/// add   x16, fp, x16                ; compute absolute address
/// ; then use [x16, #0] as the memory operand
/// ```
pub struct FrameIndexEliminator<'a> {
    /// The computed frame layout.
    layout: &'a FrameLayout,
    /// Precomputed FP-relative offset for each stack slot (indexed by slot number).
    slot_offsets: Vec<i32>,
    /// Whether a slot is runtime-sized and cannot use fixed frame offsets yet.
    runtime_sized_slots: Vec<bool>,
    /// `FP + x == SP + (x + delta)` for this frame, when SP is provably fixed
    /// from the end of the prologue to the start of the epilogue. `None` when
    /// SP moves (dynamic alloca / runtime-sized slot) or the frame shape is not
    /// the canonical FP one, in which case no slot may be re-based onto SP.
    /// See [`FrameIndexEliminator::resolve_slot_operand_for_inst`].
    sp_rebase_delta: Option<i64>,
}

/// Fail-closed frame-index legalization errors. Failed transforms must not be
/// encoded: the caller retains its function for diagnostics, not publication.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum FrameIndexEliminationError {
    #[error("runtime-sized stack slot {slot} requires dynamic SP lowering")]
    RuntimeSizedSlot { slot: usize },
    #[error("frame slot {slot} is outside the {slots}-slot frame layout")]
    InvalidSlot { slot: usize, slots: usize },
    #[error("incoming argument offset {offset} exceeds the signed frame-offset domain")]
    IncomingArgumentOffsetOverflow { offset: i64 },
    #[error("invalid frame instruction {instruction}: {reason}")]
    InvalidInstruction { instruction: u32, reason: String },
    #[error(
        "large frame-offset materialization for instruction {instruction} would clobber IP scratch {scratch:?}"
    )]
    LiveScratch { instruction: u32, scratch: PReg },
}

/// Kill switch for the SP-relative far-slot re-base (`TCG_NO_SP_FAR_SLOT=1`
/// restores byte-identical FP-relative addressing plus scratch materialization).
fn sp_far_slot_disabled() -> bool {
    std::env::var_os("TCG_NO_SP_FAR_SLOT").is_some()
}

/// `Some(delta)` when every fixed stack slot may be addressed as `SP + (fp_off
/// + delta)` at any point in the function body, else `None` (fail closed).
///
/// The Apple-canonical prologue emitted by [`emit_prologue`] is
///
/// ```asm
///   stp <pair>, [sp, #-csa]!      ; SP -= callee_saved_area_size
///   ...
///   add x29, sp, #(csa - 16)      ; FP -> saved FP/LR pair, at the TOP of the CSA
///   sub sp, sp, #sp_adj           ; locals + spills + outgoing args
/// ```
///
/// so `FP == SP_final + sp_adj + csa - 16`, giving
/// `delta = sp_adjustment() + callee_saved_area_size - 16`.
///
/// Preconditions (all refuse the re-base rather than guess):
///  * the frame actually uses FP and saved an FP/LR pair (otherwise the `add
///    x29, sp, #..` above was never emitted and the identity does not hold);
///  * no dynamic alloca and no runtime-sized slot — those move SP mid-body;
///  * not the red-zone shape, whose prologue skips the SP adjustment.
fn sp_rebase_delta_for(layout: &FrameLayout, func: &MachFunction) -> Option<i64> {
    if sp_far_slot_disabled() {
        return None;
    }
    if !layout.uses_frame_pointer || layout.callee_saved_pairs.is_empty() {
        return None;
    }
    if layout.has_dynamic_alloc || layout.uses_red_zone {
        return None;
    }
    if function_has_runtime_stack_slots(func) || function_has_dynamic_stack_alloc_pseudos(func) {
        return None;
    }
    Some(layout.sp_adjustment() as i64 + layout.callee_saved_area_size as i64 - 16)
}

impl<'a> FrameIndexEliminator<'a> {
    /// Create a new eliminator for the given layout and function.
    pub fn new(layout: &'a FrameLayout, func: &MachFunction) -> Self {
        let slot_offsets = compute_slot_offsets(func, layout);
        let runtime_sized_slots = func
            .stack_slots
            .iter()
            .map(|slot| slot.is_runtime_sized())
            .collect();
        let sp_rebase_delta = sp_rebase_delta_for(layout, func);
        Self {
            layout,
            slot_offsets,
            runtime_sized_slots,
            sp_rebase_delta,
        }
    }

    /// Resolve a stack slot index to (base_register, offset).
    ///
    /// Spill/local slots use FP-relative addressing when the frame pointer
    /// is available (always on Apple AArch64). The returned offset is signed.
    pub fn resolve_slot_operand(
        &self,
        slot_idx: usize,
    ) -> Result<(PReg, i64), FrameIndexEliminationError> {
        if self
            .runtime_sized_slots
            .get(slot_idx)
            .copied()
            .unwrap_or(false)
        {
            return Err(FrameIndexEliminationError::RuntimeSizedSlot { slot: slot_idx });
        }
        if slot_idx < self.slot_offsets.len() {
            let fp_offset = self.slot_offsets[slot_idx] as i64;
            if self.layout.uses_frame_pointer {
                // Deep frames: FP-relative offsets below -256 lose single-
                // instruction reach (LDUR window) and go through scratch
                // materialization (2-5 insts per access). The same slot seen
                // from SP is a *positive* offset with unsigned scaled-imm
                // reach in one instruction. The prologue establishes
                // FP = entry_SP - 16 (FP/LR at the top of the callee-saved
                // area) and SP_final = entry_SP - total_frame_size, so
                // FP - SP = total_frame_size - 16 and SP is static afterwards
                // unless the function has dynamic stack allocation. Prefer
                // the SP form exactly when the FP form would need scratch
                // help and the SP form is in direct reach. Small offsets keep
                // the FP form (identical output to before this preference).
                if !self.layout.has_dynamic_alloc && is_large_offset(fp_offset) {
                    let sp_offset = fp_offset + self.layout.total_frame_size as i64 - 16;
                    if !is_large_offset(sp_offset) {
                        return Ok((SP, sp_offset));
                    }
                }
                Ok((X29, fp_offset))
            } else {
                // SP-relative: FP offset + callee_saved_area + sp_adjustment
                let sp_offset = fp_offset + self.layout.sp_adjustment() as i64;
                Ok((SP, sp_offset))
            }
        } else {
            // An unknown slot does not name the outgoing-argument area. Mapping
            // it to SP+0 would silently redirect the caller's memory access.
            Err(FrameIndexEliminationError::InvalidSlot {
                slot: slot_idx,
                slots: self.slot_offsets.len(),
            })
        }
    }

    /// Resolve a stack slot for one specific memory access, preferring an
    /// SP-relative base when the FP-relative offset would NOT encode.
    ///
    /// Locals and spills live *below* FP, so their FP-relative offsets are
    /// negative and only the unscaled `LDUR/STUR` form can hold them — i.e.
    /// anything deeper than `FP-256` needs a scratch register and a second
    /// instruction (`sub x16, x29, #off` + `ldr x16, [x16]`). Measured against
    /// the same slot addressed from SP, the offset is *positive* and small
    /// (`[0, frame_size)`), which the scaled unsigned form encodes directly —
    /// one instruction, no scratch, no extra dependency on the address.
    ///
    /// The re-base is applied ONLY when
    ///  * the frame admits it at all ([`sp_rebase_delta_for`]),
    ///  * the access is a scalar register+immediate load/store whose exact
    ///    encoder scale we can derive, and
    ///  * the FP-relative offset does **not** already encode, while the
    ///    SP-relative one does — under the encoder's own predicate, so this
    ///    can never turn an encodable access into an unencodable one.
    ///
    /// Everything else keeps the historical FP-relative resolution, so the
    /// bytes for already-encodable accesses are unchanged.
    ///
    /// The `bool` says whether the re-base fired. A re-based offset is
    /// encodable *by construction* (the encoder's own predicate approved it),
    /// so the caller must NOT route it through the scratch-materialization
    /// path — `is_large_offset`'s conservative `4095` ceiling would otherwise
    /// send a perfectly encodable scaled offset (e.g. `ldr x0, [sp, #6496]`)
    /// off to a three-instruction address computation.
    fn resolve_slot_operand_for_inst(
        &self,
        slot_idx: usize,
        inst: &MachInst,
    ) -> Result<(PReg, i64, bool), FrameIndexEliminationError> {
        let (base, offset) = self.resolve_slot_operand(slot_idx)?;
        if base != X29 {
            return Ok((base, offset, false));
        }
        let Some(delta) = self.sp_rebase_delta else {
            return Ok((base, offset, false));
        };
        let Some(scale) = crate::aarch64::encode::scalar_ri_mem_scale(inst) else {
            return Ok((base, offset, false));
        };
        if crate::aarch64::encode::scalar_ri_offset_encodable(offset, scale) {
            return Ok((base, offset, false));
        }
        let sp_offset = offset + delta;
        if sp_offset >= 0 && crate::aarch64::encode::scalar_ri_offset_encodable(sp_offset, scale) {
            Ok((SP, sp_offset, true))
        } else {
            Ok((base, offset, false))
        }
    }

    /// Does this slot access still need a scratch-register address?
    ///
    /// Unchanged (`is_large_offset`) for every access that keeps its
    /// FP-relative base; never for a re-based one.
    fn slot_access_needs_scratch(
        &self,
        slot_idx: usize,
        inst: &MachInst,
    ) -> Result<bool, FrameIndexEliminationError> {
        let (_, offset, rebased) = self.resolve_slot_operand_for_inst(slot_idx, inst)?;
        Ok(!rebased && is_large_offset(offset))
    }

    /// Run the frame index elimination pass over the function.
    ///
    /// Replaces all `FrameIndex` and `StackSlot` operands with concrete
    /// `MemOp` operands. For large offsets, inserts scratch register
    /// materialization instructions.
    ///
    /// Returns statistics about the elimination.
    pub fn run(
        &self,
        func: &mut MachFunction,
    ) -> Result<EliminationStats, FrameIndexEliminationError> {
        let mut stats = EliminationStats::default();

        // Early exit: if no stack slots, no frame indices can exist.
        if func.stack_slots.is_empty() && !self.has_frame_operands(func) {
            return Ok(stats);
        }

        let mut attached = vec![false; func.insts.len()];

        // Liveness follows block/instruction references before rewriting. Admit
        // those indices here for direct users of the public frame pass too.
        if let Some(block) = func
            .block_order
            .iter()
            .find(|block| block.0 as usize >= func.blocks.len())
        {
            return Err(FrameIndexEliminationError::InvalidInstruction {
                instruction: block.0,
                reason: "block order references a block outside the arena".into(),
            });
        }
        if let Some(instruction) = func
            .blocks
            .iter()
            .flat_map(|block| &block.insts)
            .find(|instruction| instruction.0 as usize >= func.insts.len())
        {
            return Err(FrameIndexEliminationError::InvalidInstruction {
                instruction: instruction.0,
                reason: "block references an instruction outside the arena".into(),
            });
        }

        // Whole-function live-out of the IP scratch pair, so the fail-closed
        // borrow guard below sees live ranges that leave a block (post-RA
        // spill-reload CSE creates them). See `ip_scratch_block_live_out`.
        let block_live_out = ip_scratch_block_live_out(func);

        // Process each block. We must rebuild block instruction lists when
        // large offsets require inserting materialization instructions.
        let num_blocks = func.blocks.len();
        for block_idx in 0..num_blocks {
            // Retain the original block list on rejection. Inserted arena
            // instructions remain diagnostic-only until this block commits.
            let block_insts = func.blocks[block_idx].insts.clone();
            let mut new_insts = Vec::with_capacity(block_insts.len());
            let mut block_modified = false;
            let mut scratch_liveness = ScratchLiveness::new(
                &block_insts,
                block_live_out
                    .get(block_idx)
                    .copied()
                    .unwrap_or((true, true)),
            );

            for (pos, &inst_id) in block_insts.iter().enumerate() {
                if let Some(slot) = attached.get_mut(inst_id.0 as usize) {
                    *slot = true;
                }

                // Check if this instruction has any frame-related operands.
                let mut has_frame_op = false;
                let mut needs_large_offset = false;

                let scan_inst = func.insts.get(inst_id.0 as usize).ok_or_else(|| {
                    FrameIndexEliminationError::InvalidInstruction {
                        instruction: inst_id.0,
                        reason: "block references an instruction outside the arena".into(),
                    }
                })?;
                for operand in &scan_inst.operands {
                    match operand {
                        MachOperand::FrameIndex(fi) => {
                            has_frame_op = true;
                            if self.slot_access_needs_scratch(fi.0 as usize, scan_inst)? {
                                needs_large_offset = true;
                            }
                        }
                        MachOperand::StackSlot(ss) => {
                            has_frame_op = true;
                            if self.slot_access_needs_scratch(ss.0 as usize, scan_inst)? {
                                needs_large_offset = true;
                            }
                        }
                        _ => {}
                    }
                }

                if !has_frame_op {
                    new_insts.push(inst_id);
                    continue;
                }

                if self.is_stack_addr_inst(func, inst_id) {
                    let addr_insts = self.rewrite_stack_addr(func, inst_id, &mut stats)?;
                    block_modified |= addr_insts.len() != 1 || addr_insts[0] != inst_id;
                    for addr_id in addr_insts {
                        new_insts.push(addr_id);
                    }
                } else if needs_large_offset {
                    // Insert materialization instructions before the original.
                    // We need to find the frame memory operand, compute its
                    // offset, materialize it in an IP scratch register, then
                    // rewrite the operand.
                    let mat_insts = self.materialize_and_rewrite(
                        func,
                        inst_id,
                        pos,
                        &mut scratch_liveness,
                        &mut stats,
                    )?;
                    for mat_id in mat_insts {
                        new_insts.push(mat_id);
                    }
                    block_modified = true;
                } else {
                    // Small offset — just rewrite operands in place.
                    self.rewrite_operands_small(func, inst_id, &mut stats)?;
                    new_insts.push(inst_id);
                }
            }

            if block_modified || new_insts.len() != block_insts.len() {
                func.blocks[block_idx].insts = new_insts;
            } else {
                // Restore the original inst list (operands were modified in place).
                func.blocks[block_idx].insts = new_insts;
            }
        }

        // Preserve the public contract for detached arena instructions too.
        // They are not encoded, so large offsets do not need materialization;
        // they only need their abstract frame operands resolved.
        for inst_idx in 0..func.insts.len() {
            if attached.get(inst_idx).copied().unwrap_or(false) {
                continue;
            }
            let inst_id = trust_cg_ir::types::InstId(inst_idx as u32);
            if self.inst_has_frame_operands(func, inst_id) {
                self.rewrite_operands_small(func, inst_id, &mut stats)?;
            }
        }

        Ok(stats)
    }

    /// Check if any instruction has FrameIndex or StackSlot operands.
    fn has_frame_operands(&self, func: &MachFunction) -> bool {
        func.insts.iter().any(|inst| {
            inst.operands
                .iter()
                .any(|op| matches!(op, MachOperand::FrameIndex(_) | MachOperand::StackSlot(_)))
        })
    }

    fn inst_has_frame_operands(
        &self,
        func: &MachFunction,
        inst_id: trust_cg_ir::types::InstId,
    ) -> bool {
        func.insts[inst_id.0 as usize]
            .operands
            .iter()
            .any(|op| matches!(op, MachOperand::FrameIndex(_) | MachOperand::StackSlot(_)))
    }

    fn frame_operand_slot(operand: &MachOperand) -> Option<usize> {
        match operand {
            MachOperand::FrameIndex(fi) => Some(fi.0 as usize),
            MachOperand::StackSlot(ss) => Some(ss.0 as usize),
            _ => None,
        }
    }

    fn frame_operand_indices(&self, inst: &MachInst) -> Vec<(usize, usize)> {
        inst.operands
            .iter()
            .enumerate()
            .filter_map(|(idx, operand)| Self::frame_operand_slot(operand).map(|slot| (idx, slot)))
            .collect()
    }

    fn is_stack_addr_inst(&self, func: &MachFunction, inst_id: trust_cg_ir::types::InstId) -> bool {
        let inst = &func.insts[inst_id.0 as usize];
        inst.opcode == AArch64Opcode::AddPCRel
            && matches!(
                inst.operands.get(2),
                Some(MachOperand::FrameIndex(_) | MachOperand::StackSlot(_))
            )
    }

    fn base_operand(base_reg: PReg) -> MachOperand {
        if base_reg == SP {
            MachOperand::Special(SpecialReg::SP)
        } else {
            MachOperand::PReg(base_reg)
        }
    }

    fn address_scratch_for_load_destination(
        inst: &MachInst,
        frame_operand_idx: usize,
    ) -> Option<PReg> {
        if frame_operand_idx == 0 || !Self::is_single_register_load(inst.opcode) {
            return None;
        }

        let Some(MachOperand::PReg(dst)) = inst.operands.first() else {
            return None;
        };

        let scratch = match preg_class(*dst) {
            RegClass::Gpr64 => Some(*dst),
            RegClass::Gpr32 => gpr32_to_gpr64(*dst),
            _ => None,
        }?;

        if scratch == SP || scratch == XZR {
            None
        } else {
            Some(scratch)
        }
    }

    fn is_single_register_load(opcode: AArch64Opcode) -> bool {
        matches!(
            opcode,
            AArch64Opcode::LdrRI
                | AArch64Opcode::LdrbRI
                | AArch64Opcode::LdrhRI
                | AArch64Opcode::LdrsbRI
                | AArch64Opcode::LdrshRI
        )
    }

    fn inst_overlaps_scratch(&self, inst: &MachInst, scratch: PReg) -> bool {
        inst.operands.iter().any(|operand| match operand {
            MachOperand::PReg(reg) => regs_overlap(*reg, scratch),
            MachOperand::MemOp { base, .. } => regs_overlap(*base, scratch),
            _ => false,
        })
    }

    fn materialize_abs_offset(
        &self,
        func: &mut MachFunction,
        dst: PReg,
        abs_offset: u64,
    ) -> Vec<trust_cg_ir::types::InstId> {
        let mut result = Vec::with_capacity(2);
        let lo16 = (abs_offset & 0xFFFF) as i64;
        let movz = MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::PReg(dst), MachOperand::Imm(lo16)],
        );
        result.push(func.push_inst(movz));

        if abs_offset > 0xFFFF {
            let hi16 = ((abs_offset >> 16) & 0xFFFF) as i64;
            let movk = MachInst::new(
                AArch64Opcode::Movk,
                vec![
                    MachOperand::PReg(dst),
                    MachOperand::Imm(hi16),
                    MachOperand::Imm(16),
                ],
            );
            result.push(func.push_inst(movk));
        }

        result
    }

    fn rewrite_stack_addr(
        &self,
        func: &mut MachFunction,
        inst_id: trust_cg_ir::types::InstId,
        stats: &mut EliminationStats,
    ) -> Result<Vec<trust_cg_ir::types::InstId>, FrameIndexEliminationError> {
        let (dst, base_reg, offset) = {
            let inst = &func.insts[inst_id.0 as usize];
            let dst = match inst.operands.first() {
                Some(MachOperand::PReg(dst)) => *dst,
                other => {
                    return Err(FrameIndexEliminationError::InvalidInstruction {
                        instruction: inst_id.0,
                        reason: format!("StackAddr AddPCRel expected PReg dst, got {other:?}"),
                    });
                }
            };
            let Some(slot_idx) = inst.operands.get(2).and_then(Self::frame_operand_slot) else {
                return Err(FrameIndexEliminationError::InvalidInstruction {
                    instruction: inst_id.0,
                    reason: "StackAddr AddPCRel missing frame operand at index 2".into(),
                });
            };
            let (base_reg, offset) = self.resolve_slot_operand(slot_idx)?;
            (dst, base_reg, offset)
        };

        let abs_offset = offset.unsigned_abs();
        let base_operand = Self::base_operand(base_reg);
        stats.eliminated_count += 1;

        if abs_offset <= 4095 {
            let opcode = if offset >= 0 {
                AArch64Opcode::AddRI
            } else {
                AArch64Opcode::SubRI
            };
            func.insts[inst_id.0 as usize] = MachInst::new(
                opcode,
                vec![
                    MachOperand::PReg(dst),
                    base_operand,
                    MachOperand::Imm(abs_offset as i64),
                ],
            );
            return Ok(vec![inst_id]);
        }

        let mut result = self.materialize_abs_offset(func, dst, abs_offset);
        let opcode = if offset >= 0 {
            AArch64Opcode::AddRR
        } else {
            AArch64Opcode::SubRR
        };
        func.insts[inst_id.0 as usize] = MachInst::new(
            opcode,
            vec![MachOperand::PReg(dst), base_operand, MachOperand::PReg(dst)],
        );
        stats.large_offset_count += 1;
        result.push(inst_id);
        Ok(result)
    }

    /// Rewrite small-offset frame operands in place (no new instructions needed).
    fn rewrite_operands_small(
        &self,
        func: &mut MachFunction,
        inst_id: trust_cg_ir::types::InstId,
        stats: &mut EliminationStats,
    ) -> Result<(), FrameIndexEliminationError> {
        // Resolve against a snapshot: `resolve_slot_operand_for_inst` needs the
        // (still unmodified) operand list to derive the encoder's access scale,
        // and the borrow checker will not hand us both at once.
        let snapshot = func.insts[inst_id.0 as usize].clone();
        let inst = &mut func.insts[inst_id.0 as usize];
        for operand in &mut inst.operands {
            match operand {
                MachOperand::FrameIndex(fi) => {
                    let slot_idx = fi.0 as usize;
                    let (base, offset, _) =
                        self.resolve_slot_operand_for_inst(slot_idx, &snapshot)?;
                    *operand = MachOperand::MemOp { base, offset };
                    stats.eliminated_count += 1;
                }
                MachOperand::StackSlot(ss) => {
                    let slot_idx = ss.0 as usize;
                    let (base, offset, _) =
                        self.resolve_slot_operand_for_inst(slot_idx, &snapshot)?;
                    *operand = MachOperand::MemOp { base, offset };
                    stats.eliminated_count += 1;
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Materialize an address that still needs scratch after the direct FP and
    /// proven-static SP encodings have been considered. Borrow an IP register
    /// only after operand-overlap and whole-function liveness checks. Return
    /// the replacement instruction IDs, or a typed refusal if no safe
    /// address materialization exists.
    fn materialize_and_rewrite(
        &self,
        func: &mut MachFunction,
        inst_id: trust_cg_ir::types::InstId,
        pos: usize,
        scratch_liveness: &mut ScratchLiveness<'_>,
        stats: &mut EliminationStats,
    ) -> Result<Vec<trust_cg_ir::types::InstId>, FrameIndexEliminationError> {
        let mut result = Vec::with_capacity(4);

        // Large memory offsets are only supported for single-address
        // load/store forms. Rewriting multiple independent frame operands to
        // one materialized address would be a silent miscompile.
        let (frame_operand_idx, base_reg, offset) = {
            let inst = &func.insts[inst_id.0 as usize];
            let frame_operands = self.frame_operand_indices(inst);
            if frame_operands.len() != 1 {
                return Err(FrameIndexEliminationError::InvalidInstruction {
                    instruction: inst_id.0,
                    reason: format!(
                        "large frame-offset materialization requires exactly one frame operand, got {}",
                        frame_operands.len()
                    ),
                });
            }
            let (operand_idx, slot_idx) = frame_operands[0];
            let (base_reg, offset, _) = self.resolve_slot_operand_for_inst(slot_idx, inst)?;
            (operand_idx, base_reg, offset)
        };
        // `is_ip_scratch` distinguishes the two safe-scratch sources: the load's
        // OWN destination register (overwritten by the load, so its prior value
        // is dead by definition — no liveness check needed) versus a borrowed
        // IP scratch (X16/X17), which must be proven dead before we clobber it.
        let (scratch_reg, is_ip_scratch) = {
            let inst = &func.insts[inst_id.0 as usize];
            if let Some(scratch) =
                Self::address_scratch_for_load_destination(inst, frame_operand_idx)
            {
                (scratch, false)
            } else if !self.inst_overlaps_scratch(inst, X16) {
                (X16, true)
            } else if !self.inst_overlaps_scratch(inst, X17) {
                (X17, true)
            } else {
                return Err(FrameIndexEliminationError::InvalidInstruction {
                    instruction: inst_id.0,
                    reason: "both X16 and X17 are live operands; no safe address scratch register"
                        .into(),
                });
            }
        };

        // Fail-closed IP-scratch liveness guard (the pr28982b regalloc-spill
        // miscompile class). Materializing the effective address OVERWRITES the
        // borrowed IP scratch. That is only sound when the scratch is dead here;
        // if a later instruction in this block still reads it before redefining
        // it, this would silently corrupt that live value (a paired spill
        // materialization once left a live loop-carried pointer in X17 across
        // this store). A verified backend must fail closed — a named compile
        // error — rather than emit the miscompile. This never fires on
        // well-formed spill code, where X16/X17 never carry a value across the
        // spill store/load being rewritten.
        if is_ip_scratch && scratch_liveness.live_after(func, pos, scratch_reg) {
            return Err(FrameIndexEliminationError::LiveScratch {
                instruction: inst_id.0,
                scratch: scratch_reg,
            });
        }

        // Compute `base_reg + offset` into the chosen scratch. The shared helper
        // uses the single ADD/SUB #imm12 form when |offset| <= 4095 (one fewer
        // instruction than MOVZ + reg-form) and MOVZ/MOVK + reg-form otherwise —
        // the effective address left in the scratch is identical either way.
        // This path only runs on frame slots whose FP-/SP-relative offset is out
        // of the encodable immediate range, so at least one instruction is
        // always emitted before the rewrite below.
        if let Err(err) =
            emit_effective_address_into_scratch(func, scratch_reg, base_reg, offset, &mut result)
        {
            return Err(FrameIndexEliminationError::InvalidInstruction {
                instruction: inst_id.0,
                reason: err,
            });
        }

        // Rewrite the single frame memory operand to [scratch, #0]. The effective
        // address is unchanged (scratch == base_reg + offset), so the transferred
        // bytes go to/from the same address.
        let inst = &mut func.insts[inst_id.0 as usize];
        inst.operands[frame_operand_idx] = MachOperand::MemOp {
            base: scratch_reg,
            offset: 0,
        };
        stats.eliminated_count += 1;
        stats.large_offset_count += 1;
        result.push(inst_id);

        Ok(result)
    }
}

// ---------------------------------------------------------------------------
// Compact unwind encoding
// ---------------------------------------------------------------------------

/// Darwin compact unwind encoding for an AArch64 function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CompactUnwindEncoding {
    /// The 32-bit encoding value.
    pub encoding: u32,
}

impl CompactUnwindEncoding {
    /// Returns true if this encoding requires DWARF CFI fallback.
    ///
    /// When `UNWIND_ARM64_MODE_DWARF` is set, the linker expects a
    /// corresponding FDE in `__eh_frame` to describe how to unwind this
    /// function. The compact unwind entry still exists but its encoding
    /// tells the unwinder to look up the DWARF info instead.
    pub fn needs_dwarf_fallback(&self) -> bool {
        (self.encoding & 0x0F00_0000) == UNWIND_ARM64_MODE_DWARF
    }

    /// Returns the mode bits (top nibble of the encoding).
    pub fn mode(&self) -> u32 {
        self.encoding & 0x0F00_0000
    }

    /// Returns the register-pair flags (low 12 bits for FRAME mode).
    pub fn register_pair_flags(&self) -> u32 {
        self.encoding & 0x0000_0FFF
    }
}

/// Encode the Darwin compact unwind for a frame layout.
///
/// For standard FP-based frames, this produces `UNWIND_ARM64_MODE_FRAME`
/// with register-pair flags indicating which callee-saved registers are saved.
///
/// Emits `UNWIND_ARM64_MODE_FRAMELESS` for the zero-byte trivial leaf layout.
/// Falls back to `UNWIND_ARM64_MODE_DWARF` when the frame cannot be described
/// by compact unwind:
/// - Non-zero frameless functions
/// - Variable-size frames (SP moves by runtime amount)
///
/// Reference: AArch64AsmBackend.cpp `generateCompactUnwindEncoding()` (line 576)
pub fn encode_compact_unwind(layout: &FrameLayout) -> CompactUnwindEncoding {
    if !layout.uses_frame_pointer {
        if !layout.has_dynamic_alloc
            && layout.total_frame_size == 0
            && layout.callee_saved_pairs.is_empty()
        {
            return CompactUnwindEncoding {
                encoding: UNWIND_ARM64_MODE_FRAMELESS,
            };
        }

        return CompactUnwindEncoding {
            encoding: UNWIND_ARM64_MODE_DWARF,
        };
    }

    if layout.has_dynamic_alloc {
        // Variable-size frames cannot be described by compact unwind.
        // The unwinder needs full DWARF CFI to handle the dynamic SP offsets.
        return CompactUnwindEncoding {
            encoding: UNWIND_ARM64_MODE_DWARF,
        };
    }

    let mut encoding = UNWIND_ARM64_MODE_FRAME;

    // Encode which callee-saved pairs are saved (skip pair[0] = FP/LR, always implicit).
    for pair in layout.callee_saved_pairs.iter().skip(1) {
        if !pair.is_fpr {
            // GPR pair — X19-X28 encoding unchanged (19-28)
            let flag = match (pair.reg1.encoding(), pair.reg2.encoding()) {
                (19, 20) => UNWIND_ARM64_FRAME_X19_X20_PAIR,
                (21, 22) => UNWIND_ARM64_FRAME_X21_X22_PAIR,
                (23, 24) => UNWIND_ARM64_FRAME_X23_X24_PAIR,
                (25, 26) => UNWIND_ARM64_FRAME_X25_X26_PAIR,
                (27, 28) => UNWIND_ARM64_FRAME_X27_X28_PAIR,
                (r1, r2) => {
                    // Unrecognized GPR callee-saved pair — compact unwind cannot
                    // encode it. Fall back to DWARF mode so the unwinder uses
                    // full CFI instead of producing wrong unwind info.
                    eprintln!(
                        "WARNING: unrecognized callee-saved GPR pair ({}, {}) in \
                         compact unwind encoding, falling back to DWARF mode",
                        r1, r2
                    );
                    return CompactUnwindEncoding {
                        encoding: UNWIND_ARM64_MODE_DWARF,
                    };
                }
            };
            encoding |= flag;
        } else {
            // FPR pair (V8-V15 encode as D8-D15 for compact unwind)
            // V8=72, V9=73, ..., V15=79 in unified PReg encoding
            let flag = match (pair.reg1.encoding(), pair.reg2.encoding()) {
                (72, 73) => UNWIND_ARM64_FRAME_D8_D9_PAIR,   // V8/V9
                (74, 75) => UNWIND_ARM64_FRAME_D10_D11_PAIR, // V10/V11
                (76, 77) => UNWIND_ARM64_FRAME_D12_D13_PAIR, // V12/V13
                (78, 79) => UNWIND_ARM64_FRAME_D14_D15_PAIR, // V14/V15
                (r1, r2) => {
                    // Unrecognized FPR callee-saved pair — compact unwind cannot
                    // encode it. Fall back to DWARF mode so the unwinder uses
                    // full CFI instead of producing wrong unwind info.
                    eprintln!(
                        "WARNING: unrecognized callee-saved FPR pair ({}, {}) in \
                         compact unwind encoding, falling back to DWARF mode",
                        r1, r2
                    );
                    return CompactUnwindEncoding {
                        encoding: UNWIND_ARM64_MODE_DWARF,
                    };
                }
            };
            encoding |= flag;
        }
    }

    CompactUnwindEncoding { encoding }
}

// ---------------------------------------------------------------------------
// Instruction builders (private helpers)
// ---------------------------------------------------------------------------

/// STP Rt, Rt2, [SP, #-imm]! (pre-index, allocates stack space)
#[inline]
fn make_stp_pre_index(reg1: PReg, reg2: PReg, offset: i64) -> MachInst {
    MachInst::new(
        AArch64Opcode::StpPreIndex,
        vec![
            MachOperand::PReg(reg1),
            MachOperand::PReg(reg2),
            MachOperand::Special(SpecialReg::SP),
            MachOperand::Imm(offset),
        ],
    )
}

/// STP Rt, Rt2, [SP, #imm] (signed offset from current SP)
#[inline]
fn make_stp_offset(reg1: PReg, reg2: PReg, offset: i64) -> MachInst {
    MachInst::new(
        AArch64Opcode::StpRI,
        vec![
            MachOperand::PReg(reg1),
            MachOperand::PReg(reg2),
            MachOperand::Special(SpecialReg::SP),
            MachOperand::Imm(offset),
        ],
    )
}

/// LDP Rt, Rt2, [SP, #imm] (signed offset load pair)
#[inline]
fn make_ldp_offset(reg1: PReg, reg2: PReg, offset: i64) -> MachInst {
    MachInst::new(
        AArch64Opcode::LdpRI,
        vec![
            MachOperand::PReg(reg1),
            MachOperand::PReg(reg2),
            MachOperand::Special(SpecialReg::SP),
            MachOperand::Imm(offset),
        ],
    )
}

/// LDP Rt, Rt2, [base, #imm] (signed offset load pair from an arbitrary base).
///
/// Used by the dynamic-frame epilogue to restore extra callee-saved pairs from
/// FP-relative slots (FP points at the saved FP/LR pair; the extras sit below
/// it at negative offsets).
#[inline]
fn make_ldp_base_offset(reg1: PReg, reg2: PReg, base: PReg, offset: i64) -> MachInst {
    MachInst::new(
        AArch64Opcode::LdpRI,
        vec![
            MachOperand::PReg(reg1),
            MachOperand::PReg(reg2),
            MachOperand::PReg(base),
            MachOperand::Imm(offset),
        ],
    )
}

fn lower64_fpr_alias(reg: PReg) -> PReg {
    match preg_class(reg) {
        RegClass::Fpr128 => PReg::new(reg.encoding() + 32),
        RegClass::Fpr32 => PReg::new(reg.encoding() - 32),
        RegClass::Fpr64 => reg,
        _ => reg,
    }
}

fn storage_regs_for_callee_saved_pair(pair: &CalleeSavedPair) -> (PReg, PReg) {
    if pair.is_fpr {
        (lower64_fpr_alias(pair.reg1), lower64_fpr_alias(pair.reg2))
    } else {
        (pair.reg1, pair.reg2)
    }
}

/// LDP Rt, Rt2, [SP], #imm (post-index, deallocates stack space)
#[inline]
fn make_ldp_post_index(reg1: PReg, reg2: PReg, offset: i64) -> MachInst {
    MachInst::new(
        AArch64Opcode::LdpPostIndex,
        vec![
            MachOperand::PReg(reg1),
            MachOperand::PReg(reg2),
            MachOperand::Special(SpecialReg::SP),
            MachOperand::Imm(offset),
        ],
    )
}

/// MOV X29, SP (establish frame pointer)
///
/// Encoded as ADD X29, SP, #0 because register 31 in ADD context is SP,
/// whereas in ORR (logical) context register 31 is XZR.
#[inline]
fn make_mov_sp_to_fp() -> MachInst {
    make_add_fp_sp_imm(0)
}

/// ADD X29, SP, #imm — establish the frame pointer at `SP + imm`.
///
/// With the Apple-canonical FRAME layout, FP points at the saved FP/LR pair,
/// which sits at the TOP of the callee-saved area (offset `csa - 16` from the
/// post-allocation SP). `imm == 0` degenerates to `MOV X29, SP`.
#[inline]
fn make_add_fp_sp_imm(imm: i64) -> MachInst {
    MachInst::new(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::PReg(X29),
            MachOperand::Special(SpecialReg::SP),
            MachOperand::Imm(imm),
        ],
    )
}

/// MOV SP, X29 (discard dynamic stack allocations and fixed local area).
///
/// Encoded as ADD SP, X29, #0 in the ADD-immediate register context.
#[inline]
fn make_mov_fp_to_sp() -> MachInst {
    MachInst::new(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::Special(SpecialReg::SP),
            MachOperand::PReg(X29),
            MachOperand::Imm(0),
        ],
    )
}

/// SUB SP, SP, #imm (allocate stack space)
#[inline]
fn make_sub_sp_imm(imm: i64) -> MachInst {
    MachInst::new(
        AArch64Opcode::SubRI,
        vec![
            MachOperand::Special(SpecialReg::SP),
            MachOperand::Special(SpecialReg::SP),
            MachOperand::Imm(imm),
        ],
    )
}

/// ADD SP, SP, #imm (deallocate stack space)
#[inline]
fn make_add_sp_imm(imm: i64) -> MachInst {
    MachInst::new(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::Special(SpecialReg::SP),
            MachOperand::Special(SpecialReg::SP),
            MachOperand::Imm(imm),
        ],
    )
}

fn push_sub_sp_imm(insts: &mut Vec<MachInst>, imm: u32) {
    push_sp_imm_chunks(insts, imm, make_sub_sp_imm);
}

fn push_add_sp_imm(insts: &mut Vec<MachInst>, imm: u32) {
    push_sp_imm_chunks(insts, imm, make_add_sp_imm);
}

fn push_sp_imm_chunks(insts: &mut Vec<MachInst>, mut imm: u32, make: fn(i64) -> MachInst) {
    debug_assert_eq!(imm % STACK_ALIGNMENT, 0, "SP adjustment must stay aligned");
    while imm > 0 {
        let chunk = imm.min(AARCH64_SP_ADJUST_CHUNK);
        insts.push(make(i64::from(chunk)));
        imm -= chunk;
    }
}

/// RET (return via X30)
#[inline]
fn make_ret() -> MachInst {
    MachInst::new(AArch64Opcode::Ret, vec![])
}

// ---------------------------------------------------------------------------
// Utility
// ---------------------------------------------------------------------------

/// Align `value` up to the next multiple of `align`.
///
/// `align` must be a power of two.
#[inline]
#[cfg(test)]
fn align_up(value: u32, align: u32) -> u32 {
    debug_assert!(align.is_power_of_two());
    (value + align - 1) & !(align - 1)
}

fn make_nop() -> MachInst {
    MachInst::new(AArch64Opcode::Nop, vec![])
}

fn make_mov_reg(dst: PReg, src: PReg) -> MachInst {
    MachInst::new(
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(dst), MachOperand::PReg(src)],
    )
}

fn make_movz_imm(dst: PReg, imm: i64) -> MachInst {
    MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(dst), MachOperand::Imm(imm)],
    )
}

fn make_movk_imm(dst: PReg, imm: i64, shift: i64) -> MachInst {
    MachInst::new(
        AArch64Opcode::Movk,
        vec![
            MachOperand::PReg(dst),
            MachOperand::Imm(imm),
            MachOperand::Imm(shift),
        ],
    )
}

fn make_lsl_imm(dst: PReg, src: PReg, shift: i64) -> MachInst {
    MachInst::new(
        AArch64Opcode::LslRI,
        vec![
            MachOperand::PReg(dst),
            MachOperand::PReg(src),
            MachOperand::Imm(shift),
        ],
    )
}

fn make_lsr_imm(dst: PReg, src: PReg, shift: i64) -> MachInst {
    MachInst::new(
        AArch64Opcode::LsrRI,
        vec![
            MachOperand::PReg(dst),
            MachOperand::PReg(src),
            MachOperand::Imm(shift),
        ],
    )
}

fn make_uxtw(dst: PReg, src: PReg) -> MachInst {
    MachInst::new(
        AArch64Opcode::Uxtw,
        vec![MachOperand::PReg(dst), MachOperand::PReg(src)],
    )
}

fn make_mul_reg(dst: PReg, lhs: PReg, rhs: PReg) -> MachInst {
    MachInst::new(
        AArch64Opcode::MulRR,
        vec![
            MachOperand::PReg(dst),
            MachOperand::PReg(lhs),
            MachOperand::PReg(rhs),
        ],
    )
}

fn make_mov_sp_to_reg(dst: PReg) -> MachInst {
    MachInst::new(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::PReg(dst),
            MachOperand::Special(SpecialReg::SP),
            MachOperand::Imm(0),
        ],
    )
}

fn make_mov_reg_to_sp(src: PReg) -> MachInst {
    MachInst::new(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::Special(SpecialReg::SP),
            MachOperand::PReg(src),
            MachOperand::Imm(0),
        ],
    )
}

fn emit_materialize_u64(dst: PReg, value: u64, out: &mut Vec<MachInst>) {
    out.push(make_movz_imm(dst, (value & 0xFFFF) as i64));
    for shift in [16_u32, 32, 48] {
        let part = ((value >> shift) & 0xFFFF) as i64;
        if part != 0 {
            out.push(make_movk_imm(dst, part, shift as i64));
        }
    }
}

fn stack_alloc_scratch(dst: PReg, src: Option<PReg>) -> Option<PReg> {
    if !regs_overlap(dst, X16) && !src.is_some_and(|reg| regs_overlap(reg, X16)) {
        Some(X16)
    } else if !regs_overlap(dst, X17) && !src.is_some_and(|reg| regs_overlap(reg, X17)) {
        Some(X17)
    } else {
        None
    }
}

fn emit_stack_alloc_size(
    dst: PReg,
    size_operand: &MachOperand,
    unit_size: u32,
    out: &mut Vec<MachInst>,
) -> Result<(), crate::lower::LowerError> {
    match size_operand {
        MachOperand::Imm(count) => {
            if *count < 0 {
                return Err(frame_insertion_error(format!(
                    "runtime stack allocation count must be non-negative, got {count}"
                )));
            }
            // FINDING #10a: a well-typed but huge constant-count alloca (e.g.
            // [i64; ~2^61]) makes count*unit_size overflow u64. Previously this
            // tripped `.expect()` and ABORTED the compiler; now it returns a
            // typed FrameLowering error up the existing Result chain.
            let bytes = (*count as u64).checked_mul(unit_size as u64).ok_or_else(|| {
                crate::lower::LowerError::FrameLowering(format!(
                    "runtime stack allocation immediate size overflow: count {count} * unit {unit_size} exceeds u64"
                ))
            })?;
            emit_materialize_u64(dst, bytes, out);
        }
        MachOperand::PReg(src) => {
            let src64 = if preg_class(*src) == RegClass::Gpr32 {
                out.push(make_uxtw(dst, *src));
                dst
            } else {
                *src
            };

            if unit_size == 1 {
                if src64 != dst {
                    out.push(make_mov_reg(dst, src64));
                }
            } else if unit_size.is_power_of_two() {
                out.push(make_lsl_imm(dst, src64, unit_size.trailing_zeros() as i64));
            } else if let Some(scratch) = stack_alloc_scratch(dst, Some(src64)) {
                emit_materialize_u64(scratch, unit_size as u64, out);
                out.push(make_mul_reg(dst, src64, scratch));
            } else if !regs_overlap(dst, src64) {
                emit_materialize_u64(dst, unit_size as u64, out);
                out.push(make_mul_reg(dst, src64, dst));
            } else {
                // FINDING #10a class: a register-allocation shape this expansion
                // cannot lower, not an impossible state. Surface it up the
                // existing Result chain instead of aborting the compiler.
                return Err(crate::lower::LowerError::FrameLowering(format!(
                    "runtime stack allocation needs a scratch register, but both X16 and X17 \
                     conflict with dst {dst:?} and size {src64:?}"
                )));
            }
        }
        other => {
            return Err(crate::lower::LowerError::FrameLowering(format!(
                "runtime stack allocation size must be a PReg or Imm operand, got {other:?}"
            )));
        }
    }
    Ok(())
}

fn emit_round_up_power_of_two(reg: PReg, align: u32, out: &mut Vec<MachInst>) {
    debug_assert!(align.is_power_of_two());
    out.push(MachInst::new(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::PReg(reg),
            MachOperand::PReg(reg),
            MachOperand::Imm((align - 1) as i64),
        ],
    ));
    out.push(make_lsr_imm(reg, reg, align.trailing_zeros() as i64));
    out.push(make_lsl_imm(reg, reg, align.trailing_zeros() as i64));
}

fn emit_clamp_stack_alloc_minimum(reg: PReg, out: &mut Vec<MachInst>) {
    let scratch = stack_alloc_scratch(reg, None)
        .expect("runtime stack allocation minimum clamp needs an IP scratch register");
    emit_materialize_u64(scratch, STACK_ALIGNMENT as u64, out);
    out.push(MachInst::new(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(reg), MachOperand::PReg(scratch)],
    ));
    out.push(MachInst::new(
        AArch64Opcode::Csel,
        vec![
            MachOperand::PReg(reg),
            MachOperand::PReg(scratch),
            MachOperand::PReg(reg),
            MachOperand::Imm(3), // LO: unsigned reg < STACK_ALIGNMENT
        ],
    ));
}

fn emit_add_reg_imm(dst: PReg, mut src: MachOperand, mut imm: u32, out: &mut Vec<MachInst>) {
    if imm == 0 {
        match src {
            MachOperand::PReg(src) if src != dst => out.push(make_mov_reg(dst, src)),
            MachOperand::Special(SpecialReg::SP) => out.push(make_mov_sp_to_reg(dst)),
            _ => {}
        }
        return;
    }
    // ADD-immediate admits SP as its source in both the ordinary and LSL #12
    // forms. Consume the high 12-bit chunks first, then the low remainder;
    // subsequent additions use dst, so no extra scratch or source clobber is
    // needed. This handles the complete u32 outgoing-area domain.
    while imm != 0 {
        let (opcode, encoded, consumed) = if imm >= 4096 {
            let high = (imm >> 12).min(4095);
            (AArch64Opcode::AddRIShift12, high, high << 12)
        } else {
            (AArch64Opcode::AddRI, imm, imm)
        };
        out.push(MachInst::new(
            opcode,
            vec![
                MachOperand::PReg(dst),
                src,
                MachOperand::Imm(i64::from(encoded)),
            ],
        ));
        imm -= consumed;
        src = MachOperand::PReg(dst);
    }
}

/// A runtime stack allocation expanded around its probe loop.
///
/// ```text
/// setup: <dst = aligned byte count, plus the outgoing area>
///        add  s, sp, #0          ; s = target SP = SP - dst
///        sub  s, s, dst
///        add  dst, sp, #0        ; dst = cursor
/// test:  sub  dst, dst, #4096    ; next probe address (two SUB chunks)
///        cmp  dst, s
///        b.ls exit               ; within one interval of the target
/// step:  add  sp, dst, #0
///        str  xzr, [sp]
///        b    test
/// exit:  add  sp, s, #0
///        str  xzr, [sp]
///        <dst = SP + outgoing area, over-aligned if requested>
/// ```
///
/// The walk starts from a touched SP: every nonzero frame's callee-saved
/// store touches it, the static allocation of a frame with runtime
/// allocations ends with a probe, and each runtime allocation probes its final
/// SP. The frame insertion splits the containing block to lay out the loop.
struct DynamicStackAllocExpansion {
    setup: Vec<MachInst>,
    test: Vec<MachInst>,
    step: Vec<MachInst>,
    exit: Vec<MachInst>,
}

fn expand_dynamic_stack_alloc_inst(
    inst: &MachInst,
    outgoing_arg_area_size: u32,
) -> Result<Option<DynamicStackAllocExpansion>, crate::lower::LowerError> {
    if inst.opcode != AArch64Opcode::StackAlloc {
        return Ok(None);
    }

    if inst.operands.len() < 2 {
        return Err(frame_insertion_error(
            "StackAlloc requires destination and count operands",
        ));
    }

    let dst = match inst.operands.first() {
        Some(MachOperand::PReg(dst))
            if preg_class(*dst) == RegClass::Gpr64 && hw_encoding(*dst) < 31 =>
        {
            *dst
        }
        other => {
            return Err(crate::lower::LowerError::FrameLowering(format!(
                "StackAlloc expected a 64-bit GPR destination (excluding register 31), got {other:?}"
            )));
        }
    };
    let size_operand = inst.operands[1].clone();
    let immediate = |index, default| match inst.operands.get(index) {
        None => Ok(default),
        Some(MachOperand::Imm(value)) => Ok(*value),
        Some(other) => Err(frame_insertion_error(format!(
            "StackAlloc operand {index} must be an immediate, got {other:?}"
        ))),
    };
    let unit_size = immediate(2, 1)?;
    if unit_size <= 0 || unit_size > i64::from(u32::MAX) {
        return Err(frame_insertion_error(format!(
            "StackAlloc unit size must fit u32 and be positive, got {unit_size}"
        )));
    }
    let requested_align = immediate(3, i64::from(STACK_ALIGNMENT))?;
    if requested_align <= 0 || requested_align > 4096 || !(requested_align as u64).is_power_of_two()
    {
        return Err(frame_insertion_error(format!(
            "runtime stack allocation alignment {requested_align} must be a power of two <= 4096"
        )));
    }
    if let MachOperand::PReg(src) = size_operand
        && (!matches!(preg_class(src), RegClass::Gpr32 | RegClass::Gpr64) || hw_encoding(src) >= 31)
    {
        return Err(frame_insertion_error(format!(
            "StackAlloc count must be a GPR, got {src:?}"
        )));
    }
    let requested_align = requested_align as u32;

    let mut replacement = Vec::with_capacity(16);
    emit_stack_alloc_size(dst, &size_operand, unit_size as u32, &mut replacement)?;

    // Reserve enough bytes for the object, alignment slack, and the stable
    // outgoing call area below the returned pointer. SP itself remains
    // 16-byte aligned; over-alignment is applied to the returned address.
    if requested_align <= STACK_ALIGNMENT {
        emit_round_up_power_of_two(dst, STACK_ALIGNMENT, &mut replacement);
    } else {
        emit_add_reg_imm(
            dst,
            MachOperand::PReg(dst),
            requested_align - 1,
            &mut replacement,
        );
        emit_round_up_power_of_two(dst, STACK_ALIGNMENT, &mut replacement);
    }
    emit_clamp_stack_alloc_minimum(dst, &mut replacement);

    if outgoing_arg_area_size > 0 {
        emit_add_reg_imm(
            dst,
            MachOperand::PReg(dst),
            outgoing_arg_area_size,
            &mut replacement,
        );
    }

    // AArch64 ADD/SUB shifted-register encodings treat register 31 as XZR,
    // not SP, so SP is only ever read or written through ADD-immediate, where
    // register 31 is the architectural stack pointer.
    let target = stack_alloc_scratch(dst, None).ok_or_else(|| {
        frame_insertion_error(format!(
            "runtime stack allocation needs an IP scratch register distinct from {dst:?}"
        ))
    })?;
    replacement.push(make_mov_sp_to_reg(target));
    replacement.push(MachInst::new(
        AArch64Opcode::SubRR,
        vec![
            MachOperand::PReg(target),
            MachOperand::PReg(target),
            MachOperand::PReg(dst),
        ],
    ));
    replacement.push(make_mov_sp_to_reg(dst));

    let mut test = Vec::with_capacity(3);
    push_sub_reg_imm_chunks(dst, STACK_PROBE_INTERVAL, &mut test);
    test.push(MachInst::new(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(dst), MachOperand::PReg(target)],
    ));

    let step = vec![make_mov_reg_to_sp(dst), make_stack_probe()];

    let mut exit = vec![make_mov_reg_to_sp(target), make_stack_probe()];
    emit_add_reg_imm(
        dst,
        MachOperand::Special(SpecialReg::SP),
        outgoing_arg_area_size,
        &mut exit,
    );
    if requested_align > STACK_ALIGNMENT {
        emit_round_up_power_of_two(dst, requested_align, &mut exit);
    }

    Ok(Some(DynamicStackAllocExpansion {
        setup: replacement,
        test,
        step,
        exit,
    }))
}

/// `SUB reg, reg, #bytes` in encodable immediate chunks.
fn push_sub_reg_imm_chunks(reg: PReg, mut bytes: u32, out: &mut Vec<MachInst>) {
    while bytes > 0 {
        let chunk = bytes.min(AARCH64_SP_ADJUST_CHUNK);
        out.push(MachInst::new(
            AArch64Opcode::SubRI,
            vec![
                MachOperand::PReg(reg),
                MachOperand::PReg(reg),
                MachOperand::Imm(i64::from(chunk)),
            ],
        ));
        bytes -= chunk;
    }
}

/// Expand runtime stack allocation pseudos after register allocation.
///
/// `StackAlloc dst, count, unit, align` computes an aligned byte count, moves
/// SP down by it through the probed walk of [`DynamicStackAllocExpansion`],
/// and returns the newly allocated address in `dst`. For non-leaf callers,
/// each runtime allocation also leaves the fixed outgoing stack-argument area
/// below `dst` so later `[SP + offset]` call stores cannot overlap the
/// allocation's returned object. The containing block is split after the
/// pseudo; the loop blocks sit between its two halves.
fn expand_dynamic_stack_allocs(
    func: &MachFunction,
    plan: &mut FrameInsertionPlan,
    outgoing_arg_area_size: u32,
) -> Result<(), crate::lower::LowerError> {
    // Blocks created below are appended, so a continuation holding further
    // allocations from the same original block is visited later.
    let mut block_idx = 0;
    while block_idx < plan.blocks.len() {
        let block = BlockId(checked_frame_insertion_id(block_idx, 0, "block")?);
        // Match the opcode alone so a malformed pseudo reaches the operand
        // checks below instead of surviving to encoding.
        let view = plan.view(func);
        let found = plan.blocks[block_idx]
            .insts
            .iter()
            .enumerate()
            .map(|(position, &inst_id)| (position, inst_id, &view.insts[inst_id.0 as usize]))
            .find(|(_, _, inst)| inst.opcode == AArch64Opcode::StackAlloc)
            .map(|(position, inst_id, inst)| (position, inst_id, inst.clone()));
        let Some((position, inst_id, inst)) = found else {
            block_idx += 1;
            continue;
        };
        let expansion = expand_dynamic_stack_alloc_inst(&inst, outgoing_arg_area_size)?
            .ok_or_else(|| frame_insertion_error("StackAlloc expansion produced no code"))?;

        let exit = plan.split_block_tail(func, block, position + 1)?;
        plan.blocks[block_idx].insts.pop();
        plan.edited_insts.insert(inst_id.0 as usize, make_nop());
        let test = plan.create_block_after(block, 1)?;
        let step = plan.create_block_after(test, 0)?;

        for inst in expansion.setup {
            let id = plan.push_inst(inst)?;
            plan.blocks[block_idx].insts.push(id);
        }
        for inst in expansion.test.into_iter().chain([MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Imm(COND_LS), MachOperand::Block(exit)],
        )]) {
            let id = plan.push_inst(inst)?;
            plan.blocks[test.0 as usize].insts.push(id);
        }
        for inst in expansion.step.into_iter().chain([MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(test)],
        )]) {
            let id = plan.push_inst(inst)?;
            plan.blocks[step.0 as usize].insts.push(id);
        }
        let mut exit_insts = Vec::with_capacity(expansion.exit.len());
        for inst in expansion.exit {
            exit_insts.push(plan.push_inst(inst)?);
        }
        exit_insts.append(&mut plan.blocks[exit.0 as usize].insts);
        plan.blocks[exit.0 as usize].insts = exit_insts;

        plan.add_edge(block, test);
        plan.add_edge(test, exit);
        plan.add_edge(test, step);
        plan.add_edge(step, test);
        block_idx += 1;
    }
    Ok(())
}

fn retarget_rbit_return_copies(func: &MachFunction, plan: &mut FrameInsertionPlan) -> u32 {
    let mut removed = 0;

    for block_idx in 0..func.blocks.len() {
        let old_insts = std::mem::take(&mut plan.blocks[block_idx].insts);
        let mut new_insts = Vec::with_capacity(old_insts.len());
        let mut idx = 0;

        while idx < old_insts.len() {
            if idx + 2 < old_insts.len()
                && (try_remove_copy_before_rbit_return(&plan.view(func), &old_insts, idx)
                    || try_remove_uxtw_before_rbit_return(&plan.view(func), &old_insts, idx))
            {
                idx += 1;
                removed += 1;
                continue;
            }

            if idx + 2 < old_insts.len()
                && let Some((rbit_id, dst)) =
                    try_retarget_rbit_return_copy(&plan.view(func), &old_insts, idx + 1)
            {
                let mut rbit = plan.view(func).insts[rbit_id.0 as usize].clone();
                rbit.operands[0] = MachOperand::PReg(dst);
                plan.edited_insts.insert(rbit_id.0 as usize, rbit);
                new_insts.push(old_insts[idx]);
                idx += 2;
                removed += 1;
                continue;
            }

            new_insts.push(old_insts[idx]);
            idx += 1;
        }

        plan.blocks[block_idx].insts = new_insts;
    }

    removed
}

fn try_remove_copy_before_rbit_return(
    func: &FrameFunctionView<'_>,
    block_insts: &[InstId],
    copy_idx: usize,
) -> bool {
    if copy_idx + 2 >= block_insts.len() {
        return false;
    }

    let copy = &func.insts[block_insts[copy_idx].0 as usize];
    let rbit = &func.insts[block_insts[copy_idx + 1].0 as usize];
    let ret = &func.insts[block_insts[copy_idx + 2].0 as usize];

    if !is_rbit_return_copy_opcode(copy.opcode)
        || rbit.opcode != AArch64Opcode::Rbit
        || !ret.is_return()
        || copy.opcode == AArch64Opcode::Uxtw
        || copy.operands.len() < 2
        || rbit.operands.len() < 2
        || !copy.implicit_defs.is_empty()
        || !copy.implicit_uses.is_empty()
    {
        return false;
    }

    let (Some(copy_dst), Some(copy_src), Some(rbit_dst), Some(rbit_src)) = (
        copy.operands.first().and_then(MachOperand::as_preg),
        copy.operands.get(1).and_then(MachOperand::as_preg),
        rbit.operands.first().and_then(MachOperand::as_preg),
        rbit.operands.get(1).and_then(MachOperand::as_preg),
    ) else {
        return false;
    };

    rbit_dst == rbit_src
        && preg_class(rbit_src) == RegClass::Gpr32
        && hw_encoding(copy_dst) == hw_encoding(copy_src)
        && hw_encoding(copy_src) == hw_encoding(rbit_src)
}

fn try_remove_uxtw_before_rbit_return(
    func: &FrameFunctionView<'_>,
    block_insts: &[InstId],
    uxtw_idx: usize,
) -> bool {
    if uxtw_idx + 2 >= block_insts.len() {
        return false;
    }

    let uxtw = &func.insts[block_insts[uxtw_idx].0 as usize];
    let rbit = &func.insts[block_insts[uxtw_idx + 1].0 as usize];
    let ret = &func.insts[block_insts[uxtw_idx + 2].0 as usize];

    if uxtw.opcode != AArch64Opcode::Uxtw
        || rbit.opcode != AArch64Opcode::Rbit
        || !ret.is_return()
        || uxtw.operands.len() < 2
        || rbit.operands.len() < 2
        || !uxtw.implicit_defs.is_empty()
        || !uxtw.implicit_uses.is_empty()
    {
        return false;
    }

    let (Some(uxtw_dst), Some(uxtw_src), Some(rbit_dst), Some(rbit_src)) = (
        uxtw.operands.first().and_then(MachOperand::as_preg),
        uxtw.operands.get(1).and_then(MachOperand::as_preg),
        rbit.operands.first().and_then(MachOperand::as_preg),
        rbit.operands.get(1).and_then(MachOperand::as_preg),
    ) else {
        return false;
    };

    preg_class(uxtw_dst) == RegClass::Gpr64
        && preg_class(uxtw_src) == RegClass::Gpr32
        && preg_class(rbit_dst) == RegClass::Gpr32
        && preg_class(rbit_src) == RegClass::Gpr32
        && hw_encoding(uxtw_dst) == hw_encoding(uxtw_src)
        && uxtw_src == rbit_src
        && rbit_dst == rbit_src
}

fn try_retarget_rbit_return_copy(
    func: &FrameFunctionView<'_>,
    block_insts: &[InstId],
    copy_idx: usize,
) -> Option<(InstId, PReg)> {
    if copy_idx == 0 || copy_idx + 1 >= block_insts.len() {
        return None;
    }

    let rbit_id = block_insts[copy_idx - 1];
    let copy_id = block_insts[copy_idx];
    let ret_id = block_insts[copy_idx + 1];

    if !func.insts[ret_id.0 as usize].is_return() {
        return None;
    }

    let copy = &func.insts[copy_id.0 as usize];
    let copy_opcode = copy.opcode;
    if !is_rbit_return_copy_opcode(copy_opcode) || copy.operands.len() < 2 {
        return None;
    }

    let (Some(copy_dst), Some(copy_src)) = (
        copy.operands.first().and_then(MachOperand::as_preg),
        copy.operands.get(1).and_then(MachOperand::as_preg),
    ) else {
        return None;
    };

    let retarget_dst = if copy_opcode == AArch64Opcode::Uxtw {
        if matches!(copy_dst, W0 | X0) {
            W0
        } else {
            return None;
        }
    } else {
        if preg_class(copy_dst) != preg_class(copy_src) {
            return None;
        }
        copy_dst
    };

    if !matches!(retarget_dst, W0 | X0) || preg_class(retarget_dst) != preg_class(copy_src) {
        return None;
    }

    let rbit = &func.insts[rbit_id.0 as usize];
    if rbit.opcode != AArch64Opcode::Rbit || rbit.operands.len() < 2 {
        return None;
    }

    if rbit.operands.first().and_then(MachOperand::as_preg) != Some(copy_src)
        || preg_class(copy_src) != preg_class(retarget_dst)
        || !rbit.implicit_defs.is_empty()
        || !rbit.implicit_uses.is_empty()
    {
        return None;
    }

    Some((rbit_id, retarget_dst))
}

fn is_rbit_return_copy_opcode(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::Copy
            | AArch64Opcode::MovR
            | AArch64Opcode::MOVWrr
            | AArch64Opcode::MOVXrr
            | AArch64Opcode::Uxtw
    )
}

// ===========================================================================
// Shrink-wrapping (Darwin FRAME mode only)  — env: TCG_AARCH64_SHRINKWRAP
// ===========================================================================
//
// Standard frame lowering emits the prologue at function entry and an epilogue
// before every return, so a leaf-guard function (an entry test that separates a
// trivial CSR-free/call-free return from a recursive/call-bearing body) pays the
// full callee-saved save/restore even on the leaf path clang's shrink-wrapping
// skips. Shrink-wrapping SINKS the prologue to the first block `S` that dominates
// every callee-saved / call / stack-slot access, and makes the leaf return a bare
// `ret` — while keeping the SAME `FrameLayout`, so the Darwin compact-unwind FRAME
// encoding (`encode_compact_unwind`, PC-location-independent) is byte-identical
// and synchronous unwinding stays correct (every unwind-visited PC is a call
// return address, and all calls are dominated by `S`).
//
// SCOPE v1 (fail-closed on anything else):
//   * Darwin FRAME-mode compact unwind ONLY (`needs_dwarf_fallback()` false):
//     ELF/DWARF-fallback FDEs hardcode the entry prologue (`DwarfFde::from_layout`),
//     so a shrunk prologue would break them.
//   * no EH landing pads, no stack protector, no dynamic alloc / runtime stack.
//   * the entry block ends in a two-way conditional branch (the guard) and is
//     itself frame-clean (the Piece-A arg-range split moves the incoming-arg->CSR
//     copy off the entry so the guard reads the incoming register).
//   * `S` is not in a loop (the prologue must run at most once).
//   * every block NOT dominated by `S` is frame-clean (no CSR / call / slot / FP
//     dependency) — the soundness core: anything reachable without the prologue
//     must not touch the frame.
//   * there is at least one leaf return (a return not dominated by `S`).
//   * a leaf-shared join return is admitted only when each of its frame-side
//     predecessors is a single-successor block (the epilogue is appended there,
//     on the frame edge, leaving the leaf edge bare).
//
// The whole feature is behind `TCG_AARCH64_SHRINKWRAP` (default OFF); with it
// unset `insert_prologue_epilogue` is byte-identical to before.

/// Whether shrink-wrapping is allowed for this call site's target/object format.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ShrinkWrapEligibility {
    /// Never attempt shrink-wrapping (ELF / DWARF-fallback / non-Darwin, or any
    /// caller that does not opt in). This is the default for every existing
    /// caller, keeping their output byte-identical.
    Disabled,
    /// Darwin Mach-O FRAME-mode target: shrink-wrapping may be attempted
    /// (subject to full admission and the `TCG_AARCH64_SHRINKWRAP_OFF` kill
    /// switch).
    DarwinFrame,
}

/// Shrink-wrapping is ON by default (validated: torture 1064/0 with it firing,
/// bit-exact, compact-unwind byte-identical, fail-closed admission + verify).
/// `TCG_AARCH64_SHRINKWRAP_OFF` is a kill switch that restores the
/// whole-function prologue on every function.
#[inline]
fn shrink_wrap_env_enabled() -> bool {
    std::env::var_os("TCG_AARCH64_SHRINKWRAP_OFF").is_none()
}

/// Iterative block-CFG dominators as a bitset matrix. `dominates(d, b)` is true
/// when every path from entry to `b` passes through `d`. Lifted from the
/// regalloc remat dominator fixpoint (`remat.rs::natural_loop_bodies`).
struct BlockDom {
    n: usize,
    words: usize,
    dom: Vec<u64>,
}

impl BlockDom {
    #[inline]
    fn dominates(&self, d: usize, b: usize) -> bool {
        d < self.n && b < self.n && (self.dom[b * self.words + d / 64] >> (d % 64)) & 1 == 1
    }
}

/// Compute block dominators over `func`'s CFG. Returns `None` for the bail-out
/// cases (empty / oversized / out-of-range entry) so callers treat the function
/// as ineligible for shrink-wrapping.
fn compute_block_dominators(func: &FrameFunctionView<'_>) -> Option<BlockDom> {
    let n = func.blocks.len();
    if n == 0 || n > 4096 {
        return None;
    }
    let entry = func.source.entry.0 as usize;
    if entry >= n {
        return None;
    }
    let words = n.div_ceil(64);
    let mut dom = vec![u64::MAX; n * words];
    let tail_mask = if n.is_multiple_of(64) {
        u64::MAX
    } else {
        (1u64 << (n % 64)) - 1
    };
    for b in 0..n {
        dom[b * words + (words - 1)] &= tail_mask;
    }
    for w in 0..words {
        dom[entry * words + w] = 0;
    }
    dom[entry * words + entry / 64] = 1u64 << (entry % 64);

    let order: Vec<usize> = if func.source.block_order.len() == n {
        func.source
            .block_order
            .iter()
            .map(|b| b.0 as usize)
            .collect()
    } else {
        (0..n).collect()
    };

    let mut scratch = vec![0u64; words];
    let mut changed = true;
    while changed {
        changed = false;
        for &b in &order {
            if b == entry || b >= n {
                continue;
            }
            let mut seen_pred = false;
            scratch.fill(u64::MAX);
            for pred in &func.blocks[b].preds {
                let p = pred.0 as usize;
                if p >= n {
                    continue;
                }
                for w in 0..words {
                    scratch[w] &= dom[p * words + w];
                }
                seen_pred = true;
            }
            if !seen_pred {
                scratch.fill(0);
            }
            scratch[b / 64] |= 1u64 << (b % 64);
            scratch[words - 1] &= tail_mask;

            let mut differs = false;
            for w in 0..words {
                if dom[b * words + w] != scratch[w] {
                    differs = true;
                    break;
                }
            }
            if differs {
                dom[b * words..b * words + words].copy_from_slice(&scratch[..words]);
                changed = true;
            }
        }
    }
    Some(BlockDom { n, words, dom })
}

/// Blocks reachable from `entry` over successor edges.
fn compute_reachable(
    func: &FrameFunctionView<'_>,
    entry: usize,
) -> std::collections::BTreeSet<usize> {
    let n = func.blocks.len();
    let mut seen = std::collections::BTreeSet::new();
    if entry >= n {
        return seen;
    }
    let mut stack = vec![entry];
    seen.insert(entry);
    while let Some(b) = stack.pop() {
        for succ in &func.blocks[b].succs {
            let s = succ.0 as usize;
            if s < n && seen.insert(s) {
                stack.push(s);
            }
        }
    }
    seen
}

/// The set of blocks that lie inside some natural loop (i.e. are reachable from a
/// latch back to its dominating header). A block placed in this set can execute
/// more than once, so `S` must NOT be one of them (the prologue must run once).
fn blocks_in_any_loop(
    func: &FrameFunctionView<'_>,
    dom: &BlockDom,
) -> std::collections::BTreeSet<usize> {
    let n = func.blocks.len();
    let mut looped = std::collections::BTreeSet::new();
    for u in 0..n {
        for succ in &func.blocks[u].succs {
            let v = succ.0 as usize;
            if v >= n {
                continue;
            }
            // Back edge: header `v` dominates its latch `u`.
            if dom.dominates(v, u) {
                // Natural-loop body: `v` plus every node that can reach `u`
                // without passing through `v`.
                looped.insert(v);
                looped.insert(u);
                let mut stack = vec![u];
                while let Some(x) = stack.pop() {
                    if x == v {
                        continue;
                    }
                    for pred in &func.blocks[x].preds {
                        let p = pred.0 as usize;
                        if p < n && p != v && looped.insert(p) {
                            stack.push(p);
                        }
                    }
                }
            }
        }
    }
    looped
}

/// Does this instruction force a frame (touches a callee-saved register, makes a
/// call, or reads a stack slot / frame pointer)? Runs post-`eliminate_frame_indices`,
/// so stack-slot accesses appear as `MemOp { base: X29, .. }` — or, for a far slot
/// re-based by [`FrameIndexEliminator::resolve_slot_operand_for_inst`], or one the
/// deep-slot SP preference in [`FrameIndexEliminator::resolve_slot_operand`] moved,
/// as `MemOp { base: SP, .. }` / `Special(SP)` address arithmetic.
///
/// **An SP-based `MemOp` forces a frame too.** Both bases name a frame byte only
/// AFTER the prologue has run: the prologue moves SP (callee-save pre-index +
/// the locals `sub`), so an SP-relative slot access sunk ABOVE a shrunk prologue
/// would address the CALLER's stack. Any function whose guard region touches a
/// frame slot on either base must therefore keep its whole-function prologue.
/// (Before the re-base and the deep-slot preference existed, `resolve_slot_operand`
/// only produced an SP base in frames with no frame pointer, which shrink-wrapping
/// already declines — so this closes the hole the moment SP bases can appear in an
/// FP frame.)
///
/// Treating SP as frame-forcing is purely conservative — it can only decline or
/// constrain a shrink-wrap plan, and outgoing-arg SP stores sit next to calls,
/// which force a frame already.
fn inst_needs_frame(inst: &MachInst) -> bool {
    // A real call (a tail call never returns and is handled as leaf, but we
    // decline tail-call functions from shrink-wrapping entirely, so treat it as
    // frame-forcing defensively).
    if inst.is_call() {
        return true;
    }
    if is_dynamic_stack_alloc_pseudo(inst) {
        return true;
    }
    let preg_forces = |p: PReg| -> bool {
        callee_saved_gpr_index(p).is_some()
            || callee_saved_fpr_index(p).is_some()
            || p == X29
            || p == SP
    };
    for op in &inst.operands {
        match op {
            MachOperand::PReg(p) => {
                if preg_forces(*p) {
                    return true;
                }
            }
            MachOperand::MemOp { base, .. } => {
                // SP included: see the doc comment — a re-based far slot is a
                // frame access whose base is only correct after the prologue.
                if preg_forces(*base) || *base == SP {
                    return true;
                }
            }
            MachOperand::Special(SpecialReg::SP) => {
                return true;
            }
            MachOperand::StackSlot(_)
            | MachOperand::FrameIndex(_)
            | MachOperand::IncomingArg(_) => {
                return true;
            }
            _ => {}
        }
    }
    for p in inst.implicit_defs.iter().chain(inst.implicit_uses.iter()) {
        if preg_forces(*p) {
            return true;
        }
    }
    false
}

/// Does any instruction in block `b` force a frame?
fn block_needs_frame(func: &FrameFunctionView<'_>, b: usize) -> bool {
    func.blocks[b]
        .insts
        .iter()
        .any(|&id| inst_needs_frame(&func.insts[id.0 as usize]))
}

/// Does block `b` contain a return instruction?
fn block_is_return(func: &FrameFunctionView<'_>, b: usize) -> bool {
    func.blocks[b]
        .insts
        .iter()
        .any(|&id| func.insts[id.0 as usize].is_return())
}

/// Whether block `b` can host an EDGE epilogue: its only control transfer is a
/// trailing unconditional `B` (or a plain fallthrough), so the restore that
/// `emit_shrink_wrapped` places before that `B` (or at the block end) runs on
/// every exit from the block. A conditional branch, a jump-table / register
/// branch or a return anywhere in the block would leave through an exit the
/// restore does not precede.
fn block_can_host_edge_epilogue(func: &FrameFunctionView<'_>, b: usize) -> bool {
    let insts = &func.blocks[b].insts;
    insts.iter().enumerate().all(|(position, &id)| {
        let inst = &func.insts[id.0 as usize];
        if inst.is_return() || inst.opcode == AArch64Opcode::TailCall {
            return false;
        }
        // A trap pseudo carries `IS_BRANCH` only because it flows control by
        // TRAPPING (`AArch64Opcode::is_trap_pseudo`); it never leaves to a
        // block, so the restore need not precede it.
        let is_transfer = !inst.opcode.is_trap_pseudo()
            && (inst.is_branch() || inst.is_conditional_branch() || inst.is_unconditional_branch());
        !is_transfer || (position + 1 == insts.len() && inst.opcode == AArch64Opcode::B)
    })
}

/// The frame-state regions of a shrink-wrap candidate with save block `S`.
struct ShrinkWrapRegions {
    /// Blocks entered with the frame established: reachable from `S` without
    /// leaving through an edge-epilogue block.
    frame: std::collections::BTreeSet<usize>,
    /// Blocks entered WITHOUT a frame: reachable from the entry without passing
    /// `S`, or from the successor of an edge-epilogue block (whose restore has
    /// already run). Disjoint from `frame` in every admitted plan.
    leaf: std::collections::BTreeSet<usize>,
    /// Frame-only, single-successor blocks whose end carries the restore
    /// (epilogue minus `ret`) because their successor is also a leaf block.
    edge_epilogue: std::collections::BTreeSet<usize>,
}

/// Separate the frame region of save block `s` from the leaf region, or `None`.
///
/// A block reached both with and without the frame (a JOIN of a frame path and
/// a leaf path) cannot run correctly: code after it either restores registers
/// that were never saved or returns without restoring them. Each such mixed
/// block is resolved by cutting every FRAME-ONLY predecessor edge into it with
/// an edge epilogue, which is sound only when that predecessor's one exit is
/// the edge into the mixed block (`block_can_host_edge_epilogue`, a single
/// successor). The cut turns the mixed block leaf-only; the regions are then
/// recomputed, because the cut changes what the frame path reaches. A mixed
/// block whose frame-side predecessors cannot all be cut — or a cut that would
/// itself be reached in leaf state — declines the candidate. Each round adds
/// at least one cut or stops, so the loop is bounded by the block count.
fn shrink_wrap_regions(
    func: &FrameFunctionView<'_>,
    reachable: &std::collections::BTreeSet<usize>,
    entry: usize,
    s: usize,
) -> Option<ShrinkWrapRegions> {
    use std::collections::BTreeSet;
    let n = func.blocks.len();
    if s >= n || entry >= n || s == entry {
        return None;
    }
    let succs = |b: usize| {
        func.blocks[b]
            .succs
            .iter()
            .map(|succ| succ.0 as usize)
            .filter(move |&t| t < n)
    };
    let mut edge_epilogue: BTreeSet<usize> = BTreeSet::new();
    loop {
        // The frame region: forward from `S`, stopping at every cut.
        let mut frame = BTreeSet::from([s]);
        let mut stack = vec![s];
        while let Some(b) = stack.pop() {
            if edge_epilogue.contains(&b) {
                continue;
            }
            for t in succs(b) {
                if frame.insert(t) {
                    stack.push(t);
                }
            }
        }
        // The leaf region: forward from the entry and from past every cut,
        // never entering `S` (its prologue is what makes a block frame-state).
        let mut leaf = BTreeSet::new();
        let mut stack = Vec::new();
        let seeds = std::iter::once(entry).chain(edge_epilogue.iter().flat_map(|&e| succs(e)));
        for b in seeds {
            if b != s && leaf.insert(b) {
                stack.push(b);
            }
        }
        while let Some(b) = stack.pop() {
            for t in succs(b) {
                if t != s && leaf.insert(t) {
                    stack.push(t);
                }
            }
        }
        // A cut reached in leaf state would restore registers never saved.
        if edge_epilogue.iter().any(|e| leaf.contains(e)) {
            return None;
        }
        let mixed: Vec<usize> = frame.intersection(&leaf).copied().collect();
        if mixed.is_empty() {
            return Some(ShrinkWrapRegions {
                frame,
                leaf,
                edge_epilogue,
            });
        }
        let cuts_before = edge_epilogue.len();
        for &q in &mixed {
            for pred in &func.blocks[q].preds {
                let p = pred.0 as usize;
                if p >= n
                    || !reachable.contains(&p)
                    || !frame.contains(&p)
                    || leaf.contains(&p)
                    || edge_epilogue.contains(&p)
                {
                    // Leaf-only and already-cut predecessors need nothing; a
                    // MIXED predecessor is itself in `mixed` and is resolved
                    // upstream in this same round.
                    continue;
                }
                let single_successor_into_q =
                    func.blocks[p].succs.len() == 1 && func.blocks[p].succs[0].0 as usize == q;
                if !single_successor_into_q || !block_can_host_edge_epilogue(func, p) {
                    return None;
                }
                edge_epilogue.insert(p);
            }
        }
        if edge_epilogue.len() == cuts_before {
            return None;
        }
    }
}

/// A validated shrink-wrap placement: where to sink the prologue and how each
/// return is finished.
struct ShrinkWrapPlan {
    /// The save block `S`: prologue is emitted at its start.
    save_block: BlockId,
    /// Returns entered with the frame established (`shrink_wrap_regions`'
    /// frame region): emit the full epilogue (incl. `ret`) before the original
    /// `ret`.
    frame_return_blocks: Vec<BlockId>,
    /// Frame-only, single-successor blocks whose successor a leaf path also
    /// reaches (a leaf-shared join — a return, or a block on the way to one):
    /// append the epilogue (minus `ret`) at the block end so the restore runs on
    /// the frame edge while the leaf edge into the join stays bare.
    edge_epilogue_blocks: Vec<BlockId>,
    /// Return blocks left as a bare `ret` (leaf / leaf-shared join). Informational
    /// (used by the fail-closed invariant check).
    leaf_return_blocks: Vec<BlockId>,
}

/// Compute a shrink-wrap plan for `func`, or `None` if the function is not an
/// admissible leaf-guard shape (fail-closed — the caller then emits the ordinary
/// whole-function prologue). See the module comment above for the admission set.
fn compute_shrink_wrap_plan(
    func: &FrameFunctionView<'_>,
    layout: &FrameLayout,
) -> Option<ShrinkWrapPlan> {
    let dbg =
        shrink_wrap_env_enabled() && std::env::var_os("TCG_AARCH64_SHRINKWRAP_STATS").is_some();
    // --- Target / layout preconditions (Darwin FRAME mode, nothing exotic). ---
    if !layout.uses_frame_pointer || layout.has_dynamic_alloc || layout.uses_red_zone {
        return None;
    }
    if layout.callee_saved_pairs.is_empty() {
        return None;
    }
    // A probe loop needs its own block; the sunk prologue is straight-line.
    if StaticStackProbePlan::for_layout(layout).looped {
        return None;
    }
    if func.source.eh_metadata.has_eh_info() {
        return None;
    }
    if func.source.stack_protector.is_enabled() || func.source.stack_protector_slot.is_some() {
        return None;
    }
    // Must encode as compact-unwind FRAME mode (never DWARF fallback): the shrunk
    // prologue is only unwind-safe under the PC-location-independent FRAME encoding.
    if encode_compact_unwind(layout).needs_dwarf_fallback() {
        return None;
    }

    let n = func.blocks.len();
    if !(2..=4096).contains(&n) {
        return None;
    }
    let entry = func.source.entry.0 as usize;
    if entry >= n {
        return None;
    }

    // Decline any function with a tail call (special epilogue-before-branch
    // handling is out of v1 scope).
    if func
        .insts
        .iter()
        .any(|i| i.opcode == AArch64Opcode::TailCall)
    {
        return None;
    }

    // --- Entry must end in a two-way conditional branch and be frame-clean. ---
    // AArch64 lowers a two-way branch as a conditional-branch terminator GROUP:
    // `B.cond/CBZ/... target ; B fallthrough`, so the conditional branch may be the
    // last OR the second-to-last instruction.
    let entry_block = &func.blocks[entry];
    let entry_has_cond_guard = entry_block
        .insts
        .iter()
        .rev()
        .take(2)
        .any(|&id| func.insts[id.0 as usize].opcode.is_conditional_branch());
    if !entry_has_cond_guard {
        return None;
    }
    if entry_block.succs.len() != 2 {
        return None;
    }
    if block_needs_frame(func, entry) {
        // The incoming-arg->CSR copy (or any other CSR use) still sits before the
        // guard: the save point cannot sink. This is exactly what Piece A removes.
        return None;
    }

    let dom = compute_block_dominators(func)?;
    let reachable = compute_reachable(func, entry);
    let looped = blocks_in_any_loop(func, &dom);

    // Blocks that force a frame (reachable only).
    let frame_blocks: Vec<usize> = (0..n)
        .filter(|&b| reachable.contains(&b) && block_needs_frame(func, b))
        .collect();
    if frame_blocks.is_empty() {
        // Nothing to protect — the whole-function path already emits the minimal
        // frame; no shrink-wrap benefit.
        return None;
    }

    // Try each successor of the guard as the save block `S`.
    let succ0 = entry_block.succs[0];
    let succ1 = entry_block.succs[1];
    for &s_cand in &[succ0, succ1] {
        let s = s_cand.0 as usize;
        if s == entry || s >= n || !reachable.contains(&s) {
            continue;
        }
        if looped.contains(&s) {
            continue; // prologue must execute at most once
        }
        // `S` dominates every frame-forcing block.
        if !frame_blocks.iter().all(|&b| dom.dominates(s, b)) {
            continue;
        }
        // Every reachable block NOT dominated by `S` is frame-clean (soundness core).
        let non_dom_clean = (0..n)
            .all(|b| !reachable.contains(&b) || dom.dominates(s, b) || !block_needs_frame(func, b));
        if !non_dom_clean {
            continue;
        }

        // Classify returns by the FRAME STATE they are reached in, not by
        // dominance. Dominance answers "does every path pass `S`", which is
        // the wrong question for a return (or any block) that a frame path
        // can reach through a block `S` does NOT dominate: a JOIN of a leaf
        // path and a frame path, which the dominance classification took for
        // a leaf block and left without a restore. Measured (2026-09-28):
        // `core::char::methods::encode_utf8_raw_unchecked` at -O0 has the
        // frame-dominated block 13 fall into block 22 — also the leaf path's
        // successor — and 22 into the shared return 32; the frame edge 30 into
        // 32 got its restore, the frame path through 22 did not, and the final
        // stream's spill-slot net refused with `callee-saved-not-restored` at
        // block 32 (`[TCG-A64-SPILL-SLOT]`). `shrink_wrap_regions` cuts every
        // frame path with an edge epilogue on the last frame-only block before
        // a block a leaf path also reaches — or declines.
        let Some(regions) = shrink_wrap_regions(func, &reachable, entry, s) else {
            if dbg {
                eprintln!(
                    "[shrinkwrap-B] fn={} decline S={s}: no edge-epilogue cut separates the \
                     frame region from the leaf region",
                    func.source.name
                );
            }
            continue;
        };
        // Every frame-forcing block runs with the frame established and is
        // never reached in leaf state.
        if !frame_blocks
            .iter()
            .all(|b| regions.frame.contains(b) && !regions.leaf.contains(b))
        {
            continue;
        }
        let mut frame_return_blocks = Vec::new();
        let mut leaf_return_blocks = Vec::new();
        let mut ok = true;
        for b in 0..n {
            if !reachable.contains(&b) || !block_is_return(func, b) {
                continue;
            }
            match (regions.frame.contains(&b), regions.leaf.contains(&b)) {
                (true, false) => frame_return_blocks.push(BlockId(b as u32)),
                (false, true) => leaf_return_blocks.push(BlockId(b as u32)),
                _ => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok || leaf_return_blocks.is_empty() {
            continue;
        }
        let edge_epilogue_blocks: Vec<BlockId> = regions
            .edge_epilogue
            .iter()
            .map(|&b| BlockId(b as u32))
            .collect();

        let plan = ShrinkWrapPlan {
            save_block: s_cand,
            frame_return_blocks,
            edge_epilogue_blocks,
            leaf_return_blocks,
        };
        // Independent fail-closed re-verification before we touch the function.
        if verify_shrink_wrap_plan(func, &dom, &reachable, &plan) {
            if dbg {
                eprintln!(
                    "[shrinkwrap-B] fn={} ADMIT: save_block={} frame_rets={} edge_epi={} leaf_rets={}",
                    func.source.name,
                    plan.save_block.0,
                    plan.frame_return_blocks.len(),
                    plan.edge_epilogue_blocks.len(),
                    plan.leaf_return_blocks.len(),
                );
            }
            return Some(plan);
        }
    }
    None
}

/// Fail-closed frame invariant (design-mandated): re-check, INDEPENDENTLY of the
/// construction above, that `S` dominates every frame-forcing block and — by a
/// forward frame-state dataflow over every path, not by dominance at a return's
/// predecessors — that every path to a `ret` restores exactly when it saved.
/// Returns false (decline) on any violation.
fn verify_shrink_wrap_plan(
    func: &FrameFunctionView<'_>,
    dom: &BlockDom,
    reachable: &std::collections::BTreeSet<usize>,
    plan: &ShrinkWrapPlan,
) -> bool {
    let n = func.blocks.len();
    let s = plan.save_block.0 as usize;
    if s >= n {
        return false;
    }
    // (1) S dominates every frame-forcing block; every non-dominated reachable
    //     block is frame-clean.
    for b in 0..n {
        if !reachable.contains(&b) || !block_needs_frame(func, b) {
            continue;
        }
        if !dom.dominates(s, b) {
            return false;
        }
    }
    // (2) Every reachable return is accounted for exactly once and consistently.
    let frame_set: std::collections::BTreeSet<usize> = plan
        .frame_return_blocks
        .iter()
        .map(|b| b.0 as usize)
        .collect();
    let leaf_set: std::collections::BTreeSet<usize> = plan
        .leaf_return_blocks
        .iter()
        .map(|b| b.0 as usize)
        .collect();
    let edge_set: std::collections::BTreeSet<usize> = plan
        .edge_epilogue_blocks
        .iter()
        .map(|b| b.0 as usize)
        .collect();
    // Frame returns and leaf returns are disjoint; edge blocks are neither.
    if frame_set.intersection(&leaf_set).next().is_some()
        || edge_set
            .iter()
            .any(|e| frame_set.contains(e) || leaf_set.contains(e))
    {
        return false;
    }
    // (3) Edge-epilogue blocks are single-successor non-returns whose only
    //     exit follows the appended restore.
    for &e in &edge_set {
        if e >= n
            || func.blocks[e].succs.len() != 1
            || block_is_return(func, e)
            || !block_can_host_edge_epilogue(func, e)
        {
            return false;
        }
    }
    // (3b) THE FRAME STATE, as a forward dataflow over every path from the
    //      entry. This is the invariant itself, not a proxy for it: a block is
    //      entered with the frame either established or not, never both; `S`
    //      is entered only without it (so the prologue runs once) and leaves
    //      with it; an edge-epilogue block is entered only with it and leaves
    //      without it; every frame-forcing block runs with it; and a return
    //      runs in exactly the state its classification restores for. The old
    //      check read dominance at a return's IMMEDIATE predecessors, which
    //      misses a frame path that reaches a leaf-shared return through a
    //      join block `S` does not dominate — the `encode_utf8_raw_unchecked`
    //      hole (see `shrink_wrap_regions`).
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum FrameState {
        Leaf,
        Frame,
    }
    let entry = func.source.entry.0 as usize;
    if entry >= n {
        return false;
    }
    let mut entered: Vec<Option<FrameState>> = vec![None; n];
    let mut work = vec![(entry, FrameState::Leaf)];
    while let Some((b, state)) = work.pop() {
        if b >= n {
            return false;
        }
        match entered[b] {
            Some(seen) if seen == state => continue,
            Some(_) => return false,
            None => entered[b] = Some(state),
        }
        let mut state = state;
        if b == s {
            if state != FrameState::Leaf {
                return false;
            }
            state = FrameState::Frame;
        }
        if block_needs_frame(func, b) && state != FrameState::Frame {
            return false;
        }
        if block_is_return(func, b) {
            let restores_for = if frame_set.contains(&b) {
                FrameState::Frame
            } else if leaf_set.contains(&b) {
                FrameState::Leaf
            } else {
                return false;
            };
            if state != restores_for {
                return false;
            }
        }
        if edge_set.contains(&b) {
            if state != FrameState::Frame {
                return false;
            }
            state = FrameState::Leaf;
        }
        for succ in &func.blocks[b].succs {
            work.push((succ.0 as usize, state));
        }
    }
    // (4) There is a genuine leaf return (a shrink actually happens).
    !plan.leaf_return_blocks.is_empty()
}

/// Emit a shrink-wrapped frame from a validated plan: prologue at `S`, epilogue
/// before frame-dominated returns, epilogue (minus `ret`) on the frame edge into
/// a leaf-shared join return, and bare `ret` on the leaf returns.
fn emit_shrink_wrapped(
    func: &MachFunction,
    insertion: &mut FrameInsertionPlan,
    layout: &FrameLayout,
    plan: &ShrinkWrapPlan,
) -> Result<(), crate::lower::LowerError> {
    // Prologue at the start of the save block.
    let prologue = emit_prologue(layout);
    let s = plan.save_block.0 as usize;
    let old = std::mem::take(&mut insertion.blocks[s].insts);
    let mut new_insts = Vec::with_capacity(prologue.len() + old.len());
    for pi in prologue {
        let id = insertion.push_inst(pi)?;
        new_insts.push(id);
    }
    new_insts.extend(old);
    insertion.blocks[s].insts = new_insts;

    // Frame-dominated returns: insert cleanup before the original return. The
    // return carries signature-authenticated implicit ABI sink metadata, so it
    // must retain both its instruction identity and all of its fields.
    for &rb in &plan.frame_return_blocks {
        let b = rb.0 as usize;
        let old = std::mem::take(&mut insertion.blocks[b].insts);
        let mut new_insts = Vec::with_capacity(old.len() + layout.callee_saved_pairs.len() + 2);
        for &inst_id in &old {
            if insertion.view(func).insts[inst_id.0 as usize].is_return() {
                for ei in emit_epilogue_before_tail_branch(layout) {
                    let id = insertion.push_inst(ei)?;
                    new_insts.push(id);
                }
                new_insts.push(inst_id);
            } else {
                new_insts.push(inst_id);
            }
        }
        insertion.blocks[b].insts = new_insts;
    }

    // Frame edges into a leaf-shared return: epilogue minus ret, inserted before
    // a trailing unconditional branch (if any) or appended at the block end.
    for &eb in &plan.edge_epilogue_blocks {
        let b = eb.0 as usize;
        let epi = emit_epilogue_before_tail_branch(layout);
        let old = std::mem::take(&mut insertion.blocks[b].insts);
        let final_branch = old
            .last()
            .copied()
            .filter(|id| insertion.view(func).insts[id.0 as usize].opcode == AArch64Opcode::B);
        let mut new_insts = Vec::with_capacity(old.len() + epi.len());
        if let Some(branch) = final_branch {
            new_insts.extend_from_slice(&old[..old.len() - 1]);
            for ei in epi {
                let id = insertion.push_inst(ei)?;
                new_insts.push(id);
            }
            new_insts.push(branch);
        } else {
            new_insts.extend_from_slice(&old);
            for ei in epi {
                let id = insertion.push_inst(ei)?;
                new_insts.push(id);
            }
        }
        insertion.blocks[b].insts = new_insts;
    }

    // Leaf returns keep their bare `ret` (nothing to do).
    Ok(())
}

// ---------------------------------------------------------------------------
// Prologue/epilogue insertion into a MachFunction
// ---------------------------------------------------------------------------

/// Insert prologue instructions at the beginning of the entry block,
/// and epilogue instructions before every return instruction.
///
/// This is the main entry point for frame lowering after layout computation.
///
/// Existing callers get the ordinary whole-function prologue (shrink-wrapping
/// disabled), keeping their output byte-identical. The Darwin Mach-O production
/// path calls [`insert_prologue_epilogue_shrinkwrap`] to opt in.
///
/// # Performance notes
///
/// - Block lists and edited instructions are staged; the full instruction arena
///   is borrowed, not cloned. Returned errors leave the function unchanged.
/// - Epilogue instructions are generated fresh per return site rather than
///   cloning a template, avoiding heap allocation for operand Vecs.
/// - Block inst lists are only rebuilt for blocks that contain returns,
///   skipping non-terminating blocks entirely.
pub fn insert_prologue_epilogue(
    func: &mut MachFunction,
    layout: &FrameLayout,
) -> Result<(), crate::lower::LowerError> {
    insert_prologue_epilogue_impl(func, layout, ShrinkWrapEligibility::Disabled)
}

/// Frame lowering with shrink-wrap eligibility. `eligibility` reflects the
/// caller's object format: only `DarwinFrame` (Apple Mach-O, non-EH) permits
/// shrink-wrapping (on by default there), and even then subject to full
/// admission and the `TCG_AARCH64_SHRINKWRAP_OFF` kill switch (else the
/// whole-function prologue is emitted).
pub fn insert_prologue_epilogue_shrinkwrap(
    func: &mut MachFunction,
    layout: &FrameLayout,
    eligibility: ShrinkWrapEligibility,
) -> Result<(), crate::lower::LowerError> {
    insert_prologue_epilogue_impl(func, layout, eligibility)
}

fn insert_prologue_epilogue_impl(
    func: &mut MachFunction,
    layout: &FrameLayout,
    eligibility: ShrinkWrapEligibility,
) -> Result<(), crate::lower::LowerError> {
    // L10-P5: the plan numbers its prologue/epilogue instructions and blocks
    // from the arena lengths, not through the allocators, so it runs the
    // function's allocation-time admission first (a no-op unless a boundary
    // is pending). A refusal is sticky on `func`, where the pipeline reports
    // it by name.
    if let Err(error) = func.admit_ids_before_allocation() {
        return Err(frame_insertion_error(format!(
            "frame insertion refused by the machine-IR identity admission: {error}"
        )));
    }
    plan_frame_insertion(func, layout, eligibility)?.commit(func)
}

fn plan_frame_insertion(
    func: &MachFunction,
    layout: &FrameLayout,
    eligibility: ShrinkWrapEligibility,
) -> Result<FrameInsertionPlan, crate::lower::LowerError> {
    // Guard admission precedes every code edit, including dynamic-allocation
    // expansion and return-copy rewriting. Missing metadata cannot disable a
    // requested protector or turn it into shrink-wrap eligibility.
    let stack_protector_offset = stack_protector_frame_offset(func, layout)?;
    // A U10 stack-limit request is admitted (or refused) before any edit too.
    let stack_limit = stack_limit_frame_plan(func, layout)?;
    let mut insertion = FrameInsertionPlan::new(func)?;
    expand_dynamic_stack_allocs(func, &mut insertion, layout.outgoing_arg_area_size)?;
    retarget_rbit_return_copies(func, &mut insertion);

    // Shrink-wrapping attempt (Darwin FRAME mode, env-gated). On admission the
    // prologue is sunk to the save block and the leaf return is left bare; on any
    // decline we fall through to the ordinary whole-function prologue below. The
    // plan is computed and fail-closed-verified before a single instruction is
    // moved, so a declined shape is byte-identical to the whole-function path.
    if eligibility == ShrinkWrapEligibility::DarwinFrame
        && shrink_wrap_env_enabled()
        && stack_protector_offset.is_none()
        && func.stack_limit.is_none()
        && let Some(plan) = compute_shrink_wrap_plan(&insertion.view(func), layout)
    {
        emit_shrink_wrapped(func, &mut insertion, layout, &plan)?;
        return Ok(insertion);
    }

    let stack_chk_fail_block = stack_protector_offset
        .map(|_| append_stack_chk_fail_block(&mut insertion))
        .transpose()?;
    let mut prologue = emit_prologue_parts(layout, false);
    // The U10 overflow block is created empty here, so the check can name
    // it, and filled only after the exit loop below: that loop puts the
    // protector check and the `add sp` teardown in front of every TailCall,
    // and neither belongs on the overflow path (no canary was stored and no
    // SP adjustment was made when the check fails).
    let stack_limit_overflow = match &stack_limit {
        Some(_) => Some(insertion.create_block()?),
        None => None,
    };
    // Positions, in the entry block, of the check's `B.LO`s: the entry is
    // split after each, so every check branch ends its block.
    let mut stack_limit_branches = Vec::new();
    if let (Some(plan), Some(overflow)) = (&stack_limit, stack_limit_overflow) {
        let check = emit_stack_limit_check(&plan.limit, plan.sp_adj, overflow);
        stack_limit_branches = check
            .iter()
            .enumerate()
            .filter(|(_, inst)| inst.opcode == AArch64Opcode::BCond)
            .map(|(index, _)| prologue.csa_len + index)
            .collect();
        let rest = prologue.head.split_off(prologue.csa_len);
        prologue.head.extend(check);
        prologue.head.extend(rest);
    }

    // A branch, jump table, or landing pad may target the original entry as a
    // body label. Put the one-time frame setup in a new entry block so those
    // existing targets continue without saving the frame again.
    let original_entry = func.entry;
    let entry_is_target = !func.blocks[original_entry.0 as usize].preds.is_empty()
        || func.blocks.iter().any(|block| block.succs.contains(&original_entry))
        || func.block_order.iter().any(|&block_id| {
            func.blocks[block_id.0 as usize].insts.iter().any(|&inst_id| {
                func.insts[inst_id.0 as usize]
                    .operands
                    .iter()
                    .any(|operand| matches!(operand, MachOperand::Block(id) if *id == original_entry))
            })
        })
        || func.jump_tables.iter().any(|table| table.targets.contains(&original_entry))
        || func.eh_metadata.landing_pads.iter().any(|pad| pad.block == original_entry)
        || func.eh_metadata.call_sites.iter().any(|site| site.landing_pad_block == Some(original_entry));
    let has_frame_setup = !prologue.head.is_empty()
        || !prologue.tail.is_empty()
        || prologue.probe_loop.is_some()
        || stack_protector_offset.is_some()
        || stack_limit.is_some();
    let entry = if entry_is_target && has_frame_setup {
        if insertion.block_order.first().copied() != Some(original_entry) {
            return Err(frame_insertion_error(
                "cannot isolate a targeted entry absent from the start of block layout",
            ));
        }
        let one_time_entry = insertion.create_block()?;
        insertion.block_order.pop();
        insertion.block_order.insert(0, one_time_entry);
        insertion.entry = one_time_entry;
        insertion.add_edge(one_time_entry, original_entry);
        one_time_entry
    } else {
        original_entry
    };

    // Insert the prologue at the start of the one-time entry. A looped static
    // probe splits that block: its head stays at entry, its loop and residual
    // setup precede the original body.
    let body_block = match prologue.probe_loop {
        Some(iteration) => insert_static_probe_loop(func, &mut insertion, layout, iteration)?,
        None => entry,
    };

    let stack_protector_prologue = stack_protector_offset
        .map(emit_stack_protector_prologue)
        .unwrap_or_default();
    let old_body_insts = std::mem::take(&mut insertion.blocks[body_block.0 as usize].insts);
    let mut new_body_insts = Vec::with_capacity(
        prologue.tail.len() + stack_protector_prologue.len() + old_body_insts.len(),
    );
    for inst in prologue.tail.into_iter().chain(stack_protector_prologue) {
        let id = insertion.push_inst(inst)?;
        new_body_insts.push(id);
    }
    new_body_insts.extend(old_body_insts);
    insertion.blocks[body_block.0 as usize].insts = new_body_insts;

    // Use mem::take to move the old insts without cloning.
    let old_entry_insts = std::mem::take(&mut insertion.blocks[entry.0 as usize].insts);
    let mut new_entry_insts = Vec::with_capacity(prologue.head.len() + old_entry_insts.len());
    for prologue_inst in prologue.head {
        let id = insertion.push_inst(prologue_inst)?;
        new_entry_insts.push(id);
    }
    new_entry_insts.extend(old_entry_insts);
    insertion.blocks[entry.0 as usize].insts = new_entry_insts;
    // Split the entry after each check `B.LO`, so each branch terminates its
    // block and falls through to the next: every analysis then sees the
    // overflow edge leave with the state at the branch (CSA saved, SP not
    // yet adjusted). Done only now: a probe-loop split above moves every
    // unnamed entry successor to its tail, and so does each split here.
    if let Some(overflow) = stack_limit_overflow {
        let mut block = entry;
        let mut consumed = 0usize;
        for &position in &stack_limit_branches {
            let tail = insertion.split_block_tail(func, block, position + 1 - consumed)?;
            insertion.add_edge(block, overflow);
            insertion.add_edge(block, tail);
            consumed = position + 1;
            block = tail;
        }
    }

    // For each block, find return instructions and structural tail calls, then
    // insert exit cleanup before them.
    // First pass: identify which blocks contain returns to avoid unnecessary work.
    let num_blocks = insertion.blocks.len();
    for block_idx in 0..num_blocks {
        // Check if this block has any function-exit instructions.
        let has_function_exit = insertion.blocks[block_idx].insts.iter().any(|&inst_id| {
            let view = insertion.view(func);
            let inst = &view.insts[inst_id.0 as usize];
            inst.is_return() || is_tail_call(inst)
        });

        if !has_function_exit {
            continue;
        }

        // Move the old insts out to avoid borrow conflict.
        let block_insts = std::mem::take(&mut insertion.blocks[block_idx].insts);
        let mut new_insts = Vec::with_capacity(block_insts.len() + 8);

        for &inst_id in &block_insts {
            let is_return = insertion.view(func).insts[inst_id.0 as usize].is_return();
            let is_tail_branch = is_tail_call(&insertion.view(func).insts[inst_id.0 as usize]);

            if is_return || is_tail_branch {
                if let (Some(slot_offset), Some(fail_block)) =
                    (stack_protector_offset, stack_chk_fail_block)
                {
                    let check = emit_stack_protector_check(slot_offset, fail_block);
                    for check_inst in check {
                        let id = insertion.push_inst(check_inst)?;
                        new_insts.push(id);
                    }
                    let this_block = BlockId(checked_frame_insertion_id(block_idx, 0, "block")?);
                    if !insertion.blocks[block_idx].succs.contains(&fail_block) {
                        insertion.blocks[block_idx].succs.push(fail_block);
                    }
                    if !insertion.blocks[fail_block.0 as usize]
                        .preds
                        .contains(&this_block)
                    {
                        insertion.blocks[fail_block.0 as usize]
                            .preds
                            .push(this_block);
                    }
                }
                // Generate cleanup instructions fresh, then retain the original
                // exit instruction. In particular, a return's implicit ABI
                // sink set is signature-authenticated before register
                // allocation and must survive frame insertion unchanged.
                let epilogue = emit_epilogue_before_tail_branch(layout);
                for epi_inst in epilogue {
                    let id = insertion.push_inst(epi_inst)?;
                    new_insts.push(id);
                }
                new_insts.push(inst_id);
            } else {
                new_insts.push(inst_id);
            }
        }
        insertion.blocks[block_idx].insts = new_insts;
    }
    if let (Some(plan), Some(overflow)) = (&stack_limit, stack_limit_overflow) {
        for inst in emit_stack_limit_overflow(&plan.limit, layout) {
            let id = insertion.push_inst(inst)?;
            insertion.blocks[overflow.0 as usize].insts.push(id);
        }
        insertion.stack_limit_overflow_block = Some(overflow);
    }
    Ok(insertion)
}

fn is_tail_call(inst: &MachInst) -> bool {
    inst.opcode == AArch64Opcode::TailCall
}

/// Split the entry block around a static probe loop and return the block that
/// continues after it (holding the original entry instructions).
///
/// ```text
/// entry: <callee-saved stores, add x29>  movz x16, #steps
/// loop:  sub sp, sp, #4096 (two chunks); str xzr, [sp]; subs x16, x16, #1; b.ne loop
/// body:  <residual allocation and probe> <original entry instructions>
/// ```
///
/// The loop runs after the frame pointer is established, so the FP-based CFA
/// describes every iteration. An SP-based CFA cannot, so such frames fail.
fn insert_static_probe_loop(
    func: &MachFunction,
    insertion: &mut FrameInsertionPlan,
    layout: &FrameLayout,
    iteration: Vec<MachInst>,
) -> Result<BlockId, crate::lower::LowerError> {
    if !layout.uses_frame_pointer || layout.callee_saved_pairs.is_empty() {
        return Err(frame_insertion_error(format!(
            "stack probe loop for a {}-byte SP adjustment requires a frame pointer: an SP-based CFA cannot describe the loop",
            layout.sp_adjustment()
        )));
    }
    let entry = insertion.entry;
    let body = insertion.split_block_tail(func, entry, 0)?;
    let probe_loop = insertion.create_block_after(entry, 1)?;
    for inst in iteration.into_iter().chain([MachInst::new(
        AArch64Opcode::BCond,
        vec![MachOperand::Imm(COND_NE), MachOperand::Block(probe_loop)],
    )]) {
        let id = insertion.push_inst(inst)?;
        insertion.blocks[probe_loop.0 as usize].insts.push(id);
    }
    insertion.add_edge(entry, probe_loop);
    insertion.add_edge(probe_loop, probe_loop);
    insertion.add_edge(probe_loop, body);
    Ok(body)
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::function::{
        MachFunction, Signature, StackProtectorMode, StackSlot, StackSlotSizeSource,
    };
    use trust_cg_ir::inst::{AArch64Opcode, MachInst};
    use trust_cg_ir::operand::MachOperand;
    use trust_cg_ir::regs::{
        D8, D9, D10, D11, D12, D13, D14, D15, H8, H15, PReg, S8, S11, W0, W1, W16, W19, W22, W28,
        X0, X1, X16, X17, X19,
    };
    use trust_cg_ir::types::{BlockId, FrameIdx, StackSlotId};

    /// Helper: create a minimal function with given instructions in entry block.
    fn make_func(name: &str, insts: Vec<MachInst>) -> MachFunction {
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new(name.to_string(), sig);
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(BlockId(0), id);
        }
        func
    }

    /// The per-block scratch-liveness table answers exactly what the forward
    /// scan answers at every position, for both IP scratches and both
    /// live-out seeds, including reads, writes, calls, other registers and a
    /// block that lists an instruction twice (which keeps the scan).
    #[test]
    fn scratch_liveness_table_matches_forward_scan() {
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = move |limit: u64| {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (state >> 33) % limit
        };
        let mut live_answers = 0usize;
        for case in 0..400 {
            let len = 1 + next(60) as usize;
            let insts: Vec<MachInst> = (0..len)
                .map(|_| {
                    let reg = [X16, X17, W16, X0, X1][next(5) as usize];
                    match next(7) {
                        // Reads the register.
                        0 => MachInst::new(
                            AArch64Opcode::AddRI,
                            vec![
                                MachOperand::PReg(X0),
                                MachOperand::PReg(reg),
                                MachOperand::Imm(1),
                            ],
                        ),
                        // Writes the register.
                        1 => MachInst::new(
                            AArch64Opcode::MovI,
                            vec![MachOperand::PReg(reg), MachOperand::Imm(7)],
                        ),
                        // A memory base is always read.
                        2 => MachInst::new(
                            AArch64Opcode::LdrRI,
                            vec![
                                MachOperand::PReg(X1),
                                MachOperand::MemOp {
                                    base: reg,
                                    offset: 8,
                                },
                            ],
                        ),
                        3 => MachInst::new(
                            AArch64Opcode::Bl,
                            vec![MachOperand::Symbol("callee".into())],
                        ),
                        _ => MachInst::new(
                            AArch64Opcode::MovI,
                            vec![MachOperand::PReg(X0), MachOperand::Imm(3)],
                        ),
                    }
                })
                .collect();
            let func = make_func("scratch_liveness", insts);
            let mut block_insts = func.blocks[0].insts.clone();
            if case % 9 == 0 && block_insts.len() > 2 {
                let repeated = block_insts[0];
                block_insts.push(repeated);
            }
            for live_out in [(false, false), (true, false), (false, true), (true, true)] {
                let mut table = ScratchLiveness::new(&block_insts, live_out);
                for pos in 0..block_insts.len() {
                    for (reg, seed) in [(X16, live_out.0), (X17, live_out.1)] {
                        let expected =
                            scratch_live_after(&func, &block_insts[pos + 1..], reg, seed);
                        assert_eq!(
                            table.live_after(&func, pos, reg),
                            expected,
                            "case {case}, live-out {live_out:?}, position {pos}, {reg:?}"
                        );
                        live_answers += usize::from(expected);
                    }
                }
            }
        }
        assert!(live_answers > 1000, "live answers: {live_answers}");
    }

    /// Frame-index elimination of one block of `n` far-slot stores, each of
    /// which borrows an IP scratch to materialize its offset, examines `O(n)`
    /// instructions to prove the scratch dead: the per-block table scans the
    /// block once. Asking the forward scan at every access (each runs to the
    /// block end, since no later instruction touches the scratch yet)
    /// examines `O(n^2)`, and this bound fails at the 4x steps below.
    #[test]
    fn scratch_liveness_cost_grows_linearly() {
        let units_for = |stores: usize| {
            let mut insts: Vec<MachInst> = (0..stores)
                .map(|_| {
                    MachInst::new(
                        AArch64Opcode::StrRI,
                        vec![
                            MachOperand::PReg(PReg::new(0)),
                            MachOperand::FrameIndex(FrameIdx(0)),
                        ],
                    )
                })
                .collect();
            insts.push(MachInst::new(AArch64Opcode::Ret, vec![]));
            let mut func = make_func("scratch_liveness_cost", insts);
            func.alloc_stack_slot(StackSlot::new(8192, 16));
            let layout = layout_without_sp_rebase(&func, 0, false);
            let before = SCRATCH_SCAN_UNITS.with(std::cell::Cell::get);
            let stats = FrameIndexEliminator::new(&layout, &func)
                .run(&mut func)
                .unwrap();
            let units = SCRATCH_SCAN_UNITS.with(std::cell::Cell::get) - before;
            assert_eq!(
                stats.large_offset_count as usize, stores,
                "every store materializes its offset in a scratch"
            );
            units
        };
        let sizes = [64usize, 256, 1024];
        let units: Vec<u64> = sizes.iter().map(|&stores| units_for(stores)).collect();
        for step in 0..2 {
            assert!(units[step] > 0, "no scan work at {} stores", sizes[step]);
            let ratio = units[step + 1] as f64 / units[step] as f64;
            assert!(
                ratio <= 5.0,
                "scratch-liveness scans grew x{ratio:.2} from {} to {} stores ({} -> {} \
                 instructions examined)",
                sizes[step],
                sizes[step + 1],
                units[step],
                units[step + 1]
            );
        }
    }

    /// Every instruction in layout order (probe loops split blocks).
    fn laid_out_insts(func: &MachFunction) -> Vec<&MachInst> {
        func.block_order
            .iter()
            .flat_map(|block| &func.blocks[block.0 as usize].insts)
            .map(|id| &func.insts[id.0 as usize])
            .collect()
    }

    #[test]
    fn pair_memory_outgoing_pair_width_and_implicit_zero() {
        let mut failures = Vec::new();
        let mut count = 0;
        for (bank, element_bytes) in [(32, 4u32), (0, 8), (128, 4), (96, 8), (64, 16)] {
            for base in [MachOperand::PReg(SP), MachOperand::Special(SpecialReg::SP)] {
                for offset in [None, Some(0), Some(16), Some(32)] {
                    let mut operands = vec![
                        MachOperand::PReg(PReg::new(bank)),
                        MachOperand::PReg(PReg::new(bank + 1)),
                        base.clone(),
                    ];
                    if let Some(offset) = offset {
                        operands.push(MachOperand::Imm(offset));
                    }
                    let inst = MachInst::new(AArch64Opcode::StpRI, operands);
                    let func = make_func(
                        "pair_outgoing_width",
                        vec![
                            inst.clone(),
                            MachInst::new(
                                AArch64Opcode::Bl,
                                vec![MachOperand::Symbol("callee".into())],
                            ),
                        ],
                    );
                    let expected = (offset.unwrap_or(0) as u32 + 2 * element_bytes + 15) & !15;
                    let actual = compute_max_outgoing_arg_size(&func);
                    count += 1;
                    if actual != expected {
                        failures.push(format!("{inst:?}: {actual} != {expected}"));
                    }
                    // The caller-provided high-water mark is actually reserved by frame layout.
                    assert_eq!(
                        compute_frame_layout(&func, expected, false).outgoing_arg_area_size,
                        expected
                    );
                }
            }
        }
        assert_eq!(count, 40);
        assert!(
            failures.is_empty(),
            "{}/40 pair outgoing widths wrong:\n{}",
            failures.len(),
            failures.join("\n")
        );
    }

    #[test]
    fn pair_memory_outgoing_scalar_q_and_volatile_widths() {
        let mut failures = Vec::new();
        let mut count = 0;
        // The same scanner must reserve a whole Q scalar store, not only the
        // historical eight-byte estimate. These are real supported store opcodes.
        let mut rows = Vec::new();
        for opcode in [AArch64Opcode::StrRI, AArch64Opcode::VolatileStrRI] {
            for (bank, bytes) in [(32, 4u32), (0, 8), (165, 2), (128, 4), (96, 8), (64, 16)] {
                rows.push((opcode, bank, bytes));
            }
        }
        for (opcode, bytes) in [
            (AArch64Opcode::StrbRI, 1),
            (AArch64Opcode::StrhRI, 2),
            (AArch64Opcode::VolatileStrbRI, 1),
            (AArch64Opcode::VolatileStrhRI, 2),
        ] {
            rows.push((opcode, 32, bytes));
        }
        for (opcode, bank, bytes) in rows {
            for base in [MachOperand::PReg(SP), MachOperand::Special(SpecialReg::SP)] {
                for offset in [0, 8, 16] {
                    let inst = MachInst::new(
                        opcode,
                        vec![
                            MachOperand::PReg(PReg::new(bank)),
                            base.clone(),
                            MachOperand::Imm(offset),
                        ],
                    );
                    let expected = (offset as u32 + bytes + 15) & !15;
                    let actual = compute_max_outgoing_arg_size(&make_func(
                        "scalar_outgoing_width",
                        vec![inst.clone()],
                    ));
                    count += 1;
                    if actual != expected {
                        failures.push(format!("{inst:?}: {actual} != {expected}"));
                    }
                }
            }
        }
        assert_eq!(count, 96);
        assert!(
            failures.is_empty(),
            "{}/96 scalar outgoing widths wrong; first32:\n{}",
            failures.len(),
            failures
                .iter()
                .take(32)
                .cloned()
                .collect::<Vec<_>>()
                .join("\n")
        );
    }

    #[test]
    fn pair_memory_outgoing_scalar_implicit_zero() {
        let mut rows = Vec::new();
        for opcode in [AArch64Opcode::StrRI, AArch64Opcode::VolatileStrRI] {
            for (register, bytes) in [
                (W0, 4u32),
                (X0, 8),
                (trust_cg_ir::regs::H0, 2),
                (trust_cg_ir::regs::S0, 4),
                (trust_cg_ir::regs::D0, 8),
                (trust_cg_ir::regs::V0, 16),
            ] {
                rows.push((opcode, register, bytes));
            }
        }
        for (opcode, bytes) in [
            (AArch64Opcode::StrbRI, 1),
            (AArch64Opcode::StrhRI, 2),
            (AArch64Opcode::VolatileStrbRI, 1),
            (AArch64Opcode::VolatileStrhRI, 2),
        ] {
            rows.push((opcode, W0, bytes));
        }
        assert_eq!(rows.len(), 16);
        let mut failures = Vec::new();
        let mut count = 0;
        for (opcode, register, bytes) in rows {
            for base in [MachOperand::PReg(SP), MachOperand::Special(SpecialReg::SP)] {
                let inst = MachInst::new(opcode, vec![MachOperand::PReg(register), base]);
                let mut explicit = inst.clone();
                explicit.operands.push(MachOperand::Imm(0));
                let encoded = crate::aarch64::encode::encode_instruction(&inst);
                let zero_encoded = crate::aarch64::encode::encode_instruction(&explicit);
                let expected = (bytes + 15) & !15;
                let actual = compute_max_outgoing_arg_size(&make_func(
                    "scalar_implicit_zero",
                    vec![inst.clone()],
                ));
                count += 1;
                if encoded.is_err()
                    || encoded.as_ref().ok() != zero_encoded.as_ref().ok()
                    || actual != expected
                {
                    failures.push(format!("{inst:?}: outgoing {actual} != {expected}; omitted encoding={encoded:?}, explicit-zero encoding={zero_encoded:?}"));
                }
            }
        }
        assert_eq!(count, 32);
        assert!(
            failures.is_empty(),
            "{}/32 scalar implicit-zero contracts failed:\n{}",
            failures.len(),
            failures.join("\n")
        );
    }

    #[test]
    fn pair_memory_outgoing_scanner_does_not_credit_malformed_or_other_bases() {
        let good = vec![
            MachOperand::PReg(X0),
            MachOperand::PReg(X1),
            MachOperand::PReg(SP),
            MachOperand::Imm(0),
        ];
        let mut bad = Vec::new();
        let mut extra = good.clone();
        extra.push(MachOperand::Imm(0));
        bad.push(extra);
        bad.push(good[..2].to_vec());
        for offset in [
            MachOperand::PReg(X0),
            MachOperand::Imm(1),
            MachOperand::Imm(512),
            MachOperand::Imm(i64::MAX),
            MachOperand::Imm(i64::MIN),
            MachOperand::Imm(-8),
        ] {
            let mut operands = good.clone();
            operands[3] = offset;
            bad.push(operands);
        }
        for base in [X19, W0, trust_cg_ir::regs::WSP, trust_cg_ir::regs::XZR] {
            let mut operands = good.clone();
            operands[2] = MachOperand::PReg(base);
            bad.push(operands);
        }
        for data in [
            SP,
            trust_cg_ir::regs::WSP,
            PReg::new(162),
            PReg::new(4095),
            PReg::new(96),
        ] {
            let mut operands = good.clone();
            operands[0] = MachOperand::PReg(data);
            bad.push(operands);
        }
        let mut failures = Vec::new();
        assert_eq!(bad.len(), 17);
        for operands in bad {
            let inst = MachInst::new(AArch64Opcode::StpRI, operands);
            let func = make_func("pair_non_outgoing", vec![inst.clone()]);
            let actual = std::panic::catch_unwind(|| compute_max_outgoing_arg_size(&func));
            if !matches!(actual, Ok(0)) {
                failures.push(format!("{inst:?}: {actual:?}"));
            }
        }
        for opcode in [
            AArch64Opcode::LdpRI,
            AArch64Opcode::LdpPostIndex,
            AArch64Opcode::StpPreIndex,
            AArch64Opcode::NeonStpQPost,
            AArch64Opcode::NeonLdpQPost,
        ] {
            let func = make_func(
                "not_outgoing_store",
                vec![MachInst::new(opcode, good.clone())],
            );
            assert_eq!(compute_max_outgoing_arg_size(&func), 0, "{opcode:?}");
        }
        assert!(
            failures.is_empty(),
            "{}/17 malformed/non-outgoing pair controls failed:\n{}",
            failures.len(),
            failures.join("\n")
        );
    }

    fn outgoing_frame_sum_fixture(
        opcode: AArch64Opcode,
        base: MachOperand,
        offset: Option<i64>,
        local_bytes: u32,
    ) -> MachFunction {
        let mut operands = vec![MachOperand::PReg(X0), base];
        if let Some(offset) = offset {
            operands.push(MachOperand::Imm(offset));
        }
        let mut func = make_func(
            "outgoing_frame_sum",
            vec![
                MachInst::new(opcode, operands),
                MachInst::new(
                    AArch64Opcode::Bl,
                    vec![MachOperand::Symbol("external_frame_sum_probe".into())],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        if local_bytes != 0 {
            func.alloc_stack_slot(StackSlot::new(local_bytes, 16));
        }
        func
    }

    #[test]
    fn outgoing_frame_sum_overflow_is_structured_refusal_not_panic() {
        use crate::pipeline::{OptLevel, Pipeline, PipelineConfig, PipelineError};
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level: OptLevel::O0,
            target_triple: "aarch64-unknown-linux-gnu".into(),
            ..PipelineConfig::default()
        });
        let mut attempts = 0;
        let mut failures = Vec::new();
        for opcode in [AArch64Opcode::StrRI, AArch64Opcode::VolatileStrRI] {
            for base in [MachOperand::PReg(SP), MachOperand::Special(SpecialReg::SP)] {
                for (offset, local_bytes, outgoing) in [
                    (4_294_967_264i64, 0, 4_294_967_280u32),
                    (4_294_967_248i64, 32, 4_294_967_264u32),
                ] {
                    let mut func =
                        outgoing_frame_sum_fixture(opcode, base.clone(), Some(offset), local_bytes);
                    // The individually representable outgoing area is the
                    // prerequisite, not a substitute for complete-frame bounds.
                    assert_eq!(compute_max_outgoing_arg_size(&func), outgoing);
                    assert!(scan_function(&func).has_calls);
                    assert!(
                        u64::from(outgoing) + u64::from(local_bytes) + 16 > u64::from(u32::MAX)
                    );
                    let before = format!("{func:?}");
                    attempts += 1;
                    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        pipeline.encode_and_emit(&mut func)
                    }));
                    let refused = matches!(
                        &outcome,
                        Ok(Err(PipelineError::FrameLowering(crate::lower::LowerError::FrameLowering(detail))))
                            if detail.contains("frame") && detail.contains("overflow")
                    );
                    if !refused || format!("{func:?}") != before {
                        let detail = match outcome {
                            Err(_) => "PANIC".into(),
                            Ok(Err(error)) => format!("wrong refusal: {error:?}"),
                            Ok(Ok(bytes)) => format!("unexpected object: {} bytes", bytes.len()),
                        };
                        failures.push(format!(
                            "{opcode:?}/{base:?} offset={offset} local={local_bytes}: {detail}"
                        ));
                    }
                }
            }
        }
        eprintln!(
            "OUTGOING_FRAME_SUM negative_attempts={attempts} failures={}",
            failures.len()
        );
        assert_eq!(attempts, 8);
        assert!(
            failures.is_empty(),
            "{} / 8 complete-frame refusals failed:\n{}",
            failures.len(),
            failures.join("\n")
        );
    }

    #[test]
    fn outgoing_frame_sum_valid_boundaries_reach_real_elf_emission() {
        use crate::pipeline::{OptLevel, Pipeline, PipelineConfig};
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level: OptLevel::O0,
            target_triple: "aarch64-unknown-linux-gnu".into(),
            ..PipelineConfig::default()
        });
        let mut attempts = 0;
        let mut failures = Vec::new();
        for opcode in [AArch64Opcode::StrRI, AArch64Opcode::VolatileStrRI] {
            for base in [MachOperand::PReg(SP), MachOperand::Special(SpecialReg::SP)] {
                for offset in [None, Some(0), Some(4088), Some(32760)] {
                    for local_bytes in [0, 32] {
                        let mut func =
                            outgoing_frame_sum_fixture(opcode, base.clone(), offset, local_bytes);
                        let expected_outgoing = ((offset.unwrap_or(0) + 8 + 15) & !15) as u32;
                        let outgoing = compute_max_outgoing_arg_size(&func);
                        assert_eq!(outgoing, expected_outgoing);
                        let layout = compute_frame_layout(&func, outgoing, false);
                        assert!(!layout.is_leaf && layout.uses_frame_pointer);
                        assert_eq!(layout.outgoing_arg_area_size, expected_outgoing);
                        assert_eq!(
                            layout.total_frame_size,
                            16 + local_bytes + expected_outgoing
                        );
                        attempts += 1;
                        let outcome =
                            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                pipeline.encode_and_emit(&mut func)
                            }));
                        if !matches!(&outcome, Ok(Ok(bytes)) if bytes.len() > 64 && bytes.starts_with(b"\x7fELF"))
                        {
                            let detail = match outcome {
                                Err(_) => "PANIC".into(),
                                Ok(Err(error)) => format!("{error:?}"),
                                Ok(Ok(bytes)) => {
                                    format!("non-ELF/truncated object: {} bytes", bytes.len())
                                }
                            };
                            failures.push(format!("{opcode:?}/{base:?} offset={offset:?} local={local_bytes}: {detail}"));
                        }
                    }
                }
            }
        }
        eprintln!(
            "OUTGOING_FRAME_SUM positive_attempts={attempts} failures={}",
            failures.len()
        );
        assert_eq!(attempts, 32);
        assert!(
            failures.is_empty(),
            "{} / 32 valid frame emissions failed:\n{}",
            failures.len(),
            failures.join("\n")
        );
    }

    fn checked_layout_for_test(
        func: &MachFunction,
        outgoing: u32,
        dynamic: bool,
    ) -> Result<FrameLayout, crate::lower::LowerError> {
        if dynamic {
            try_compute_frame_layout_dynamic(func, outgoing, false)
        } else {
            try_compute_frame_layout(func, outgoing, false)
        }
    }

    #[test]
    fn outgoing_frame_checked_total_and_alignment_boundaries() {
        let mut count = 0;
        for dynamic in [false, true] {
            let func =
                outgoing_frame_sum_fixture(AArch64Opcode::StrRI, MachOperand::PReg(SP), Some(0), 0);
            for outgoing in [0u32, 1, 15, 16, 4095, u32::MAX - 31] {
                let layout = checked_layout_for_test(&func, outgoing, dynamic).unwrap();
                let rounded = (u64::from(outgoing) + 15) & !15;
                assert_eq!(u64::from(layout.total_frame_size), rounded + 16);
                assert_eq!(u64::from(layout.outgoing_arg_area_size), rounded);
                count += 1;
            }
            for outgoing in [u32::MAX - 30, u32::MAX - 15, u32::MAX] {
                assert!(
                    matches!(checked_layout_for_test(&func, outgoing, dynamic), Err(crate::lower::LowerError::FrameLowering(detail)) if detail.contains("overflow"))
                );
                count += 1;
            }
            // The raw sum fits u32 but its final rounding does not.
            let mut rounded_overflow = func.clone();
            rounded_overflow.alloc_stack_slot(StackSlot::new(1, 1));
            assert!(
                matches!(checked_layout_for_test(&rounded_overflow, u32::MAX - 31, dynamic), Err(crate::lower::LowerError::FrameLowering(detail)) if detail.contains("alignment"))
            );
            count += 1;
        }
        assert_eq!(count, 20);
    }

    #[test]
    fn outgoing_frame_checked_signed_offsets_include_csa_anchor() {
        let mut count = 0;
        for dynamic in [false, true] {
            let mut func =
                outgoing_frame_sum_fixture(AArch64Opcode::StrRI, MachOperand::PReg(SP), Some(0), 0);
            // Each signed size is valid; their cumulative offset is exactly
            // i32::MIN and must remain accepted with the zero FP/LR anchor.
            func.alloc_stack_slot(StackSlot::new(1 << 30, 1));
            func.alloc_stack_slot(StackSlot::new(1 << 30, 1));
            let layout = checked_layout_for_test(&func, 0, dynamic).unwrap();
            assert_eq!(layout.fp_to_spill_offset, 0);
            assert_eq!(
                stack_slot_frame_offsets(&func, &layout),
                vec![Some(-(1 << 30)), Some(i32::MIN)]
            );
            count += 1;
            // One additional saved GPR pair moves that actual anchor by -16.
            let mut shifted = func.clone();
            let id = shifted.push_inst(MachInst::new(
                AArch64Opcode::MovR,
                vec![MachOperand::PReg(X19), MachOperand::PReg(X0)],
            ));
            shifted.blocks[0].insts.insert(0, id);
            assert!(
                matches!(checked_layout_for_test(&shifted, 0, dynamic), Err(crate::lower::LowerError::FrameLowering(detail)) if detail.contains("CSA-anchored"))
            );
            count += 1;

            let mut maximum_csa =
                outgoing_frame_sum_fixture(AArch64Opcode::StrRI, MachOperand::PReg(SP), Some(0), 0);
            for raw in 19..=28 {
                let id = maximum_csa.push_inst(MachInst::new(
                    AArch64Opcode::MovR,
                    vec![MachOperand::PReg(PReg::new(raw)), MachOperand::PReg(X0)],
                ));
                maximum_csa.blocks[0].insts.insert(0, id);
            }
            for raw in 104..=111 {
                let id = maximum_csa.push_inst(MachInst::new(
                    AArch64Opcode::FmovFprFpr,
                    vec![
                        MachOperand::PReg(PReg::new(raw)),
                        MachOperand::PReg(PReg::new(96)),
                    ],
                ));
                maximum_csa.blocks[0].insts.insert(0, id);
            }
            maximum_csa.alloc_stack_slot(StackSlot::new((1u32 << 31) - 144, 16));
            let layout = checked_layout_for_test(&maximum_csa, 0, dynamic).unwrap();
            assert_eq!(
                (layout.callee_saved_area_size, layout.fp_to_spill_offset),
                (160, -144)
            );
            assert_eq!(
                stack_slot_frame_offsets(&maximum_csa, &layout),
                vec![Some(i32::MIN)]
            );
            count += 1;
            maximum_csa.stack_slots[0].size += 1;
            assert!(
                matches!(checked_layout_for_test(&maximum_csa, 0, dynamic), Err(crate::lower::LowerError::FrameLowering(detail)) if detail.contains("CSA-anchored"))
            );
            count += 1;
        }
        assert_eq!(count, 8);
    }

    #[test]
    fn outgoing_frame_checked_raw_slot_metadata_and_packing() {
        let mut count = 0;
        for dynamic in [false, true] {
            let empty =
                outgoing_frame_sum_fixture(AArch64Opcode::StrRI, MachOperand::PReg(SP), Some(0), 0);
            let mut malformed = Vec::new();
            for size in [1u32 << 31, u32::MAX] {
                malformed.push(StackSlot::new(size, 16));
            }
            malformed.push(StackSlot::new(0, 1 << 31));
            for runtime in [false, true] {
                for align in [0, 3] {
                    let mut slot = if runtime {
                        StackSlot::new_dynamic(StackSlotSizeSource::Unknown, 16)
                    } else {
                        StackSlot::new(8, 16)
                    };
                    // Public/deserialized metadata bypasses constructor guards.
                    slot.align = align;
                    malformed.push(slot);
                }
            }
            assert_eq!(malformed.len(), 7);
            for slot in malformed {
                let mut func = empty.clone();
                func.stack_slots.push(slot);
                assert!(matches!(
                    checked_layout_for_test(&func, 0, dynamic),
                    Err(crate::lower::LowerError::FrameLowering(_))
                ));
                count += 1;
            }
            let mut packed = empty.clone();
            for (size, align) in [(1, 16), (17, 32), (3, 8)] {
                packed.alloc_stack_slot(StackSlot::new(size, align));
            }
            let layout = checked_layout_for_test(&packed, 0, dynamic).unwrap();
            assert_eq!(layout.spill_area_size, 88); // 72 downward extent + 16 slack.
            assert_eq!(layout.total_frame_size, 112);
            assert_eq!(
                stack_slot_frame_offsets(&packed, &layout),
                vec![Some(-16), Some(-64), Some(-72)]
            );
            count += 1;
        }
        assert_eq!(count, 16);
    }

    #[test]
    fn outgoing_frame_checked_minimum_fp_offset_stackaddr_encodes() {
        let mut func = make_func(
            "minimum_fp_offset",
            vec![
                MachInst::new(
                    AArch64Opcode::AddPCRel,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::PReg(SP),
                        MachOperand::StackSlot(StackSlotId(1)),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(1 << 30, 1));
        func.alloc_stack_slot(StackSlot::new(1 << 30, 1));
        // Force the actual FP path; do not emit or execute a huge prologue.
        let layout = try_compute_frame_layout_dynamic(&func, 0, false).unwrap();
        assert_eq!(stack_slot_frame_offsets(&func, &layout)[1], Some(i32::MIN));
        eliminate_frame_indices(&mut func, &layout).unwrap();
        let words = func.blocks[0]
            .insts
            .iter()
            .map(|&id| crate::aarch64::encode::encode_instruction(func.inst(id)).unwrap())
            .collect::<Vec<_>>();
        // Independent MOVZ X0,#0; MOVK X0,#0x8000,LSL#16;
        // SUB X0,X29,X0; RET. The magnitude is unsigned 2^31, not truncated.
        assert_eq!(words, [0xd280_0000, 0xf2b0_0000, 0xcb00_03a0, 0xd65f_03c0]);
    }

    fn compute_shrink_wrap_plan(
        func: &MachFunction,
        layout: &FrameLayout,
    ) -> Option<ShrinkWrapPlan> {
        super::compute_shrink_wrap_plan(&FrameFunctionView::original(func), layout)
    }

    fn emit_shrink_wrapped(func: &mut MachFunction, layout: &FrameLayout, plan: &ShrinkWrapPlan) {
        let mut insertion = FrameInsertionPlan::new(func).unwrap();
        super::emit_shrink_wrapped(func, &mut insertion, layout, plan).unwrap();
        insertion.commit(func).unwrap();
    }

    /// Helper: a frame layout whose SP is NOT a stable base, so out-of-range
    /// frame offsets keep the historical FP-relative + scratch-materialization
    /// lowering.
    ///
    /// [`sp_rebase_delta_for`] re-bases a far slot onto SP (one encodable
    /// instruction) whenever SP is provably fixed across the body, which is the
    /// common case. The pins below exercise the *fallback* machinery — scratch
    /// selection, IP-liveness fail-close, MOVZ/ADD materialization — which is
    /// still the only lowering for a frame that moves SP (a dynamic alloca),
    /// so they build exactly that frame shape.
    fn layout_without_sp_rebase(
        func: &MachFunction,
        out_args: u32,
        has_calls: bool,
    ) -> FrameLayout {
        let mut layout = compute_frame_layout(func, out_args, has_calls);
        layout.has_dynamic_alloc = true;
        layout
    }

    /// Helper: create a function that uses specific callee-saved GPRs.
    fn make_func_with_callee_saved_gprs(regs: &[PReg]) -> MachFunction {
        let mut insts = vec![];
        for &r in regs {
            // Use the register in a simple MOV.
            insts.push(MachInst::new(
                AArch64Opcode::MovR,
                vec![MachOperand::PReg(r), MachOperand::PReg(r)],
            ));
        }
        insts.push(MachInst::new(AArch64Opcode::Ret, vec![]));
        make_func("test_cs_gprs", insts)
    }

    /// Helper: create a function that uses specific callee-saved FPRs.
    fn make_func_with_callee_saved_fprs(regs: &[PReg]) -> MachFunction {
        let mut insts = vec![];
        for &r in regs {
            insts.push(MachInst::new(
                AArch64Opcode::MovR,
                vec![MachOperand::PReg(r), MachOperand::PReg(r)],
            ));
        }
        insts.push(MachInst::new(AArch64Opcode::Ret, vec![]));
        make_func("test_cs_fprs", insts)
    }

    // ---- Shrink-wrapping helpers + tests ----

    fn push_block(func: &mut MachFunction, insts: Vec<MachInst>) -> BlockId {
        let bid = BlockId(func.blocks.len() as u32);
        func.blocks.push(trust_cg_ir::function::MachBlock::new());
        func.block_order.push(bid);
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(bid, id);
        }
        bid
    }

    /// The canonical leaf-guard diamond in post-RA form:
    ///   entry:  cbz w0, ret            (frame-clean guard; succs [save, ret])
    ///   save:   bl f ; mov x19,x19     (CSR + call; the frame region)   -> ret
    ///   ret:    mov w0, w0 ; ret        (shared bare return; preds [entry, save])
    fn make_leaf_guard_func() -> MachFunction {
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new("leafguard".to_string(), sig);
        // entry block (index 0) already exists.
        let entry = BlockId(0);
        // Placeholder targets filled after blocks exist; build blocks first.
        let save = push_block(
            &mut func,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![MachOperand::Symbol("f".into())]),
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![MachOperand::PReg(X19), MachOperand::PReg(X19)],
                ),
            ],
        );
        let ret = push_block(
            &mut func,
            vec![
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![MachOperand::PReg(W0), MachOperand::PReg(W0)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        // entry guard: cbz w0, ret  (fallthrough = save)
        let guard = func.push_inst(MachInst::new(
            AArch64Opcode::Cbz,
            vec![MachOperand::PReg(W0), MachOperand::Block(ret)],
        ));
        func.append_inst(entry, guard);
        // CFG edges.
        func.add_edge(entry, save);
        func.add_edge(entry, ret);
        func.add_edge(save, ret);
        func
    }

    fn leaf_guard_layout(func: &MachFunction) -> FrameLayout {
        compute_frame_layout(func, 0, false)
    }

    #[test]
    fn shrinkwrap_declines_sp_form_slot_access_outside_saved_region() {
        // Regression: the deep-slot SP preference resolves a slot access to
        // MemOp { base: SP, .. }, which the shrink-wrap frame predicate used
        // to treat as frame-clean. On the bare leaf path the prologue never
        // runs, so the access would execute with SP = entry_SP and touch the
        // CALLER's frame. The predicate must classify SP-based slot forms as
        // frame-forcing so this plan is declined.
        let mut func = make_leaf_guard_func();
        func.alloc_stack_slot(StackSlot::new(8192, 16));
        let ldr = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![MachOperand::PReg(X0), MachOperand::FrameIndex(FrameIdx(0))],
        ));
        let ret_block = BlockId(2);
        func.blocks[ret_block.0 as usize].insts.insert(0, ldr);

        let layout = leaf_guard_layout(&func);
        assert!(layout.uses_frame_pointer && !layout.has_dynamic_alloc);
        eliminate_frame_indices(&mut func, &layout).unwrap();

        // The fixture must still exercise the SP form (deep slot, in-reach
        // positive SP offset) or this test stops guarding the interaction.
        let first = func.blocks[ret_block.0 as usize].insts[0];
        match &func.inst(first).operands[1] {
            MachOperand::MemOp { base, offset } => {
                assert_eq!(*base, SP, "fixture must take the SP form");
                assert!((0..=AARCH64_MAX_IMM_OFFSET).contains(offset));
            }
            other => panic!("expected resolved MemOp, got {other:?}"),
        }
        assert!(
            inst_needs_frame(func.inst(first)),
            "SP-form slot access must be frame-forcing"
        );
        assert!(
            compute_shrink_wrap_plan(&func, &layout).is_none(),
            "plan with a frame access outside the saved region must be declined"
        );
    }

    #[test]
    fn shrinkwrap_declines_looped_stack_probes_and_sinks_unrolled_ones() {
        let mut looped = make_leaf_guard_func();
        looped.alloc_stack_slot(StackSlot::new(1 << 20, 16));
        let layout = leaf_guard_layout(&looped);
        assert!(StaticStackProbePlan::for_layout(&layout).looped);
        assert!(compute_shrink_wrap_plan(&looped, &layout).is_none());

        let mut unrolled = make_leaf_guard_func();
        unrolled.alloc_stack_slot(StackSlot::new(
            STACK_PROBE_MAX_UNROLL * STACK_PROBE_INTERVAL,
            16,
        ));
        let layout = leaf_guard_layout(&unrolled);
        let plan = StaticStackProbePlan::for_layout(&layout);
        assert_eq!((plan.steps, plan.looped), (STACK_PROBE_MAX_UNROLL, false));
        let shrink = compute_shrink_wrap_plan(&unrolled, &layout).expect("unrolled probes sink");
        emit_shrink_wrapped(&mut unrolled, &layout, &shrink);
        let save = &unrolled.blocks[shrink.save_block.0 as usize];
        let probes = save
            .insts
            .iter()
            .filter(|id| is_stack_probe(unrolled.inst(**id)))
            .count();
        assert_eq!(probes, STACK_PROBE_MAX_UNROLL as usize);
    }

    #[test]
    fn looped_static_probe_splits_the_entry_into_a_valid_loop() {
        let mut func = make_func("looped_probe", vec![make_ret()]);
        func.alloc_stack_slot(StackSlot::new(1 << 20, 16));
        let ret = func.blocks[0].insts[0];
        let layout = compute_frame_layout(&func, 0, false);
        insert_prologue_epilogue(&mut func, &layout).unwrap();
        crate::pipeline::validate_aarch64_mach_function(&func).unwrap();
        assert_eq!(func.block_order.len(), 3);
        let [entry, probe_loop, body] = [0, 1, 2].map(|i| func.block_order[i]);
        assert_eq!(entry, func.entry);
        let insts = |block: BlockId| {
            func.blocks[block.0 as usize]
                .insts
                .iter()
                .map(|id| func.inst(*id).clone())
                .collect::<Vec<_>>()
        };
        let head = insts(entry);
        assert!(head.iter().all(|inst| !is_stack_probe(inst)));
        assert_eq!(head.last().unwrap().opcode, AArch64Opcode::Movz);
        let iteration = insts(probe_loop);
        assert_eq!(
            iteration.iter().map(|inst| inst.opcode).collect::<Vec<_>>(),
            [
                AArch64Opcode::SubRI,
                AArch64Opcode::SubRI,
                AArch64Opcode::StrRI,
                AArch64Opcode::SubsRI,
                AArch64Opcode::BCond,
            ]
        );
        assert!(is_stack_probe(&iteration[2]));
        assert_eq!(func.blocks[probe_loop.0 as usize].loop_depth, 1);
        assert_eq!(func.blocks[probe_loop.0 as usize].succs, [probe_loop, body]);
        assert!(func.blocks[body.0 as usize].insts.contains(&ret));
    }

    #[test]
    fn framed_entry_backedge_bypasses_one_time_prologue() {
        for probed in [false, true] {
            let mut func = make_func("entry_backedge", vec![]);
            let body_entry = func.entry;
            let loop_block = push_block(
                &mut func,
                vec![MachInst::new(
                    AArch64Opcode::B,
                    vec![MachOperand::Block(body_entry)],
                )],
            );
            let exit = push_block(&mut func, vec![make_ret()]);
            let guard = func.push_inst(MachInst::new(
                AArch64Opcode::Cbz,
                vec![MachOperand::PReg(W0), MachOperand::Block(exit)],
            ));
            func.append_inst(body_entry, guard);
            let to_loop = func.push_inst(MachInst::new(
                AArch64Opcode::B,
                vec![MachOperand::Block(loop_block)],
            ));
            func.append_inst(body_entry, to_loop);
            func.add_edge(body_entry, exit);
            func.add_edge(body_entry, loop_block);
            func.add_edge(loop_block, body_entry);
            let original_body = func.blocks[body_entry.0 as usize].insts.clone();
            if probed {
                func.alloc_stack_slot(StackSlot::new(1 << 20, 16));
            }

            let layout = compute_frame_layout(&func, 0, false);
            assert!(layout.uses_frame_pointer);
            assert_eq!(StaticStackProbePlan::for_layout(&layout).looped, probed);
            insert_prologue_epilogue(&mut func, &layout).unwrap();

            assert_ne!(func.entry, body_entry);
            assert_eq!(func.block_order[0], func.entry);
            let body_pos = func
                .block_order
                .iter()
                .position(|&id| id == body_entry)
                .unwrap();
            assert_eq!(body_pos, if probed { 3 } else { 1 });
            assert_eq!(func.blocks[body_entry.0 as usize].insts, original_body);
            let before_body = func.block_order[body_pos - 1];
            assert!(
                func.blocks[before_body.0 as usize]
                    .succs
                    .contains(&body_entry)
            );
            assert_eq!(func.blocks[loop_block.0 as usize].succs, [body_entry]);
            assert_eq!(
                func.inst(func.blocks[func.entry.0 as usize].insts[0])
                    .opcode,
                AArch64Opcode::StpPreIndex
            );
            crate::pipeline::validate_aarch64_mach_function(&func).unwrap();
        }
    }

    #[test]
    fn test_shrinkwrap_admits_leaf_guard_diamond() {
        let func = make_leaf_guard_func();
        let layout = leaf_guard_layout(&func);
        assert!(layout.uses_frame_pointer);
        assert!(!layout.is_leaf);
        // X19/X20 pair + FP/LR pair.
        assert_eq!(layout.callee_saved_pairs.len(), 2);
        let plan = compute_shrink_wrap_plan(&func, &layout).expect("should admit");
        assert_eq!(plan.save_block, BlockId(1)); // the save block
        assert_eq!(plan.edge_epilogue_blocks, vec![BlockId(1)]);
        assert_eq!(plan.leaf_return_blocks, vec![BlockId(2)]);
        assert!(plan.frame_return_blocks.is_empty());
    }

    #[test]
    fn test_shrinkwrap_declines_sp_relative_slot_access_in_guard() {
        // REGRESSION (gcc-c-torture 20041011-1.c, caught by the ship gate):
        // a far spill slot re-based onto SP is still a FRAME access. If the
        // guard region is allowed to look frame-clean because its base is SP
        // rather than X29, the prologue sinks below the access and the store
        // lands in the CALLER's frame — `t1` aborted with a smashed stack.
        let mut func = make_leaf_guard_func();
        let spill = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::PReg(X16),
                MachOperand::MemOp {
                    base: SP,
                    offset: 0x18,
                },
            ],
        ));
        func.blocks[0].insts.insert(0, spill);
        let layout = leaf_guard_layout(&func);
        assert!(
            compute_shrink_wrap_plan(&func, &layout).is_none(),
            "an SP-based frame access in the guard region must force the prologue to the entry"
        );
    }

    #[test]
    fn test_inst_needs_frame_counts_sp_based_memops() {
        // The predicate itself, independent of any plan shape.
        let sp_access = MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::PReg(PReg::new(0)),
                MachOperand::MemOp {
                    base: SP,
                    offset: 8,
                },
            ],
        );
        assert!(inst_needs_frame(&sp_access));
        let fp_access = MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::PReg(PReg::new(0)),
                MachOperand::MemOp {
                    base: X29,
                    offset: -8,
                },
            ],
        );
        assert!(inst_needs_frame(&fp_access));
        // A plain register move still does not force a frame.
        let clean = MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::PReg(W0), MachOperand::PReg(W0)],
        );
        assert!(!inst_needs_frame(&clean));
    }

    #[test]
    fn test_shrinkwrap_declines_dirty_entry() {
        // Put a callee-saved use in the entry block: the save point cannot sink.
        let mut func = make_leaf_guard_func();
        let dirty = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::PReg(X19), MachOperand::PReg(X19)],
        ));
        // Insert before the guard (front of entry).
        func.blocks[0].insts.insert(0, dirty);
        let layout = leaf_guard_layout(&func);
        assert!(compute_shrink_wrap_plan(&func, &layout).is_none());
    }

    #[test]
    fn test_shrinkwrap_declines_eh() {
        let mut func = make_leaf_guard_func();
        func.eh_metadata.personality = Some("__gxx_personality_v0".to_string());
        let layout = leaf_guard_layout(&func);
        assert!(compute_shrink_wrap_plan(&func, &layout).is_none());
    }

    #[test]
    fn test_shrinkwrap_declines_loop_save_block() {
        // Make the save block a self-loop: the prologue would run every iteration.
        let mut func = make_leaf_guard_func();
        let save = BlockId(1);
        func.add_edge(save, save); // save -> save back edge
        let layout = leaf_guard_layout(&func);
        assert!(
            compute_shrink_wrap_plan(&func, &layout).is_none(),
            "a save block inside a loop must be declined"
        );
    }

    #[test]
    fn test_shrinkwrap_declines_multi_guard_no_leaf() {
        // Entry falls into two call-bearing successors, neither a clean leaf.
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new("noleaf".to_string(), sig);
        let a = push_block(
            &mut func,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![MachOperand::Symbol("f".into())]),
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![MachOperand::PReg(X19), MachOperand::PReg(X19)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let b = push_block(
            &mut func,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![MachOperand::Symbol("g".into())]),
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![MachOperand::PReg(X19), MachOperand::PReg(X19)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let guard = func.push_inst(MachInst::new(
            AArch64Opcode::Cbz,
            vec![MachOperand::PReg(W0), MachOperand::Block(b)],
        ));
        func.append_inst(BlockId(0), guard);
        func.add_edge(BlockId(0), a);
        func.add_edge(BlockId(0), b);
        let layout = leaf_guard_layout(&func);
        // Both successors are frame-dirty; no clean leaf return exists.
        assert!(compute_shrink_wrap_plan(&func, &layout).is_none());
    }

    #[test]
    fn test_shrinkwrap_fail_closed_invariant_rejects_bad_save_block() {
        // Hand-build a plan whose save block does NOT dominate a frame-forcing
        // block (point S at the shared return, which does not dominate `save`).
        let func = make_leaf_guard_func();
        let dom = compute_block_dominators(&FrameFunctionView::original(&func)).unwrap();
        let reachable = compute_reachable(&FrameFunctionView::original(&func), 0);
        let bad_plan = ShrinkWrapPlan {
            save_block: BlockId(2), // the return block — does NOT dominate save(1)
            frame_return_blocks: vec![],
            edge_epilogue_blocks: vec![],
            leaf_return_blocks: vec![BlockId(2)],
        };
        assert!(
            !verify_shrink_wrap_plan(
                &FrameFunctionView::original(&func),
                &dom,
                &reachable,
                &bad_plan
            ),
            "the fail-closed invariant must reject a save block that does not \
             dominate all frame-forcing blocks"
        );
    }

    /// Walk every path of an EMITTED function and require that the callee-saved
    /// area is allocated exactly once before any return that restores it, and
    /// released exactly when it was allocated: a block is entered at one frame
    /// depth only, `StpPreIndex` (the CSA-allocating save) takes depth 0 -> 1,
    /// `LdpPostIndex` (the CSA-releasing restore) takes 1 -> 0, and every `ret`
    /// runs at depth 0. This is the property the final-stream spill-slot net
    /// checks as `callee-saved-not-restored`.
    fn assert_frame_balanced_on_every_path(func: &MachFunction) {
        let n = func.blocks.len();
        let mut entered: Vec<Option<u8>> = vec![None; n];
        let mut work = vec![(func.entry.0 as usize, 0u8)];
        while let Some((b, depth)) = work.pop() {
            match entered[b] {
                Some(seen) if seen == depth => continue,
                Some(seen) => panic!("block {b} is entered at frame depth {seen} AND {depth}"),
                None => entered[b] = Some(depth),
            }
            let mut depth = depth;
            for &id in &func.blocks[b].insts {
                let inst = &func.insts[id.0 as usize];
                match inst.opcode {
                    AArch64Opcode::StpPreIndex => {
                        assert_eq!(depth, 0, "block {b}: second callee-saved allocation");
                        depth = 1;
                    }
                    AArch64Opcode::LdpPostIndex => {
                        assert_eq!(depth, 1, "block {b}: restore of an unsaved frame");
                        depth = 0;
                    }
                    _ if inst.is_return() => {
                        assert_eq!(
                            depth, 0,
                            "block {b}: `ret` with callee-saved registers not restored"
                        );
                    }
                    _ => {}
                }
            }
            for succ in &func.blocks[b].succs {
                work.push((succ.0 as usize, depth));
            }
        }
    }

    /// The `encode_utf8_raw_unchecked` shape (2026-09-28): a frame path reaches
    /// the shared bare return THROUGH a join block the save block does not
    /// dominate.
    ///
    /// ```text
    ///   0 entry: cbz w0, 1 ; b 2          (frame-clean guard)
    ///   1 leaf:  b 4
    ///   2 save:  bl f ; mov x19,x19 ; cbz w1, 3 ; b 5
    ///   3 mid:   b 4                        (frame-only, falls into the join)
    ///   4 join:  b 6                        (preds [leaf, mid]: NOT dominated by 2)
    ///   5 edge:  b 6                        (frame-only)
    ///   6 ret:   ret                        (preds [join, edge])
    /// ```
    ///
    /// Dominance at the return's immediate predecessors classified `join` as a
    /// leaf predecessor and put the only restore on `edge`, so the path
    /// `2 -> 3 -> 4 -> 6` returned with x19/x29/x30 still the frame's. Returns
    /// the function and its (join, mid, edge, ret) block ids.
    fn make_frame_path_through_leaf_join_func() -> (MachFunction, [BlockId; 4]) {
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new("frame_through_join".to_string(), sig);
        let entry = BlockId(0);
        let leaf = push_block(&mut func, vec![]);
        let save = push_block(
            &mut func,
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![MachOperand::Symbol("f".into())]),
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![MachOperand::PReg(X19), MachOperand::PReg(X19)],
                ),
            ],
        );
        let mid = push_block(&mut func, vec![]);
        let join = push_block(&mut func, vec![]);
        let edge = push_block(&mut func, vec![]);
        let ret = push_block(&mut func, vec![MachInst::new(AArch64Opcode::Ret, vec![])]);
        let branch = |func: &mut MachFunction, from: BlockId, inst: MachInst| {
            let id = func.push_inst(inst);
            func.append_inst(from, id);
        };
        branch(
            &mut func,
            entry,
            MachInst::new(
                AArch64Opcode::Cbz,
                vec![MachOperand::PReg(W0), MachOperand::Block(leaf)],
            ),
        );
        branch(
            &mut func,
            entry,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(save)]),
        );
        branch(
            &mut func,
            leaf,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(join)]),
        );
        branch(
            &mut func,
            save,
            MachInst::new(
                AArch64Opcode::Cbz,
                vec![MachOperand::PReg(W1), MachOperand::Block(mid)],
            ),
        );
        branch(
            &mut func,
            save,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(edge)]),
        );
        branch(
            &mut func,
            mid,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(join)]),
        );
        branch(
            &mut func,
            join,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(ret)]),
        );
        branch(
            &mut func,
            edge,
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(ret)]),
        );
        func.add_edge(entry, leaf);
        func.add_edge(entry, save);
        func.add_edge(leaf, join);
        func.add_edge(save, mid);
        func.add_edge(save, edge);
        func.add_edge(mid, join);
        func.add_edge(join, ret);
        func.add_edge(edge, ret);
        (func, [join, mid, edge, ret])
    }

    #[test]
    fn test_shrinkwrap_restores_on_a_frame_path_through_a_non_dominated_join() {
        let (mut func, [join, mid, edge, ret]) = make_frame_path_through_leaf_join_func();
        let layout = leaf_guard_layout(&func);
        let plan = compute_shrink_wrap_plan(&func, &layout)
            .expect("the shape is admissible once the frame path into the join is cut");
        assert_eq!(plan.save_block, BlockId(2));
        // BOTH frame edges into leaf-reached blocks carry the restore: `mid`
        // (into the join) as well as `edge` (into the return).
        assert_eq!(plan.edge_epilogue_blocks, vec![mid, edge]);
        assert_eq!(plan.leaf_return_blocks, vec![ret]);
        assert!(plan.frame_return_blocks.is_empty());
        emit_shrink_wrapped(&mut func, &layout, &plan);
        assert_frame_balanced_on_every_path(&func);
        // The join stays bare: it is leaf-state on both of its edges now.
        assert!(
            func.blocks[join.0 as usize]
                .insts
                .iter()
                .all(|&id| func.insts[id.0 as usize].opcode == AArch64Opcode::B)
        );
    }

    #[test]
    fn test_shrinkwrap_verifier_rejects_the_dominance_only_plan() {
        // The plan the dominance classification produced for this shape: the
        // restore on `edge` only. The independent frame-state check must refuse
        // it, whatever the planner says.
        let (func, [_join, _mid, edge, ret]) = make_frame_path_through_leaf_join_func();
        let view = FrameFunctionView::original(&func);
        let dom = compute_block_dominators(&view).unwrap();
        let reachable = compute_reachable(&view, 0);
        let dominance_only_plan = ShrinkWrapPlan {
            save_block: BlockId(2),
            frame_return_blocks: vec![],
            edge_epilogue_blocks: vec![edge],
            leaf_return_blocks: vec![ret],
        };
        assert!(
            !verify_shrink_wrap_plan(&view, &dom, &reachable, &dominance_only_plan),
            "a frame path reaching a bare `ret` through a non-dominated join must be rejected"
        );
    }

    #[test]
    fn test_shrinkwrap_declines_a_join_whose_frame_predecessor_cannot_be_cut() {
        // `mid` now has a SECOND exit (a frame return), so the restore cannot be
        // placed on its edge into the join alone: the candidate must decline
        // (whole-function prologue) rather than return from `ret` unrestored.
        let (mut func, [join, mid, _edge, _ret]) = make_frame_path_through_leaf_join_func();
        let frame_ret = push_block(&mut func, vec![MachInst::new(AArch64Opcode::Ret, vec![])]);
        let mid_insts = std::mem::take(&mut func.blocks[mid.0 as usize].insts);
        let cond = func.push_inst(MachInst::new(
            AArch64Opcode::Cbz,
            vec![MachOperand::PReg(W1), MachOperand::Block(frame_ret)],
        ));
        func.blocks[mid.0 as usize].insts = std::iter::once(cond).chain(mid_insts).collect();
        func.add_edge(mid, frame_ret);
        assert_eq!(func.blocks[mid.0 as usize].succs, vec![join, frame_ret]);
        let layout = leaf_guard_layout(&func);
        assert!(compute_shrink_wrap_plan(&func, &layout).is_none());
        insert_prologue_epilogue_impl(&mut func, &layout, ShrinkWrapEligibility::DarwinFrame)
            .unwrap();
        assert_frame_balanced_on_every_path(&func);
    }

    #[test]
    fn test_shrinkwrap_leaf_guard_diamond_is_frame_balanced() {
        let mut func = make_leaf_guard_func();
        let layout = leaf_guard_layout(&func);
        let plan = compute_shrink_wrap_plan(&func, &layout).unwrap();
        emit_shrink_wrapped(&mut func, &layout, &plan);
        assert_frame_balanced_on_every_path(&func);
    }

    #[test]
    fn test_shrinkwrap_unwind_encoding_byte_identical() {
        // The compact-unwind encoding is a pure function of FrameLayout, which
        // shrink-wrapping does not change — so it is byte-identical pre/post.
        let mut func = make_leaf_guard_func();
        let layout = leaf_guard_layout(&func);
        let before = encode_compact_unwind(&layout).encoding;
        let plan = compute_shrink_wrap_plan(&func, &layout).unwrap();
        emit_shrink_wrapped(&mut func, &layout, &plan);
        let after = encode_compact_unwind(&layout).encoding;
        assert_eq!(before, after, "compact-unwind encoding must be identical");
        assert_eq!(before & 0x0F00_0000, UNWIND_ARM64_MODE_FRAME);
    }

    #[test]
    fn test_shrinkwrap_emission_places_prologue_at_save_and_leaves_leaf_bare() {
        let mut func = make_leaf_guard_func();
        let layout = leaf_guard_layout(&func);
        let plan = compute_shrink_wrap_plan(&func, &layout).unwrap();
        emit_shrink_wrapped(&mut func, &layout, &plan);

        let is_prologue_store =
            |op: AArch64Opcode| matches!(op, AArch64Opcode::StpPreIndex | AArch64Opcode::StpRI);
        let is_epilogue_load =
            |op: AArch64Opcode| matches!(op, AArch64Opcode::LdpPostIndex | AArch64Opcode::LdpRI);

        // Entry (block 0) has NO prologue store (still just the guard).
        let entry_has_prologue = func.blocks[0]
            .insts
            .iter()
            .any(|&id| is_prologue_store(func.insts[id.0 as usize].opcode));
        assert!(!entry_has_prologue, "entry must stay prologue-free");

        // Save block (1) begins with a prologue store (the CSA-allocating STP).
        let save_first = func.blocks[1].insts[0];
        assert!(is_prologue_store(func.insts[save_first.0 as usize].opcode));

        // Save block ends with an epilogue LOAD (minus ret) on the frame edge.
        let save_last = *func.blocks[1].insts.last().unwrap();
        assert!(is_epilogue_load(func.insts[save_last.0 as usize].opcode));
        assert!(
            !func.blocks[1]
                .insts
                .iter()
                .any(|&id| func.insts[id.0 as usize].is_return()),
            "the frame edge must NOT ret; it falls through to the shared bare ret"
        );

        // The leaf/shared return (block 2) is a bare ret (no epilogue load).
        let ret_has_epilogue = func.blocks[2]
            .insts
            .iter()
            .any(|&id| is_epilogue_load(func.insts[id.0 as usize].opcode));
        assert!(!ret_has_epilogue, "the leaf return must be bare");
        assert!(
            func.blocks[2]
                .insts
                .iter()
                .any(|&id| func.insts[id.0 as usize].is_return())
        );
    }

    #[test]
    fn test_shrinkwrap_disabled_eligibility_keeps_prologue_at_entry() {
        // With eligibility Disabled (the default for every existing caller), the
        // whole-function prologue is emitted at entry regardless of env.
        let mut func = make_leaf_guard_func();
        let layout = leaf_guard_layout(&func);
        insert_prologue_epilogue_impl(&mut func, &layout, ShrinkWrapEligibility::Disabled).unwrap();
        let entry_has_prologue = func.blocks[0].insts.iter().any(|&id| {
            matches!(
                func.insts[id.0 as usize].opcode,
                AArch64Opcode::StpPreIndex | AArch64Opcode::StpRI
            )
        });
        assert!(
            entry_has_prologue,
            "Disabled eligibility must not shrink-wrap"
        );
    }

    #[test]
    fn test_align_up() {
        assert_eq!(align_up(0, 16), 0);
        assert_eq!(align_up(1, 16), 16);
        assert_eq!(align_up(15, 16), 16);
        assert_eq!(align_up(16, 16), 16);
        assert_eq!(align_up(17, 16), 32);
        assert_eq!(align_up(32, 16), 32);
        assert_eq!(align_up(7, 8), 8);
        assert_eq!(align_up(8, 8), 8);
    }

    #[test]
    fn test_layout_empty_leaf() {
        // Empty leaf function: no callee-saves, no spills, no calls.
        let func = make_func(
            "empty_leaf",
            vec![MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        let layout = compute_frame_layout(&func, 0, false);

        assert!(layout.is_leaf);
        assert!(layout.uses_frame_pointer);
        // FP/LR pair always saved on Apple.
        assert_eq!(layout.callee_saved_pairs.len(), 1);
        assert_eq!(layout.callee_saved_area_size, 16);
        assert_eq!(layout.spill_area_size, 0);
        assert_eq!(layout.outgoing_arg_area_size, 0);
        assert_eq!(layout.total_frame_size, 16);
    }

    #[test]
    fn test_layout_with_callee_saved_gprs() {
        // Function uses X19 and X20.
        let func = make_func_with_callee_saved_gprs(&[X19, X20]);
        let layout = compute_frame_layout(&func, 0, false);

        // FP/LR + X19/X20 pair = 2 pairs.
        assert_eq!(layout.callee_saved_pairs.len(), 2);
        assert_eq!(layout.callee_saved_area_size, 32);
        assert_eq!(layout.total_frame_size, 32);
    }

    #[test]
    fn test_layout_with_all_callee_saved() {
        // Function uses all callee-saved GPRs (X19-X28) and all FPRs (V8-V15).
        let mut regs: Vec<PReg> = (19..=28).map(PReg::new).collect();
        let fprs: Vec<PReg> = (72..=79).map(PReg::new).collect(); // V8-V15
        regs.extend(fprs);
        let func = make_func_with_callee_saved_gprs(&regs);
        let layout = compute_frame_layout(&func, 0, false);

        // FP/LR + 5 GPR pairs + 4 FPR pairs = 10 pairs.
        assert_eq!(layout.callee_saved_pairs.len(), 10);
        assert_eq!(layout.callee_saved_area_size, 160);
        assert_eq!(layout.total_frame_size, 160);
    }

    #[test]
    fn test_layout_with_spills() {
        // Function with 3 spill slots.
        let mut func = make_func("spills", vec![MachInst::new(AArch64Opcode::Ret, vec![])]);
        func.alloc_stack_slot(StackSlot::new(8, 8));
        func.alloc_stack_slot(StackSlot::new(8, 8));
        func.alloc_stack_slot(StackSlot::new(4, 4));

        let layout = compute_frame_layout(&func, 0, false);

        // Stack slots: 8 + 8 + 4 = 20 bytes.
        assert_eq!(layout.spill_area_size, 20);
        // Total: 16 (FP/LR) + 20 (spills) = 36, aligned to 48.
        assert_eq!(layout.total_frame_size, 48);
    }

    #[test]
    fn test_slot_area_covers_downward_alignment_padding() {
        // Regression: gcc-c-torture pr65369. A large align-16 local array
        // followed by the 8-byte stack-protector canary slot (allocated last,
        // hence lowest). The downward allocator rounds the array's base DOWN to
        // 16, introducing padding that an upward-packing area sum under-counts —
        // which used to place the canary slot BELOW SP where a callee clobbered
        // it. The reserved slot area MUST cover the lowest slot offset.
        let mut func = make_func(
            "ssp_layout",
            vec![MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        func.alloc_stack_slot(StackSlot::new(97, 16)); // input[97], 16-aligned
        func.alloc_stack_slot(StackSlot::new(8, 8)); // canary

        let layout = compute_frame_layout(&func, 0, false);
        let offsets = stack_slot_frame_offsets(&func, &layout);
        let lowest = offsets.iter().flatten().copied().min().unwrap();

        // The lowest slot must sit at or above the bottom of the reserved slot
        // area (fp_to_spill_offset - spill_area_size); otherwise it falls below
        // SP. Before the fix, spill_area_size was 0x70 while the canary landed
        // at fp_to_spill_offset - 0x78 — 8 bytes too low.
        let area_bottom = layout.fp_to_spill_offset - layout.spill_area_size as i32;
        assert!(
            lowest >= area_bottom,
            "lowest slot {lowest} is below the reserved area bottom {area_bottom} \
             (spill_area_size={}) — a callee would clobber it",
            layout.spill_area_size,
        );
        // Downward extent is 0x78 (input base rounds to -112, canary to -120),
        // not the naive upward sum of 0x70.
        assert_eq!(layout.spill_area_size, 0x78);
    }

    #[test]
    fn test_stack_slot_frame_offsets_exposes_fixed_fp_offsets() {
        let mut func = make_func(
            "slot_offsets",
            vec![MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        func.alloc_stack_slot(StackSlot::new(8, 8));
        func.alloc_stack_slot(StackSlot::new(16, 16));
        func.alloc_stack_slot(StackSlot::new_dynamic(StackSlotSizeSource::Unknown, 16));
        func.alloc_stack_slot(StackSlot::new(4, 4));

        let layout = compute_frame_layout(&func, 0, false);

        assert_eq!(
            stack_slot_frame_offsets(&func, &layout),
            vec![Some(-8), Some(-32), None, Some(-36)]
        );
    }

    #[test]
    fn test_layout_with_outgoing_args() {
        // Non-leaf function with outgoing args.
        let func = make_func(
            "with_call",
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![MachOperand::Imm(0)]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let layout = compute_frame_layout(&func, 24, false);

        assert!(!layout.is_leaf);
        // Outgoing args: 24 aligned to 32.
        assert_eq!(layout.outgoing_arg_area_size, 32);
        // Total: 16 (FP/LR) + 32 (args) = 48.
        assert_eq!(layout.total_frame_size, 48);
    }

    #[test]
    fn test_layout_alignment_enforcement() {
        // Ensure total frame size is always 16-byte aligned.
        let mut func = make_func(
            "align_test",
            vec![MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        // One 1-byte slot: forces alignment padding.
        func.alloc_stack_slot(StackSlot::new(1, 1));

        let layout = compute_frame_layout(&func, 0, false);

        assert_eq!(layout.total_frame_size % 16, 0);
        // 16 (FP/LR) + 1 (slot) = 17, aligned to 32.
        assert_eq!(layout.total_frame_size, 32);
    }

    #[test]
    fn test_red_zone_eligible() {
        // Leaf function with no spills and small frame.
        let func = make_func(
            "leaf",
            vec![
                MachInst::new(AArch64Opcode::Nop, vec![]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let layout = compute_frame_layout(&func, 0, true);

        assert!(layout.is_leaf);
        assert!(layout.uses_red_zone);
    }

    #[test]
    fn test_zero_frame_trivial_leaf_when_enabled() {
        let mut func = make_func(
            "rbit_leaf",
            vec![
                MachInst::new(
                    AArch64Opcode::Rbit,
                    vec![MachOperand::PReg(W0), MachOperand::PReg(W0)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(4, 4));

        let layout = compute_frame_layout(&func, 0, true);

        assert!(layout.is_leaf);
        assert!(!layout.uses_frame_pointer);
        assert!(layout.callee_saved_pairs.is_empty());
        assert_eq!(layout.callee_saved_area_size, 0);
        assert_eq!(layout.total_frame_size, 0);
        assert!(emit_prologue(&layout).is_empty());

        let epilogue = emit_epilogue(&layout);
        assert_eq!(epilogue.len(), 1);
        assert_eq!(epilogue[0].opcode, AArch64Opcode::Ret);
        assert_eq!(
            encode_compact_unwind(&layout).encoding,
            UNWIND_ARM64_MODE_FRAMELESS
        );
    }

    #[test]
    fn stack_guard_admission_requires_a_reserved_fixed_guard_slot() {
        for slot in [
            None,
            Some(StackSlot::new(4, 4)),
            Some(StackSlot::new_dynamic(StackSlotSizeSource::Unknown, 16)),
        ] {
            let mut func = make_func(
                "bad_guard_slot",
                vec![MachInst::new(AArch64Opcode::Ret, vec![])],
            );
            func.stack_protector = StackProtectorMode::StackGuard;
            // Missing, undersized, or runtime-sized guard storage must not
            // silently turn a protected function into an unprotected one.
            func.stack_protector_slot = Some(trust_cg_ir::StackSlotId(0));
            if let Some(slot) = slot {
                func.stack_slots.push(slot);
            }
            let layout = compute_frame_layout(&func, 0, true);
            let before = format!("{func:?}");
            assert!(insert_prologue_epilogue(&mut func, &layout).is_err());
            assert_eq!(format!("{func:?}"), before);
        }
    }

    #[test]
    fn stack_guard_admission_rejects_missing_reservation_before_frame_edits() {
        let mut func = make_func(
            "missing_guard_slot",
            vec![MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        func.stack_protector = StackProtectorMode::StackGuard;
        let layout = compute_frame_layout(&func, 0, true);
        let before = format!("{func:?}");
        assert!(insert_prologue_epilogue(&mut func, &layout).is_err());
        assert_eq!(format!("{func:?}"), before);
    }

    #[test]
    fn stack_guard_admission_reservation_is_checked_and_idempotent() {
        let mut func = make_func(
            "guard_reservation",
            vec![MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        ensure_stack_protector_slot(&mut func).unwrap();
        assert!(func.stack_slots.is_empty());
        func.stack_protector = StackProtectorMode::StackGuard;
        ensure_stack_protector_slot(&mut func).unwrap();
        assert_eq!(func.stack_slots, [StackSlot::new(8, 16)]);
        let before = format!("{func:?}");
        ensure_stack_protector_slot(&mut func).unwrap();
        assert_eq!(format!("{func:?}"), before);
        for slot in [
            StackSlot::new(8, 8),
            StackSlot::new(16, 16),
            StackSlot::new_dynamic(StackSlotSizeSource::Unknown, 16),
        ] {
            func.stack_slots[0] = slot;
            let invalid = format!("{func:?}");
            assert!(ensure_stack_protector_slot(&mut func).is_err());
            assert_eq!(format!("{func:?}"), invalid);
        }
    }

    #[test]
    fn stack_guard_admission_shrinkwrap_cannot_hide_a_missing_guard() {
        let mut func = make_func(
            "guard_shrinkwrap",
            vec![MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        func.stack_protector = StackProtectorMode::StackGuard;
        let layout = compute_frame_layout(&func, 0, true);
        let before = format!("{func:?}");
        assert!(
            insert_prologue_epilogue_shrinkwrap(
                &mut func,
                &layout,
                ShrinkWrapEligibility::DarwinFrame
            )
            .is_err()
        );
        assert_eq!(format!("{func:?}"), before);
    }

    #[test]
    fn test_stack_protector_trivial_leaf_uses_frame_before_guard_save() {
        let mut func = make_func("ssp_leaf", vec![MachInst::new(AArch64Opcode::Ret, vec![])]);
        func.stack_protector = StackProtectorMode::StackGuard;
        ensure_stack_protector_slot(&mut func).unwrap();

        let layout = compute_frame_layout(&func, 0, true);

        assert!(layout.is_leaf);
        assert!(layout.uses_frame_pointer);
        assert!(!layout.uses_red_zone);
        assert_eq!(layout.callee_saved_pairs.len(), 1);
        // The canary slot is 16-byte aligned (one full granule) so that hoisting
        // it above the locals cannot shift any other slot off its alignment.
        assert_eq!(layout.spill_area_size, 16);
        assert_eq!(layout.total_frame_size, 32);

        insert_prologue_epilogue(&mut func, &layout).unwrap();

        let entry_insts = &func.blocks[func.entry.0 as usize].insts;
        let opcodes: Vec<AArch64Opcode> = entry_insts
            .iter()
            .map(|inst_id| func.inst(*inst_id).opcode)
            .collect();
        assert_eq!(opcodes[0], AArch64Opcode::StpPreIndex);
        assert_eq!(opcodes[1], AArch64Opcode::AddRI);
        assert_eq!(opcodes[2], AArch64Opcode::SubRI);

        let guard_store_index = entry_insts
            .iter()
            .position(|inst_id| {
                let inst = func.inst(*inst_id);
                inst.opcode == AArch64Opcode::StrRI
                    && matches!(
                        inst.operands.as_slice(),
                        [
                            MachOperand::PReg(reg),
                            MachOperand::MemOp { base, offset },
                        ] if *reg == X16 && *base == X29 && *offset == -16
                    )
            })
            .expect("stack protector should save guard to the fixed FP-relative slot");
        assert!(
            guard_store_index > 2,
            "guard save must run after the frame pointer prologue: {opcodes:?}"
        );
    }

    /// A representative matrix of local-slot shapes for the frame-layout pins:
    /// narrow scalars, wide scalars, over-aligned buffers, odd-sized char
    /// arrays (the classic smashable buffer), and runtime-sized allocas.
    fn protector_layout_slot_shapes() -> Vec<Vec<StackSlot>> {
        vec![
            vec![StackSlot::new(64, 1)],
            vec![StackSlot::new(1, 1)],
            vec![StackSlot::new(97, 16)],
            vec![StackSlot::new(4, 4), StackSlot::new(8, 8)],
            vec![
                StackSlot::new(3, 1),
                StackSlot::new(4, 4),
                StackSlot::new(8, 8),
                StackSlot::new(16, 16),
            ],
            vec![StackSlot::new(32, 32), StackSlot::new(7, 1)],
            vec![
                StackSlot::new(12, 4),
                StackSlot::new_dynamic(StackSlotSizeSource::Unknown, 16),
                StackSlot::new(40, 8),
            ],
            vec![
                StackSlot::new(1, 1),
                StackSlot::new(1, 1),
                StackSlot::new(1, 1),
                StackSlot::new(255, 16),
                StackSlot::new(9, 1),
            ],
        ]
    }

    fn make_protected_func(name: &str, slots: &[StackSlot]) -> MachFunction {
        let mut func = make_func(name, vec![MachInst::new(AArch64Opcode::Ret, vec![])]);
        for slot in slots {
            func.alloc_stack_slot(*slot);
        }
        func.stack_protector = StackProtectorMode::StackGuard;
        ensure_stack_protector_slot(&mut func).unwrap();
        func
    }

    /// SECURITY PIN. The stack-protector canary must sit ABOVE every other
    /// stack slot, adjacent to the saved FP/LR frame record.
    ///
    /// A canary allocated in program order lands LAST, and since slots grow
    /// downward that makes it the DEEPEST slot — below every local buffer. An
    /// upward buffer overflow then reaches the saved return address without
    /// ever crossing the guard, so the protector cannot fire for the threat
    /// model it exists for. Witness before the fix: Queens `_Doit` kept the
    /// canary at x29-0xe8 with every address-taken local at x29-0x14..-0xdc
    /// ABOVE it, and a real smash silently corrupted the frame instead of
    /// trapping.
    #[test]
    fn stack_protector_canary_sits_above_every_other_slot() {
        for (case, slots) in protector_layout_slot_shapes().iter().enumerate() {
            let func = make_protected_func(&format!("ssp_above_{case}"), slots);
            let layout = compute_frame_layout(&func, 0, false);
            let offsets = stack_slot_frame_offsets(&func, &layout);

            let protector_id = func
                .stack_protector_slot
                .expect("protected function must have a canary slot");
            let canary = offsets[protector_id.0 as usize]
                .expect("the canary is a fixed-size slot and must have a static offset");

            for (idx, offset) in offsets.iter().enumerate() {
                if idx == protector_id.0 as usize {
                    continue;
                }
                let Some(offset) = *offset else { continue };
                assert!(
                    offset < canary,
                    "case {case}: slot {idx} sits at {offset} which is NOT below the \
                     canary at {canary} — an overflow of that slot can reach the \
                     saved FP/LR without crossing the guard",
                );
            }

            // Adjacent to the frame record: nothing may be reserved between the
            // top of the local area and the canary's own granule.
            assert_eq!(
                canary,
                layout.fp_to_spill_offset - STACK_ALIGNMENT as i32,
                "case {case}: canary must be the first slot below the frame record",
            );
        }
    }

    /// The reserved slot area must cover every slot the layout actually places,
    /// for the protector-hoisted order. `compute_stack_slot_area` (frame SIZE)
    /// and `stack_slot_frame_offsets` (slot ADDRESSES) run the same downward
    /// algorithm and agree only because they share `stack_slot_layout_order`;
    /// desynchronizing them pushes the deepest slots past SP into the
    /// outgoing-argument area, where a callee's stores destroy them. That is
    /// exactly the failure mode that produced five gcc-c-torture miscompiles
    /// when this hoist was first attempted.
    #[test]
    fn stack_protector_hoist_keeps_slot_area_and_offsets_in_sync() {
        for (case, slots) in protector_layout_slot_shapes().iter().enumerate() {
            let func = make_protected_func(&format!("ssp_sync_{case}"), slots);
            let layout = compute_frame_layout(&func, 0, false);
            let offsets = stack_slot_frame_offsets(&func, &layout);

            let area_bottom = layout.fp_to_spill_offset - layout.spill_area_size as i32;
            for (idx, offset) in offsets.iter().enumerate() {
                let Some(offset) = *offset else { continue };
                assert!(
                    offset >= area_bottom,
                    "case {case}: slot {idx} at {offset} falls below the reserved area \
                     bottom {area_bottom} (spill_area_size={}) — a callee would clobber it",
                    layout.spill_area_size,
                );
            }

            // Every fixed slot keeps its own alignment despite the hoist.
            for (idx, offset) in offsets.iter().enumerate() {
                let Some(offset) = *offset else { continue };
                let align = func.stack_slots[idx].align as i32;
                assert_eq!(
                    offset & (align - 1),
                    0,
                    "case {case}: slot {idx} at {offset} is not {align}-byte aligned",
                );
            }

            // Slots must not overlap.
            let mut placed: Vec<(i32, i32)> = offsets
                .iter()
                .enumerate()
                .filter_map(|(idx, offset)| {
                    offset.map(|offset| (offset, offset + func.stack_slots[idx].size as i32))
                })
                .collect();
            placed.sort_unstable();
            for pair in placed.windows(2) {
                assert!(
                    pair[0].1 <= pair[1].0,
                    "case {case}: slot ranges {:?} and {:?} overlap",
                    pair[0],
                    pair[1],
                );
            }
        }
    }

    /// Hoisting the canary must not perturb the layout of functions that have
    /// no protector: `stack_slot_layout_order` degrades to plain allocation
    /// order when `stack_protector_slot` is `None`.
    #[test]
    fn stack_slot_layout_order_is_identity_without_a_protector() {
        for (case, slots) in protector_layout_slot_shapes().iter().enumerate() {
            let mut func = make_func(
                &format!("no_ssp_{case}"),
                vec![MachInst::new(AArch64Opcode::Ret, vec![])],
            );
            for slot in slots {
                func.alloc_stack_slot(*slot);
            }
            let order: Vec<usize> = stack_slot_layout_order(&func).collect();
            assert_eq!(order, (0..slots.len()).collect::<Vec<_>>(), "case {case}");
        }
    }

    #[test]
    fn test_stack_protector_guard_offset_requires_frame_pointer() {
        let mut func = make_func("ssp_no_fp", vec![MachInst::new(AArch64Opcode::Ret, vec![])]);
        func.stack_protector = StackProtectorMode::StackGuard;
        ensure_stack_protector_slot(&mut func).unwrap();
        let mut layout = compute_frame_layout(&func, 0, true);
        layout.uses_frame_pointer = false;

        let before = format!("{func:?}");
        let error = insert_prologue_epilogue(&mut func, &layout).unwrap_err();
        assert!(error.to_string().contains("requires a frame pointer"));
        assert_eq!(format!("{func:?}"), before);
    }

    #[test]
    fn test_insert_prologue_epilogue_retargets_rbit_return_copy() {
        let mut func = make_func(
            "rbit_return_copy",
            vec![
                MachInst::new(
                    AArch64Opcode::Rbit,
                    vec![MachOperand::PReg(W1), MachOperand::PReg(W0)],
                ),
                MachInst::new(
                    AArch64Opcode::Uxtw,
                    vec![MachOperand::PReg(X0), MachOperand::PReg(W1)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let layout = compute_frame_layout(&func, 0, true);

        insert_prologue_epilogue(&mut func, &layout).unwrap();

        let block_insts = &func.blocks[func.entry.0 as usize].insts;
        assert_eq!(block_insts.len(), 2);
        let rbit = func.inst(block_insts[0]);
        assert_eq!(rbit.opcode, AArch64Opcode::Rbit);
        assert_eq!(
            rbit.operands,
            vec![MachOperand::PReg(W0), MachOperand::PReg(W0)]
        );
        assert_eq!(func.inst(block_insts[1]).opcode, AArch64Opcode::Ret);
    }

    #[test]
    fn test_insert_prologue_epilogue_removes_uxtw_before_rbit_return() {
        let mut func = make_func(
            "rbit_return_uxtw",
            vec![
                MachInst::new(
                    AArch64Opcode::Uxtw,
                    vec![MachOperand::PReg(X0), MachOperand::PReg(W0)],
                ),
                MachInst::new(
                    AArch64Opcode::Rbit,
                    vec![MachOperand::PReg(W0), MachOperand::PReg(W0)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let layout = compute_frame_layout(&func, 0, true);

        insert_prologue_epilogue(&mut func, &layout).unwrap();

        let block_insts = &func.blocks[func.entry.0 as usize].insts;
        assert_eq!(block_insts.len(), 2);
        assert_eq!(func.inst(block_insts[0]).opcode, AArch64Opcode::Rbit);
        assert_eq!(func.inst(block_insts[1]).opcode, AArch64Opcode::Ret);
    }

    #[test]
    fn test_insert_prologue_epilogue_removes_identity_mov_before_rbit_return() {
        let mut func = make_func(
            "rbit_return_identity_mov",
            vec![
                MachInst::new(
                    AArch64Opcode::MOVWrr,
                    vec![MachOperand::PReg(W0), MachOperand::PReg(W0)],
                ),
                MachInst::new(
                    AArch64Opcode::Rbit,
                    vec![MachOperand::PReg(W0), MachOperand::PReg(W0)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let layout = compute_frame_layout(&func, 0, true);

        insert_prologue_epilogue(&mut func, &layout).unwrap();

        let block_insts = &func.blocks[func.entry.0 as usize].insts;
        assert_eq!(block_insts.len(), 2);
        assert_eq!(func.inst(block_insts[0]).opcode, AArch64Opcode::Rbit);
        assert_eq!(func.inst(block_insts[1]).opcode, AArch64Opcode::Ret);
    }

    #[test]
    fn test_insert_prologue_epilogue_removes_x_to_w_mov_before_rbit_return() {
        let mut func = make_func(
            "rbit_return_x_to_w_mov",
            vec![
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![MachOperand::PReg(W0), MachOperand::PReg(X0)],
                ),
                MachInst::new(
                    AArch64Opcode::Rbit,
                    vec![MachOperand::PReg(W0), MachOperand::PReg(W0)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let layout = compute_frame_layout(&func, 0, true);

        insert_prologue_epilogue(&mut func, &layout).unwrap();

        let block_insts = &func.blocks[func.entry.0 as usize].insts;
        assert_eq!(block_insts.len(), 2);
        assert_eq!(func.inst(block_insts[0]).opcode, AArch64Opcode::Rbit);
        assert_eq!(func.inst(block_insts[1]).opcode, AArch64Opcode::Ret);
    }

    #[test]
    fn test_insert_prologue_epilogue_cleans_up_before_symbol_tail_branch() {
        let mut func = make_func(
            "tail_caller",
            vec![MachInst::new(
                AArch64Opcode::TailCall,
                vec![MachOperand::Symbol("tail_callee".to_string())],
            )],
        );
        func.alloc_stack_slot(StackSlot::new(8, 8));

        let layout = compute_frame_layout(&func, 0, false);
        assert!(
            layout.is_leaf,
            "tail calls do not write LR or return locally"
        );
        assert!(layout.uses_frame_pointer);
        assert!(layout.sp_adjustment() > 0);

        insert_prologue_epilogue(&mut func, &layout).unwrap();

        let opcodes: Vec<AArch64Opcode> = func.blocks[func.entry.0 as usize]
            .insts
            .iter()
            .map(|inst_id| func.inst(*inst_id).opcode)
            .collect();

        assert_eq!(opcodes.last(), Some(&AArch64Opcode::TailCall));
        assert!(
            !opcodes.contains(&AArch64Opcode::Ret),
            "tail branch cleanup must not insert a local return"
        );
        assert_eq!(
            &opcodes[opcodes.len() - 3..],
            &[
                AArch64Opcode::AddRI,
                AArch64Opcode::LdpPostIndex,
                AArch64Opcode::TailCall,
            ],
            "symbol tail branches must restore the frame before branching"
        );
    }

    #[test]
    fn test_zero_frame_disabled_for_callee_saved_leaf() {
        let func = make_func_with_callee_saved_gprs(&[X19]);
        let layout = compute_frame_layout(&func, 0, true);

        assert!(layout.is_leaf);
        assert!(layout.uses_frame_pointer);
        assert_eq!(layout.callee_saved_pairs.len(), 2);
        assert_eq!(layout.callee_saved_area_size, 32);
    }

    #[test]
    fn test_red_zone_disabled_for_non_leaf() {
        let func = make_func(
            "non_leaf",
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![MachOperand::Imm(0)]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let layout = compute_frame_layout(&func, 0, true);

        assert!(!layout.is_leaf);
        assert!(!layout.uses_red_zone);
    }

    #[test]
    fn test_red_zone_disabled_with_spills() {
        let mut func = make_func(
            "leaf_spills",
            vec![
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![MachOperand::PReg(X0), MachOperand::FrameIndex(FrameIdx(0))],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(8, 8));
        let layout = compute_frame_layout(&func, 0, true);

        assert!(layout.is_leaf);
        assert!(!layout.uses_red_zone); // Has stack slots.
    }

    #[test]
    fn test_red_zone_disabled_for_dynamic_frame() {
        let func = make_func(
            "leaf_dynamic_frame",
            vec![MachInst::new(AArch64Opcode::Ret, vec![])],
        );

        let layout = compute_frame_layout_dynamic(&func, 0, true);

        assert!(layout.is_leaf);
        assert!(layout.has_dynamic_alloc);
        assert!(!layout.uses_red_zone);
    }

    #[test]
    fn test_prologue_simple() {
        // Simple function: just FP/LR, no other callee-saves, no spills.
        let func = make_func("simple", vec![MachInst::new(AArch64Opcode::Ret, vec![])]);
        let layout = compute_frame_layout(&func, 0, false);
        let prologue = emit_prologue(&layout);

        // Expect: STP X29, X30, [SP, #-16]!; ADD X29, SP, #0 (MOV X29, SP)
        assert_eq!(prologue.len(), 2);
        assert_eq!(prologue[0].opcode, AArch64Opcode::StpPreIndex);
        assert_eq!(prologue[1].opcode, AArch64Opcode::AddRI);
    }

    #[test]
    fn test_prologue_with_callee_saves_and_spills() {
        let mut func = make_func_with_callee_saved_gprs(&[X19, X20, X21, X22]);
        func.alloc_stack_slot(StackSlot::new(16, 8));

        let layout = compute_frame_layout(&func, 0, false);
        let prologue = emit_prologue(&layout);

        // Apple-canonical FRAME layout (csa = 3 pairs * 16 = 48). Extra pairs
        // sit BELOW FP in register-number order (X19 at [FP-8], X20 at [FP-16],
        // X21 at [FP-24], X22 at [FP-32]); FP/LR sit at the TOP ([FP]/[FP+8]):
        //   STP X22, X21, [SP, #-48]!   ; bottom pair, pre-index allocates CSA
        //   STP X20, X19, [SP, #16]     ; next extra pair (reversed regs)
        //   STP X29, X30, [SP, #32]     ; FP/LR at the top of the CSA
        //   ADD X29, SP, #32            ; FP -> FP/LR slot
        //   SUB SP, SP, #16             ; spill area, aligned
        assert_eq!(prologue.len(), 5);
        assert_eq!(prologue[0].opcode, AArch64Opcode::StpPreIndex);
        assert_eq!(prologue[1].opcode, AArch64Opcode::StpRI);
        assert_eq!(prologue[2].opcode, AArch64Opcode::StpRI);
        assert_eq!(prologue[3].opcode, AArch64Opcode::AddRI);
        assert_eq!(prologue[4].opcode, AArch64Opcode::SubRI);

        // Bottom pre-index store saves the highest-numbered pair (X22, X21) and
        // allocates the whole 48-byte callee-saved area.
        assert_eq!(prologue[0].operands[0], MachOperand::PReg(X22));
        assert_eq!(prologue[0].operands[1], MachOperand::PReg(X21));
        assert_eq!(prologue[0].operands[3], MachOperand::Imm(-48));

        // X20/X19 stored just below FP/LR (reversed so X19 lands at [FP-8]).
        assert_eq!(prologue[1].operands[0], MachOperand::PReg(X20));
        assert_eq!(prologue[1].operands[1], MachOperand::PReg(X19));
        assert_eq!(prologue[1].operands[3], MachOperand::Imm(16));

        // FP/LR at the top of the CSA, FP established there.
        assert_eq!(prologue[2].operands[0], MachOperand::PReg(X29));
        assert_eq!(prologue[2].operands[1], MachOperand::PReg(X30));
        assert_eq!(prologue[2].operands[3], MachOperand::Imm(32));
        assert_eq!(prologue[3].operands[0], MachOperand::PReg(X29));
        assert_eq!(prologue[3].operands[2], MachOperand::Imm(32));
    }

    #[test]
    fn test_prologue_epilogue_split_large_sp_adjustments() {
        let mut func = make_func(
            "large_frame",
            vec![MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        func.alloc_stack_slot(StackSlot::new(8432, 16));

        let layout = compute_frame_layout(&func, 0, false);
        assert!(
            layout.sp_adjustment() > 4095,
            "test must exercise an immediate larger than ADD/SUB imm12"
        );

        let prologue = emit_prologue(&layout);
        let prologue_chunks: Vec<i64> = prologue
            .iter()
            .filter(|inst| inst.opcode == AArch64Opcode::SubRI)
            .map(sp_adjustment_imm)
            .collect();
        assert_eq!(
            prologue_chunks.iter().sum::<i64>(),
            i64::from(layout.sp_adjustment())
        );
        assert!(
            prologue_chunks
                .iter()
                .all(|imm| (1..=i64::from(AARCH64_ADD_SUB_IMM12_MAX)).contains(imm))
        );
        assert!(
            prologue_chunks
                .iter()
                .all(|imm| imm % i64::from(STACK_ALIGNMENT) == 0)
        );
        for inst in prologue
            .iter()
            .filter(|inst| inst.opcode == AArch64Opcode::SubRI)
        {
            crate::aarch64::encode_instruction(inst)
                .expect("large-frame prologue SP chunk must be encodable");
        }

        let epilogue = emit_epilogue(&layout);
        let epilogue_chunks: Vec<i64> = epilogue
            .iter()
            .filter(|inst| inst.opcode == AArch64Opcode::AddRI)
            .map(sp_adjustment_imm)
            .collect();
        assert_eq!(
            epilogue_chunks.iter().sum::<i64>(),
            i64::from(layout.sp_adjustment())
        );
        assert!(
            epilogue_chunks
                .iter()
                .all(|imm| (1..=i64::from(AARCH64_ADD_SUB_IMM12_MAX)).contains(imm))
        );
        assert!(
            epilogue_chunks
                .iter()
                .all(|imm| imm % i64::from(STACK_ALIGNMENT) == 0)
        );
        for inst in epilogue
            .iter()
            .filter(|inst| inst.opcode == AArch64Opcode::AddRI)
        {
            crate::aarch64::encode_instruction(inst)
                .expect("large-frame epilogue SP chunk must be encodable");
        }
    }

    fn sp_adjustment_imm(inst: &MachInst) -> i64 {
        match inst.operands.get(2) {
            Some(MachOperand::Imm(imm)) => *imm,
            other => panic!("expected SP adjustment immediate, got {other:?}"),
        }
    }

    #[test]
    fn test_epilogue_simple() {
        let func = make_func("simple", vec![MachInst::new(AArch64Opcode::Ret, vec![])]);
        let layout = compute_frame_layout(&func, 0, false);
        let epilogue = emit_epilogue(&layout);

        // LDP X29, X30, [SP], #16 (post-index); RET
        assert_eq!(epilogue.len(), 2);
        assert_eq!(epilogue[0].opcode, AArch64Opcode::LdpPostIndex);
        assert_eq!(epilogue[1].opcode, AArch64Opcode::Ret);
    }

    #[test]
    fn test_epilogue_with_callee_saves_and_spills() {
        let mut func = make_func_with_callee_saved_gprs(&[X19, X20, X21, X22]);
        func.alloc_stack_slot(StackSlot::new(16, 8));

        let layout = compute_frame_layout(&func, 0, false);
        let epilogue = emit_epilogue(&layout);

        // ADD SP, SP, #16
        // LDP X21, X22, [SP, #32]   (signed offset)
        // LDP X19, X20, [SP, #16]   (signed offset)
        // LDP X29, X30, [SP], #48   (post-index)
        // RET
        assert_eq!(epilogue.len(), 5);
        assert_eq!(epilogue[0].opcode, AArch64Opcode::AddRI);
        assert_eq!(epilogue[1].opcode, AArch64Opcode::LdpRI);
        assert_eq!(epilogue[2].opcode, AArch64Opcode::LdpRI);
        assert_eq!(epilogue[3].opcode, AArch64Opcode::LdpPostIndex);
        assert_eq!(epilogue[4].opcode, AArch64Opcode::Ret);
    }

    #[test]
    fn test_prologue_epilogue_symmetry() {
        // Verify prologue saves and epilogue restores match.
        let func = make_func_with_callee_saved_gprs(&[X19, X20, X25, X26]);
        let layout = compute_frame_layout(&func, 0, false);

        let prologue = emit_prologue(&layout);
        let epilogue = emit_epilogue(&layout);

        // Count STP in prologue vs LDP in epilogue.
        // STP: StpPreIndex (FP/LR) + StpRI (X19/X20) + StpRI (X25/X26) = 1 pre-index + 2 offset = 3 total
        // LDP: LdpRI (X25/X26) + LdpRI (X19/X20) + LdpPostIndex (FP/LR) = 2 offset + 1 post-index = 3 total
        let stp_count = prologue
            .iter()
            .filter(|i| i.opcode == AArch64Opcode::StpRI || i.opcode == AArch64Opcode::StpPreIndex)
            .count();
        let ldp_count = epilogue
            .iter()
            .filter(|i| i.opcode == AArch64Opcode::LdpRI || i.opcode == AArch64Opcode::LdpPostIndex)
            .count();

        assert_eq!(stp_count, 3);
        assert_eq!(ldp_count, 3);
    }

    #[test]
    fn test_frame_index_elimination() {
        // Create a function with a FrameIndex operand and eliminate it.
        let mut func = make_func(
            "fi_test",
            vec![
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(PReg::new(0)), // X0
                        MachOperand::FrameIndex(FrameIdx(0)),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(8, 8));

        let layout = compute_frame_layout(&func, 0, false);
        eliminate_frame_indices(&mut func, &layout).unwrap();

        // The FrameIndex should be replaced with a MemOp.
        let inst = &func.insts[0];
        match &inst.operands[1] {
            MachOperand::MemOp { base, offset } => {
                assert_eq!(*base, X29); // FP-relative
                // Offset should be negative (below FP).
                assert!(*offset < 0, "FP offset should be negative, got {}", offset);
            }
            other => panic!("Expected MemOp, got {:?}", other),
        }
    }

    #[test]
    fn test_frame_index_multiple_slots() {
        // Multiple stack slots with different alignments.
        let mut func = make_func(
            "fi_multi",
            vec![
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(PReg::new(0)),
                        MachOperand::FrameIndex(FrameIdx(0)),
                    ],
                ),
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(PReg::new(1)),
                        MachOperand::FrameIndex(FrameIdx(1)),
                    ],
                ),
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(PReg::new(2)),
                        MachOperand::FrameIndex(FrameIdx(2)),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(8, 8)); // Slot 0
        func.alloc_stack_slot(StackSlot::new(4, 4)); // Slot 1
        func.alloc_stack_slot(StackSlot::new(1, 1)); // Slot 2

        let layout = compute_frame_layout(&func, 0, false);
        eliminate_frame_indices(&mut func, &layout).unwrap();

        // All FrameIndex operands should be replaced.
        for (i, inst) in func.insts[..3].iter().enumerate() {
            match &inst.operands[1] {
                MachOperand::MemOp { base, .. } => {
                    assert_eq!(*base, X29);
                }
                other => panic!("Slot {} not eliminated: {:?}", i, other),
            }
        }

        // Verify offsets are distinct and decreasing.
        let offsets: Vec<i64> = (0..3)
            .map(|i| match &func.insts[i].operands[1] {
                MachOperand::MemOp { offset, .. } => *offset,
                _ => unreachable!(),
            })
            .collect();

        // Each subsequent slot should be at a lower (more negative) offset.
        assert!(
            offsets[0] > offsets[1],
            "slot 0 offset {} > slot 1 offset {}",
            offsets[0],
            offsets[1]
        );
        assert!(
            offsets[1] > offsets[2],
            "slot 1 offset {} > slot 2 offset {}",
            offsets[1],
            offsets[2]
        );
    }

    #[test]
    fn test_stack_slots_stay_inside_adjusted_sp_with_callee_saves() {
        let mut insts = Vec::new();
        for reg in 19..=28 {
            let preg = PReg::new(reg);
            insts.push(MachInst::new(
                AArch64Opcode::MovR,
                vec![MachOperand::PReg(preg), MachOperand::PReg(preg)],
            ));
        }
        insts.push(MachInst::new(
            AArch64Opcode::Blr,
            vec![MachOperand::PReg(X16)],
        ));
        insts.push(MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut func = make_func("callee_saves_slots", insts);
        func.alloc_stack_slot(StackSlot::new(40, 8));
        func.alloc_stack_slot(StackSlot::new(8, 8));
        func.alloc_stack_slot(StackSlot::new(8, 8));

        let layout = compute_frame_layout(&func, 0, false);
        assert_eq!(layout.callee_saved_area_size, 96);
        assert_eq!(layout.sp_adjustment(), 64);

        // Apple-canonical layout: FP points at the saved FP/LR pair (top of the
        // CSA), so locals/spills start `csa - 16 = 80` bytes BELOW FP and grow
        // downward. Slot 0 (40) -> FP-120, slot 1 (8) -> FP-128, slot 2 (8) ->
        // FP-136.
        let offsets = compute_slot_offsets(&func, &layout);
        assert_eq!(offsets, vec![-120, -128, -136]);

        // Every slot must stay at or above the final SP. The deepest addressable
        // FP-relative offset is `-(csa - 16) - sp_adjustment` (FP down to SP).
        let min_fp_offset =
            -((layout.callee_saved_area_size as i32 - 16) + layout.sp_adjustment() as i32);
        for offset in offsets {
            assert!(
                offset >= min_fp_offset,
                "slot at FP{offset} is below final SP (min {min_fp_offset}) for layout {layout:?}"
            );
        }
    }

    #[test]
    fn test_compact_unwind_fp_only() {
        // Function with only FP/LR saved.
        let func = make_func("fp_only", vec![MachInst::new(AArch64Opcode::Ret, vec![])]);
        let layout = compute_frame_layout(&func, 0, false);
        let cu = encode_compact_unwind(&layout);

        // Should be FRAME mode with no register-pair flags.
        assert_eq!(cu.encoding, UNWIND_ARM64_MODE_FRAME);
    }

    #[test]
    fn test_compact_unwind_with_gpr_pairs() {
        let func = make_func_with_callee_saved_gprs(&[X19, X20, X21, X22]);
        let layout = compute_frame_layout(&func, 0, false);
        let cu = encode_compact_unwind(&layout);

        let expected = UNWIND_ARM64_MODE_FRAME
            | UNWIND_ARM64_FRAME_X19_X20_PAIR
            | UNWIND_ARM64_FRAME_X21_X22_PAIR;
        assert_eq!(cu.encoding, expected);
    }

    #[test]
    fn test_compact_unwind_with_fpr_pairs() {
        let func = make_func_with_callee_saved_fprs(&[V8, V9, V10, V11]);
        let layout = compute_frame_layout(&func, 0, false);
        let cu = encode_compact_unwind(&layout);

        let expected = UNWIND_ARM64_MODE_FRAME
            | UNWIND_ARM64_FRAME_D8_D9_PAIR
            | UNWIND_ARM64_FRAME_D10_D11_PAIR;
        assert_eq!(cu.encoding, expected);
    }

    #[test]
    fn test_compact_unwind_all_regs() {
        // All callee-saved registers.
        let mut regs: Vec<PReg> = (19..=28).map(PReg::new).collect();
        let fprs: Vec<PReg> = (72..=79).map(PReg::new).collect(); // V8-V15
        regs.extend(fprs);
        let func = make_func_with_callee_saved_gprs(&regs);
        let layout = compute_frame_layout(&func, 0, false);
        let cu = encode_compact_unwind(&layout);

        let expected = UNWIND_ARM64_MODE_FRAME
            | UNWIND_ARM64_FRAME_X19_X20_PAIR
            | UNWIND_ARM64_FRAME_X21_X22_PAIR
            | UNWIND_ARM64_FRAME_X23_X24_PAIR
            | UNWIND_ARM64_FRAME_X25_X26_PAIR
            | UNWIND_ARM64_FRAME_X27_X28_PAIR
            | UNWIND_ARM64_FRAME_D8_D9_PAIR
            | UNWIND_ARM64_FRAME_D10_D11_PAIR
            | UNWIND_ARM64_FRAME_D12_D13_PAIR
            | UNWIND_ARM64_FRAME_D14_D15_PAIR;
        assert_eq!(cu.encoding, expected);
    }

    #[test]
    fn test_compact_unwind_single_gpr() {
        // Only X19 used — still saves X19/X20 as a pair.
        let func = make_func_with_callee_saved_gprs(&[X19]);
        let layout = compute_frame_layout(&func, 0, false);
        let cu = encode_compact_unwind(&layout);

        let expected = UNWIND_ARM64_MODE_FRAME | UNWIND_ARM64_FRAME_X19_X20_PAIR;
        assert_eq!(cu.encoding, expected);
    }

    #[test]
    fn test_insert_prologue_epilogue() {
        static RETURN_USES: [PReg; 1] = [X0];

        // Create a simple function and insert prologue/epilogue.
        let func_insts = vec![
            MachInst::new(AArch64Opcode::Nop, vec![]),
            MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_uses(&RETURN_USES),
        ];
        let mut func = make_func("insert_test", func_insts);
        let original_ret_id = func.blocks[0].insts[1];
        let layout = compute_frame_layout(&func, 0, false);

        insert_prologue_epilogue(&mut func, &layout).unwrap();

        // Entry block should start with prologue instructions.
        let entry_insts = &func.blocks[0].insts;
        assert!(
            entry_insts.len() >= 3,
            "Expected at least prologue + NOP + epilogue"
        );

        // First instruction should be STP pre-index (prologue start).
        assert_eq!(func.inst(entry_insts[0]).opcode, AArch64Opcode::StpPreIndex);

        // The original authenticated RET remains last; frame insertion must
        // not replace it with a fresh bare RET and lose its ABI sink metadata.
        let last_id = *entry_insts.last().unwrap();
        assert_eq!(last_id, original_ret_id);
        assert_eq!(func.inst(last_id).opcode, AArch64Opcode::Ret);
        assert_eq!(func.inst(last_id).implicit_uses, RETURN_USES);
    }

    #[test]
    fn test_sp_adjustment() {
        let mut func = make_func("sp_adj", vec![MachInst::new(AArch64Opcode::Ret, vec![])]);
        func.alloc_stack_slot(StackSlot::new(32, 8));

        let layout = compute_frame_layout(&func, 0, false);

        // sp_adjustment = total - callee_saved_area
        assert_eq!(
            layout.sp_adjustment(),
            layout.total_frame_size - layout.callee_saved_area_size
        );
        assert!(layout.sp_adjustment() >= 32); // At least covers the 32-byte slot.
    }

    #[test]
    fn test_callee_saved_pair_offsets() {
        // Verify callee-saved pair FP offsets are correct and non-overlapping.
        let func = make_func_with_callee_saved_gprs(&[X19, X20, X23, X24]);
        let layout = compute_frame_layout(&func, 0, false);

        // Pair 0: FP/LR at offset 0
        assert_eq!(layout.callee_saved_pairs[0].fp_offset, 0);
        assert_eq!(layout.callee_saved_pairs[0].reg1, X29);

        // Subsequent pairs have decreasing (more negative) offsets.
        for i in 1..layout.callee_saved_pairs.len() {
            assert!(
                layout.callee_saved_pairs[i].fp_offset < layout.callee_saved_pairs[i - 1].fp_offset
            );
        }
    }

    #[test]
    fn test_scan_callee_saved_gprs() {
        let func = make_func_with_callee_saved_gprs(&[X19, X22, X28]);
        let scan = scan_function(&func);

        assert!(scan.gpr_used & (1 << 0) != 0); // X19
        assert!(scan.gpr_used & (1 << 1) == 0); // X20 not used
        assert!(scan.gpr_used & (1 << 3) != 0); // X22
        assert!(scan.gpr_used & (1 << 9) != 0); // X28
    }

    #[test]
    fn test_scan_callee_saved_gpr_aliases() {
        let func = make_func_with_callee_saved_gprs(&[W19, W22, W28]);
        let scan = scan_function(&func);

        assert!(scan.gpr_used & (1 << 0) != 0); // W19 aliases X19
        assert!(scan.gpr_used & (1 << 3) != 0); // W22 aliases X22
        assert!(scan.gpr_used & (1 << 9) != 0); // W28 aliases X28
    }

    #[test]
    fn test_scan_callee_saved_fprs() {
        let func = make_func_with_callee_saved_fprs(&[V8, V11, V15]);
        let scan = scan_function(&func);

        assert!(scan.fpr_used & (1 << 0) != 0); // V8
        assert!(scan.fpr_used & (1 << 3) != 0); // V11
        assert!(scan.fpr_used & (1 << 7) != 0); // V15
        assert!(scan.fpr_used & (1 << 1) == 0); // V9 not used
    }

    #[test]
    fn test_scan_callee_saved_fpr_aliases() {
        let func = make_func_with_callee_saved_fprs(&[D8, S11, D15]);
        let scan = scan_function(&func);

        assert!(scan.fpr_used & (1 << 0) != 0); // D8 aliases V8
        assert!(scan.fpr_used & (1 << 3) != 0); // S11 aliases V11
        assert!(scan.fpr_used & (1 << 7) != 0); // D15 aliases V15
        assert!(scan.fpr_used & (1 << 1) == 0); // V9 not used
    }

    // RANK 2 soundness fix: H8-H15 (Fpr16) must map to the same callee-saved
    // bit index as V8-V15 / D8-D15 / S8-S15 so an F16 value live across a call
    // triggers the existing D8-D15 STP/LDP save instead of being clobbered.
    #[test]
    fn test_callee_saved_fpr_index_h_range() {
        // H8 (enc 173) -> bit 0; H15 (enc 180) -> bit 7. Same indices as the
        // V/D/S arms, so the existing D8-D15 prologue save covers the H alias.
        assert_eq!(callee_saved_fpr_index(H8), Some(0));
        assert_eq!(callee_saved_fpr_index(H15), Some(7));
        // H8/H15 share the same physical V register (root) as D8/D15.
        assert_eq!(callee_saved_fpr_index(H8), callee_saved_fpr_index(D8));
        assert_eq!(callee_saved_fpr_index(H15), callee_saved_fpr_index(D15));
    }

    #[test]
    fn test_scan_callee_saved_fpr_h_aliases() {
        // An F16 value placed in H8/H15 must set the fpr_used bit (it didn't
        // before the fix — it silently fell through to None).
        let func = make_func_with_callee_saved_fprs(&[H8, H15]);
        let scan = scan_function(&func);

        assert!(scan.fpr_used & (1 << 0) != 0); // H8 aliases V8
        assert!(scan.fpr_used & (1 << 7) != 0); // H15 aliases V15
        assert!(scan.fpr_used & (1 << 1) == 0); // V9 not used
    }

    #[test]
    fn test_layout_callee_saved_fpr_h_aliases_emits_save() {
        // End-to-end frame layout: using H8/H15 must produce FPR callee-saved
        // pairs (the existing D8-D15 STP/LDP path), so the value is preserved.
        let func = make_func_with_callee_saved_fprs(&[H8, H15]);
        let layout = compute_frame_layout(&func, 0, false);

        let fpr_pairs: Vec<_> = layout
            .callee_saved_pairs
            .iter()
            .filter(|p| p.is_fpr)
            .collect();
        // H8 -> bit 0 (pair V8/V9), H15 -> bit 7 (pair V14/V15): two FPR pairs.
        assert_eq!(fpr_pairs.len(), 2, "expected two FPR save pairs for H8+H15");

        // The prologue must store the lower-64 (D-register) aliases that cover
        // the H8/H15 low-16-bit values. With the Apple-canonical layout the
        // bottom (highest-numbered) pair V14/V15 is saved by the pre-index store
        // that allocates the CSA, and V8/V9 is saved just below FP via a signed
        // offset. Each pair stores its registers reversed (lower number at the
        // higher, closer-to-FP, address) — so D9,D8 and D15,D14.
        let prologue = emit_prologue(&layout);
        let preidx_fpr: Vec<_> = prologue
            .iter()
            .filter(|inst| inst.opcode == AArch64Opcode::StpPreIndex)
            .map(|inst| (inst.operands[0].clone(), inst.operands[1].clone()))
            .filter(|(a, _)| matches!(a, MachOperand::PReg(p) if *p == D8 || *p == D9 || *p == D10 || *p == D11 || *p == D12 || *p == D13 || *p == D14 || *p == D15))
            .collect();
        let stp_fpr: Vec<_> = prologue
            .iter()
            .filter(|inst| inst.opcode == AArch64Opcode::StpRI)
            .map(|inst| (inst.operands[0].clone(), inst.operands[1].clone()))
            .filter(|(a, _)| matches!(a, MachOperand::PReg(p) if *p == D8 || *p == D9 || *p == D10 || *p == D11 || *p == D12 || *p == D13 || *p == D14 || *p == D15))
            .collect();
        assert_eq!(
            preidx_fpr,
            vec![(MachOperand::PReg(D15), MachOperand::PReg(D14))],
            "H15 must be saved via the bottom-of-CSA D15/D14 pre-index STP"
        );
        assert_eq!(
            stp_fpr,
            vec![(MachOperand::PReg(D9), MachOperand::PReg(D8))],
            "H8 must be saved via the D9/D8 STP pair just below FP"
        );
    }

    #[test]
    fn test_scan_callee_saved_implicit_aliases() {
        static DEFS: [PReg; 2] = [W28, D15];
        static USES: [PReg; 2] = [W19, S8];

        let func = make_func(
            "implicit_aliases",
            vec![
                MachInst::new(AArch64Opcode::Nop, vec![])
                    .with_implicit_defs(&DEFS)
                    .with_implicit_uses(&USES),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let scan = scan_function(&func);

        assert!(scan.gpr_used & (1 << 0) != 0); // W19 aliases X19
        assert!(scan.gpr_used & (1 << 9) != 0); // W28 aliases X28
        assert!(scan.fpr_used & (1 << 0) != 0); // S8 aliases V8
        assert!(scan.fpr_used & (1 << 7) != 0); // D15 aliases V15
    }

    #[test]
    fn test_layout_with_callee_saved_aliases() {
        let func = make_func(
            "layout_aliases",
            vec![
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![MachOperand::PReg(W19), MachOperand::PReg(W19)],
                ),
                MachInst::new(
                    AArch64Opcode::FmovFprFpr,
                    vec![MachOperand::PReg(D8), MachOperand::PReg(D8)],
                ),
                MachInst::new(
                    AArch64Opcode::FmovFprFpr,
                    vec![MachOperand::PReg(S11), MachOperand::PReg(S11)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let layout = compute_frame_layout(&func, 0, false);

        // FP/LR + X19/X20 + V8/V9 + V10/V11.
        assert_eq!(layout.callee_saved_pairs.len(), 4);
        assert_eq!(layout.callee_saved_area_size, 64);
        assert_eq!(layout.callee_saved_pairs[1].reg1, X19);
        assert_eq!(layout.callee_saved_pairs[1].reg2, X20);
        assert!(layout.callee_saved_pairs[2].is_fpr);
        assert_eq!(layout.callee_saved_pairs[2].reg1, V8);
        assert_eq!(layout.callee_saved_pairs[2].reg2, V9);
        assert!(layout.callee_saved_pairs[3].is_fpr);
        assert_eq!(layout.callee_saved_pairs[3].reg1, V10);
        assert_eq!(layout.callee_saved_pairs[3].reg2, V11);
    }

    #[test]
    fn test_emit_callee_saved_fpr_pairs_uses_lower64_storage_aliases() {
        let func = make_func_with_callee_saved_fprs(&[V8, V9, V10, V11]);
        let layout = compute_frame_layout(&func, 0, false);

        // Canonical layout (pairs = [FP/LR, V8/V9, V10/V11], csa = 48):
        //   STP D11, D10, [SP, #-48]!   ; V10/V11 at the bottom (pre-index)
        //   STP D9,  D8,  [SP, #16]     ; V8/V9 just below FP (reversed regs)
        //   STP X29, X30, [SP, #32]     ; FP/LR at the top
        //   ADD X29, SP, #32
        // Each pair is stored with registers reversed so the lower-numbered
        // register lands at the HIGHER address (closer to FP), matching what
        // libunwind's FRAME-mode restore expects. Saves use the lower-64
        // D-register aliases of V8-V15.
        let prologue = emit_prologue(&layout);

        // The pre-index store saves the bottom (highest-numbered) FPR pair.
        let preidx: Vec<_> = prologue
            .iter()
            .filter(|inst| inst.opcode == AArch64Opcode::StpPreIndex)
            .map(|inst| (inst.operands[0].clone(), inst.operands[1].clone()))
            .collect();
        assert_eq!(
            preidx,
            vec![(MachOperand::PReg(D11), MachOperand::PReg(D10))]
        );

        // The remaining FPR pair is stored with a signed offset (reversed regs).
        let stp_fpr: Vec<_> = prologue
            .iter()
            .filter(|inst| inst.opcode == AArch64Opcode::StpRI)
            .map(|inst| (inst.operands[0].clone(), inst.operands[1].clone()))
            .filter(|(a, _)| {
                matches!(a, MachOperand::PReg(p)
                    if [D8, D9, D10, D11, D12, D13, D14, D15].contains(p))
            })
            .collect();
        assert_eq!(
            stp_fpr,
            vec![(MachOperand::PReg(D9), MachOperand::PReg(D8))]
        );

        // Epilogue mirrors the prologue: V8/V9 reloaded via offset, V10/V11 via
        // the post-index that deallocates the CSA. (FP/LR reload is excluded by
        // filtering for the D-register aliases.)
        let epilogue = emit_epilogue(&layout);
        let ldp_off: Vec<_> = epilogue
            .iter()
            .filter(|inst| inst.opcode == AArch64Opcode::LdpRI)
            .map(|inst| (inst.operands[0].clone(), inst.operands[1].clone()))
            .filter(|(a, _)| {
                matches!(a, MachOperand::PReg(p)
                    if [D8, D9, D10, D11, D12, D13, D14, D15].contains(p))
            })
            .collect();
        assert_eq!(
            ldp_off,
            vec![(MachOperand::PReg(D9), MachOperand::PReg(D8))]
        );
        let ldp_postidx: Vec<_> = epilogue
            .iter()
            .filter(|inst| inst.opcode == AArch64Opcode::LdpPostIndex)
            .map(|inst| (inst.operands[0].clone(), inst.operands[1].clone()))
            .filter(|(a, _)| {
                matches!(a, MachOperand::PReg(p)
                    if [D8, D9, D10, D11, D12, D13, D14, D15].contains(p))
            })
            .collect();
        assert_eq!(
            ldp_postidx,
            vec![(MachOperand::PReg(D11), MachOperand::PReg(D10))]
        );
    }

    // --- has_dynamic_alloc field tests ---

    #[test]
    fn test_layout_default_no_dynamic_alloc() {
        let func = make_func("no_alloca", vec![MachInst::new(AArch64Opcode::Ret, vec![])]);
        let layout = compute_frame_layout(&func, 0, false);
        assert!(!layout.has_dynamic_alloc);
    }

    #[test]
    fn test_layout_dynamic_alloc_flag() {
        let func = make_func(
            "with_alloca",
            vec![MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        let layout = compute_frame_layout_dynamic(&func, 0, false);
        assert!(layout.has_dynamic_alloc);
    }

    #[test]
    fn test_runtime_stack_slot_marks_layout_dynamic_and_keeps_fixed_area() {
        let mut func = make_func(
            "with_runtime_slot",
            vec![MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        func.alloc_stack_slot(StackSlot::new(8, 8));
        func.alloc_stack_slot(StackSlot::new_dynamic(StackSlotSizeSource::Value(3), 16));

        let layout = compute_frame_layout(&func, 0, false);

        assert!(function_has_runtime_stack_slots(&func));
        assert!(layout.has_dynamic_alloc);
        assert_eq!(
            layout.spill_area_size, 8,
            "runtime-sized slots are not folded into the fixed frame area"
        );
    }

    #[test]
    fn test_stack_alloc_pseudo_marks_layout_dynamic() {
        let func = make_func(
            "stack_alloc_pseudo",
            vec![
                MachInst::new(
                    AArch64Opcode::StackAlloc,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::PReg(X1),
                        MachOperand::Imm(8),
                        MachOperand::Imm(8),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let layout = compute_frame_layout(&func, 0, true);

        assert!(layout.has_dynamic_alloc);
        assert!(!layout.uses_red_zone);
    }

    #[test]
    fn test_dynamic_epilogue_restores_sp_from_fp() {
        let func = make_func(
            "dynamic_epilogue",
            vec![MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        let layout = compute_frame_layout_dynamic(&func, 0, false);

        let epilogue = emit_epilogue(&layout);

        assert_eq!(epilogue[0].opcode, AArch64Opcode::AddRI);
        assert_eq!(
            epilogue[0].operands[0],
            MachOperand::Special(SpecialReg::SP)
        );
        assert_eq!(epilogue[0].operands[1], MachOperand::PReg(X29));
        assert_eq!(epilogue[0].operands[2], MachOperand::Imm(0));
    }

    #[test]
    fn unreachable_runtime_allocation_expands_outside_the_layout() {
        let mut func = make_func("dead_alloc", vec![make_ret()]);
        let dead = BlockId(func.blocks.len() as u32);
        func.blocks.push(trust_cg_ir::function::MachBlock::new());
        for inst in [frame_insert_alloc(3, 8, 16), make_ret()] {
            let id = func.push_inst(inst);
            func.append_inst(dead, id);
        }
        let layout = compute_frame_layout_dynamic(&func, 0, false);
        insert_prologue_epilogue(&mut func, &layout).unwrap();
        assert_eq!(func.block_order, vec![func.entry]);
        assert_eq!(
            func.blocks.len(),
            5,
            "test, step and exit blocks stay unlaid"
        );
        assert!(
            func.blocks
                .iter()
                .flat_map(|block| &block.insts)
                .all(|id| func.inst(*id).opcode != AArch64Opcode::StackAlloc)
        );
        crate::pipeline::validate_aarch64_mach_function(&func).unwrap();
    }

    /// A branch that stays in the block a runtime allocation splits keeps its
    /// recorded edge (the L05-P8 length witness branches to a trap block
    /// mid-block); the tail keeps the edges its own terminator names.
    #[test]
    fn allocation_split_keeps_edges_named_by_the_head() {
        let mut func = make_func(
            "witness_then_alloc",
            vec![
                MachInst::new(
                    AArch64Opcode::CmpRI,
                    vec![MachOperand::PReg(X1), MachOperand::Imm(0)],
                ),
                MachInst::new(
                    AArch64Opcode::BCond,
                    vec![MachOperand::Imm(0b0000), MachOperand::Block(BlockId(1))],
                ),
                frame_insert_alloc(3, 8, 16),
                MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(2))]),
            ],
        );
        let trap = BlockId(1);
        let exit = BlockId(2);
        for (block, inst) in [
            (
                trap,
                MachInst::new(AArch64Opcode::Brk, vec![MachOperand::Imm(1)]),
            ),
            (exit, make_ret()),
        ] {
            assert_eq!(func.create_block(), block);
            let id = func.push_inst(inst);
            func.append_inst(block, id);
        }
        func.add_edge(BlockId(0), exit);
        func.add_edge(BlockId(0), trap);
        let layout = compute_frame_layout_dynamic(&func, 0, false);
        insert_prologue_epilogue(&mut func, &layout).unwrap();

        let holder = |opcode: AArch64Opcode| {
            func.block_order
                .iter()
                .copied()
                .find(|block| {
                    func.blocks[block.0 as usize]
                        .insts
                        .iter()
                        .any(|id| func.inst(*id).opcode == opcode)
                })
                .expect("instruction laid out")
        };
        let head = holder(AArch64Opcode::BCond);
        let tail = func
            .block_order
            .iter()
            .copied()
            .find(|block| {
                func.blocks[block.0 as usize].insts.iter().any(|id| {
                    func.inst(*id).opcode == AArch64Opcode::B
                        && func.inst(*id).operands == vec![MachOperand::Block(exit)]
                })
            })
            .expect("tail laid out");
        assert_ne!(head, tail, "the allocation splits the block");
        assert!(func.blocks[head.0 as usize].succs.contains(&trap));
        assert!(!func.blocks[head.0 as usize].succs.contains(&exit));
        assert_eq!(func.blocks[tail.0 as usize].succs, vec![exit]);
        assert!(func.blocks[trap.0 as usize].preds.contains(&head));
        assert!(!func.blocks[trap.0 as usize].preds.contains(&tail));
        assert_eq!(func.blocks[exit.0 as usize].preds, vec![tail]);
        crate::pipeline::validate_aarch64_mach_function(&func).unwrap();
    }

    /// A jump table the head's `ADR` names keeps its entries on both halves:
    /// the table's `BR` may follow the split point.
    #[test]
    fn allocation_split_keeps_head_named_jump_table_entries_on_both_halves() {
        let mut func = make_func(
            "table_then_alloc",
            vec![
                MachInst::new(
                    AArch64Opcode::Adr,
                    vec![MachOperand::PReg(X16), MachOperand::JumpTableIndex(0)],
                ),
                frame_insert_alloc(3, 8, 16),
                MachInst::new(AArch64Opcode::Br, vec![MachOperand::PReg(X16)]),
            ],
        );
        let arms = [BlockId(1), BlockId(2)];
        for arm in arms {
            assert_eq!(func.create_block(), arm);
            let id = func.push_inst(make_ret());
            func.append_inst(arm, id);
            func.add_edge(BlockId(0), arm);
        }
        func.jump_tables.push(trust_cg_ir::function::JumpTableData {
            min_val: 0,
            targets: arms.to_vec(),
        });
        let layout = compute_frame_layout_dynamic(&func, 0, false);
        insert_prologue_epilogue(&mut func, &layout).unwrap();
        let holder = |opcode: AArch64Opcode| {
            func.block_order
                .iter()
                .copied()
                .find(|block| {
                    func.blocks[block.0 as usize]
                        .insts
                        .iter()
                        .any(|id| func.inst(*id).opcode == opcode)
                })
                .expect("instruction laid out")
        };
        let (head, tail) = (holder(AArch64Opcode::Adr), holder(AArch64Opcode::Br));
        assert_ne!(head, tail, "the allocation splits the block");
        for arm in arms {
            assert!(func.blocks[head.0 as usize].succs.contains(&arm));
            assert!(func.blocks[tail.0 as usize].succs.contains(&arm));
            assert!(func.blocks[arm.0 as usize].preds.contains(&head));
            assert!(func.blocks[arm.0 as usize].preds.contains(&tail));
        }
    }

    #[test]
    fn test_insert_prologue_expands_stack_alloc_pseudo() {
        let mut func = make_func(
            "dynamic_stack_alloc",
            vec![
                MachInst::new(
                    AArch64Opcode::StackAlloc,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::PReg(X1),
                        MachOperand::Imm(8),
                        MachOperand::Imm(8),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let layout = compute_frame_layout(&func, 0, false);

        insert_prologue_epilogue(&mut func, &layout).unwrap();

        let entry_insts = laid_out_insts(&func);
        assert!(
            entry_insts
                .iter()
                .all(|inst| inst.opcode != AArch64Opcode::StackAlloc),
            "StackAlloc pseudo must be expanded before encoding"
        );
        assert!(
            entry_insts.windows(3).any(|window| {
                window[0].opcode == AArch64Opcode::AddRI
                    && window[0].operands
                        == vec![
                            MachOperand::PReg(X16),
                            MachOperand::Special(SpecialReg::SP),
                            MachOperand::Imm(0),
                        ]
                    && window[1].opcode == AArch64Opcode::SubRR
                    && window[1].operands
                        == vec![
                            MachOperand::PReg(X16),
                            MachOperand::PReg(X16),
                            MachOperand::PReg(X0),
                        ]
                    && window[2].opcode == AArch64Opcode::AddRI
                    && window[2].operands
                        == vec![
                            MachOperand::PReg(X0),
                            MachOperand::Special(SpecialReg::SP),
                            MachOperand::Imm(0),
                        ]
            }),
            "expanded dynamic allocation must compute the target SP through a real GPR"
        );
        assert!(
            entry_insts.windows(2).any(|window| {
                window[0].opcode == AArch64Opcode::AddRI
                    && window[0].operands
                        == vec![
                            MachOperand::Special(SpecialReg::SP),
                            MachOperand::PReg(X16),
                            MachOperand::Imm(0),
                        ]
                    && is_stack_probe(window[1])
            }),
            "the final SP of a runtime allocation must be probed"
        );
        assert!(
            entry_insts.iter().all(|inst| {
                !(matches!(inst.opcode, AArch64Opcode::AddRR | AArch64Opcode::SubRR)
                    && inst
                        .operands
                        .contains(&MachOperand::Special(SpecialReg::SP)))
            }),
            "ADD/SUB register forms must not mention SP; register 31 encodes XZR there"
        );
        assert!(
            entry_insts.iter().any(|inst| {
                inst.opcode == AArch64Opcode::AddRI
                    && inst.operands[0] == MachOperand::PReg(X0)
                    && inst.operands[1] == MachOperand::Special(SpecialReg::SP)
            }),
            "expanded dynamic allocation must return the new SP in the destination register"
        );
    }

    #[test]
    fn frame_insert_negative_count_is_transactional_error() {
        assert_frame_insert_operand_error(-1, 1, 16);
    }

    #[test]
    fn frame_insert_invalid_unit_is_transactional_error() {
        for unit in [0, -1, i64::from(u32::MAX) + 1] {
            assert_frame_insert_operand_error(1, unit, 16);
        }
    }

    #[test]
    fn frame_insert_invalid_alignment_is_transactional_error() {
        for align in [0, -1, 3, 8192] {
            assert_frame_insert_operand_error(1, 1, align);
        }
    }

    fn frame_insert_alloc(count: i64, unit: i64, align: i64) -> MachInst {
        MachInst::new(
            AArch64Opcode::StackAlloc,
            vec![
                MachOperand::PReg(X0),
                MachOperand::Imm(count),
                MachOperand::Imm(unit),
                MachOperand::Imm(align),
            ],
        )
    }

    fn assert_frame_insert_operand_error(count: i64, unit: i64, align: i64) {
        // A valid allocation before the invalid one detects partial expansion,
        // not merely failure before the first append.
        let mut func = make_func(
            "frame_insert_invalid",
            vec![
                frame_insert_alloc(1, 1, 16),
                frame_insert_alloc(count, unit, align),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let layout = compute_frame_layout_dynamic(&func, 0, false);
        let before = format!("{func:?}");
        assert!(matches!(
            insert_prologue_epilogue(&mut func, &layout),
            Err(crate::lower::LowerError::FrameLowering(_))
        ));
        assert_eq!(format!("{func:?}"), before);
    }

    #[test]
    fn frame_insert_outgoing_area_4096_lowers() {
        assert_frame_insert_large_outgoing_area(4096);
    }

    #[test]
    fn frame_insert_outgoing_area_8192_lowers() {
        assert_frame_insert_large_outgoing_area(8192);
    }

    #[test]
    fn frame_insert_large_additions_encode_exact_unsigned_arithmetic() {
        // Replay the actual encoded ADD words, independently of the builder's
        // opcode/operand representation. No native execution is needed.
        for amount in [
            1,
            4095,
            4096,
            4097,
            8192,
            0x00ff_f000,
            0x0100_0001,
            u32::MAX,
        ] {
            for source in [
                MachOperand::Special(SpecialReg::SP),
                MachOperand::PReg(X1),
                MachOperand::PReg(X0),
            ] {
                let mut insts = Vec::new();
                emit_add_reg_imm(X0, source.clone(), amount, &mut insts);
                let initial = 0x1234_5678_0000_0000u64;
                let mut regs = [initial; 32];
                for (index, inst) in insts.iter().enumerate() {
                    let word = crate::aarch64::encode::encode_instruction(inst).unwrap();
                    assert_eq!(
                        word & 0xff80_0000,
                        0x9100_0000,
                        "64-bit, non-flag-setting ADD immediate"
                    );
                    let rd = (word & 31) as usize;
                    let rn = ((word >> 5) & 31) as usize;
                    assert_eq!(rd, 0, "only the destination may be clobbered");
                    if index == 0 {
                        assert_eq!(
                            rn,
                            match source {
                                MachOperand::Special(SpecialReg::SP) => 31,
                                MachOperand::PReg(reg) => usize::from(hw_encoding(reg)),
                                _ => unreachable!(),
                            }
                        );
                    } else {
                        assert_eq!(rn, rd, "continuation must read the partial sum");
                    }
                    let imm = u64::from((word >> 10) & 4095)
                        << (if word & (1 << 22) != 0 { 12 } else { 0 });
                    regs[rd] = regs[rn].wrapping_add(imm);
                }
                assert_eq!(regs[0], initial + u64::from(amount));
                assert_eq!(regs[1], initial);
                assert_eq!(regs[31], initial, "forming an address must not change SP");
            }
        }
    }

    #[test]
    fn frame_insert_id_domain_checks_final_valid_id_and_overflow() {
        for arena in ["instruction", "block"] {
            assert_eq!(
                checked_frame_insertion_id(u32::MAX as usize, 0, arena).unwrap(),
                u32::MAX
            );
            assert!(checked_frame_insertion_id(u32::MAX as usize, 1, arena).is_err());
            assert!(checked_frame_insertion_id(usize::MAX, 1, arena).is_err());
        }
        let func = make_func("checked_frame_ids", vec![make_ret()]);
        let before = format!("{func:?}");
        let mut plan = FrameInsertionPlan::new(&func).unwrap();
        // Exercise the production append check with a synthetic logical base;
        // no multi-billion-instruction allocation is needed and no fake plan
        // is committed to the real function.
        plan.original_inst_count = u32::MAX as usize;
        assert_eq!(plan.push_inst(make_nop()).unwrap(), InstId(u32::MAX));
        assert!(plan.push_inst(make_nop()).is_err());
        assert_eq!(plan.added_insts.len(), 1);
        assert_eq!(format!("{func:?}"), before);
    }

    #[test]
    fn frame_insert_staged_append_refusal_preserves_input() {
        let func = make_func(
            "frame_id_refusal",
            vec![frame_insert_alloc(1, 1, 16), make_ret()],
        );
        let before = format!("{func:?}");
        let mut plan = FrameInsertionPlan::new(&func).unwrap();
        plan.original_inst_count = u32::MAX as usize;
        assert!(expand_dynamic_stack_allocs(&func, &mut plan, 0).is_err());
        assert_eq!(format!("{func:?}"), before);
        assert_eq!(plan.added_insts.len(), 1);
    }

    #[test]
    fn frame_insert_rejects_malformed_optional_operands_and_registers() {
        let mut malformed = Vec::new();
        for (index, value) in [
            (0, MachOperand::PReg(D8)),
            (0, MachOperand::PReg(W0)),
            (1, MachOperand::PReg(D8)),
            (2, MachOperand::PReg(X1)),
            (3, MachOperand::PReg(X1)),
        ] {
            let mut inst = frame_insert_alloc(1, 1, 16);
            inst.operands[index] = value;
            malformed.push(inst);
        }
        malformed.push(MachInst::new(AArch64Opcode::StackAlloc, vec![]));
        for inst in malformed {
            let mut func = make_func(
                "malformed_frame_alloc",
                vec![frame_insert_alloc(1, 1, 16), inst, make_ret()],
            );
            let layout = compute_frame_layout_dynamic(&func, 0, false);
            let before = format!("{func:?}");
            assert!(insert_prologue_epilogue(&mut func, &layout).is_err());
            assert_eq!(format!("{func:?}"), before);
        }
    }

    #[test]
    fn frame_insert_plan_commits_exact_counts_and_preserves_return_metadata() {
        for protected in [false, true] {
            let mut func = make_func(
                "frame_insert_metadata",
                vec![
                    frame_insert_alloc(3, 8, 16),
                    MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_uses(&[X0]),
                ],
            );
            func.signature.returns = vec![trust_cg_ir::function::Type::I64];
            let ret = func.blocks[0].insts[1];
            func.set_inst_lowering_provenance(
                ret,
                trust_cg_ir::provenance::LoweringProvenance::Synthetic {
                    reason: trust_cg_ir::provenance::SyntheticReason::PrologueEpilogue,
                },
            );
            if protected {
                func.stack_protector = StackProtectorMode::StackGuard;
                ensure_stack_protector_slot(&mut func).unwrap();
            }
            let layout = compute_frame_layout_dynamic(&func, 4096, false);
            let before = format!("{func:?}");
            let old_ret = format!("{:?}", func.inst(ret));
            let old_provenance = func.lowering_provenance.clone();
            let old_inst_count = func.insts.len();
            let old_block_count = func.blocks.len();
            let plan =
                plan_frame_insertion(&func, &layout, ShrinkWrapEligibility::Disabled).unwrap();
            assert_eq!(
                format!("{func:?}"),
                before,
                "planning must not mutate the owner"
            );
            let additions = plan.added_insts.len();
            // One runtime allocation adds its probe-loop test, step and exit
            // blocks; the protector adds its failure block.
            assert_eq!(
                plan.blocks.len(),
                old_block_count + 3 + usize::from(protected)
            );
            plan.commit(&mut func).unwrap();
            assert_eq!(func.insts.len(), old_inst_count + additions);
            assert_eq!(format!("{:?}", func.inst(ret)), old_ret);
            assert_eq!(func.lowering_provenance, old_provenance);
            assert_eq!(
                func.blocks
                    .iter()
                    .flat_map(|block| &block.insts)
                    .filter(|&&id| id == ret)
                    .count(),
                1
            );
            assert!(
                func.blocks
                    .iter()
                    .flat_map(|block| &block.insts)
                    .all(|id| (id.0 as usize) < func.insts.len())
            );
        }
    }

    fn assert_frame_insert_large_outgoing_area(outgoing: u32) {
        let mut func = make_func(
            "frame_insert_large_outgoing",
            vec![
                frame_insert_alloc(3, 8, 16),
                MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![
                        MachOperand::PReg(X1),
                        MachOperand::Special(SpecialReg::SP),
                        MachOperand::Imm(i64::from(outgoing - 8)),
                    ],
                ),
                MachInst::new(
                    AArch64Opcode::Bl,
                    vec![MachOperand::Symbol("callee".into())],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        assert_eq!(compute_max_outgoing_arg_size(&func), outgoing);
        let layout = compute_frame_layout_dynamic(&func, outgoing, false);
        let return_id = func.blocks[0].insts[3];
        let original_return = format!("{:?}", func.inst(return_id));
        insert_prologue_epilogue(&mut func, &layout).unwrap();
        // The probe loop splits the block: the return continues after it.
        let return_block = func
            .blocks
            .iter()
            .position(|block| block.insts.contains(&return_id))
            .unwrap();
        assert_ne!(return_block, 0);
        assert_eq!(format!("{:?}", func.inst(return_id)), original_return);
        assert!(
            func.blocks
                .iter()
                .flat_map(|block| &block.insts)
                .all(|id| func.inst(*id).opcode != AArch64Opcode::StackAlloc)
        );
        let dynamic = expand_dynamic_stack_alloc_inst(&frame_insert_alloc(3, 8, 16), outgoing)
            .unwrap()
            .unwrap();
        assert!(
            dynamic
                .setup
                .iter()
                .chain(&dynamic.test)
                .chain(&dynamic.step)
                .chain(&dynamic.exit)
                .all(|inst| crate::aarch64::encode::encode_instruction(inst).is_ok())
        );
        let address = dynamic
            .exit
            .iter()
            .rev()
            .take_while(|inst| {
                matches!(
                    inst.opcode,
                    AArch64Opcode::AddRI | AArch64Opcode::AddRIShift12
                )
            })
            .collect::<Vec<_>>();
        // The last sequence constructs dst = new_SP + outgoing, after SP was
        // moved. Read the encoded immediates, including their actual shift bit.
        let mut total = 0u64;
        for inst in address {
            if inst.operands.first() != Some(&MachOperand::PReg(X0)) {
                break;
            }
            let word = crate::aarch64::encode::encode_instruction(inst).unwrap();
            total += u64::from((word >> 10) & 4095) << (if word & (1 << 22) != 0 { 12 } else { 0 });
        }
        assert_eq!(total, u64::from(outgoing));
    }

    #[test]
    fn test_stack_alloc_constant_count_size_overflow_returns_err() {
        // FINDING #10a: a well-typed but enormous constant-count alloca
        // (count * unit_size overflows u64) previously aborted the compiler
        // via `.expect()`. It must now return a typed FrameLowering error.
        // count = i64::MAX is non-negative and
        // unit_size = 8 is in (0, u32::MAX]; their u64 product overflows.
        let mut func = make_func(
            "overflow_stack_alloc",
            vec![
                MachInst::new(
                    AArch64Opcode::StackAlloc,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::Imm(i64::MAX),
                        MachOperand::Imm(8),
                        MachOperand::Imm(8),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let layout = compute_frame_layout_dynamic(&func, 0, false);
        let res = insert_prologue_epilogue(&mut func, &layout);
        assert!(
            matches!(res, Err(crate::lower::LowerError::FrameLowering(_))),
            "expected FrameLowering error, got {res:?}"
        );
    }

    #[test]
    fn test_stack_alloc_constant_count_in_range_size_still_lowers() {
        // FINDING #10a boundary: a constant-count alloca whose byte size fits
        // u64 must still lower successfully (no behavior change for valid IR).
        let mut func = make_func(
            "in_range_stack_alloc",
            vec![
                MachInst::new(
                    AArch64Opcode::StackAlloc,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::Imm(16),
                        MachOperand::Imm(8),
                        MachOperand::Imm(8),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let layout = compute_frame_layout_dynamic(&func, 0, false);
        insert_prologue_epilogue(&mut func, &layout)
            .expect("in-range constant-count alloca must lower");
    }

    #[test]
    fn test_stack_alloc_clamps_zero_byte_request_above_fixed_frame_bottom() {
        let mut func = make_func(
            "dynamic_stack_alloc_minimum",
            vec![
                MachInst::new(
                    AArch64Opcode::StackAlloc,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::PReg(X1),
                        MachOperand::Imm(8),
                        MachOperand::Imm(8),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(8, 8));
        let layout = compute_frame_layout(&func, 0, false);

        insert_prologue_epilogue(&mut func, &layout).unwrap();

        let entry_insts: Vec<_> = func.blocks[func.entry.0 as usize]
            .insts
            .iter()
            .map(|id| &func.insts[id.0 as usize])
            .collect();
        let clamp_pos = entry_insts
            .windows(3)
            .position(|window| {
                window[0].opcode == AArch64Opcode::Movz
                    && window[0].operands == vec![MachOperand::PReg(X16), MachOperand::Imm(16)]
                    && window[1].opcode == AArch64Opcode::CmpRR
                    && window[1].operands == vec![MachOperand::PReg(X0), MachOperand::PReg(X16)]
                    && window[2].opcode == AArch64Opcode::Csel
                    && window[2].operands
                        == vec![
                            MachOperand::PReg(X0),
                            MachOperand::PReg(X16),
                            MachOperand::PReg(X0),
                            MachOperand::Imm(3),
                        ]
            })
            .expect("StackAlloc must clamp runtime byte count to at least one stack quantum");
        let subtract_pos = entry_insts
            .iter()
            .position(|inst| {
                inst.opcode == AArch64Opcode::SubRR
                    && inst.operands
                        == vec![
                            MachOperand::PReg(X16),
                            MachOperand::PReg(X16),
                            MachOperand::PReg(X0),
                        ]
            })
            .expect("expanded StackAlloc must subtract from SP");

        assert!(
            clamp_pos < subtract_pos,
            "minimum-size clamp must run before SP is moved for the dynamic object"
        );
    }

    #[test]
    fn test_stack_alloc_non_power_unit_can_reuse_destination_when_ip_regs_are_operands() {
        let mut func = make_func(
            "dynamic_stack_alloc_ip_cross",
            vec![
                MachInst::new(
                    AArch64Opcode::StackAlloc,
                    vec![
                        MachOperand::PReg(X17),
                        MachOperand::PReg(X16),
                        MachOperand::Imm(3),
                        MachOperand::Imm(8),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let layout = compute_frame_layout(&func, 0, false);

        insert_prologue_epilogue(&mut func, &layout).unwrap();

        let entry_insts: Vec<_> = func.blocks[func.entry.0 as usize]
            .insts
            .iter()
            .map(|id| &func.insts[id.0 as usize])
            .collect();
        assert!(
            entry_insts.iter().any(|inst| {
                inst.opcode == AArch64Opcode::Movz
                    && inst.operands == vec![MachOperand::PReg(X17), MachOperand::Imm(3)]
            }),
            "unit size can be materialized into the destination after preserving the source"
        );
        assert!(
            entry_insts.iter().any(|inst| {
                inst.opcode == AArch64Opcode::MulRR
                    && inst.operands
                        == vec![
                            MachOperand::PReg(X17),
                            MachOperand::PReg(X16),
                            MachOperand::PReg(X17),
                        ]
            }),
            "multiply must read the original source and the destination-held unit size"
        );
    }

    #[test]
    fn test_stack_alloc_with_outgoing_args_returns_pointer_above_call_area() {
        let mut func = make_func(
            "dynamic_stack_alloc_with_call_args",
            vec![
                MachInst::new(
                    AArch64Opcode::StackAlloc,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::PReg(X1),
                        MachOperand::Imm(8),
                        MachOperand::Imm(8),
                    ],
                ),
                MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![
                        MachOperand::PReg(X1),
                        MachOperand::Special(SpecialReg::SP),
                        MachOperand::Imm(24),
                    ],
                ),
                MachInst::new(
                    AArch64Opcode::Bl,
                    vec![MachOperand::Symbol("callee".into())],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let outgoing_arg_size = compute_max_outgoing_arg_size(&func);
        let layout = compute_frame_layout(&func, outgoing_arg_size, false);
        assert_eq!(layout.outgoing_arg_area_size, 32);

        insert_prologue_epilogue(&mut func, &layout).unwrap();

        let entry_insts = laid_out_insts(&func);
        assert!(
            entry_insts.iter().any(|inst| {
                inst.opcode == AArch64Opcode::AddRI
                    && inst.operands
                        == vec![
                            MachOperand::PReg(X0),
                            MachOperand::Special(SpecialReg::SP),
                            MachOperand::Imm(32),
                        ]
            }),
            "dynamic allocation must return SP + outgoing_arg_area_size so stack args below SP do not overlap the alloca"
        );
    }

    #[test]
    fn test_insert_prologue_expands_overaligned_stack_alloc_pseudo() {
        let mut func = make_func(
            "overaligned_dynamic_stack_alloc",
            vec![
                MachInst::new(
                    AArch64Opcode::StackAlloc,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::PReg(X1),
                        MachOperand::Imm(8),
                        MachOperand::Imm(32),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let layout = compute_frame_layout(&func, 0, false);

        insert_prologue_epilogue(&mut func, &layout).unwrap();

        let entry_insts = laid_out_insts(&func);
        assert!(
            entry_insts.iter().any(|inst| {
                inst.opcode == AArch64Opcode::AddRI
                    && inst.operands
                        == vec![
                            MachOperand::PReg(X0),
                            MachOperand::PReg(X0),
                            MachOperand::Imm(31),
                        ]
            }),
            "over-aligned dynamic allocation must include alignment slack"
        );
        assert!(
            entry_insts.iter().any(|inst| {
                inst.opcode == AArch64Opcode::LsrRI
                    && inst.operands
                        == vec![
                            MachOperand::PReg(X0),
                            MachOperand::PReg(X0),
                            MachOperand::Imm(5),
                        ]
            }) && entry_insts.iter().any(|inst| {
                inst.opcode == AArch64Opcode::LslRI
                    && inst.operands
                        == vec![
                            MachOperand::PReg(X0),
                            MachOperand::PReg(X0),
                            MachOperand::Imm(5),
                        ]
            }),
            "returned pointer must be rounded up to the requested 32-byte alignment"
        );
    }

    #[test]
    fn test_runtime_stack_slot_disables_red_zone() {
        let mut func = make_func(
            "runtime_slot_leaf",
            vec![MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        func.alloc_stack_slot(StackSlot::new_dynamic(StackSlotSizeSource::Unknown, 16));

        let layout = compute_frame_layout(&func, 0, true);

        assert!(layout.is_leaf);
        assert!(layout.has_dynamic_alloc);
        assert!(!layout.uses_red_zone);
    }

    #[test]
    fn test_compact_unwind_dynamic_alloc_dwarf_fallback() {
        let func = make_func(
            "alloca_func",
            vec![MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        let layout = compute_frame_layout_dynamic(&func, 0, false);
        let cu = encode_compact_unwind(&layout);

        assert_eq!(cu.encoding, UNWIND_ARM64_MODE_DWARF);
        assert!(cu.needs_dwarf_fallback());
    }

    // --- CompactUnwindEncoding method tests ---

    #[test]
    fn test_encoding_needs_dwarf_fallback() {
        let frame = CompactUnwindEncoding {
            encoding: UNWIND_ARM64_MODE_FRAME,
        };
        assert!(!frame.needs_dwarf_fallback());

        let dwarf = CompactUnwindEncoding {
            encoding: UNWIND_ARM64_MODE_DWARF,
        };
        assert!(dwarf.needs_dwarf_fallback());

        let frameless = CompactUnwindEncoding {
            encoding: UNWIND_ARM64_MODE_FRAMELESS,
        };
        assert!(!frameless.needs_dwarf_fallback());
    }

    #[test]
    fn test_encoding_mode() {
        let frame = CompactUnwindEncoding {
            encoding: UNWIND_ARM64_MODE_FRAME | UNWIND_ARM64_FRAME_X19_X20_PAIR,
        };
        assert_eq!(frame.mode(), UNWIND_ARM64_MODE_FRAME);

        let dwarf = CompactUnwindEncoding {
            encoding: UNWIND_ARM64_MODE_DWARF,
        };
        assert_eq!(dwarf.mode(), UNWIND_ARM64_MODE_DWARF);
    }

    #[test]
    fn test_encoding_register_pair_flags() {
        let encoding = CompactUnwindEncoding {
            encoding: UNWIND_ARM64_MODE_FRAME
                | UNWIND_ARM64_FRAME_X19_X20_PAIR
                | UNWIND_ARM64_FRAME_D8_D9_PAIR,
        };
        let flags = encoding.register_pair_flags();
        assert_ne!(flags & UNWIND_ARM64_FRAME_X19_X20_PAIR, 0);
        assert_ne!(flags & UNWIND_ARM64_FRAME_D8_D9_PAIR, 0);
        assert_eq!(flags & UNWIND_ARM64_FRAME_X21_X22_PAIR, 0);
    }

    #[test]
    fn test_encoding_zero_register_pair_flags_for_dwarf() {
        let encoding = CompactUnwindEncoding {
            encoding: UNWIND_ARM64_MODE_DWARF,
        };
        assert_eq!(encoding.register_pair_flags(), 0);
    }

    // --- Unrecognized register pair fallback tests (#97) ---

    #[test]
    fn test_compact_unwind_unrecognized_gpr_pair_falls_back_to_dwarf() {
        // Create a frame layout with a GPR pair that isn't a standard AArch64
        // callee-saved pair. This tests that encode_compact_unwind falls back
        // to DWARF mode instead of silently dropping the pair.
        let layout = FrameLayout {
            callee_saved_pairs: vec![
                CalleeSavedPair {
                    reg1: X29,
                    reg2: X30,
                    fp_offset: 0,
                    is_fpr: false,
                },
                // X0/X1 is not a valid callee-saved pair
                CalleeSavedPair {
                    reg1: PReg::new(0), // X0
                    reg2: PReg::new(1), // X1
                    fp_offset: -16,
                    is_fpr: false,
                },
            ],
            callee_saved_area_size: 32,
            spill_area_size: 0,
            local_area_size: 0,
            outgoing_arg_area_size: 0,
            total_frame_size: 32,
            uses_frame_pointer: true,
            is_leaf: true,
            uses_red_zone: false,
            fp_to_spill_offset: 0,
            has_dynamic_alloc: false,
        };

        let cu = encode_compact_unwind(&layout);
        assert_eq!(
            cu.encoding, UNWIND_ARM64_MODE_DWARF,
            "Unrecognized GPR pair must trigger DWARF fallback, not be silently dropped"
        );
        assert!(cu.needs_dwarf_fallback());
    }

    #[test]
    fn test_compact_unwind_unrecognized_fpr_pair_falls_back_to_dwarf() {
        // Create a frame layout with an FPR pair that isn't a standard AArch64
        // callee-saved pair. Tests fallback for unrecognized FPR pairs.
        let layout = FrameLayout {
            callee_saved_pairs: vec![
                CalleeSavedPair {
                    reg1: X29,
                    reg2: X30,
                    fp_offset: 0,
                    is_fpr: false,
                },
                // V0/V1 (encoding 64,65) is not a callee-saved FPR pair
                CalleeSavedPair {
                    reg1: PReg::new(64), // V0
                    reg2: PReg::new(65), // V1
                    fp_offset: -16,
                    is_fpr: true,
                },
            ],
            callee_saved_area_size: 32,
            spill_area_size: 0,
            local_area_size: 0,
            outgoing_arg_area_size: 0,
            total_frame_size: 32,
            uses_frame_pointer: true,
            is_leaf: true,
            uses_red_zone: false,
            fp_to_spill_offset: 0,
            has_dynamic_alloc: false,
        };

        let cu = encode_compact_unwind(&layout);
        assert_eq!(
            cu.encoding, UNWIND_ARM64_MODE_DWARF,
            "Unrecognized FPR pair must trigger DWARF fallback, not be silently dropped"
        );
        assert!(cu.needs_dwarf_fallback());
    }

    #[test]
    fn test_compact_unwind_valid_pair_after_unrecognized_not_reached() {
        // If the first non-FP/LR pair is unrecognized, we should fall back to
        // DWARF immediately. The valid X19/X20 pair after it should not be
        // reached — verifying early return behavior.
        let layout = FrameLayout {
            callee_saved_pairs: vec![
                CalleeSavedPair {
                    reg1: X29,
                    reg2: X30,
                    fp_offset: 0,
                    is_fpr: false,
                },
                // Bogus GPR pair
                CalleeSavedPair {
                    reg1: PReg::new(5), // X5
                    reg2: PReg::new(6), // X6
                    fp_offset: -16,
                    is_fpr: false,
                },
                // Valid pair that should never be reached
                CalleeSavedPair {
                    reg1: X19,
                    reg2: X20,
                    fp_offset: -32,
                    is_fpr: false,
                },
            ],
            callee_saved_area_size: 48,
            spill_area_size: 0,
            local_area_size: 0,
            outgoing_arg_area_size: 0,
            total_frame_size: 48,
            uses_frame_pointer: true,
            is_leaf: true,
            uses_red_zone: false,
            fp_to_spill_offset: 0,
            has_dynamic_alloc: false,
        };

        let cu = encode_compact_unwind(&layout);
        assert_eq!(
            cu.encoding, UNWIND_ARM64_MODE_DWARF,
            "Early DWARF fallback on unrecognized pair"
        );
    }

    // =======================================================================
    // FrameIndexEliminator tests
    // =======================================================================

    #[test]
    fn test_fie_simple_frame() {
        // Simple function with a few stack slots and FrameIndex operands.
        let mut func = make_func(
            "fie_simple",
            vec![
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(PReg::new(0)),
                        MachOperand::FrameIndex(FrameIdx(0)),
                    ],
                ),
                MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![
                        MachOperand::PReg(PReg::new(1)),
                        MachOperand::FrameIndex(FrameIdx(1)),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(8, 8));
        func.alloc_stack_slot(StackSlot::new(8, 8));

        let layout = compute_frame_layout(&func, 0, false);
        let fie = FrameIndexEliminator::new(&layout, &func);
        let stats = fie.run(&mut func).unwrap();

        // Both FrameIndex operands should be eliminated.
        assert_eq!(stats.eliminated_count, 2);
        assert_eq!(stats.large_offset_count, 0);

        // Verify operands are now MemOp with FP (X29) as base.
        match &func.insts[0].operands[1] {
            MachOperand::MemOp { base, offset } => {
                assert_eq!(*base, X29);
                assert!(*offset < 0, "FP offset should be negative, got {}", offset);
            }
            other => panic!("Expected MemOp, got {:?}", other),
        }
        match &func.insts[1].operands[1] {
            MachOperand::MemOp { base, offset } => {
                assert_eq!(*base, X29);
                assert!(*offset < 0, "FP offset should be negative, got {}", offset);
            }
            other => panic!("Expected MemOp, got {:?}", other),
        }

        // Offsets should be distinct (different slots).
        let off0 = match &func.insts[0].operands[1] {
            MachOperand::MemOp { offset, .. } => *offset,
            _ => unreachable!(),
        };
        let off1 = match &func.insts[1].operands[1] {
            MachOperand::MemOp { offset, .. } => *offset,
            _ => unreachable!(),
        };
        assert_ne!(off0, off1, "Different slots must have different offsets");
    }

    // -----------------------------------------------------------------
    // SP-relative far-slot re-base (`TCG_NO_SP_FAR_SLOT` kill switch)
    // -----------------------------------------------------------------

    /// A one-load function over a frame deep enough that the slot sits below
    /// `FP-256` (so the FP-relative offset does NOT encode) while still being a
    /// small POSITIVE displacement from SP.
    fn far_slot_load_func(name: &str, slot_bytes: u32) -> MachFunction {
        let mut func = make_func(
            name,
            vec![
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(PReg::new(0)),
                        MachOperand::FrameIndex(FrameIdx(0)),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(slot_bytes, 16));
        func
    }

    #[test]
    fn far_slot_rebases_onto_sp_with_no_materialization() {
        let mut func = far_slot_load_func("far_slot_sp", 4096);
        let layout = compute_frame_layout(&func, 0, false);
        let fp_offset = FrameIndexEliminator::new(&layout, &func).slot_offsets[0] as i64;
        assert!(
            is_large_offset(fp_offset),
            "test setup: FP offset {fp_offset} must be out of immediate range"
        );

        let stats = FrameIndexEliminator::new(&layout, &func)
            .run(&mut func)
            .unwrap();
        assert_eq!(stats.large_offset_count, 0, "no scratch should be needed");
        // The load is untouched apart from its operand: still exactly two insts.
        assert_eq!(func.blocks[0].insts.len(), 2);
        let ldr = func.inst(func.blocks[0].insts[0]);
        let MachOperand::MemOp { base, offset } = ldr.operands[1] else {
            panic!("expected a resolved MemOp, got {:?}", ldr.operands[1]);
        };
        assert_eq!(base, SP, "far slot must re-base onto SP");
        // Address identity: SP + offset names the SAME byte as FP + fp_offset.
        let delta = sp_rebase_delta_for(&layout, &func).expect("fixed SP frame");
        assert_eq!(offset, fp_offset + delta);
        assert!(
            crate::aarch64::encode::scalar_ri_offset_encodable(offset, 8),
            "re-based offset {offset} must encode for an 8-byte access"
        );
    }

    #[test]
    fn far_slot_rebase_refuses_when_sp_is_not_fixed() {
        // A dynamic alloca moves SP, so the slot must stay FP-relative and pay
        // the scratch materialization.
        let mut func = far_slot_load_func("far_slot_dyn", 4096);
        let layout = layout_without_sp_rebase(&func, 0, false);
        assert!(sp_rebase_delta_for(&layout, &func).is_none());
        let stats = FrameIndexEliminator::new(&layout, &func)
            .run(&mut func)
            .unwrap();
        assert_eq!(stats.large_offset_count, 1);
        assert!(func.blocks[0].insts.len() > 2, "expected materialization");
    }

    #[test]
    fn near_slot_keeps_fp_relative_addressing() {
        // Inside `FP-256` the FP-relative offset already encodes, so the
        // re-base must NOT fire — this is what keeps the bytes of every
        // ordinary frame access unchanged.
        let mut func = far_slot_load_func("near_slot", 32);
        let layout = compute_frame_layout(&func, 0, false);
        let fp_offset = FrameIndexEliminator::new(&layout, &func).slot_offsets[0] as i64;
        assert!(!is_large_offset(fp_offset));
        FrameIndexEliminator::new(&layout, &func)
            .run(&mut func)
            .unwrap();
        let MachOperand::MemOp { base, offset } = func.inst(func.blocks[0].insts[0]).operands[1]
        else {
            panic!("expected a resolved MemOp");
        };
        assert_eq!(base, X29);
        assert_eq!(offset, fp_offset);
    }

    #[test]
    fn far_slot_rebase_respects_access_scale() {
        // The re-base uses the ENCODER's own predicate, so it can never turn an
        // unencodable access into a differently-unencodable one: whatever base
        // is chosen, the resulting offset encodes for that access size.
        for (opcode, reg, scale) in [
            (AArch64Opcode::LdrbRI, PReg::new(0), 1_i64),
            (AArch64Opcode::LdrhRI, PReg::new(0), 2),
            (AArch64Opcode::LdrRI, PReg::new(0), 8),
        ] {
            let mut func = make_func(
                "scale_probe",
                vec![
                    MachInst::new(
                        opcode,
                        vec![MachOperand::PReg(reg), MachOperand::FrameIndex(FrameIdx(0))],
                    ),
                    MachInst::new(AArch64Opcode::Ret, vec![]),
                ],
            );
            func.alloc_stack_slot(StackSlot::new(4096, 16));
            let layout = compute_frame_layout(&func, 0, false);
            FrameIndexEliminator::new(&layout, &func)
                .run(&mut func)
                .unwrap();
            let inst = func.inst(func.blocks[0].insts[0]);
            if let MachOperand::MemOp { offset, .. } = inst.operands[1] {
                assert!(
                    crate::aarch64::encode::scalar_ri_offset_encodable(offset, scale),
                    "offset {offset} must encode at scale {scale}"
                );
            }
        }
    }

    #[test]
    fn sp_rebase_delta_matches_the_emitted_prologue() {
        // `FP == SP_final + delta` is the identity the whole transform rests on;
        // derive it independently from the prologue instruction stream.
        let mut func = far_slot_load_func("delta_probe", 4096);
        func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::PReg(X19), MachOperand::PReg(X19)],
        ));
        let layout = compute_frame_layout(&func, 0, true);
        let delta = sp_rebase_delta_for(&layout, &func).expect("fixed SP frame");
        // Walk the prologue: SP moves by the pre-index STP and the final SUB;
        // FP is established as `add x29, sp, #imm` at that point.
        let mut sp = 0_i64; // relative to function entry
        let mut fp = None;
        for inst in emit_prologue(&layout) {
            let imm = match inst.operands.last() {
                Some(MachOperand::Imm(i)) => *i,
                _ => continue,
            };
            match inst.opcode {
                // `stp <pair>, [sp, #-csa]!` — the pre-index allocates the CSA.
                AArch64Opcode::StpPreIndex => sp += imm,
                // `add x29, sp, #(csa - 16)` — FP established off the CURRENT SP.
                AArch64Opcode::AddRI if matches!(inst.operands.first(), Some(MachOperand::PReg(p)) if *p == X29) =>
                {
                    fp = Some(sp + imm);
                }
                // `sub sp, sp, #sp_adj` — locals + spills + outgoing args.
                AArch64Opcode::SubRI => sp -= imm,
                _ => {}
            }
        }
        let fp = fp.expect("prologue must establish FP");
        assert_eq!(
            delta,
            fp - sp,
            "sp_rebase_delta must equal FP - SP_final as emitted"
        );
    }

    #[test]
    fn frame_slot_beyond_ldur_window_prefers_sp_form() {
        // A slot at the BOTTOM of a deep frame is far from FP (needs scratch
        // materialization) but right above SP (one-instruction positive
        // offset). The eliminator must take the SP form: no materialization,
        // MemOp base = SP, offset = fp_offset + total_frame_size - 16.
        let mut func = make_func(
            "sp_pref",
            vec![
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(PReg::new(0)),
                        MachOperand::FrameIndex(FrameIdx(0)),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(8192, 16));

        let layout = compute_frame_layout(&func, 0, false);
        let fp_offset = stack_slot_frame_offsets(&func, &layout)[0].unwrap() as i64;
        assert!(
            is_large_offset(fp_offset),
            "fixture must be outside the FP window, got {fp_offset}"
        );
        let fie = FrameIndexEliminator::new(&layout, &func);
        let stats = fie.run(&mut func).unwrap();

        assert_eq!(stats.eliminated_count, 1);
        assert_eq!(stats.large_offset_count, 0, "SP form needs no scratch");
        let block_insts = &func.blocks[0].insts;
        assert_eq!(block_insts.len(), 2, "no materialization instructions");
        match &func.inst(block_insts[0]).operands[1] {
            MachOperand::MemOp { base, offset } => {
                assert_eq!(*base, SP);
                let expected = fp_offset + layout.total_frame_size as i64 - 16;
                assert_eq!(*offset, expected);
                assert!((0..=AARCH64_MAX_IMM_OFFSET).contains(offset));
            }
            other => panic!("expected MemOp, got {other:?}"),
        }
    }

    #[test]
    fn sp_form_offset_accounts_for_callee_saved_area() {
        // With an extra callee-saved pair the CSA is 32, so FP - SP is
        // total_frame_size - 16, NOT sp_adjustment() (= total - CSA). Using
        // sp_adjustment here would address 16 bytes below the slot.
        let mut func = make_func(
            "sp_pref_csa",
            vec![
                // Touch X19 so the layout gains an extra callee-saved pair.
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![MachOperand::PReg(X19), MachOperand::PReg(X19)],
                ),
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![MachOperand::PReg(X19), MachOperand::FrameIndex(FrameIdx(0))],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(8192, 16));

        let layout = compute_frame_layout(&func, 0, false);
        assert!(
            layout.callee_saved_area_size > 16,
            "fixture needs an extra callee-saved pair, got CSA {}",
            layout.callee_saved_area_size
        );
        let fp_offset = stack_slot_frame_offsets(&func, &layout)[0].unwrap() as i64;
        let fie = FrameIndexEliminator::new(&layout, &func);
        let (base, offset) = fie.resolve_slot_operand(0).unwrap();
        assert_eq!(base, SP);
        assert_eq!(offset, fp_offset + layout.total_frame_size as i64 - 16);
        assert_ne!(
            offset,
            fp_offset + layout.sp_adjustment() as i64,
            "CSA > 16 must make the two formulas disagree for this fixture"
        );
    }

    #[test]
    fn sp_form_disabled_under_dynamic_alloc() {
        // Dynamic stack allocation moves SP mid-function; the SP preference
        // must switch off and keep the FP-relative form.
        let mut func = make_func(
            "sp_pref_dyn",
            vec![
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(PReg::new(0)),
                        MachOperand::FrameIndex(FrameIdx(0)),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(8192, 16));

        let mut layout = compute_frame_layout(&func, 0, false);
        layout.has_dynamic_alloc = true;
        let fie = FrameIndexEliminator::new(&layout, &func);
        let (base, offset) = fie.resolve_slot_operand(0).unwrap();
        assert_eq!(base, X29, "dynamic alloc must keep the FP base");
        assert!(offset < 0);
    }

    #[test]
    fn test_fie_large_frame() {
        // Function with many stack slots so that offsets exceed 4096.
        // Create a function with a very large stack frame.
        let mut func = make_func(
            "fie_large",
            vec![
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(PReg::new(0)),
                        MachOperand::FrameIndex(FrameIdx(0)),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        // Allocate one very large slot to push offset beyond 4096.
        func.alloc_stack_slot(StackSlot::new(8192, 16));

        let layout = layout_without_sp_rebase(&func, 0, false);
        let fie = FrameIndexEliminator::new(&layout, &func);
        let stats = fie.run(&mut func).unwrap();

        assert_eq!(stats.eliminated_count, 1);
        assert_eq!(stats.large_offset_count, 1);

        // The block should now have more instructions (materialization + original + ret).
        let block_insts = &func.blocks[0].insts;
        assert!(
            block_insts.len() > 2,
            "Expected materialization instructions, got {} insts",
            block_insts.len()
        );

        // First instruction(s) should be MOVZ/ADD for offset materialization.
        let first_inst = func.inst(block_insts[0]);
        assert_eq!(
            first_inst.opcode,
            AArch64Opcode::Movz,
            "Expected MOVZ for large offset materialization"
        );

        // The rewritten load should use its destination as the address scratch.
        // Find the LdrRI instruction in the block.
        let ldr_inst_id = block_insts
            .iter()
            .find(|&&id| func.inst(id).opcode == AArch64Opcode::LdrRI);
        assert!(ldr_inst_id.is_some(), "LdrRI should still be in the block");
        let ldr_inst = func.inst(*ldr_inst_id.unwrap());
        match &ldr_inst.operands[1] {
            MachOperand::MemOp { base, offset } => {
                assert_eq!(*base, X0, "Large offset load should use its destination");
                assert_eq!(*offset, 0, "After materialization, offset should be 0");
            }
            other => panic!("Expected rewritten MemOp, got {:?}", other),
        }
    }

    #[test]
    fn test_eliminate_frame_indices_uses_large_offset_path() {
        let mut func = make_func(
            "fi_large_wrapper",
            vec![
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(PReg::new(0)),
                        MachOperand::FrameIndex(FrameIdx(0)),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(8192, 16));

        let layout = layout_without_sp_rebase(&func, 0, false);
        eliminate_frame_indices(&mut func, &layout).unwrap();

        let block_insts = &func.blocks[0].insts;
        assert!(
            block_insts.len() > 2,
            "Expected materialization instructions, got {} insts",
            block_insts.len()
        );

        let first_inst = func.inst(block_insts[0]);
        assert_eq!(first_inst.opcode, AArch64Opcode::Movz);

        let ldr_inst_id = block_insts
            .iter()
            .find(|&&id| func.inst(id).opcode == AArch64Opcode::LdrRI)
            .copied()
            .expect("LdrRI should still be present");
        match &func.inst(ldr_inst_id).operands[1] {
            MachOperand::MemOp { base, offset } => {
                assert_eq!(*base, X0);
                assert_eq!(*offset, 0);
            }
            other => panic!("Expected rewritten MemOp, got {:?}", other),
        }
    }

    #[test]
    fn eliminate_frame_indices_fails_closed_on_live_ip_scratch_clobber() {
        // Reconstructs the pr28982b spill-materialization hazard: two far-offset
        // spill stores where the FIRST stores X16 (forcing the eliminator to
        // borrow X17 as the address scratch) while X17 still holds a live value
        // that the SECOND store reads. Overwriting X17 there is the loop-carried
        // pointer miscompile; the eliminator must reject with a typed error.
        let mut func = make_func(
            "live_ip_scratch_clobber",
            vec![
                MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![
                        MachOperand::PReg(X16),
                        MachOperand::StackSlot(StackSlotId(1)),
                    ],
                ),
                MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![
                        MachOperand::PReg(X17),
                        MachOperand::StackSlot(StackSlotId(2)),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        // Slot 0 is a large local, so slots 1 and 2 sit at far FP offsets that
        // require scratch-register address materialization.
        func.alloc_stack_slot(StackSlot::new(8192, 16)); // slot 0 (forces far offsets)
        func.alloc_stack_slot(StackSlot::new(8, 8)); // slot 1
        func.alloc_stack_slot(StackSlot::new(8, 8)); // slot 2

        let layout = layout_without_sp_rebase(&func, 0, false);
        let before = func.clone();
        assert!(matches!(
            eliminate_frame_indices(&mut func, &layout),
            Err(FrameIndexEliminationError::LiveScratch { scratch: X17, .. })
        ));
        assert_eq!(format!("{func:?}"), format!("{before:?}"));
    }

    #[test]
    fn eliminate_frame_indices_allows_dead_ip_scratch_far_store() {
        // Counterpart to the fail-closed test: when the borrowed IP scratch (X17,
        // chosen because the store value is X16) is NOT read again before the
        // block ends, materialization is sound and must proceed without panic.
        let mut func = make_func(
            "dead_ip_scratch_ok",
            vec![
                MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![
                        MachOperand::PReg(X16),
                        MachOperand::StackSlot(StackSlotId(1)),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(8192, 16)); // slot 0
        func.alloc_stack_slot(StackSlot::new(8, 8)); // slot 1

        let layout = compute_frame_layout(&func, 0, false);
        eliminate_frame_indices(&mut func, &layout).unwrap();

        // The store survives with its frame operand rewritten to [scratch, #0].
        let has_store = func.blocks[0]
            .insts
            .iter()
            .any(|&id| func.inst(id).opcode == AArch64Opcode::StrRI);
        assert!(
            has_store,
            "far-offset store must be materialized, not dropped"
        );
    }

    #[test]
    fn eliminate_frame_indices_resolves_incoming_arg_after_callee_saved_area() {
        let mut func = make_func(
            "incoming_stack_arg",
            vec![
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(PReg::new(0)),
                        MachOperand::PReg(X29),
                        MachOperand::IncomingArg(8),
                    ],
                ),
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![MachOperand::PReg(X19), MachOperand::PReg(X19)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let layout = compute_frame_layout(&func, 0, false);
        assert_eq!(
            layout.callee_saved_area_size, 32,
            "FP/LR plus the X19/X20 callee-saved pair should be in the saved area"
        );

        eliminate_frame_indices(&mut func, &layout).unwrap();

        // Apple-canonical layout: FP points at the saved FP/LR pair, so the
        // caller's SP (CFA) is at FP+16 and incoming stack args sit just above
        // it. IncomingArg(8) -> [FP, #16 + 8] = [FP, #24], INDEPENDENT of the
        // extra X19/X20 pair (which now lives BELOW FP, not above it).
        let load = &func.insts[0];
        assert_eq!(load.opcode, AArch64Opcode::LdrRI);
        assert_eq!(load.operands[1], MachOperand::PReg(X29));
        assert_eq!(load.operands[2], MachOperand::Imm(24));
        assert!(
            !load
                .operands
                .iter()
                .any(|op| matches!(op, MachOperand::IncomingArg(_))),
            "incoming stack args must be concrete FP-relative offsets before encoding"
        );
    }

    #[test]
    fn eliminate_frame_indices_materializes_large_offsets_without_clobbering_x16() {
        let mut func = make_func(
            "large_store_x16",
            vec![
                MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![MachOperand::PReg(X16), MachOperand::FrameIndex(FrameIdx(0))],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(512, 16));

        let layout = layout_without_sp_rebase(&func, 0, false);
        eliminate_frame_indices(&mut func, &layout).unwrap();

        let block_insts = &func.blocks[0].insts;
        assert!(
            block_insts.len() > 2,
            "public frame elimination should insert address materialization"
        );
        // -512 fits the ±4095 immediate range, so the address is computed with a
        // single SUB #imm12 (not the old MOVZ + reg-form sequence). The scratch
        // must still avoid X16 (the value being stored).
        let addr = func.inst(block_insts[0]);
        assert_eq!(addr.opcode, AArch64Opcode::SubRI);
        assert_eq!(addr.operands[0], MachOperand::PReg(X17));
        assert_eq!(addr.operands[1], MachOperand::PReg(X29));
        assert_eq!(addr.operands[2], MachOperand::Imm(512));

        let store_inst_id = block_insts
            .iter()
            .find(|&&id| func.inst(id).opcode == AArch64Opcode::StrRI)
            .copied()
            .expect("store should remain after frame elimination");
        let store = func.inst(store_inst_id);
        assert_eq!(store.operands[0], MachOperand::PReg(X16));
        match &store.operands[1] {
            MachOperand::MemOp { base, offset } => {
                assert_eq!(*base, X17, "X17 avoids clobbering the stored X16 value");
                assert_eq!(*offset, 0);
            }
            other => panic!("Expected materialized MemOp, got {:?}", other),
        }
    }

    #[test]
    fn eliminate_frame_indices_respects_w16_x16_overlap_for_scratch() {
        let mut func = make_func(
            "large_store_w16",
            vec![
                MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![MachOperand::PReg(W16), MachOperand::FrameIndex(FrameIdx(0))],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(512, 16));

        let layout = layout_without_sp_rebase(&func, 0, false);
        eliminate_frame_indices(&mut func, &layout).unwrap();

        let store_inst_id = func.blocks[0]
            .insts
            .iter()
            .find(|&&id| func.inst(id).opcode == AArch64Opcode::StrRI)
            .copied()
            .expect("store should remain after frame elimination");
        let store = func.inst(store_inst_id);
        assert_eq!(store.operands[0], MachOperand::PReg(W16));
        match &store.operands[1] {
            MachOperand::MemOp { base, offset } => {
                assert_eq!(*base, X17, "W16 overlaps X16 and must force X17 scratch");
                assert_eq!(*offset, 0);
            }
            other => panic!("Expected materialized MemOp, got {:?}", other),
        }
    }

    #[test]
    fn eliminate_frame_indices_uses_load_destination_for_large_offset_reload() {
        let mut func = make_func(
            "large_reload_x17",
            vec![
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![MachOperand::PReg(X17), MachOperand::FrameIndex(FrameIdx(0))],
                ),
                MachInst::new(
                    AArch64Opcode::Madd,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::PReg(X16),
                        MachOperand::PReg(X1),
                        MachOperand::PReg(X17),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(512, 16));

        let layout = layout_without_sp_rebase(&func, 0, false);
        eliminate_frame_indices(&mut func, &layout).unwrap();

        let load_inst_id = func.blocks[0]
            .insts
            .iter()
            .find(|&&id| func.inst(id).opcode == AArch64Opcode::LdrRI)
            .copied()
            .expect("load should remain after frame elimination");
        let load = func.inst(load_inst_id);
        assert_eq!(load.operands[0], MachOperand::PReg(X17));
        match &load.operands[1] {
            MachOperand::MemOp { base, offset } => {
                assert_eq!(
                    *base, X17,
                    "large reload should use its destination as address scratch"
                );
                assert_eq!(*offset, 0);
            }
            other => panic!("Expected materialized MemOp, got {:?}", other),
        }
    }

    #[test]
    fn eliminate_frame_indices_lowers_stack_addr_to_real_address_arithmetic() {
        let mut func = make_func(
            "stack_addr",
            vec![
                MachInst::new(
                    AArch64Opcode::AddPCRel,
                    vec![
                        MachOperand::PReg(PReg::new(0)),
                        MachOperand::PReg(SP),
                        MachOperand::StackSlot(StackSlotId(0)),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(512, 16));

        func.alloc_stack_slot(StackSlot::new(8192, 16)); // padding below: keep the accessed slot outside the SP positive window too
        let layout = compute_frame_layout(&func, 0, false);
        eliminate_frame_indices(&mut func, &layout).unwrap();

        let addr = func.inst(func.blocks[0].insts[0]);
        assert_eq!(addr.opcode, AArch64Opcode::SubRI);
        assert_eq!(addr.operands[0], MachOperand::PReg(PReg::new(0)));
        assert_eq!(addr.operands[1], MachOperand::PReg(X29));
        assert_eq!(addr.operands[2], MachOperand::Imm(512));
        assert!(
            !addr
                .operands
                .iter()
                .any(|op| matches!(op, MachOperand::StackSlot(_) | MachOperand::FrameIndex(_))),
            "StackAddr lowering must not leave abstract frame operands for AddPCRel encoding"
        );
    }

    #[test]
    fn eliminate_frame_indices_rejects_runtime_stack_slot_fixed_resolution() {
        let mut func = make_func(
            "runtime_stack_addr",
            vec![MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![
                    MachOperand::PReg(PReg::new(0)),
                    MachOperand::PReg(SP),
                    MachOperand::StackSlot(StackSlotId(0)),
                ],
            )],
        );
        func.alloc_stack_slot(StackSlot::new_dynamic(StackSlotSizeSource::Unknown, 16));

        let layout = compute_frame_layout(&func, 0, false);
        let before = func.clone();
        assert_eq!(
            eliminate_frame_indices(&mut func, &layout),
            Err(FrameIndexEliminationError::RuntimeSizedSlot { slot: 0 })
        );
        assert_eq!(format!("{func:?}"), format!("{before:?}"));
    }

    #[test]
    fn eliminate_frame_indices_rewrites_detached_arena_frame_operands() {
        let mut func = make_func(
            "detached_frame_operand",
            vec![MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        func.alloc_stack_slot(StackSlot::new(8, 8));
        let detached = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::PReg(PReg::new(0)),
                MachOperand::FrameIndex(FrameIdx(0)),
            ],
        ));

        let layout = compute_frame_layout(&func, 0, false);
        eliminate_frame_indices(&mut func, &layout).unwrap();

        match &func.inst(detached).operands[1] {
            MachOperand::MemOp { base, offset } => {
                assert_eq!(*base, X29);
                assert!(*offset < 0);
            }
            other => panic!(
                "Expected detached operand rewrite to MemOp, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn test_fie_mixed_slots() {
        // Function with slots of different sizes and alignments.
        let mut func = make_func(
            "fie_mixed",
            vec![
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(PReg::new(0)),
                        MachOperand::FrameIndex(FrameIdx(0)),
                    ],
                ),
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(PReg::new(1)),
                        MachOperand::FrameIndex(FrameIdx(1)),
                    ],
                ),
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(PReg::new(2)),
                        MachOperand::FrameIndex(FrameIdx(2)),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(16, 16)); // 16-byte aligned local
        func.alloc_stack_slot(StackSlot::new(8, 8)); // 8-byte spill
        func.alloc_stack_slot(StackSlot::new(1, 1)); // 1-byte local

        let layout = compute_frame_layout(&func, 0, false);
        let fie = FrameIndexEliminator::new(&layout, &func);
        let stats = fie.run(&mut func).unwrap();

        assert_eq!(stats.eliminated_count, 3);

        // All operands should be MemOp now.
        let offsets: Vec<i64> = (0..3)
            .map(|i| match &func.insts[i].operands[1] {
                MachOperand::MemOp { base, offset } => {
                    assert_eq!(*base, X29);
                    *offset
                }
                other => panic!("Slot {} not eliminated: {:?}", i, other),
            })
            .collect();

        // Each subsequent slot should be at a lower (more negative) offset.
        assert!(
            offsets[0] > offsets[1],
            "slot 0 > slot 1: {} > {}",
            offsets[0],
            offsets[1]
        );
        assert!(
            offsets[1] > offsets[2],
            "slot 1 > slot 2: {} > {}",
            offsets[1],
            offsets[2]
        );
    }

    #[test]
    fn test_fie_outgoing_arg_area() {
        // Non-leaf function with outgoing arg area and stack slots.
        let mut func = make_func(
            "fie_args",
            vec![
                MachInst::new(AArch64Opcode::Bl, vec![MachOperand::Imm(0)]),
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(PReg::new(0)),
                        MachOperand::FrameIndex(FrameIdx(0)),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(8, 8));

        let layout = compute_frame_layout(&func, 32, false);
        assert!(!layout.is_leaf);
        assert_eq!(layout.outgoing_arg_area_size, 32);

        let fie = FrameIndexEliminator::new(&layout, &func);
        let stats = fie.run(&mut func).unwrap();

        assert_eq!(stats.eliminated_count, 1);
        // Spill slot should use FP-relative addressing.
        match &func.insts[1].operands[1] {
            MachOperand::MemOp { base, .. } => {
                assert_eq!(*base, X29, "Spill slot should use FP-relative addressing");
            }
            other => panic!("Expected MemOp, got {:?}", other),
        }
    }

    #[test]
    fn test_fie_fp_vs_sp_relative() {
        // Test that when uses_frame_pointer is true, we get FP-relative addressing.
        let mut func = make_func(
            "fie_fp",
            vec![
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(PReg::new(0)),
                        MachOperand::FrameIndex(FrameIdx(0)),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(8, 8));

        // Standard layout (uses_frame_pointer = true on Apple AArch64).
        let layout = compute_frame_layout(&func, 0, false);
        assert!(layout.uses_frame_pointer);

        let fie = FrameIndexEliminator::new(&layout, &func);
        let (base, _offset) = fie.resolve_slot_operand(0).unwrap();
        assert_eq!(base, X29, "With FP, should use FP-relative");

        // Test SP-relative by creating a layout with uses_frame_pointer=false.
        let sp_layout = FrameLayout {
            uses_frame_pointer: false,
            ..layout.clone()
        };
        let fie_sp = FrameIndexEliminator::new(&sp_layout, &func);
        let (base_sp, _offset_sp) = fie_sp.resolve_slot_operand(0).unwrap();
        assert_eq!(base_sp, SP, "Without FP, should use SP-relative");
    }

    #[test]
    fn test_fie_stats_tracking() {
        // Verify stats are correctly tracked.
        let mut func = make_func(
            "fie_stats",
            vec![
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(PReg::new(0)),
                        MachOperand::FrameIndex(FrameIdx(0)),
                    ],
                ),
                MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![
                        MachOperand::PReg(PReg::new(1)),
                        MachOperand::FrameIndex(FrameIdx(0)),
                    ],
                ),
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(PReg::new(2)),
                        MachOperand::FrameIndex(FrameIdx(1)),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(8, 8));
        func.alloc_stack_slot(StackSlot::new(4, 4));

        let layout = compute_frame_layout(&func, 0, false);
        let fie = FrameIndexEliminator::new(&layout, &func);
        let stats = fie.run(&mut func).unwrap();

        assert_eq!(
            stats.eliminated_count, 3,
            "Should eliminate 3 frame indices"
        );
        assert_eq!(stats.large_offset_count, 0, "No large offsets expected");
    }

    #[test]
    fn test_fie_no_frame_indices() {
        // Function with no frame index operands — should be a no-op.
        let mut func = make_func(
            "fie_noop",
            vec![
                MachInst::new(
                    AArch64Opcode::AddRR,
                    vec![
                        MachOperand::PReg(PReg::new(0)),
                        MachOperand::PReg(PReg::new(1)),
                        MachOperand::PReg(PReg::new(2)),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );

        let layout = compute_frame_layout(&func, 0, false);
        let fie = FrameIndexEliminator::new(&layout, &func);
        let stats = fie.run(&mut func).unwrap();

        assert_eq!(stats.eliminated_count, 0);
        assert_eq!(stats.large_offset_count, 0);
        assert_eq!(func.blocks[0].insts.len(), 2, "Block should be unchanged");
    }

    #[test]
    fn test_is_large_offset() {
        // Boundary cases for AArch64 immediate range.
        assert!(!is_large_offset(0));
        assert!(!is_large_offset(100));
        assert!(!is_large_offset(4095));
        assert!(is_large_offset(4096));
        assert!(is_large_offset(10000));
        assert!(!is_large_offset(-1));
        assert!(!is_large_offset(-256));
        assert!(is_large_offset(-257));
        assert!(is_large_offset(-1000));
        assert!(is_large_offset(i64::MAX));
        assert!(is_large_offset(i64::MIN));
    }

    #[test]
    fn test_fie_resolve_slot_operand() {
        // Directly test resolve_slot_operand for correctness.
        let mut func = make_func(
            "fie_resolve",
            vec![MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        func.alloc_stack_slot(StackSlot::new(8, 8));
        func.alloc_stack_slot(StackSlot::new(16, 16));

        let layout = compute_frame_layout(&func, 0, false);
        let fie = FrameIndexEliminator::new(&layout, &func);

        let (base0, off0) = fie.resolve_slot_operand(0).unwrap();
        let (base1, off1) = fie.resolve_slot_operand(1).unwrap();

        assert_eq!(base0, X29);
        assert_eq!(base1, X29);
        // Both offsets should be negative (below FP).
        assert!(off0 < 0, "slot 0 offset should be negative: {}", off0);
        assert!(off1 < 0, "slot 1 offset should be negative: {}", off1);
        // Slot 1 should be at a lower offset than slot 0.
        assert!(
            off0 > off1,
            "slot 0 ({}) should be above slot 1 ({})",
            off0,
            off1
        );
    }

    #[test]
    fn test_fie_out_of_range_slot() {
        // Test defensive handling of out-of-range slot index.
        let func = make_func("fie_oob", vec![MachInst::new(AArch64Opcode::Ret, vec![])]);

        let layout = compute_frame_layout(&func, 0, false);
        let fie = FrameIndexEliminator::new(&layout, &func);

        // An unknown slot must not silently redirect an access to SP+0.
        assert_eq!(
            fie.resolve_slot_operand(0),
            Err(FrameIndexEliminationError::InvalidSlot { slot: 0, slots: 0 })
        );
    }

    #[test]
    fn frame_elimination_rejects_unknown_slot_without_redirecting_memory() {
        let mut func = make_func(
            "unknown_slot",
            vec![MachInst::new(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::StackSlot(StackSlotId(1)),
                ],
            )],
        );
        func.alloc_stack_slot(StackSlot::new(8, 8));
        let layout = compute_frame_layout(&func, 0, false);
        let before = format!("{func:?}");
        assert_eq!(
            eliminate_frame_indices(&mut func, &layout),
            Err(FrameIndexEliminationError::InvalidSlot { slot: 1, slots: 1 })
        );
        assert_eq!(format!("{func:?}"), before);
    }

    #[test]
    fn frame_elimination_rejects_malformed_stack_address_destination() {
        let mut func = make_func(
            "invalid_stack_address",
            vec![MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![
                    MachOperand::Imm(0),
                    MachOperand::PReg(SP),
                    MachOperand::StackSlot(StackSlotId(0)),
                ],
            )],
        );
        func.alloc_stack_slot(StackSlot::new(8, 8));
        let layout = compute_frame_layout(&func, 0, false);
        let before = format!("{func:?}");
        let error = eliminate_frame_indices(&mut func, &layout).unwrap_err();
        assert!(matches!(
            error,
            FrameIndexEliminationError::InvalidInstruction { .. }
        ));
        assert!(error.to_string().contains("PReg dst"));
        assert_eq!(format!("{func:?}"), before);
    }

    #[test]
    fn frame_elimination_rejects_incoming_offset_overflow() {
        let mut func = make_func(
            "invalid_incoming_offset",
            vec![MachInst::new(
                AArch64Opcode::AddRI,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X29),
                    MachOperand::IncomingArg(i64::MAX),
                ],
            )],
        );
        let layout = compute_frame_layout(&func, 0, false);
        let before = format!("{func:?}");
        assert_eq!(
            eliminate_frame_indices(&mut func, &layout),
            Err(FrameIndexEliminationError::IncomingArgumentOffsetOverflow { offset: i64::MAX })
        );
        assert_eq!(format!("{func:?}"), before);
    }

    #[test]
    fn test_fie_elimination_stats_default() {
        let stats = EliminationStats::default();
        assert_eq!(stats.eliminated_count, 0);
        assert_eq!(stats.large_offset_count, 0);
    }

    // -----------------------------------------------------------------------
    // legalize_large_mem_offsets — the pre-encode offset safety net
    // -----------------------------------------------------------------------

    fn opcodes(func: &MachFunction) -> Vec<AArch64Opcode> {
        func.blocks[0]
            .insts
            .iter()
            .map(|&id| func.inst(id).opcode)
            .collect()
    }

    fn gpr_ri_opcodes() -> [AArch64Opcode; 14] {
        use AArch64Opcode as Op;
        [
            Op::LdrRI,
            Op::StrRI,
            Op::LdrbRI,
            Op::LdrhRI,
            Op::LdrsbRI,
            Op::LdrshRI,
            Op::StrbRI,
            Op::StrhRI,
            Op::VolatileLdrRI,
            Op::VolatileStrRI,
            Op::VolatileLdrbRI,
            Op::VolatileLdrhRI,
            Op::VolatileStrbRI,
            Op::VolatileStrhRI,
        ]
    }

    #[test]
    fn gpr_ri_legalizer_does_not_launder_malformed_resolved_shapes() {
        let mut rewritten = Vec::new();
        let mut attempted = 0;
        for opcode in gpr_ri_opcodes() {
            for operands in [
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X1),
                    MachOperand::Imm(32768),
                    MachOperand::Imm(8),
                ],
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::MemOp {
                        base: X1,
                        offset: 32768,
                    },
                    MachOperand::Imm(8),
                ],
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X1),
                    MachOperand::MemOp {
                        base: X1,
                        offset: 32768,
                    },
                ],
            ] {
                attempted += 1;
                let mut func = make_func("bad_ri_shape", vec![MachInst::new(opcode, operands)]);
                let before = format!("{func:?}");
                if legalize_large_mem_offsets(&mut func).is_ok() && format!("{func:?}") != before {
                    rewritten.push(format!(
                        "{opcode:?}: malformed operands were rewritten: {func:?}"
                    ));
                }
            }
        }
        assert_eq!(attempted, 42);
        assert!(
            rewritten.is_empty(),
            "{} of {attempted} malformed shapes rewritten:\n{}",
            rewritten.len(),
            rewritten.join("\n")
        );
    }

    /// Source-level address-sequence check, not native execution. Arithmetic
    /// must use a real X register, preserve the requested delta, and leave one
    /// unchanged-kind memory access with the original transfer and flags.
    fn check_gpr_ri_legalization(
        inst: MachInst,
        requested: i64,
        zero_transfer: bool,
    ) -> Result<(), String> {
        let transfer = inst.operands[0].clone();
        let flags = inst.flags;
        let opcode = inst.opcode;
        let mut func = make_func("valid_far_ri", vec![inst]);
        legalize_large_mem_offsets(&mut func)?;
        let access = func.inst(InstId(0));
        let [actual_transfer, MachOperand::MemOp { base, offset: 0 }] = access.operands.as_slice()
        else {
            return Err(format!(
                "{opcode:?}: missing legalized address: {:?}",
                access.operands
            ));
        };
        if *actual_transfer != transfer || access.opcode != opcode || access.flags != flags {
            return Err(format!("{opcode:?}: transfer/opcode/flags changed"));
        }
        if base.encoding() > 30 || (zero_transfer && *base != X16 && *base != X17) {
            return Err(format!(
                "{opcode:?}: invalid effective-address scratch {base:?}"
            ));
        }
        let ids = &func.blocks[0].insts;
        if ids.len() < 2 || ids.last() != Some(&InstId(0)) {
            return Err(format!("{opcode:?}: missing ordered materialization"));
        }
        assert_eq!(
            eval_scratch_delta(&func, &ids[..ids.len() - 1], *base, X1),
            requested
        );
        for id in ids {
            crate::aarch64::encode::encode_instruction(func.inst(*id))
                .map_err(|error| format!("{opcode:?}: {error}"))?;
        }
        Ok(())
    }

    #[test]
    fn gpr_ri_legalizer_never_uses_zero_register_as_address_scratch() {
        use AArch64Opcode as Op;
        let mut failures = Vec::new();
        let mut attempted = 0;
        for opcode in [
            Op::LdrRI,
            Op::LdrbRI,
            Op::LdrhRI,
            Op::LdrsbRI,
            Op::LdrshRI,
            Op::VolatileLdrRI,
            Op::VolatileLdrbRI,
            Op::VolatileLdrhRI,
        ] {
            for transfer in [
                MachOperand::PReg(PReg::new(160)),
                MachOperand::PReg(PReg::new(161)),
                MachOperand::Special(SpecialReg::XZR),
                MachOperand::Special(SpecialReg::WZR),
            ] {
                for offset in [-300, 32768] {
                    attempted += 1;
                    let inst = MachInst::new(
                        opcode,
                        vec![
                            transfer.clone(),
                            MachOperand::PReg(X1),
                            MachOperand::Imm(offset),
                        ],
                    );
                    if let Err(error) = check_gpr_ri_legalization(inst, offset, true) {
                        failures.push(format!("{opcode:?}/{transfer:?}/{offset}: {error}"));
                    }
                }
            }
        }
        assert_eq!(attempted, 64);
        assert!(
            failures.is_empty(),
            "{} of {attempted} zero-transfer cases failed:\n{}",
            failures.len(),
            failures.join("\n")
        );
    }

    #[test]
    fn gpr_ri_legalizer_preserves_all_fourteen_large_offset_forms() {
        let mut failures = Vec::new();
        let mut attempted = 0;
        for opcode in gpr_ri_opcodes() {
            for transfer in [W0, X0] {
                for split in [false, true] {
                    for offset in [-300, 32768] {
                        attempted += 1;
                        let operands = if split {
                            vec![
                                MachOperand::PReg(transfer),
                                MachOperand::PReg(X1),
                                MachOperand::Imm(offset),
                            ]
                        } else {
                            vec![
                                MachOperand::PReg(transfer),
                                MachOperand::MemOp { base: X1, offset },
                            ]
                        };
                        if let Err(error) = check_gpr_ri_legalization(
                            MachInst::new(opcode, operands),
                            offset,
                            false,
                        ) {
                            failures.push(format!(
                                "{opcode:?}/{transfer:?}/split={split}/{offset}: {error}"
                            ));
                        }
                    }
                }
            }
        }
        assert_eq!(attempted, 112);
        assert!(
            failures.is_empty(),
            "{} of {attempted} legal forms failed:\n{}",
            failures.len(),
            failures.join("\n")
        );
    }

    #[test]
    fn gpr_ri_legalizer_preserves_unresolved_frames_and_legacy_typed_aliases() {
        let mut failures = Vec::new();
        let mut attempted = 0;
        for opcode in gpr_ri_opcodes() {
            for frame in [
                MachOperand::FrameIndex(FrameIdx(0)),
                MachOperand::StackSlot(StackSlotId(0)),
            ] {
                attempted += 1;
                let inst = MachInst::new(opcode, vec![MachOperand::PReg(X0), frame]);
                if crate::aarch64::encode::scalar_ri_mem_scale(&inst).is_none() {
                    failures.push(format!(
                        "{opcode:?}: transfer scale unavailable before frame resolution"
                    ));
                }
                let mut func = make_func("unresolved_ri", vec![inst]);
                let before = format!("{func:?}");
                legalize_large_mem_offsets(&mut func)
                    .expect("early legalizer defers unresolved frame operands");
                assert_eq!(format!("{func:?}"), before);
            }
        }
        assert_eq!(attempted, 28);
        // Existing typed aliases are not part of the tightened 14-op contract.
        // Their valid address materialization remains available and unchanged.
        for (opcode, transfer) in [
            (AArch64Opcode::STRWui, W0),
            (AArch64Opcode::STRXui, X0),
            (AArch64Opcode::STRSui, PReg::new(128)),
            (AArch64Opcode::STRDui, PReg::new(96)),
        ] {
            let inst = MachInst::new(
                opcode,
                vec![
                    MachOperand::PReg(transfer),
                    MachOperand::PReg(X1),
                    MachOperand::Imm(32768),
                ],
            );
            if let Err(error) = check_gpr_ri_legalization(inst, 32768, false) {
                failures.push(format!("legacy {opcode:?}: {error}"));
            }
        }
        assert!(
            failures.is_empty(),
            "unresolved/legacy controls failed:\n{}",
            failures.join("\n")
        );
    }

    #[test]
    fn gpr_ri_legalizer_post_repair_volatile_fp_far_offsets() {
        use trust_cg_ir::regs::{D0, H0, S0, V0};

        // Eight opcode/width forms, each in both address layouts at two
        // offsets beyond every H/S/D/Q immediate range. This is source-level
        // materialization and encoding coverage, not native execution.
        let mut failures = Vec::new();
        let mut attempted = 0;
        for opcode in [AArch64Opcode::VolatileLdrRI, AArch64Opcode::VolatileStrRI] {
            for transfer in [H0, S0, D0, V0] {
                for split in [false, true] {
                    for offset in [-300, 65536] {
                        attempted += 1;
                        let operands = if split {
                            vec![
                                MachOperand::PReg(transfer),
                                MachOperand::PReg(X1),
                                MachOperand::Imm(offset),
                            ]
                        } else {
                            vec![
                                MachOperand::PReg(transfer),
                                MachOperand::MemOp { base: X1, offset },
                            ]
                        };
                        if let Err(error) = check_gpr_ri_legalization(
                            MachInst::new(opcode, operands),
                            offset,
                            false,
                        ) {
                            failures.push(format!(
                                "{opcode:?}/{transfer:?}/split={split}/{offset}: {error}"
                            ));
                        }
                    }
                }
            }
        }
        assert_eq!(attempted, 32);
        assert!(
            failures.is_empty(),
            "{} of {attempted} volatile FP forms failed:\n{}",
            failures.len(),
            failures.join("\n")
        );
    }

    #[test]
    fn gpr_ri_legalizer_post_repair_preserves_malformed_address_banks() {
        use trust_cg_ir::regs::{D0, H0, NZCV, S0, V0, WZR};

        let mut failures = Vec::new();
        let mut attempted = 0;
        for opcode in gpr_ri_opcodes() {
            // W0/WSP, all FP widths, both ZR widths, system and unknown PRegs.
            let mut addresses = Vec::new();
            for base in [
                W0,
                PReg::new(63),
                H0,
                S0,
                D0,
                V0,
                XZR,
                WZR,
                NZCV,
                PReg::new(u16::MAX),
            ] {
                addresses.push(vec![MachOperand::MemOp {
                    base,
                    offset: 65536,
                }]);
                addresses.push(vec![MachOperand::PReg(base), MachOperand::Imm(65536)]);
            }
            for base in [SpecialReg::XZR, SpecialReg::WZR] {
                addresses.push(vec![MachOperand::Special(base), MachOperand::Imm(65536)]);
            }
            for address in addresses {
                attempted += 1;
                let mut operands = vec![MachOperand::PReg(X0)];
                operands.extend(address);
                let mut func = make_func("bad_ri_base", vec![MachInst::new(opcode, operands)]);
                let before = format!("{func:?}");
                let result = legalize_large_mem_offsets(&mut func);
                if result.is_err() || format!("{func:?}") != before {
                    failures.push(format!("{opcode:?}: malformed base was not deferred unchanged: {result:?}: {func:?}"));
                }
                if crate::aarch64::encode::encode_instruction(func.inst(InstId(0))).is_ok() {
                    failures.push(format!("{opcode:?}: malformed base encoded: {func:?}"));
                }
            }
        }
        assert_eq!(attempted, 308);
        assert!(
            failures.is_empty(),
            "malformed address controls failed:\n{}",
            failures.join("\n")
        );
    }

    #[test]
    fn legalize_negative_out_of_range_store_uses_free_scratch() {
        // Repro shape: spill/canary store `str x16, [x29, #-384]`. -384 is below
        // the unscaled floor (-256), fits neither immediate form, so it must be
        // legalized. Value is X16, so the scratch must be X17.
        let mut func = make_func(
            "neg_store",
            vec![
                MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![
                        MachOperand::PReg(X16),
                        MachOperand::MemOp {
                            base: X29,
                            offset: -384,
                        },
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        legalize_large_mem_offsets(&mut func).expect("legalization must succeed");
        assert_eq!(
            opcodes(&func),
            vec![
                AArch64Opcode::SubRI,
                AArch64Opcode::StrRI,
                AArch64Opcode::Ret
            ]
        );
        let sub = func.inst(func.blocks[0].insts[0]);
        assert_eq!(sub.operands[0], MachOperand::PReg(X17)); // scratch != stored value x16
        assert_eq!(sub.operands[1], MachOperand::PReg(X29));
        assert_eq!(sub.operands[2], MachOperand::Imm(384));
        let st = func.inst(func.blocks[0].insts[1]);
        assert_eq!(st.operands[0], MachOperand::PReg(X16));
        assert_eq!(
            st.operands[1],
            MachOperand::MemOp {
                base: X17,
                offset: 0
            }
        );
    }

    #[test]
    fn legalize_load_reuses_destination_and_preserves_live_scratch_carrier() {
        // Regression for the stack-protector miscompile: the epilogue keeps the
        // guard value in X16 ACROSS the out-of-range canary load
        // `ldr x17, [x29, #-384]` (a following consumer reads X16). The old
        // operand-only scratch check clobbered X16. The pass must legalize the
        // load WITHOUT writing X16 — reusing the load's own destination (X17).
        let mut func = make_func(
            "live_carrier",
            vec![
                // x16 <- guard (in-range load, untouched)
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(X16),
                        MachOperand::MemOp {
                            base: X0,
                            offset: 0,
                        },
                    ],
                ),
                // canary load, OUT OF RANGE
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(X17),
                        MachOperand::MemOp {
                            base: X29,
                            offset: -384,
                        },
                    ],
                ),
                // consumer reading X16 -> X16 is LIVE across the canary load
                MachInst::new(
                    AArch64Opcode::AddRR,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::PReg(X16),
                        MachOperand::PReg(X17),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        legalize_large_mem_offsets(&mut func).expect("legalization must succeed");
        // No address-materialization instruction may write X16 (the live guard).
        for &id in &func.blocks[0].insts {
            let inst = func.inst(id);
            if matches!(
                inst.opcode,
                AArch64Opcode::SubRI
                    | AArch64Opcode::AddRI
                    | AArch64Opcode::SubRR
                    | AArch64Opcode::AddRR
                    | AArch64Opcode::Movz
            ) && let Some(MachOperand::PReg(d)) = inst.operands.first()
            {
                assert_ne!(
                    hw_encoding(*d),
                    16,
                    "legalization clobbered X16 (a live guard carrier) via {:?}",
                    inst.opcode
                );
            }
        }
        // The canary load (destination X17) now addresses through X17 itself
        // (dest reuse), offset 0 — NOT through X16 (which still holds the guard).
        let canary = func.blocks[0]
            .insts
            .iter()
            .map(|&id| func.inst(id))
            .find(|i| {
                i.opcode == AArch64Opcode::LdrRI
                    && i.operands.first() == Some(&MachOperand::PReg(X17))
                    && matches!(
                        i.operands.get(1),
                        Some(MachOperand::MemOp { offset: 0, .. })
                    )
            })
            .expect("legalized canary load present");
        match &canary.operands[1] {
            MachOperand::MemOp { base, offset } => {
                assert_eq!(
                    hw_encoding(*base),
                    17,
                    "canary load base should be x17 (dest reuse)"
                );
                assert_eq!(*offset, 0);
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn legalize_in_range_offsets_are_untouched() {
        // Byte-identity: every offset already fits, so the pass must be a no-op.
        let mut func = make_func(
            "in_range",
            vec![
                // -256: unscaled floor (in range)
                MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::MemOp {
                            base: X29,
                            offset: -256,
                        },
                    ],
                ),
                // 4095*8 = 32760: max scaled dword offset (in range)
                MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(X1),
                        MachOperand::MemOp {
                            base: X29,
                            offset: 32760,
                        },
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let before = func.blocks[0].insts.clone();
        legalize_large_mem_offsets(&mut func).expect("no-op");
        assert_eq!(
            func.blocks[0].insts, before,
            "in-range accesses must be untouched"
        );
    }

    #[test]
    fn legalize_far_positive_byte_store_materializes_via_movz_add() {
        // Byte store at +5000 exceeds the byte-scaled max (4095), so the >4095
        // path materializes the magnitude and adds it as a register.
        let mut func = make_func(
            "far_pos",
            vec![
                MachInst::new(
                    AArch64Opcode::StrbRI,
                    vec![
                        MachOperand::PReg(W0),
                        MachOperand::MemOp {
                            base: X29,
                            offset: 5000,
                        },
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        legalize_large_mem_offsets(&mut func).expect("legalization must succeed");
        // 5000 (0x1388) fits 16 bits -> single MOVZ, then ADD (reg), then STRB.
        assert_eq!(
            opcodes(&func),
            vec![
                AArch64Opcode::Movz,
                AArch64Opcode::AddRR,
                AArch64Opcode::StrbRI,
                AArch64Opcode::Ret
            ]
        );
    }

    #[test]
    fn legalize_sp_base_far_offset_fails_closed() {
        // SP base with |offset| > 4095 needs a second scratch to add to SP; the
        // shifted-register form cannot take SP as Rn, so the pass fails closed
        // rather than emit wrong code.
        let mut func = make_func(
            "sp_far",
            vec![
                MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::MemOp {
                            base: SP,
                            offset: -5000,
                        },
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let err = legalize_large_mem_offsets(&mut func).unwrap_err();
        assert!(
            err.contains("fail-closed"),
            "expected fail-closed, got: {err}"
        );
    }

    // -----------------------------------------------------------------------
    // emit_effective_address_into_scratch — the shared frame-address helper.
    // Single ADD/SUB #imm12 for |off| <= 4095 (one fewer instruction than the
    // old MOVZ + reg-form); MOVZ/MOVK + shifted-register form beyond it.
    // -----------------------------------------------------------------------

    /// Symbolically evaluate the address-materialization sequence emitted into
    /// `out` and return the value the scratch ends up holding, expressed as
    /// `base + delta` (so `delta` must equal the requested offset). Panics on any
    /// instruction shape the helper never emits — that is itself a violation of
    /// the effective-address contract, not just an unexpected opcode.
    fn eval_scratch_delta(func: &MachFunction, out: &[InstId], scratch: PReg, base: PReg) -> i64 {
        let base_op = addr_base_operand(base);
        let mut mat: i64 = 0; // running value materialized into scratch by MOVZ/MOVK
        let mut delta: Option<i64> = None; // final base-relative delta
        for &id in out {
            let inst = func.inst(id);
            let imm = |i: usize| match inst.operands.get(i) {
                Some(MachOperand::Imm(v)) => *v,
                other => panic!("expected Imm operand at {i}, got {other:?}"),
            };
            assert_eq!(
                inst.operands[0],
                MachOperand::PReg(scratch),
                "every materialization instruction must write the scratch"
            );
            match inst.opcode {
                AArch64Opcode::Movz => mat = imm(1) & 0xFFFF,
                AArch64Opcode::Movk => {
                    assert_eq!(imm(2), 16, "helper only emits MOVK at lsl #16");
                    mat = (mat & !(0xFFFF << 16)) | ((imm(1) & 0xFFFF) << 16);
                }
                AArch64Opcode::AddRI => {
                    assert_eq!(inst.operands[1], base_op);
                    delta = Some(imm(2));
                }
                AArch64Opcode::SubRI => {
                    assert_eq!(inst.operands[1], base_op);
                    delta = Some(-imm(2));
                }
                AArch64Opcode::AddRR => {
                    assert_eq!(inst.operands[1], base_op);
                    assert_eq!(inst.operands[2], MachOperand::PReg(scratch));
                    delta = Some(mat);
                }
                AArch64Opcode::SubRR => {
                    assert_eq!(inst.operands[1], base_op);
                    assert_eq!(inst.operands[2], MachOperand::PReg(scratch));
                    delta = Some(-mat);
                }
                other => panic!("unexpected opcode {other:?} in address materialization"),
            }
        }
        delta.expect("sequence must end with a base-relative ADD/SUB")
    }

    #[test]
    fn emit_addr_small_offsets_use_single_imm12() {
        // 0x144 (324) is the ReedSolomon-style spill offset: it fits the ±4095
        // immediate window, so the address is ONE instruction — not MOVZ + reg.
        // Both signs and the ±4095 boundary are covered.
        for &off in &[0x144_i64, -0x144, 1, -1, 4095, -4095, 256, -256] {
            let mut func = make_func("emit_small", vec![]);
            let mut out = Vec::new();
            emit_effective_address_into_scratch(&mut func, X16, X29, off, &mut out)
                .expect("small offset must succeed");
            assert_eq!(out.len(), 1, "off={off} must be a single instruction");
            let inst = func.inst(out[0]);
            let expected = if off >= 0 {
                AArch64Opcode::AddRI
            } else {
                AArch64Opcode::SubRI
            };
            assert_eq!(inst.opcode, expected, "off={off}");
            assert_eq!(inst.operands[0], MachOperand::PReg(X16));
            assert_eq!(inst.operands[1], MachOperand::PReg(X29));
            assert_eq!(inst.operands[2], MachOperand::Imm(off.abs()), "off={off}");
            // Effective-address equivalence: scratch == base + off exactly.
            assert_eq!(eval_scratch_delta(&func, &out, X16, X29), off, "off={off}");
        }
    }

    #[test]
    fn emit_addr_beyond_imm12_keeps_movz_movk_reg_form() {
        // Just past the imm12 boundary, and a two-halfword magnitude: the long
        // MOVZ(/MOVK) + shifted-register form is retained and stays correct.
        for &off in &[4096_i64, -4096, 0x1_2345, -0x1_2345, 0xFFFF, 0x1_0000] {
            let mut func = make_func("emit_large", vec![]);
            let mut out = Vec::new();
            emit_effective_address_into_scratch(&mut func, X16, X29, off, &mut out)
                .expect("32-bit offset must succeed for an FP base");
            assert!(out.len() >= 2, "off={off} needs materialization");
            assert_eq!(func.inst(out[0]).opcode, AArch64Opcode::Movz, "off={off}");
            let tail = func.inst(*out.last().unwrap()).opcode;
            let expected_tail = if off >= 0 {
                AArch64Opcode::AddRR
            } else {
                AArch64Opcode::SubRR
            };
            assert_eq!(tail, expected_tail, "off={off}");
            // MOVK appears iff the magnitude needs the upper halfword.
            let has_movk = out
                .iter()
                .any(|&id| func.inst(id).opcode == AArch64Opcode::Movk);
            assert_eq!(has_movk, off.unsigned_abs() > 0xFFFF, "off={off}");
            assert_eq!(eval_scratch_delta(&func, &out, X16, X29), off, "off={off}");
        }
    }

    #[test]
    fn emit_addr_sp_base_small_ok_but_large_fails_closed() {
        // The immediate ADD/SUB form accepts SP as Rn, so a small SP-relative
        // offset is still a single instruction...
        let mut func = make_func("emit_sp_small", vec![]);
        let mut out = Vec::new();
        emit_effective_address_into_scratch(&mut func, X16, SP, -0x144, &mut out)
            .expect("small SP offset uses the SP-safe immediate form");
        assert_eq!(out.len(), 1);
        assert_eq!(func.inst(out[0]).opcode, AArch64Opcode::SubRI);
        assert_eq!(func.inst(out[0]).operands[1], addr_base_operand(SP));

        // ...but the shifted-register form cannot add to SP (SP decodes as XZR
        // there), so a large SP offset FAILS CLOSED instead of emitting wrong code.
        let mut func2 = make_func("emit_sp_large", vec![]);
        let mut out2 = Vec::new();
        let err = emit_effective_address_into_scratch(&mut func2, X16, SP, -5000, &mut out2)
            .expect_err("large SP offset must fail closed");
        assert!(
            err.contains("fail-closed"),
            "expected fail-closed, got: {err}"
        );
        assert!(
            out2.is_empty(),
            "fail-closed must not leave partial instructions"
        );
    }

    #[test]
    fn eliminate_frame_indices_uses_sub_imm12_for_all_access_sizes() {
        // A 324-byte (0x144) slot resolves to FP-#0x144 — below the unscaled
        // floor (-256) yet inside the ±4095 window: exactly the regime the fix
        // targets. Every load/store width must reach it via a single SUB #imm12
        // (formerly MOVZ + SUB reg), for all five access sizes plus their
        // sign-extending / store variants.
        let load = |op| {
            MachInst::new(
                op,
                vec![MachOperand::PReg(X0), MachOperand::FrameIndex(FrameIdx(0))],
            )
        };
        let store = |op| {
            MachInst::new(
                op,
                vec![MachOperand::PReg(X1), MachOperand::FrameIndex(FrameIdx(0))],
            )
        };
        let cases = [
            load(AArch64Opcode::LdrRI),
            load(AArch64Opcode::LdrbRI),
            load(AArch64Opcode::LdrhRI),
            load(AArch64Opcode::LdrsbRI),
            load(AArch64Opcode::LdrshRI),
            store(AArch64Opcode::StrRI),
            store(AArch64Opcode::StrbRI),
            store(AArch64Opcode::StrhRI),
        ];
        for access in cases {
            let opcode = access.opcode;
            let mut func = make_func(
                "slot_0x144",
                vec![access, MachInst::new(AArch64Opcode::Ret, vec![])],
            );
            func.alloc_stack_slot(StackSlot::new(0x144, 4));
            let layout = layout_without_sp_rebase(&func, 0, false);
            eliminate_frame_indices(&mut func, &layout).unwrap();

            let block = &func.blocks[0].insts;
            // Exactly SUB #imm12 ; <access> ; RET — no MOVZ/MOVK anywhere.
            assert_eq!(
                block.len(),
                3,
                "{opcode:?}: expected sub+access+ret, got {block:?}"
            );
            let addr = func.inst(block[0]);
            assert_eq!(
                addr.opcode,
                AArch64Opcode::SubRI,
                "{opcode:?}: must use sub-imm12"
            );
            assert_eq!(addr.operands[1], MachOperand::PReg(X29));
            assert_eq!(addr.operands[2], MachOperand::Imm(0x144), "{opcode:?}");
            let scratch = match &addr.operands[0] {
                MachOperand::PReg(p) => *p,
                other => panic!("{opcode:?}: scratch not a PReg: {other:?}"),
            };
            // The access itself now addresses [scratch, #0], same effective address.
            let acc = func.inst(block[1]);
            assert_eq!(acc.opcode, opcode);
            let mem = acc
                .operands
                .iter()
                .find_map(|o| match o {
                    MachOperand::MemOp { base, offset } => Some((*base, *offset)),
                    _ => None,
                })
                .expect("rewritten access must carry a MemOp");
            assert_eq!(
                mem,
                (scratch, 0),
                "{opcode:?}: access must go through the scratch address"
            );
        }
    }

    #[test]
    fn eliminate_frame_indices_keeps_movz_form_beyond_imm12() {
        // A slot pushing the offset past -4095 must retain the MOVZ + SUB reg
        // long form (the fix only shortens the in-window case).
        let mut func = make_func(
            "slot_far",
            vec![
                MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![MachOperand::PReg(X1), MachOperand::FrameIndex(FrameIdx(0))],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(5000, 8)); // |offset| = 5000 > 4095
        let layout = layout_without_sp_rebase(&func, 0, false);
        eliminate_frame_indices(&mut func, &layout).unwrap();

        let block = &func.blocks[0].insts;
        assert_eq!(func.inst(block[0]).opcode, AArch64Opcode::Movz);
        assert!(
            block
                .iter()
                .any(|&id| func.inst(id).opcode == AArch64Opcode::SubRR),
            "far negative offset must fold the base with a shifted-register SUB"
        );
    }
}
