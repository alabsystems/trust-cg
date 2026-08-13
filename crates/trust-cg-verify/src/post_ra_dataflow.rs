// trust-cg-verify/post_ra_dataflow.rs - TV-5 post-fixup register-dataflow validation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! TV-5: register-dataflow validation of the FINAL post-fixup x86-64 stream
//! (the "tied-ghost-operand dataflow check", `[TCG-POST-RA-DATAFLOW]`).
//!
//! # What this closes
//!
//! Everything the x86 pipeline does AFTER register allocation — the spill
//! store/reload materialization, the formal-argument parallel-copy fixup, the
//! two-address fixup, frame lowering, dynamic-alloc expansion, branch
//! resolution, and any future post-RA peephole — used to be covered only by
//! the TV-4 STRUCTURAL recheck ([`crate::post_regalloc_recheck`]: block
//! integrity + opcode legality). Register def-use / value-flow after regalloc
//! was unvalidated: a post-fixup transform that deleted a load-bearing
//! two-address bridge copy (`mov dst<-lhs`) passed the recheck and the binary
//! MISCOMPILED SILENTLY. This module adds a block-local symbolic copy-flow
//! walk plus a CFG-wide lane-aware call-clobber fixed point over the final
//! stream. The core tied-form obligation is, at every instruction
//! (where the encoder reads `operands[0]` as the tied
//! read+write destination and IGNORES `operands[1]`):
//!
//! ```text
//! x86_regs_overlap(preg(op0), preg(op1))  OR  sym(op0) == sym(op1)
//! ```
//!
//! The preserved-but-encoder-ignored `operands[1]` ("ghost operand") is the
//! per-instruction certificate of the intended tied source. All three
//! `fixup_two_address` arms establish this obligation block-locally on sound
//! code: arm 1 (commutative swap) makes op1 alias op0, arm 2 (non-commutative
//! scratch triangle) rewrites op0 AND op1 to one scratch, arm 3 inserts the
//! adjacent bridge copy and pushes the instruction with `operands[1]`
//! UNCHANGED. Deleting/corrupting/clobbering a bridge copy therefore ALWAYS
//! breaks the obligation, and every sound stream discharges it without any
//! cross-block reasoning (no CFG, no fixpoint, no meet — the regalloc
//! validator's historical loop-header false-positive class is structurally
//! unreachable).
//!
//! # Load-bearing convention (ghost operands)
//!
//! `operands[1]` of a tied-form instruction is the encoder-ignored ghost of
//! the intended tied source; **no post-RA pass may rewrite or delete
//! `operands[1]` of a tied-form instruction, EXCEPT via a sym-faithful
//! rename** — this validator's core obligation reads it. A sym-faithful
//! rename redirects the ghost to the source of a deleted copy whose value
//! the ghost's register provably held at that point, applied in lockstep
//! with every real (encoder-visible) read of that register in the same
//! window; the value the ghost names is unchanged, so the obligation still
//! discharges through the walk's copy propagation. The carve-out is
//! REQUIRED, not merely permitted: a pass that deletes such a copy but
//! skips the ghost slot leaves a STALE ghost sym while the renamed real
//! reads carry the new one, and this validator would refute the sound
//! output (pinned by `x86_movrr_coalesce_ghost_skip_variant_refuted_by_tv5`
//! in `trust-cg-codegen`). The x86 post-fixup `MovRR` coalescer
//! (`coalesce_x86_redundant_movrr_copies`) is the one such pass today.
//! Rewriting `operands[1] := operands[0]` (self-certification) remains
//! forbidden; pinned contract tests in `trust-cg-codegen`
//! (`x86_fixup_two_address_ghost_contract_pinned`) guard the current fixup
//! arms, and fully closing that hole needs a future captured-spec v2
//! design.
//!
//! # Scope
//!
//! * **x86-only.** The aarch64 post-RA stream is owned by the AS lane,
//!   mirroring the `reject_unsupported_x86_isel` precedent.
//! * This validator proves value-ROUTING consistency at tied sites plus
//!   enforced call/register/flags clobber discipline. It does NOT re-prove
//!   instruction arithmetic (SMT lowering certs upstream), allocation
//!   correctness (the regalloc translation validator upstream), or encode
//!   fidelity (the ENC-3 decode-check gate downstream).
//! * The access model is verify-owned and independent — it deliberately does
//!   NOT reuse codegen's `x86_operand_access` (private, wrong dependency
//!   direction, and a shared model would be a common-mode hazard: the
//!   empirically proven miscompile came exactly from applying the pre-fixup
//!   operand model to the post-fixup stream).
//!
//! # Documented v1 misses (each sound to skip; none can cause a false
//! positive)
//!
//! * Wrong-value routing at NON-tied use slots (a rename of `operands[2]` of
//!   a tied op, or of a plain use, to a wrong-but-defined register): no spec
//!   exists in-stream; pre-fixup routing is owned by the regalloc TV.
//!   The captured-spec Stage A check ([`crate::post_ra_captured_spec`],
//!   WARN-only rollout) now covers the register half of this miss over the
//!   post-fixup coalescing window.
//! * Self-certifying ghost corruption (`operands[1] := operands[0]`):
//!   mitigated by the convention above + the pinned contract test.
//! * A buggy commutative swap applied to a NON-commutative opcode
//!   self-certifies via the overlap arm (any swap leaves op1 aliasing op0);
//!   the operand-ORDER correctness of the fixup arms is pinned by the
//!   codegen contract test instead.
//! * Memory value dataflow (wrong spill slot store/load, frame overlap):
//!   registers only in v1. Never a false-positive source (kills make syms
//!   fresher); slot-injectivity checking is a future increment.
//! * `Ret` return-register reads, scratch-cluster containment,
//!   callee-saved restore correctness, branch `Imm`
//!   displacement values (provisional until encode; re-patched from block
//!   offsets), and post-recheck byte-level mutations (ENC-3's jurisdiction)
//!   are all out of scope.
//! * Call clobbers are ABI-aware: System V and Windows x64 use their exact
//!   volatile GPR/XMM sets, while lowering-captured exact result metadata marks
//!   only registers the particular call actually returns as definitions. Thus
//!   a void call clobbers even RAX/RDX/XMM0/XMM1, and enforcing a clobber read
//!   cannot reject a value held in a Windows callee-saved RSI/RDI/XMM6-15.
//!
//! # Enforcement
//!
//! Production is unconditionally ENFORCE ([`X86_POST_RA_DATAFLOW_DEFAULT`]).
//! A process environment variable cannot downgrade a final-stream correctness
//! invariant. Reads of call-clobbered registers or arithmetic flags fail
//! closed. CF/PF/AF/ZF/SF/OF validity is propagated independently across the
//! complete CFG: each consumer is accepted only when every flag it actually
//! reads is defined on every reachable predecessor path, is not subsequently
//! clobbered by a call, and is not made undefined by a partial flag producer.

use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicU64, Ordering};

use trust_cg_ir::regs::VReg;
use trust_cg_ir::x86_64_ops::{X86CondCode, X86Opcode};
use trust_cg_ir::x86_64_regs::{
    self, R8, R9, R10, R11, RAX, RCX, RDX, RSP, X86_CALLER_SAVED_GPRS, X86PReg, XMM0, XMM1,
    x86_containing_gpr64, x86_preg_name, x86_regs_overlap,
};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::x86_64_isel::{
    X86CallAbi, X86ISelFunction, X86ISelInst, X86ISelOperand, x86_scalar_return_result_regs,
};

pub(crate) const WINDOWS_X64_CALLER_SAVED_GPRS: [X86PReg; 7] = [RAX, RCX, RDX, R8, R9, R10, R11];

use crate::post_regalloc_recheck::PostRegallocRecheckMode;

// ---------------------------------------------------------------------------
// Violations
// ---------------------------------------------------------------------------

/// Which post-RA register-dataflow property broke.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PostRaDataflowViolationKind {
    /// At a tied-form instruction, the tied destination `operands[0]` neither
    /// overlaps the ghost source `operands[1]` nor carries the same symbolic
    /// value — the load-bearing bridge copy was deleted, redirected, or
    /// clobbered (the empirically proven silent-miscompile class).
    TiedOperandValueMismatch,
    /// A `VReg` operand on the FINAL post-fixup stream has no physical
    /// register in the allocation map — the encoder would resolve it to
    /// nothing and emit a wrong or unencodable instruction.
    UnallocatedVReg,
    /// An instruction's operand shape is not one this validator's exhaustive
    /// access model admits (e.g. a `Phi` surviving past regalloc, a tied-form
    /// site whose destination or ghost is not a register). Fail-closed: an
    /// unknown shape is never silently treated as "no access".
    MalformedOperands,
    /// An instruction reads a register whose only value is a call clobber
    /// (caller-saved, not a return register).
    ReadOfCallClobberedReg,
    /// An instruction reads a VREG-NAMED operand whose caller-saved register
    /// home was clobbered by a call after the vreg's last def-by-name, on at
    /// least one reachable CFG path. Unlike [`Self::ReadOfCallClobberedReg`]
    /// (a physical-lane property), this survives the LAUNDER miss: a post-call
    /// redefinition of the PHYSICAL register by a different value clears the
    /// lane taint but cannot restore the named vreg's value — only a def OF
    /// the vreg (a reload, a copy into it, a fresh result) un-severs it. This
    /// is the fail-closed net for the O0 cross-call regalloc class (bug #66).
    CallSeveredVRegRead,
    /// An instruction consumes one or more arithmetic flags last clobbered by
    /// a call on at least one reachable CFG path.
    ReadOfClobberedFlags,
    /// An instruction consumes one or more arithmetic flags that are undefined
    /// on at least one reachable CFG path. This includes function/block entry,
    /// explicitly undefined instruction results, and preserved flags that had
    /// no earlier definition.
    ReadOfUndefinedFlags,
}

impl PostRaDataflowViolationKind {
    /// Greppable tag for the diagnostic line.
    pub fn tag(self) -> &'static str {
        match self {
            Self::TiedOperandValueMismatch => "tied-operand-value-mismatch",
            Self::UnallocatedVReg => "unallocated-vreg",
            Self::MalformedOperands => "malformed-operands",
            Self::ReadOfCallClobberedReg => "read-of-call-clobbered-reg",
            Self::CallSeveredVRegRead => "call-severed-vreg-read",
            Self::ReadOfClobberedFlags => "read-of-clobbered-flags",
            Self::ReadOfUndefinedFlags => "read-of-undefined-flags",
        }
    }

    /// `true` for the kinds that fail a compile closed under ENFORCE.
    pub fn enforce_tier(self) -> bool {
        matches!(
            self,
            Self::TiedOperandValueMismatch
                | Self::UnallocatedVReg
                | Self::MalformedOperands
                | Self::ReadOfCallClobberedReg
                | Self::CallSeveredVRegRead
                | Self::ReadOfClobberedFlags
                | Self::ReadOfUndefinedFlags
        )
    }
}

/// A single post-RA register-dataflow violation. In ENFORCE mode any
/// enforce-tier one of these fails the function's compile closed.
#[derive(Debug, Clone)]
pub struct PostRaDataflowViolation {
    /// Which property broke.
    pub kind: PostRaDataflowViolationKind,
    /// Human-readable diagnostic (names the function, block, instruction
    /// index, opcode, and the involved registers/symbols).
    pub detail: String,
}

// ---------------------------------------------------------------------------
// Mode + telemetry (dedicated to TV-5; the TV-4 structural counter is NOT
// overloaded, so corpus warn-sweeps can distinguish the two gates)
// ---------------------------------------------------------------------------

/// Default mode for the x86-64 post-RA dataflow check: ENFORCE.
pub const X86_POST_RA_DATAFLOW_DEFAULT: PostRegallocRecheckMode = PostRegallocRecheckMode::Enforce;

/// Resolve the active production mode. This gate is a correctness invariant,
/// not a rollout preference, so environment variables cannot weaken it.
pub fn post_ra_dataflow_mode() -> PostRegallocRecheckMode {
    X86_POST_RA_DATAFLOW_DEFAULT
}

/// Process-wide count of post-RA dataflow violations observed (any tier, warn
/// or enforce) — telemetry for warn-only rollouts and for tests.
static DATAFLOW_HITS: AtomicU64 = AtomicU64::new(0);

/// Total post-RA dataflow violations observed by this process.
pub fn post_ra_dataflow_hit_count() -> u64 {
    DATAFLOW_HITS.load(Ordering::Relaxed)
}

/// Record one violation: bump the process-wide counter and print a greppable
/// one-line report. `failing` is true only when THIS violation will fail the
/// compile (ENFORCE mode and an enforce-tier kind).
fn record(arch: &str, function_name: &str, kind_tag: &str, detail: &str, failing: bool) {
    DATAFLOW_HITS.fetch_add(1, Ordering::Relaxed);
    let tag = if failing {
        "[TCG-POST-RA-DATAFLOW-FAIL]"
    } else {
        "[TCG-POST-RA-DATAFLOW-WARN]"
    };
    eprintln!("{tag} arch={arch} fn={function_name} kind={kind_tag}: {detail}");
}

// ---------------------------------------------------------------------------
// Location space: dense 33-slot array (16 GPR roots + 16 XMM + EFLAGS)
// ---------------------------------------------------------------------------

/// Number of tracked locations: GPR64 roots 0..=15, XMM0-15 as 16..=31,
/// EFLAGS as 32.
pub(crate) const NUM_LOCS: usize = 33;

/// The EFLAGS location.
pub(crate) const FLAGS_LOC: u8 = 32;

/// Arithmetic EFLAGS tracked by the x86 condition-code/ADC/SBB consumers.
/// Masks use semantic flag positions, independent of architectural RFLAGS bit
/// numbers, so the complete validity set fits in the final `CallTaintState`
/// cell alongside reachability and provenance.
pub(crate) type FlagMask = u16;
const FLAG_CF: FlagMask = 1 << 0;
const FLAG_PF: FlagMask = 1 << 1;
const FLAG_AF: FlagMask = 1 << 2;
const FLAG_ZF: FlagMask = 1 << 3;
const FLAG_SF: FlagMask = 1 << 4;
const FLAG_OF: FlagMask = 1 << 5;
const FLAGS_ALL: FlagMask = FLAG_CF | FLAG_PF | FLAG_AF | FLAG_ZF | FLAG_SF | FLAG_OF;
const FLAGS_LOGIC_DEFINED: FlagMask = FLAG_CF | FLAG_PF | FLAG_ZF | FLAG_SF | FLAG_OF;
const FLAGS_MUL_DEFINED: FlagMask = FLAG_CF | FLAG_OF;
const FLAGS_MUL_UNDEFINED: FlagMask = FLAG_PF | FLAG_AF | FLAG_ZF | FLAG_SF;

/// Map a physical register to its tracked location: any GPR (64/32/16/8-bit)
/// canonicalizes to its containing GPR64 root (encodings 0..=15); XMM0-15 map
/// to 16..=31. RFLAGS/RIP (never operands) return `None` — a `None` loc
/// read/def is silently skipped, EXCEPT at a tied site where it is
/// malformed-operands. RSP/RBP are ordinary GPR roots — tracked like any
/// other, never special-cased.
pub(crate) fn loc_of(p: X86PReg) -> Option<u8> {
    if let Some(root) = x86_containing_gpr64(p) {
        return Some(root.encoding() as u8);
    }
    let e = p.encoding();
    if (64..=79).contains(&e) {
        return Some((e - 64 + 16) as u8);
    }
    None
}

pub(crate) const GPR_LANE_MASK: u16 = 0x00ff;
pub(crate) const XMM_LANE_MASK: u16 = 0xffff;

/// Byte lanes semantically read through a physical-register operand.
pub(crate) fn preg_read_mask(p: X86PReg) -> u16 {
    match p.encoding() {
        0..=15 => GPR_LANE_MASK,
        16..=31 => 0x000f,
        32..=47 => 0x0003,
        48..=63 => 0x0001,
        64..=79 => XMM_LANE_MASK,
        _ => 0,
    }
}

/// Byte lanes overwritten by an ordinary x86 register definition. A GPR32
/// write defines the full 64-bit root because the ISA zeroes bits 63:32;
/// GPR8/GPR16 writes preserve the upper lanes.
pub(crate) fn preg_write_mask(p: X86PReg) -> u16 {
    match p.encoding() {
        0..=31 => GPR_LANE_MASK,
        32..=47 => 0x0003,
        48..=63 => 0x0001,
        64..=79 => XMM_LANE_MASK,
        _ => 0,
    }
}

pub(crate) fn low_bits_lane_mask(bits: u16) -> u16 {
    let bytes = usize::from(bits / 8);
    if bytes >= 16 {
        XMM_LANE_MASK
    } else {
        ((1u32 << bytes) - 1) as u16
    }
}

/// Scalar XMM opcodes only consume/overwrite their low scalar lane and preserve
/// the remaining destination lanes. Memory-to-XMM moves and MOVD/MOVQ are not
/// listed: those instructions define zeros in the upper lanes.
///
/// Returns `(read_mask, write_mask)`. The cross-width scalar converts are the
/// only ASYMMETRIC entries: the hardware consumes the SOURCE scalar width and
/// defines the DESTINATION scalar width (`cvtss2sd` reads 4 source bytes and
/// writes 8; `cvtsd2ss` reads 8 and writes 4). A symmetric mask either
/// over-reads the source (fail-closing correct f32 blends whose bytes 4-7 are
/// architectural garbage) or under-reads it (missing taint in an f64 source's
/// upper scalar bytes).
fn scalar_xmm_lane_masks(opcode: X86Opcode) -> Option<(u16, u16)> {
    use X86Opcode::*;
    if matches!(opcode, Cvtss2sd) {
        Some((0x000f, 0x00ff))
    } else if matches!(opcode, Cvtsd2ss) {
        Some((0x00ff, 0x000f))
    } else if matches!(
        opcode,
        MovssRR
            | Addss
            | Subss
            | Mulss
            | Divss
            | Minss
            | Maxss
            | Cmpss
            | Sqrtss
            | Roundss
            | Cvtsi2ss
            | Cvtss2si
            | Cvttss2si
            | Ucomiss
            | MovssMR
            | MovdFromXmm
    ) {
        Some((0x000f, 0x000f))
    } else if matches!(
        opcode,
        MovsdRR
            | Addsd
            | Subsd
            | Mulsd
            | Divsd
            | Minsd
            | Maxsd
            | Cmpsd
            | Sqrtsd
            | Roundsd
            | Cvtsi2sd
            | Cvtsd2si
            | Cvttsd2si
            | Ucomisd
            | MovsdMR
            | MovqFromXmm
    ) {
        Some((0x00ff, 0x00ff))
    } else {
        None
    }
}

fn refine_scalar_xmm_lane_accesses(opcode: X86Opcode, acc: &mut InstAccess) {
    let Some((read_mask, write_mask)) = scalar_xmm_lane_masks(opcode) else {
        return;
    };
    for read in &mut acc.lane_reads {
        if (16..32).contains(&read.loc) {
            read.mask &= read_mask;
        }
    }
    for def in &mut acc.lane_defs {
        if (16..32).contains(&def.loc) {
            def.mask &= write_mask;
        }
    }
    if let Some(tied) = &mut acc.tied
        && loc_of(tied.dst).is_some_and(|loc| (16..32).contains(&loc))
    {
        tied.read_mask &= read_mask;
    }
}

// ---------------------------------------------------------------------------
// Symbolic value domain
// ---------------------------------------------------------------------------

/// The symbolic value held by a location. Copies propagate syms unchanged;
/// every other def mints a fresh `Def`. The `loc` field in `Def`/`CallClobber`
/// is the ORIGINAL definition location, so a multi-def instruction (e.g.
/// `Idiv` defining RAX and RDX) gives its two roots DIFFERENT syms — a
/// same-instruction two-root pair can never discharge a tied obligation by
/// false equality.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Sym {
    /// The opaque block-entry byte lane of location `loc`. Re-minted at every
    /// block entry: register copy-flow remains block-local by construction.
    BlockIn { loc: u8, lane: u8 },
    /// One byte lane produced by in-block instruction `inst`.
    Def { inst: u32, loc: u8, lane: u8 },
    /// One byte lane clobbered (not meaningfully defined) by a call.
    CallClobber { inst: u32, loc: u8, lane: u8 },
}

pub(crate) const SYMBOLIC_LANES: usize = 16;
type SymbolicState = [[Sym; SYMBOLIC_LANES]; NUM_LOCS];

// ---------------------------------------------------------------------------
// Verify-owned tied-index mirror of codegen's x86_two_address_lhs_operand_index
// ---------------------------------------------------------------------------

/// The register-register two-address opcode set — a verbatim verify-side
/// mirror of codegen's `is_x86_two_address_rr` (pipeline.rs). Unit-pinned via
/// [`post_ra_tied_lhs_index`] tests so codegen-side drift surfaces as a test
/// diff, not a silent classification gap.
fn is_post_ra_two_address_rr(opcode: X86Opcode) -> bool {
    use X86Opcode::*;
    matches!(
        opcode,
        AddRR
            | SubRR
            | AdcRR
            | SbbRR
            | AndRR
            | OrRR
            | XorRR
            | ImulRR
            | Addsd
            | Subsd
            | Mulsd
            | Divsd
            | Andpd
            | Addss
            | Subss
            | Mulss
            | Divss
            | Andps
            | Pand
            | Pandn
            | Por
            | Pxor
            | Pcmpeqb
            | Pcmpeqw
            | Pcmpgtb
            | Pcmpgtw
            | Pcmpeqd
            | Pcmpgtd
            | Paddb
            | Paddw
            | Paddd
            | Psubb
            | Psubw
            | Psubd
            | Paddq
            | Psubq
            | Pmullw
            | Pmuludq
            | Punpcklbw
            | Punpckldq
            | Packuswb
            | Punpckhbw
            | Punpcklqdq
            | Pmulld
            | Psadbw
            | Pcmpeqq
            | Pcmpgtq
            | Addps
            | Subps
            | Mulps
            | Divps
            | Addpd
            | Subpd
            | Mulpd
            | Divpd
            | Minsd
            | Maxsd
            | Minss
            | Maxss
            | Cmpsd
            | Cmpss
    )
}

/// Exact arithmetic-flag effect for integer ALU forms shared across the
/// register/register, register/immediate, and register/memory families.
/// Returns `(definitely-defined, definitely-undefined)`; unmentioned flags are
/// preserved. SSE/XMM forms return empty masks.
fn integer_alu_flag_effect(opcode: X86Opcode) -> (FlagMask, FlagMask) {
    use X86Opcode::*;
    match opcode {
        AddRR | SubRR | AdcRR | SbbRR | AddRI | SubRI | AddRM | SubRM => (FLAGS_ALL, 0),
        AndRR | OrRR | XorRR | AndRI | OrRI | XorRI | TestRR | TestRI | TestRM => {
            (FLAGS_LOGIC_DEFINED, FLAG_AF)
        }
        ImulRR | ImulRRI | ImulRM | ImulRMSib => (FLAGS_MUL_DEFINED, FLAGS_MUL_UNDEFINED),
        _ => (0, 0),
    }
}

fn is_post_ra_three_address_ri(opcode: X86Opcode) -> bool {
    use X86Opcode::*;
    matches!(opcode, AddRI | SubRI | AndRI | OrRI | XorRI)
}

fn is_post_ra_shift_ri(opcode: X86Opcode) -> bool {
    use X86Opcode::*;
    matches!(
        opcode,
        ShlRI | ShrRI | SarRI | RolRI | Pslld | Psrld | Psrad | Psllq | Psrlq
    )
}

fn is_post_ra_shift_rr(opcode: X86Opcode) -> bool {
    use X86Opcode::*;
    matches!(opcode, ShlRR | ShrRR | SarRR)
}

fn is_post_ra_explicit_source_unary(opcode: X86Opcode) -> bool {
    matches!(opcode, X86Opcode::Neg | X86Opcode::Not)
}

/// Verify-owned mirror of codegen's `x86_two_address_lhs_operand_index`,
/// byte-for-byte semantics: returns `Some(1)` iff `operands[1]` of this
/// instruction is the encoder-ignored tied ghost source.
pub fn post_ra_tied_lhs_index(inst: &X86ISelInst) -> Option<usize> {
    if matches!(inst.opcode, X86Opcode::Pinsrd | X86Opcode::Pinsrq) && inst.operands.len() >= 4 {
        return Some(1);
    }

    if inst.operands.len() >= 3
        && (is_post_ra_two_address_rr(inst.opcode)
            || is_post_ra_three_address_ri(inst.opcode)
            || is_post_ra_shift_ri(inst.opcode))
    {
        return Some(1);
    }

    if inst.operands.len() == 2
        && (is_post_ra_shift_rr(inst.opcode) || is_post_ra_explicit_source_unary(inst.opcode))
    {
        return Some(1);
    }

    None
}

// ---------------------------------------------------------------------------
// Access model (verify-owned; independent of codegen's x86_operand_access)
// ---------------------------------------------------------------------------

/// The result of resolving one operand against the allocation map.
enum Resolved {
    Preg(X86PReg),
    UnallocVReg(VReg),
    NotAReg,
}

fn resolve_reg(op: &X86ISelOperand, alloc: &HashMap<VReg, X86PReg>) -> Resolved {
    match op {
        X86ISelOperand::VReg(v) => match alloc.get(v) {
            Some(p) => Resolved::Preg(*p),
            None => Resolved::UnallocVReg(*v),
        },
        X86ISelOperand::PReg(p) => Resolved::Preg(*p),
        _ => Resolved::NotAReg,
    }
}

/// One instruction's register accesses, classified by the exhaustive opcode
/// model below.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct CallResultLoc {
    pub(crate) loc: u8,
    pub(crate) defined_bits: u16,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LaneAccess {
    pub(crate) loc: u8,
    pub(crate) mask: u16,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LaneCopy {
    pub(crate) dst: u8,
    pub(crate) src: u8,
    /// Source lanes read by the copy.
    pub(crate) read_mask: u16,
    /// Destination lanes overwritten by the copy. Lanes outside this mask are
    /// preserved; lanes in the mask but outside `read_mask` are defined zeros
    /// (the x86 GPR32 zero-extension rule).
    pub(crate) write_mask: u16,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct TiedAccess {
    pub(crate) dst: X86PReg,
    pub(crate) ghost: X86PReg,
    /// Exact destination byte lanes whose pre-transfer value the encoded
    /// instruction consumes. Scalar SSE forms use only their low 4/8 bytes;
    /// packed XMM forms use all 16 bytes.
    pub(crate) read_mask: u16,
}

#[derive(Default)]
pub(crate) struct InstAccess {
    /// Exact byte lanes read at each root. This is the load-bearing
    /// call-clobber model.
    pub(crate) lane_reads: Vec<LaneAccess>,
    /// Exact byte lanes overwritten by each definition.
    pub(crate) lane_defs: Vec<LaneAccess>,
    /// Width-aware copy effect shared by caller-clobber taint and symbolic
    /// tied-value identities.
    pub(crate) lane_copy: Option<LaneCopy>,
    /// Register-register `Xchg`: swap the two locations' syms.
    pub(crate) xchg: Option<(u8, u8)>,
    /// A tied-ghost site: `(dst_preg, ghost_preg)`; the obligation is checked
    /// against the PRE-transfer state.
    pub(crate) tied: Option<TiedAccess>,
    /// Exact arithmetic flags consumed from the pre-instruction state.
    pub(crate) flags_use_mask: FlagMask,
    /// Arithmetic flags definitely defined on every execution of the
    /// instruction. Their prior undefined/call-clobber provenance is killed.
    pub(crate) flags_def_mask: FlagMask,
    /// Arithmetic flags definitely overwritten with architecturally undefined
    /// values. Prior call-clobber provenance is killed and replaced by
    /// undefined provenance.
    pub(crate) flags_undef_mask: FlagMask,
    /// Arithmetic flags that may become undefined on a value-dependent path
    /// while another path preserves them (currently variable-count shifts).
    /// Existing invalid provenance must therefore also be preserved.
    pub(crate) flags_may_undef_mask: FlagMask,
    /// Exact result locations declared by a call. `Some([])` is an explicit
    /// void/sret call; `None` means this is not a call. The declaration is
    /// schema-checked during classification before it can authorize a Def.
    pub(crate) call_result_locs: Option<Vec<CallResultLoc>>,
    /// `VReg` operands missing from the allocation map (each one violation).
    pub(crate) unallocated: Vec<VReg>,
    /// Virtual registers this instruction READS by name (the operand is a
    /// `VReg`, not a raw `PReg`). Feeds the call-severed check: reading a
    /// vreg whose caller-saved home was clobbered by a call since its last
    /// def-by-name is a violation the preg-lane taint cannot see once another
    /// value redefines the physical register (the launder miss, header
    /// "Documented v1 misses").
    pub(crate) vreg_reads: Vec<VReg>,
    /// Virtual registers this instruction DEFINES by name (a reload, a copy
    /// destination, a fresh result). A def-by-name is the ONLY event that
    /// un-severs a vreg.
    pub(crate) vreg_defs: Vec<VReg>,
    /// XMM lane-wise garbage FLOW: set for the packed ops whose destination
    /// byte lane `i` is a pure function of byte lane `i` of their register
    /// inputs (packed bitwise `Pand`/`Pandn`/`Por`/`Pxor` and the
    /// full-register `MovdqaRR` copy). For these ops a call-clobber-tainted
    /// input lane is NOT a semantic use — the scalar-float libcall lowerings
    /// (min/max/clamp sign-mask blends after an `fmaf`-style call) route
    /// architectural upper-lane garbage through them by design. The taint
    /// PROPAGATES into the same destination lane (union of the inputs' taint,
    /// never cleared by the full-width def) instead of failing the read, and
    /// every SEMANTIC consumer — scalar ops, stores, call arguments, `Ret`
    /// result lanes, and every packed op NOT in this set — still checks its
    /// lanes, so genuinely-wrong dataflow still fails closed downstream.
    pub(crate) xmm_lanewise_flow: Option<XmmLanewiseFlow>,
}

/// Locations participating in an XMM lane-wise flow: `dst` is the written
/// location, `srcs` the register inputs whose lane taints union into it
/// (`dst` itself is a source for the two-address bitwise forms; a folded
/// memory rhs contributes no source — memory is not taint-tracked, and its
/// address GPRs remain ordinary checked reads).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct XmmLanewiseFlow {
    pub(crate) dst: u8,
    pub(crate) srcs: Vec<u8>,
}

impl XmmLanewiseFlow {
    /// `true` iff `loc` is one of the flow's XMM participants — the exact
    /// set whose reads are re-classified from "semantic use" to "lane-wise
    /// propagation" for this instruction.
    fn covers(&self, loc: u8) -> bool {
        (16..32).contains(&loc) && (self.dst == loc || self.srcs.contains(&loc))
    }
}

impl InstAccess {
    fn read_preg(&mut self, p: X86PReg) {
        if let Some(loc) = loc_of(p) {
            self.lane_reads.push(LaneAccess {
                loc,
                mask: preg_read_mask(p),
            });
        }
    }

    /// Read only the LOW `bits` of a physical register — a call's declared
    /// per-argument read width. Never wider than the register operand's own
    /// carrier (the intersection with `preg_read_mask`), so a width-alias
    /// register cannot smuggle a wider read.
    fn read_preg_low_bits(&mut self, p: X86PReg, bits: u16) {
        if let Some(loc) = loc_of(p) {
            self.lane_reads.push(LaneAccess {
                loc,
                mask: low_bits_lane_mask(bits) & preg_read_mask(p),
            });
        }
    }

    fn def_preg(&mut self, p: X86PReg) {
        if let Some(loc) = loc_of(p) {
            self.lane_defs.push(LaneAccess {
                loc,
                mask: preg_write_mask(p),
            });
        }
    }

    /// Read a direct register operand (a `VReg`/`PReg`); every other operand
    /// kind carries no direct register read.
    fn read_reg(&mut self, op: &X86ISelOperand, alloc: &HashMap<VReg, X86PReg>) {
        if let X86ISelOperand::VReg(v) = op {
            self.vreg_reads.push(*v);
        }
        match resolve_reg(op, alloc) {
            Resolved::Preg(p) => self.read_preg(p),
            Resolved::UnallocVReg(v) => self.unallocated.push(v),
            Resolved::NotAReg => {}
        }
    }

    /// Read a source operand: memory operands read their address registers
    /// (a `StackSlot` base is not a register read — legal pre-resolve;
    /// post-frame-resolution bases are `PReg(RBP)`); register operands read
    /// their root; `Imm`/`FImm`/`Block`/`CondCode`/`Symbol`/`StackSlot`/
    /// `ConstPoolEntry` carry no register dataflow.
    fn read_reg_or_mem(&mut self, op: &X86ISelOperand, alloc: &HashMap<VReg, X86PReg>) {
        match op {
            X86ISelOperand::MemAddr { base, .. } => self.read_reg(base, alloc),
            X86ISelOperand::SibMemAddr { base, index, .. } => {
                self.read_reg(base, alloc);
                self.read_reg(index, alloc);
            }
            _ => self.read_reg(op, alloc),
        }
    }

    /// Define a direct register operand.
    fn def_reg(&mut self, op: &X86ISelOperand, alloc: &HashMap<VReg, X86PReg>) {
        if let X86ISelOperand::VReg(v) = op {
            self.vreg_defs.push(*v);
        }
        match resolve_reg(op, alloc) {
            Resolved::Preg(p) => self.def_preg(p),
            Resolved::UnallocVReg(v) => self.unallocated.push(v),
            Resolved::NotAReg => {}
        }
    }

    /// Read AND define a direct register operand (in-place forms).
    fn read_def_reg(&mut self, op: &X86ISelOperand, alloc: &HashMap<VReg, X86PReg>) {
        if let X86ISelOperand::VReg(v) = op {
            self.vreg_reads.push(*v);
            self.vreg_defs.push(*v);
        }
        match resolve_reg(op, alloc) {
            Resolved::Preg(p) => {
                self.read_preg(p);
                self.def_preg(p);
            }
            Resolved::UnallocVReg(v) => self.unallocated.push(v),
            Resolved::NotAReg => {}
        }
    }
}

/// Shorthand for a malformed-operands classification error.
fn malformed(inst: &X86ISelInst, why: &str) -> String {
    format!(
        "opcode {:?} with operands {:?}: {why}",
        inst.opcode, inst.operands
    )
}

/// Detect the x86 dependency-breaking zero idiom: an `XorRR`/`Pxor` whose
/// register operands ALL resolve to one identical trackable physical register
/// — the tied 3-op `xor r, r, r` the unsigned Div/Rem lowering emits to clear
/// RDX/EDX, and the in-place 2-op `pxor x, x` vector-zero shape. The result
/// (and, for `XorRR`, every defined flag: CF=OF=SF=0, ZF=1, PF of zero) is
/// architecturally independent of the register's prior value — the hardware
/// consumes no bit of it (Intel SDM dependency-breaking idiom) — so the site
/// is a pure DEFINITION. Modeling the syntactic read here would falsely
/// fail-closed e.g. every unsigned div/rem reached after any call (RDX holds
/// only call taint until this very instruction defines it). Returns the
/// destination register to define; any other shape (distinct registers,
/// memory, unallocated `VReg`s, an untrackable register, or an inadmissible
/// operand count) returns `None` and keeps the exact read+tied
/// classification, so no discharge path opens for non-identical operands.
fn post_ra_zero_idiom_dst(inst: &X86ISelInst, alloc: &HashMap<VReg, X86PReg>) -> Option<X86PReg> {
    if !matches!(inst.opcode, X86Opcode::XorRR | X86Opcode::Pxor)
        || !matches!(inst.operands.len(), 2 | 3)
    {
        return None;
    }
    let mut regs = inst.operands.iter().map(|op| match resolve_reg(op, alloc) {
        Resolved::Preg(p) => Some(p),
        _ => None,
    });
    let dst = regs.next()??;
    loc_of(dst)?;
    regs.all(|reg| reg == Some(dst)).then_some(dst)
}

/// Classify a tied-ghost site: the destination `operands[0]` is read+written
/// by the hardware, the ghost `operands[1]` is NOT read by the encoder (it is
/// the obligation certificate), and both must be registers with tracked
/// locations.
fn classify_tied_site(
    inst: &X86ISelInst,
    alloc: &HashMap<VReg, X86PReg>,
    acc: &mut InstAccess,
) -> Result<(), String> {
    // Vreg-named capture: the tied destination is read AND written by the
    // hardware. The ghost `operands[1]` is NOT a hardware read (it is the
    // obligation certificate), so it carries no vreg-named access.
    if let X86ISelOperand::VReg(v) = &inst.operands[0] {
        acc.vreg_reads.push(*v);
        acc.vreg_defs.push(*v);
    }
    let dst = resolve_reg(&inst.operands[0], alloc);
    let ghost = resolve_reg(&inst.operands[1], alloc);
    match (dst, ghost) {
        (Resolved::Preg(d), Resolved::Preg(g)) => {
            if loc_of(d).is_none() || loc_of(g).is_none() {
                return Err(malformed(
                    inst,
                    "tied-form destination/ghost must be a trackable GPR/XMM register",
                ));
            }
            acc.read_preg(d);
            acc.def_preg(d);
            acc.tied = Some(TiedAccess {
                dst: d,
                ghost: g,
                read_mask: preg_read_mask(d),
            });
            Ok(())
        }
        (Resolved::UnallocVReg(v), _) | (_, Resolved::UnallocVReg(v)) => {
            // Already a hard violation on its own; the tied obligation is
            // skipped (there is no register to compare).
            acc.unallocated.push(v);
            Ok(())
        }
        (Resolved::NotAReg, _) | (_, Resolved::NotAReg) => Err(malformed(
            inst,
            "tied-form destination and ghost operands must both be registers",
        )),
    }
}

fn add_definite_flag_effect(acc: &mut InstAccess, defined: FlagMask, undefined: FlagMask) {
    debug_assert_eq!(defined & undefined, 0);
    acc.flags_def_mask |= defined;
    acc.flags_undef_mask |= undefined;
}

/// Exact arithmetic flags read by one x86 condition code.
fn condition_flag_mask(cc: X86CondCode) -> FlagMask {
    use X86CondCode::*;
    match cc {
        O | NO => FLAG_OF,
        B | AE => FLAG_CF,
        E | NE => FLAG_ZF,
        BE | A => FLAG_CF | FLAG_ZF,
        S | NS => FLAG_SF,
        P | NP => FLAG_PF,
        L | GE => FLAG_SF | FLAG_OF,
        LE | G => FLAG_ZF | FLAG_SF | FLAG_OF,
    }
}

/// Extract and validate the sole condition-code operand of Jcc/SETcc/CMOVcc.
/// The encoder requires one; accepting a missing/ambiguous condition here
/// would make the verifier reason about a different flag use than is emitted.
fn conditional_inst_flag_use(inst: &X86ISelInst) -> Result<FlagMask, String> {
    let mut codes = inst.operands.iter().filter_map(|operand| match operand {
        X86ISelOperand::CondCode(cc) => Some(*cc),
        _ => None,
    });
    let Some(cc) = codes.next() else {
        return Err(malformed(
            inst,
            "conditional instruction requires exactly one condition-code operand",
        ));
    };
    if codes.next().is_some() {
        return Err(malformed(
            inst,
            "conditional instruction has multiple condition-code operands",
        ));
    }
    Ok(condition_flag_mask(cc))
}

/// Architecturally effective immediate shift count after the x86 operand-size
/// mask. `None` is returned only when an already-invalid unallocated VReg keeps
/// the operand width unknowable; that instruction fails closed independently.
fn immediate_shift_count(
    inst: &X86ISelInst,
    alloc: &HashMap<VReg, X86PReg>,
) -> Result<Option<u8>, String> {
    let Some(X86ISelOperand::Imm(raw_count)) = inst.operands.last() else {
        return Err(malformed(
            inst,
            "shift-by-immediate instruction requires a trailing immediate count",
        ));
    };
    let count_mask = match resolve_reg(&inst.operands[0], alloc) {
        Resolved::Preg(reg) => match reg.encoding() {
            0..=15 => 0x3f,
            16..=31 => 0x1f,
            _ => {
                return Err(malformed(
                    inst,
                    "integer shift destination must be a 32- or 64-bit GPR",
                ));
            }
        },
        Resolved::UnallocVReg(_) => return Ok(None),
        Resolved::NotAReg => {
            return Err(malformed(
                inst,
                "integer shift destination must be a register",
            ));
        }
    };
    Ok(Some(((*raw_count as u64) & count_mask) as u8))
}

fn classify_immediate_shift_flags(
    inst: &X86ISelInst,
    alloc: &HashMap<VReg, X86PReg>,
    acc: &mut InstAccess,
) -> Result<(), String> {
    match immediate_shift_count(inst, alloc)? {
        // A zero effective count preserves every flag.
        Some(0) | None => {}
        // A count of one defines OF; every nonzero count defines CF/PF/ZF/SF
        // and leaves AF undefined.
        Some(1) => add_definite_flag_effect(
            acc,
            FLAG_CF | FLAG_PF | FLAG_ZF | FLAG_SF | FLAG_OF,
            FLAG_AF,
        ),
        // For larger effective counts OF is architecturally undefined.
        Some(_) => add_definite_flag_effect(
            acc,
            FLAG_CF | FLAG_PF | FLAG_ZF | FLAG_SF,
            FLAG_AF | FLAG_OF,
        ),
    }
    Ok(())
}

/// ROL by immediate: CF takes the last bit rotated out; OF is defined ONLY for a
/// 1-bit rotate and architecturally undefined for any other count; **SF, ZF, AF
/// and PF are UNAFFECTED**.
///
/// ⚑ THIS IS NOT THE SHL/SHR MODEL, which DEFINES PF/ZF/SF. Reusing
/// [`classify_immediate_shift_flags`] here would claim the rotate defines flags
/// it actually PRESERVES, so a later reader of ZF would be attributed to the
/// rotate instead of the compare that really set it. That is a WRONG-VALUE
/// model, not a conservative one, and it is precisely the sort of thing this
/// pass exists to catch.
fn classify_immediate_rotate_flags(
    inst: &X86ISelInst,
    alloc: &HashMap<VReg, X86PReg>,
    acc: &mut InstAccess,
) -> Result<(), String> {
    match immediate_shift_count(inst, alloc)? {
        // A zero effective count preserves every flag.
        Some(0) | None => {}
        // A 1-bit rotate defines CF and OF; the rest are untouched.
        Some(1) => add_definite_flag_effect(acc, FLAG_CF | FLAG_OF, 0),
        // Larger counts define CF; OF is architecturally undefined.
        Some(_) => add_definite_flag_effect(acc, FLAG_CF, FLAG_OF),
    }
    Ok(())
}

/// The exhaustive access model over the FINAL post-fixup stream.
///
/// The match is deliberately EXHAUSTIVE over `X86Opcode` with NO wildcard
/// arm: adding a new opcode is a compile error here, never a silent
/// "no access" classification. Returns `Err(detail)` for operand shapes the
/// model does not admit (fail-closed as malformed-operands).
pub(crate) fn classify_x86_post_ra_inst(
    inst: &X86ISelInst,
    alloc: &HashMap<VReg, X86PReg>,
    call_abi: X86CallAbi,
) -> Result<InstAccess, String> {
    use X86Opcode::*;
    let mut acc = InstAccess::default();
    let n = inst.operands.len();
    let is_call = matches!(inst.opcode, Call | CallR | CallM);
    match (is_call, &inst.call_result_regs) {
        (false, None) => {}
        (false, Some(_)) => {
            return Err(malformed(
                inst,
                "non-call instruction carries call-result register metadata",
            ));
        }
        (true, None) => {
            return Err(malformed(
                inst,
                "call is missing its exact result-register declaration",
            ));
        }
        (true, Some(regs)) => {
            let mut result_locs = Vec::with_capacity(regs.len());
            for &result in regs {
                let reg = result.reg;
                // These are the only result registers emitted by the current
                // x86 lowering boundary (scalar, i128, and <=2-eightbyte
                // aggregate returns). Width aliases are rejected: metadata is
                // expressed in canonical ABI registers, never operand widths.
                if !matches!(reg, RAX | RDX | XMM0 | XMM1) {
                    return Err(malformed(
                        inst,
                        "call-result metadata names a non-result ABI register",
                    ));
                }
                let abi_allows = match call_abi {
                    X86CallAbi::SystemV => {
                        X86_CALLER_SAVED_GPRS.contains(&reg) || (64..=79).contains(&reg.encoding())
                    }
                    X86CallAbi::WindowsX64 => {
                        WINDOWS_X64_CALLER_SAVED_GPRS.contains(&reg)
                            || (64..=69).contains(&reg.encoding())
                    }
                };
                if !abi_allows {
                    return Err(malformed(
                        inst,
                        "call-result metadata names a register preserved by the active ABI",
                    ));
                }
                let Some(loc) = loc_of(reg) else {
                    return Err(malformed(
                        inst,
                        "call-result metadata must name a trackable GPR/XMM register",
                    ));
                };
                let width_is_valid = if reg == RAX || reg == RDX {
                    matches!(result.defined_bits, 8 | 16 | 32 | 64)
                } else {
                    matches!(result.defined_bits, 16 | 32 | 64 | 128)
                };
                if !width_is_valid {
                    return Err(malformed(
                        inst,
                        "call-result metadata has an invalid defined-bit width for its register class",
                    ));
                }
                if result_locs
                    .iter()
                    .any(|entry: &CallResultLoc| entry.loc == loc)
                {
                    return Err(malformed(
                        inst,
                        "call-result metadata contains a duplicate register location",
                    ));
                }
                result_locs.push(CallResultLoc {
                    loc,
                    defined_bits: result.defined_bits,
                });
            }
            acc.call_result_locs = Some(result_locs);
        }
    }
    match inst.opcode {
        // --- Sym-propagating copies (exactly the fixup copy-opcode set). ---
        // Byte-lane transfer preserves the exact MovRR32 zero-extension and
        // MovssRR/MovsdRR partial-register merge semantics.
        MovRR | MovRR32 | MovssRR | MovsdRR | MovdqaRR => {
            if n != 2 {
                return Err(malformed(
                    inst,
                    "register copy must have exactly 2 operands",
                ));
            }
            // Vreg-named capture for the call-severed check: the copy reads
            // its source vreg's value and freshly defines its destination
            // vreg (the classification below is loc-level via lane_copy and
            // bypasses the capturing helpers).
            if let X86ISelOperand::VReg(v) = &inst.operands[1] {
                acc.vreg_reads.push(*v);
            }
            if let X86ISelOperand::VReg(v) = &inst.operands[0] {
                acc.vreg_defs.push(*v);
            }
            match (
                resolve_reg(&inst.operands[0], alloc),
                resolve_reg(&inst.operands[1], alloc),
            ) {
                (Resolved::Preg(d), Resolved::Preg(s)) => match (loc_of(d), loc_of(s)) {
                    (Some(dl), Some(sl)) => {
                        acc.read_preg(s);
                        let (read_mask, write_mask) = match inst.opcode {
                            X86Opcode::MovRR32 => (0x000f, GPR_LANE_MASK),
                            X86Opcode::MovssRR => (0x000f, 0x000f),
                            X86Opcode::MovsdRR => (0x00ff, 0x00ff),
                            _ => (preg_read_mask(s), preg_write_mask(d)),
                        };
                        acc.lane_copy = Some(LaneCopy {
                            dst: dl,
                            src: sl,
                            read_mask,
                            write_mask,
                        });
                        // A full-register XMM copy moves each byte lane
                        // verbatim: a clobber-tainted source lane is not a
                        // semantic use, it flows into the same destination
                        // lane (the `lane_copy` taint transfer is already
                        // exact). Scalar `MovssRR`/`MovsdRR` copies stay
                        // ordinary checked reads: their low lanes ARE the
                        // semantic scalar value.
                        if inst.opcode == X86Opcode::MovdqaRR
                            && (16..32).contains(&dl)
                            && (16..32).contains(&sl)
                        {
                            acc.xmm_lanewise_flow = Some(XmmLanewiseFlow {
                                dst: dl,
                                srcs: vec![sl],
                            });
                        }
                    }
                    _ => {
                        return Err(malformed(
                            inst,
                            "register copy operands must be trackable GPR/XMM registers",
                        ));
                    }
                },
                (Resolved::UnallocVReg(v), other) => {
                    acc.unallocated.push(v);
                    if let Resolved::UnallocVReg(v2) = other {
                        acc.unallocated.push(v2);
                    }
                }
                (Resolved::Preg(d), Resolved::UnallocVReg(v)) => {
                    // Source unknown: the destination still becomes SOME
                    // value — a fresh def keeps later syms honest.
                    acc.unallocated.push(v);
                    acc.def_preg(d);
                }
                _ => {
                    return Err(malformed(inst, "register copy operands must be registers"));
                }
            }
        }

        // --- Exchange. Register-register form swaps the two syms. The
        // memory form (`xchg reg, [mem]` — the ISel atomic-swap bridge shape,
        // pinned by codegen's `test_xchg_memory_isel_bridge_encodes_i64`)
        // reads AND freshly defines the register (its old value goes to
        // memory — memory value dataflow is untracked in v1) and reads the
        // address registers. ---
        Xchg => {
            if n != 2 {
                return Err(malformed(inst, "Xchg must have exactly 2 operands"));
            }
            let has_mem = inst.operands.iter().any(|op| {
                matches!(
                    op,
                    X86ISelOperand::MemAddr { .. } | X86ISelOperand::SibMemAddr { .. }
                )
            });
            if has_mem {
                for op in &inst.operands {
                    match op {
                        X86ISelOperand::MemAddr { .. } | X86ISelOperand::SibMemAddr { .. } => {
                            acc.read_reg_or_mem(op, alloc);
                        }
                        _ => acc.read_def_reg(op, alloc),
                    }
                }
            } else {
                // Vreg-named capture: an RR exchange reads AND redefines both
                // named vregs (each receives the other's value).
                for op in &inst.operands {
                    if let X86ISelOperand::VReg(v) = op {
                        acc.vreg_reads.push(*v);
                        acc.vreg_defs.push(*v);
                    }
                }
                match (
                    resolve_reg(&inst.operands[0], alloc),
                    resolve_reg(&inst.operands[1], alloc),
                ) {
                    (Resolved::Preg(a), Resolved::Preg(b)) => match (loc_of(a), loc_of(b)) {
                        (Some(al), Some(bl)) => {
                            acc.read_preg(a);
                            acc.read_preg(b);
                            acc.xchg = Some((al, bl));
                        }
                        _ => {
                            return Err(malformed(
                                inst,
                                "Xchg operands must be trackable GPR registers",
                            ));
                        }
                    },
                    (Resolved::UnallocVReg(v), _) | (_, Resolved::UnallocVReg(v)) => {
                        acc.unallocated.push(v);
                    }
                    _ => return Err(malformed(inst, "Xchg operands must be registers")),
                }
            }
        }

        // --- Two-address RR family (tied 3-op form or in-place 2-op form).
        // The folded packed rhs (a spilled XMM rhs folded to a stack MemAddr)
        // makes operands[2]/operands[1] legitimately memory. ---
        AddRR | SubRR | AdcRR | SbbRR | AndRR | OrRR | XorRR | ImulRR | Addsd | Subsd | Mulsd
        | Divsd | Andpd | Addss | Subss | Mulss | Divss | Andps | Pand | Pandn | Por | Pxor
        | Pcmpeqb | Pcmpeqw | Pcmpgtb | Pcmpgtw | Pcmpeqd | Pcmpgtd | Paddb | Paddw | Paddd
        | Psubb | Psubw | Psubd | Paddq | Psubq | Pmullw | Pmuludq | Punpcklbw | Punpckldq
        | Packuswb | Punpckhbw | Punpcklqdq | Pmulld | Psadbw | Pcmpeqq | Pcmpgtq | Addps
        | Subps | Mulps | Divps | Addpd | Subpd | Mulpd | Divpd | Minsd | Maxsd | Minss | Maxss
        | Cmpsd | Cmpss => {
            let (defined, undefined) = integer_alu_flag_effect(inst.opcode);
            add_definite_flag_effect(&mut acc, defined, undefined);
            if matches!(inst.opcode, AdcRR | SbbRR) {
                acc.flags_use_mask = FLAG_CF;
            }
            if let Some(dst) = post_ra_zero_idiom_dst(inst, alloc) {
                // `xor r, r` / `pxor x, x`: a pure definition. No prior-value
                // read exists to check (the flag effect above is exact — a
                // constant result defines constant flags), the def kills
                // exactly the ISA write mask, and the dst==ghost tied
                // obligation is vacuous (the general path discharges it via
                // `x86_regs_overlap` anyway).
                acc.def_preg(dst);
                // Vreg-named capture: the zero idiom freshly DEFINES its vreg
                // (and reads nothing — the hardware consumes no prior bit), so
                // it must un-sever it like any other def-by-name.
                if let X86ISelOperand::VReg(v) = &inst.operands[0] {
                    acc.vreg_defs.push(*v);
                }
            } else if post_ra_tied_lhs_index(inst) == Some(1) {
                classify_tied_site(inst, alloc, &mut acc)?;
                acc.read_reg_or_mem(&inst.operands[2], alloc);
            } else if n == 2 {
                acc.read_def_reg(&inst.operands[0], alloc);
                acc.read_reg_or_mem(&inst.operands[1], alloc);
            } else {
                return Err(malformed(
                    inst,
                    "two-address RR opcode must be the tied 3-operand or in-place 2-operand form",
                ));
            }
            // Packed BITWISE forms are byte-lane-wise (`dst[i] = f(dst[i],
            // src[i])`): a clobber-tainted input lane is garbage-flow, not a
            // semantic use — the scalar min/max/clamp sign-mask blends after
            // a float libcall route architectural upper-lane garbage through
            // them by design. Register the flow so the taint walk PROPAGATES
            // (union, no full-width-def launder) instead of failing the
            // read; every non-lane-wise packed op, scalar op, store, call
            // argument, and `Ret` result lane still checks its reads, so a
            // wrong routing still fails closed at its first semantic use.
            // The zero idiom (`pxor x, x`) is explicitly EXCLUDED: it is a
            // pure definition whose def must keep KILLING taint.
            if matches!(inst.opcode, Pand | Pandn | Por | Pxor)
                && post_ra_zero_idiom_dst(inst, alloc).is_none()
                && let Resolved::Preg(d) = resolve_reg(&inst.operands[0], alloc)
                && let Some(dl) = loc_of(d)
                && (16..32).contains(&dl)
            {
                // Two-address: the destination's own lanes are inputs.
                let mut srcs = vec![dl];
                let rhs_index = if post_ra_tied_lhs_index(inst) == Some(1) {
                    2
                } else {
                    1
                };
                if let Some(rhs) = inst.operands.get(rhs_index)
                    && let Resolved::Preg(s) = resolve_reg(rhs, alloc)
                    && let Some(sl) = loc_of(s)
                    && (16..32).contains(&sl)
                {
                    srcs.push(sl);
                }
                acc.xmm_lanewise_flow = Some(XmmLanewiseFlow { dst: dl, srcs });
            }
        }

        // --- ALU reg-imm family (tied 3-op [dst, ghost, imm] or in-place
        // 2-op [dst, imm]). The immediate carries no register dataflow. ---
        AddRI | SubRI | AndRI | OrRI | XorRI => {
            let (defined, undefined) = integer_alu_flag_effect(inst.opcode);
            add_definite_flag_effect(&mut acc, defined, undefined);
            if post_ra_tied_lhs_index(inst) == Some(1) {
                classify_tied_site(inst, alloc, &mut acc)?;
            } else if n == 2 {
                acc.read_def_reg(&inst.operands[0], alloc);
            } else {
                return Err(malformed(
                    inst,
                    "ALU reg-imm opcode must be the tied 3-operand or in-place 2-operand form",
                ));
            }
        }

        // --- Shift-by-immediate family (integer forms write EFLAGS; the
        // packed XMM forms touch no EFLAGS). Psllq/Psrlq are the i64-lane
        // siblings of Pslld/Psrld (same 0x73-group in-place XMM shift). ---
        ShlRI | ShrRI | SarRI | RolRI | Pslld | Psrld | Psrad | Psllq | Psrlq => {
            if post_ra_tied_lhs_index(inst) == Some(1) {
                classify_tied_site(inst, alloc, &mut acc)?;
            } else if n == 2 {
                acc.read_def_reg(&inst.operands[0], alloc);
            } else {
                return Err(malformed(
                    inst,
                    "shift-by-imm opcode must be the tied 3-operand or in-place 2-operand form",
                ));
            }
            if matches!(inst.opcode, ShlRI | ShrRI | SarRI) {
                classify_immediate_shift_flags(inst, alloc, &mut acc)?;
            } else if inst.opcode == RolRI {
                // Rotates have their OWN flag semantics — see the note there.
                classify_immediate_rotate_flags(inst, alloc, &mut acc)?;
            }
        }

        // --- Shift-by-CL family (implicit RCX-root read). ---
        ShlRR | ShrRR | SarRR => {
            // CL may be zero, in which case every flag is preserved. Therefore
            // no prior invalidity can be killed without value reasoning. AF is
            // undefined for a nonzero count and OF for counts greater than one.
            acc.flags_may_undef_mask = FLAG_AF | FLAG_OF;
            acc.read_preg(x86_64_regs::RCX);
            if post_ra_tied_lhs_index(inst) == Some(1) {
                classify_tied_site(inst, alloc, &mut acc)?;
            } else if n == 1 {
                acc.read_def_reg(&inst.operands[0], alloc);
            } else {
                return Err(malformed(
                    inst,
                    "shift-by-CL opcode must be the tied 2-operand or in-place 1-operand form",
                ));
            }
        }

        // --- Explicit-source unary (NEG writes EFLAGS; NOT does not). ---
        Neg | Not => {
            if inst.opcode == Neg {
                acc.flags_def_mask = FLAGS_ALL;
            }
            if post_ra_tied_lhs_index(inst) == Some(1) {
                classify_tied_site(inst, alloc, &mut acc)?;
            } else if n == 1 {
                acc.read_def_reg(&inst.operands[0], alloc);
            } else {
                return Err(malformed(
                    inst,
                    "unary opcode must be the tied 2-operand or in-place 1-operand form",
                ));
            }
        }

        // --- SSE4.1 lane insert (tied 4-op [dst, ghost, scalar, imm] or
        // in-place 3-op [dst, scalar, imm]). No EFLAGS. ---
        Pinsrd | Pinsrq => {
            if post_ra_tied_lhs_index(inst) == Some(1) {
                classify_tied_site(inst, alloc, &mut acc)?;
                acc.read_reg_or_mem(&inst.operands[2], alloc);
            } else if n == 3 {
                acc.read_def_reg(&inst.operands[0], alloc);
                acc.read_reg_or_mem(&inst.operands[1], alloc);
            } else {
                return Err(malformed(
                    inst,
                    "Pinsr opcode must be the tied 4-operand or in-place 3-operand form",
                ));
            }
        }

        // --- Simple in-place read+write forms. ---
        Inc | Dec => {
            if n == 0 {
                return Err(malformed(inst, "Inc/Dec requires a destination operand"));
            }
            acc.flags_def_mask = FLAGS_ALL & !FLAG_CF;
            acc.read_def_reg(&inst.operands[0], alloc);
        }
        Bswap => {
            if n == 0 {
                return Err(malformed(inst, "Bswap requires a destination operand"));
            }
            acc.read_def_reg(&inst.operands[0], alloc);
        }

        // --- Conditional move: dst is read+written (the not-taken lane keeps
        // the old dst), every other register operand is read, EFLAGS consumed.
        Cmovcc | Cmovcc32 => {
            if n == 0 {
                return Err(malformed(inst, "Cmovcc requires a destination operand"));
            }
            acc.flags_use_mask = conditional_inst_flag_use(inst)?;
            acc.read_def_reg(&inst.operands[0], alloc);
            for op in &inst.operands[1..] {
                acc.read_reg_or_mem(op, alloc);
            }
        }

        // --- Two-address reg-mem ALU (dst read+written, memory recursed). ---
        AddRM | SubRM | ImulRM | ImulRMSib => {
            if n == 0 {
                return Err(malformed(inst, "RM ALU requires a destination operand"));
            }
            let (defined, undefined) = integer_alu_flag_effect(inst.opcode);
            add_definite_flag_effect(&mut acc, defined, undefined);
            acc.read_def_reg(&inst.operands[0], alloc);
            for op in &inst.operands[1..] {
                acc.read_reg_or_mem(op, alloc);
            }
        }

        // --- SSE4.1 byte select (implicit XMM0 mask read). ---
        Pblendvb => {
            if n == 0 {
                return Err(malformed(inst, "Pblendvb requires a destination operand"));
            }
            acc.read_preg(XMM0);
            acc.read_def_reg(&inst.operands[0], alloc);
            for op in &inst.operands[1..] {
                acc.read_reg_or_mem(op, alloc);
            }
        }

        // --- Compare-and-exchange: RAX-root accumulator read+written; the
        // r/m operand (op0 when register-form) is read, and additionally
        // written only in the register form. ---
        Cmpxchg | Cmpxchg8 | Cmpxchg16 => {
            acc.flags_def_mask = FLAGS_ALL;
            acc.read_preg(RAX);
            acc.def_preg(RAX);
            let has_mem = inst.operands.iter().any(|op| {
                matches!(
                    op,
                    X86ISelOperand::MemAddr { .. } | X86ISelOperand::SibMemAddr { .. }
                )
            });
            for op in &inst.operands {
                acc.read_reg_or_mem(op, alloc);
            }
            if !has_mem {
                if n == 0 {
                    return Err(malformed(inst, "register-form Cmpxchg requires operands"));
                }
                acc.def_reg(&inst.operands[0], alloc);
            }
        }

        // --- Atomic RMW CAS-loop pseudos: the encoder's retry loop pins the
        // RAX-root accumulator and the R10-root scratch and zero-extends the
        // old value into dst (operands[0]); the value and memory operands are
        // read. dst's PRE-value is NOT read (a fresh def). ---
        AtomicRmwCasLoop | AtomicRmwCasLoop8 | AtomicRmwCasLoop16 => {
            if n == 0 {
                return Err(malformed(inst, "CAS-loop pseudo requires operands"));
            }
            acc.flags_def_mask = FLAGS_ALL;
            acc.def_reg(&inst.operands[0], alloc);
            acc.def_preg(RAX);
            acc.def_preg(x86_64_regs::R10);
            for op in &inst.operands[1..] {
                acc.read_reg_or_mem(op, alloc);
            }
        }

        // --- Implicit accumulator widen/divide/multiply cluster. ---
        Cdq | Cqo => {
            acc.read_preg(RAX);
            acc.def_preg(RDX);
        }
        Idiv | Div => {
            acc.flags_undef_mask = FLAGS_ALL;
            acc.read_preg(RAX);
            acc.read_preg(RDX);
            acc.def_preg(RAX);
            acc.def_preg(RDX);
            for op in &inst.operands {
                acc.read_reg_or_mem(op, alloc);
            }
        }
        Mul => {
            add_definite_flag_effect(&mut acc, FLAGS_MUL_DEFINED, FLAGS_MUL_UNDEFINED);
            acc.read_preg(RAX);
            acc.def_preg(RAX);
            acc.def_preg(RDX);
            for op in &inst.operands {
                acc.read_reg_or_mem(op, alloc);
            }
        }

        // --- Plain destination defs: operands[0] freshly defined,
        // operands[1..] read (memory recursed). ---
        MovRI | MovRM8 | MovRM16 | MovRM32 | MovRM | MovRMSib | MovsxdRMSib | MovRM32Sib
        | MovRM8Sib | VolatileMovRM8 | VolatileMovRM16 | VolatileMovRM32 | VolatileMovRM
        | VolatileMovssRM | VolatileMovsdRM | VolatileMovdquRM | VolatileMovdqaRM | Movzx
        | MovzxW | MovsxB | MovsxW | Movsx | Lea | LeaSib | LeaRip | MovRipRel | MovRipRelTlv
        | MovssRipRel | MovsdRipRel | MovsdRM | MovssRM | MovsdRMSib | MovssRMSib | MovdquRM
        | MovdqaRM | Sqrtsd | Sqrtss | Roundsd | Roundss | Cvtsi2sd | Cvtsd2si | Cvtsi2ss
        | Cvtss2si | Cvtsd2ss | Cvtss2sd | Cvttsd2si | Cvttss2si | MovdToXmm | MovdFromXmm
        | MovqToXmm | MovqFromXmm | Pshufd | Pmovmskb | Pextrd | Pextrq | V4I32MaskExtract
        | V2I64MaskExtract | V16I8MaskExtract | V8I16MaskExtract | V128BoolSelect => {
            if n == 0 {
                return Err(malformed(inst, "destination-def opcode requires operands"));
            }
            acc.def_reg(&inst.operands[0], alloc);
            for op in &inst.operands[1..] {
                acc.read_reg_or_mem(op, alloc);
            }
        }

        // --- Flag-consuming byte set. ---
        Setcc => {
            if n == 0 {
                return Err(malformed(inst, "Setcc requires a destination operand"));
            }
            acc.flags_use_mask = conditional_inst_flag_use(inst)?;
            acc.def_reg(&inst.operands[0], alloc);
        }

        // --- Flag-writing destination defs. ---
        ImulRRI | Bsf | Bsr | Tzcnt | Lzcnt | Popcnt => {
            if n == 0 {
                return Err(malformed(inst, "destination-def opcode requires operands"));
            }
            match inst.opcode {
                ImulRRI => {
                    let (defined, undefined) = integer_alu_flag_effect(inst.opcode);
                    add_definite_flag_effect(&mut acc, defined, undefined);
                }
                Bsf | Bsr => {
                    add_definite_flag_effect(&mut acc, FLAG_ZF, FLAGS_ALL & !FLAG_ZF);
                }
                Tzcnt | Lzcnt => {
                    let defined = FLAG_CF | FLAG_ZF;
                    add_definite_flag_effect(&mut acc, defined, FLAGS_ALL & !defined);
                }
                Popcnt => acc.flags_def_mask = FLAGS_ALL,
                _ => unreachable!(),
            }
            acc.def_reg(&inst.operands[0], alloc);
            for op in &inst.operands[1..] {
                acc.read_reg_or_mem(op, alloc);
            }
        }

        // --- Dynamic stack allocation pseudo (expanded during frame
        // lowering; classified honestly so a straggler cannot slip by). ---
        StackAlloc => {
            if n == 0 {
                return Err(malformed(inst, "StackAlloc requires a destination operand"));
            }
            acc.def_reg(&inst.operands[0], alloc);
            acc.read_preg(RSP);
            acc.def_preg(RSP);
            for op in &inst.operands[1..] {
                acc.read_reg_or_mem(op, alloc);
            }
        }

        // --- Pure flag producers: all register operands read, EFLAGS
        // written, no register defs. ---
        CmpRR | CmpRI | CmpRI8 | CmpRM | TestRR | TestRI | TestRM | Ucomisd | Ucomiss | Ptest
        | BtRI => {
            match inst.opcode {
                CmpRR | CmpRI | CmpRI8 | CmpRM | Ucomisd | Ucomiss | Ptest => {
                    acc.flags_def_mask = FLAGS_ALL;
                }
                TestRR | TestRI | TestRM => {
                    add_definite_flag_effect(&mut acc, FLAGS_LOGIC_DEFINED, FLAG_AF);
                }
                BtRI => {
                    add_definite_flag_effect(
                        &mut acc,
                        FLAG_CF,
                        FLAG_PF | FLAG_AF | FLAG_SF | FLAG_OF,
                    );
                }
                _ => unreachable!(),
            }
            for op in &inst.operands {
                acc.read_reg_or_mem(op, alloc);
            }
        }

        // --- Stores: value register + address registers read, no defs. ---
        MovMR8 | MovMR16 | MovMR32 | MovMR | MovMRSib | MovMR32Sib | MovMR8Sib | MovsdMR
        | MovssMR | MovdquMR | MovdqaMR | VolatileMovMR8 | VolatileMovMR16 | VolatileMovMR32
        | VolatileMovMR | VolatileMovssMR | VolatileMovsdMR | VolatileMovdquMR
        | VolatileMovdqaMR => {
            for op in &inst.operands {
                acc.read_reg_or_mem(op, alloc);
            }
        }

        // --- Stack push/pop (implicit RSP update). ---
        Push => {
            acc.read_preg(RSP);
            acc.def_preg(RSP);
            for op in &inst.operands {
                acc.read_reg_or_mem(op, alloc);
            }
        }
        Pop => {
            if n == 0 {
                return Err(malformed(inst, "Pop requires a destination operand"));
            }
            acc.read_preg(RSP);
            acc.def_preg(RSP);
            acc.def_reg(&inst.operands[0], alloc);
        }

        // --- Control flow. Ret's sig-derived return-register reads are
        // added by the DRIVER (`check_x86_post_ra_dataflow_with_abi`), which
        // owns the function signature this per-inst classifier cannot see —
        // the former "deliberate v1 miss" is closed there. Branch
        // displacements are provisional Imm values until encode — no
        // register dataflow. ---
        Jmp | Ret | Ud2 => {}
        // Indirect jump-table dispatch: unlike direct Jmp, JmpR READS its target
        // register (operands[0]) and defines nothing. Its CFG successors (all
        // table targets ∪ default) live on `block.successors`, set by the ISel,
        // so the transfer is transparent to the successor-based dataflow fixpoint.
        JmpR => {
            for op in &inst.operands {
                acc.read_reg_or_mem(op, alloc);
            }
        }
        Jcc => {
            acc.flags_use_mask = conditional_inst_flag_use(inst)?;
        }

        // --- Calls: argument registers read (from the instruction's
        // call_arg_regs implicit-use list) at their DECLARED per-argument
        // width; the transfer applies exact metadata-declared result defs +
        // ABI caller-saved clobbers. ---
        //
        // The width matters: SysV/Win64 define only the LOW bytes of a
        // narrow argument's register — the caller owes no zero/sign-
        // extension (a 1-byte fieldless enum such as `atomic::Ordering`
        // arrives as plain i8; LLVM ground truth), and both LLVM-compiled
        // and this backend's callees consume lane width only. Modeling every
        // argument as a full 8-byte read raised false read-of-call-clobbered
        // positives whenever arg setup legitimately defined only the
        // argument's own lanes after an earlier call (the REGALLOC-063
        // narrow-arg-after-call FP, 2026-07-13). The lowering records the
        // exact source width per register with full carrier width as its
        // conservative default, so a WIDE argument whose upper lanes carry
        // call taint still fails closed. Width metadata is schema-checked
        // here exactly like the result side: an inadmissible width is
        // malformed (fail-closed), never a silently weakened read.
        Call | CallR | CallM => {
            for arg in &inst.call_arg_regs {
                let width_is_valid = match arg.reg.encoding() {
                    // GPR carriers (any alias width).
                    0..=63 => matches!(arg.read_bits, 8 | 16 | 32 | 64),
                    // XMM carriers.
                    64..=79 => matches!(arg.read_bits, 16 | 32 | 64 | 128),
                    _ => false,
                };
                if !width_is_valid {
                    return Err(malformed(
                        inst,
                        "call-argument metadata has an invalid read-bit width for its register class",
                    ));
                }
                acc.read_preg_low_bits(arg.reg, arg.read_bits);
            }
            match inst.opcode {
                CallR => {
                    if n == 0 {
                        return Err(malformed(inst, "CallR requires a callee operand"));
                    }
                    acc.read_reg(&inst.operands[0], alloc);
                }
                CallM => {
                    for op in &inst.operands {
                        acc.read_reg_or_mem(op, alloc);
                    }
                }
                _ => {}
            }
        }

        // --- Neutral (no register dataflow). ---
        Nop | NopMulti | Mfence => {}

        // --- A Phi must never survive past regalloc (x86 lowers phis
        // pre-RA); one reaching the final stream is corruption. ---
        Phi => {
            return Err(malformed(
                inst,
                "Phi must not survive to the post-RA stream",
            ));
        }

        // --- Proof-only guard carriers (expanded pre-RA; an honest read-only
        // classification means a straggler cannot cause a false positive). ---
        TrapBoundsCheckExact | TrapNullIfZeroExact | TrapDivZeroExact | TrapShiftRangeExact => {
            acc.flags_def_mask = FLAGS_ALL;
            for op in &inst.operands {
                acc.read_reg_or_mem(op, alloc);
            }
        }
    }
    refine_scalar_xmm_lane_accesses(inst.opcode, &mut acc);
    Ok(acc)
}

// ---------------------------------------------------------------------------
// CFG-wide caller-clobber lane dataflow
// ---------------------------------------------------------------------------

type CallTaintState = [u16; NUM_LOCS];

// EFLAGS uses the otherwise-unused final cell of CallTaintState as a compact
// per-flag CFG provenance lattice. `0` is unreachable (the fixed-point bottom),
// so an unreachable cycle cannot manufacture a valid flag definition.
// Reachable predecessor states meet by bitwise OR: an undefined or
// call-clobbered provenance bit for any consumed flag poisons the join until a
// real definition of that exact flag kills both provenance bits.
const FLAGS_REACHABLE: u16 = 1 << 0;
const FLAGS_UNDEFINED_SHIFT: u32 = 1;
const FLAGS_CALL_CLOBBERED_SHIFT: u32 = 7;

const fn encoded_undefined_flags(mask: FlagMask) -> u16 {
    mask << FLAGS_UNDEFINED_SHIFT
}

const fn encoded_call_clobbered_flags(mask: FlagMask) -> u16 {
    mask << FLAGS_CALL_CLOBBERED_SHIFT
}

fn undefined_flags(state: u16) -> FlagMask {
    (state >> FLAGS_UNDEFINED_SHIFT) & FLAGS_ALL
}

fn call_clobbered_flags(state: u16) -> FlagMask {
    (state >> FLAGS_CALL_CLOBBERED_SHIFT) & FLAGS_ALL
}

fn flag_mask_label(mask: FlagMask) -> String {
    [
        (FLAG_CF, "CF"),
        (FLAG_PF, "PF"),
        (FLAG_AF, "AF"),
        (FLAG_ZF, "ZF"),
        (FLAG_SF, "SF"),
        (FLAG_OF, "OF"),
    ]
    .into_iter()
    .filter_map(|(bit, name)| (mask & bit != 0).then_some(name))
    .collect::<Vec<_>>()
    .join("|")
}

fn transfer_call_taint(state: &mut CallTaintState, acc: &InstAccess, call_abi: X86CallAbi) {
    let reachable = state[FLAGS_LOC as usize] & FLAGS_REACHABLE != 0;
    if !reachable {
        return;
    }

    if let Some(copy) = acc.lane_copy {
        let copied = state[copy.src as usize] & copy.read_mask;
        let dst = &mut state[copy.dst as usize];
        *dst = (*dst & !copy.write_mask) | copied;
    } else if let Some((a, b)) = acc.xchg {
        state.swap(a as usize, b as usize);
    } else if let Some(flow) = &acc.xmm_lanewise_flow {
        // Packed lane-wise bitwise op: destination lane `i` is a pure
        // function of its register inputs' lane `i`, so the exact post-state
        // taint is the UNION of the inputs' taints — the full-width def must
        // NOT launder clobber garbage clean (the read check was suppressed
        // for exactly these locations).
        let mut taint = 0u16;
        for &src in &flow.srcs {
            taint |= state[src as usize];
        }
        state[flow.dst as usize] = taint;
    } else {
        for def in &acc.lane_defs {
            state[def.loc as usize] &= !def.mask;
        }
    }

    if let Some(results) = &acc.call_result_locs {
        let caller_saved_gprs: &[X86PReg] = match call_abi {
            X86CallAbi::SystemV => &X86_CALLER_SAVED_GPRS,
            X86CallAbi::WindowsX64 => &WINDOWS_X64_CALLER_SAVED_GPRS,
        };
        for &reg in caller_saved_gprs {
            if let Some(loc) = loc_of(reg) {
                state[loc as usize] = GPR_LANE_MASK;
            }
        }
        let caller_saved_xmm_count = match call_abi {
            X86CallAbi::SystemV => 16,
            X86CallAbi::WindowsX64 => 6,
        };
        for xmm in 0..caller_saved_xmm_count {
            if let Some(loc) = loc_of(X86PReg::new(64 + xmm)) {
                state[loc as usize] = XMM_LANE_MASK;
            }
        }
        for result in results {
            state[result.loc as usize] &= !low_bits_lane_mask(result.defined_bits);
        }
        state[FLAGS_LOC as usize] = FLAGS_REACHABLE | encoded_call_clobbered_flags(FLAGS_ALL);
    }

    debug_assert_eq!(
        acc.flags_def_mask & (acc.flags_undef_mask | acc.flags_may_undef_mask),
        0
    );
    debug_assert_eq!(acc.flags_undef_mask & acc.flags_may_undef_mask, 0);
    let flags = &mut state[FLAGS_LOC as usize];
    let definitely_defined = encoded_undefined_flags(acc.flags_def_mask)
        | encoded_call_clobbered_flags(acc.flags_def_mask);
    *flags &= !definitely_defined;

    // A definitely-undefined result replaces earlier call-clobber provenance;
    // a maybe-undefined result (variable shift) must preserve it because the
    // zero-count path preserves the old flag.
    *flags &= !encoded_call_clobbered_flags(acc.flags_undef_mask);
    *flags |= encoded_undefined_flags(acc.flags_undef_mask | acc.flags_may_undef_mask);
}

/// Apply the register definitions performed by the Itanium unwinder while
/// transferring control from a protected call site to its landing pad.
///
/// This is deliberately an edge transfer, not a block-entry exemption: an
/// ordinary CFG predecessor of the same block must retain its call taint. The
/// unwinder defines the full exception-pointer register RAX and the low 32-bit
/// selector in EDX; no other caller-saved register or EFLAGS is blessed.
fn transfer_x86_eh_edge_defs(state: &mut CallTaintState) {
    if let Some(rax) = loc_of(RAX) {
        state[rax as usize] &= !low_bits_lane_mask(64);
    }
    if let Some(rdx) = loc_of(RDX) {
        state[rdx as usize] &= !low_bits_lane_mask(32);
    }
}

fn merge_call_taint_predecessors(
    state: &mut CallTaintState,
    outputs: &HashMap<Block, CallTaintState>,
    eh_outputs: &HashMap<(Block, Block), CallTaintState>,
    normal_edges: &HashSet<(Block, Block)>,
    block_preds: &[Block],
    dst: Block,
) {
    for &pred in block_preds {
        let edge = (pred, dst);
        if normal_edges.contains(&edge)
            && let Some(edge_state) = outputs.get(&pred)
        {
            for (dst_lane, src_lane) in state.iter_mut().zip(edge_state) {
                *dst_lane |= *src_lane;
            }
        }
        if let Some(edge_state) = eh_outputs.get(&edge) {
            for (dst_lane, src_lane) in state.iter_mut().zip(edge_state) {
                *dst_lane |= *src_lane;
            }
        }
    }
}

/// Resolve block-granular EH metadata to the exact protected call instruction.
///
/// `EhCallSite` currently names a call block, not an instruction. Sound
/// exceptional-edge state therefore requires exactly one eligible machine call
/// in that block. Zero or multiple calls are ambiguous and fail closed; a
/// future per-instruction call-site identity can relax this without guessing.
fn unique_x86_eh_calls(
    func: &X86ISelFunction,
) -> Result<HashMap<Block, (usize, Block)>, Vec<String>> {
    let mut protected = HashMap::new();
    let mut seen_edges = HashSet::new();
    let mut errors = Vec::new();

    for site in &func.eh_info.call_sites {
        let edge = (site.call_block, site.landing_pad_block);
        if !seen_edges.insert(edge) {
            errors.push(format!(
                "duplicate EH call-site edge {} -> {}",
                site.call_block.0, site.landing_pad_block.0
            ));
            continue;
        }
        if protected.contains_key(&site.call_block) {
            errors.push(format!(
                "EH call block {} has multiple call-site records; block-granular metadata cannot identify one protected transfer",
                site.call_block.0
            ));
            continue;
        }
        let Some(block) = func.blocks.get(&site.call_block) else {
            errors.push(format!(
                "EH call site names missing call block {}",
                site.call_block.0
            ));
            continue;
        };
        if !block.successors.contains(&site.landing_pad_block) {
            errors.push(format!(
                "EH call-site edge {} -> {} is absent from successor metadata",
                site.call_block.0, site.landing_pad_block.0
            ));
            continue;
        }
        let calls: Vec<_> = block
            .insts
            .iter()
            .enumerate()
            .filter_map(|(idx, inst)| {
                matches!(
                    inst.opcode,
                    X86Opcode::Call | X86Opcode::CallR | X86Opcode::CallM
                )
                .then_some(idx)
            })
            .collect();
        let [call_idx] = calls.as_slice() else {
            errors.push(format!(
                "EH call block {} contains {} eligible calls; exactly one is required by block-granular call-site metadata",
                site.call_block.0,
                calls.len()
            ));
            continue;
        };
        protected.insert(site.call_block, (*call_idx, site.landing_pad_block));
    }

    if errors.is_empty() {
        Ok(protected)
    } else {
        Err(errors)
    }
}

/// Least fixed point of "may still contain call-clobbered bytes" at every
/// block entry. Meet is bitwise OR: a read is unsafe if any predecessor path
/// can reach it with a clobbered lane. Definitions kill exactly the lanes the
/// ISA overwrites; copies propagate source taint and preserve untouched lanes.
fn call_taint_block_entries(
    func: &X86ISelFunction,
    alloc: &HashMap<VReg, X86PReg>,
    call_abi: X86CallAbi,
) -> Result<HashMap<Block, CallTaintState>, Vec<String>> {
    let entry_block = func.block_order.first().copied();
    let protected_calls = unique_x86_eh_calls(func)?;
    let exceptional_edges: HashSet<(Block, Block)> = protected_calls
        .iter()
        .map(|(&src, &(_, dst))| (src, dst))
        .collect();
    let mut normal_edges = HashSet::new();
    let mut preds: HashMap<Block, Vec<Block>> = func
        .block_order
        .iter()
        .copied()
        .map(|block| (block, Vec::new()))
        .collect();
    for &src in &func.block_order {
        let Some(block) = func.blocks.get(&src) else {
            continue;
        };
        let explicit_normal_targets: HashSet<Block> = block
            .insts
            .iter()
            .flat_map(|inst| inst.operands.iter())
            .filter_map(|operand| match operand {
                X86ISelOperand::Block(target) => Some(*target),
                _ => None,
            })
            .collect();
        for &dst in &block.successors {
            if let Some(dst_preds) = preds.get_mut(&dst) {
                dst_preds.push(src);
            }
            let edge = (src, dst);
            // Successors are set-valued, so a malformed Invoke can collapse
            // its explicit normal branch and exceptional transfer onto this
            // same pair. A protected pair is exceptional by default, but an
            // encoded Block target proves an ordinary transfer exists too;
            // retain both states and meet them independently below.
            if !exceptional_edges.contains(&edge) || explicit_normal_targets.contains(&dst) {
                normal_edges.insert(edge);
            }
        }
    }

    let mut outputs: HashMap<Block, CallTaintState> = func
        .block_order
        .iter()
        .copied()
        .map(|block| (block, [0; NUM_LOCS]))
        .collect();
    let mut eh_outputs: HashMap<(Block, Block), CallTaintState> = protected_calls
        .iter()
        .map(|(&src, &(_, dst))| ((src, dst), [0; NUM_LOCS]))
        .collect();
    loop {
        let mut changed = false;
        for &block_id in &func.block_order {
            let mut state = [0; NUM_LOCS];
            if Some(block_id) == entry_block {
                state[FLAGS_LOC as usize] = FLAGS_REACHABLE | encoded_undefined_flags(FLAGS_ALL);
            }
            if let Some(block_preds) = preds.get(&block_id) {
                merge_call_taint_predecessors(
                    &mut state,
                    &outputs,
                    &eh_outputs,
                    &normal_edges,
                    block_preds,
                    block_id,
                );
            }
            if let Some(block) = func.blocks.get(&block_id) {
                for (inst_idx, inst) in block.insts.iter().enumerate() {
                    if let Ok(acc) = classify_x86_post_ra_inst(inst, alloc, call_abi) {
                        transfer_call_taint(&mut state, &acc, call_abi);
                    }
                    if let Some(&(protected_idx, landing_pad)) = protected_calls.get(&block_id)
                        && inst_idx == protected_idx
                    {
                        let mut exceptional_state = state;
                        transfer_x86_eh_edge_defs(&mut exceptional_state);
                        let edge = (block_id, landing_pad);
                        if eh_outputs.get(&edge) != Some(&exceptional_state) {
                            eh_outputs.insert(edge, exceptional_state);
                            changed = true;
                        }
                    }
                }
            }
            if outputs.get(&block_id) != Some(&state) {
                outputs.insert(block_id, state);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let mut entries = HashMap::with_capacity(func.block_order.len());
    for &block_id in &func.block_order {
        let mut state = [0; NUM_LOCS];
        if Some(block_id) == entry_block {
            state[FLAGS_LOC as usize] = FLAGS_REACHABLE | encoded_undefined_flags(FLAGS_ALL);
        }
        if let Some(block_preds) = preds.get(&block_id) {
            merge_call_taint_predecessors(
                &mut state,
                &outputs,
                &eh_outputs,
                &normal_edges,
                block_preds,
                block_id,
            );
        }
        entries.insert(block_id, state);
    }
    Ok(entries)
}

// ---------------------------------------------------------------------------
// CFG-wide vreg-named call-severed dataflow (the #66 net)
// ---------------------------------------------------------------------------

/// Deterministically-ordered set of vregs whose caller-saved register home has
/// been clobbered by a call since their last def-by-name.
type SeveredSet = std::collections::BTreeSet<VReg>;

/// The trackable ROOT locations a call clobbers under `call_abi` — exactly the
/// sets [`transfer_call_taint`] havocs, so the vreg-named net and the lane
/// taint agree on what a call destroys.
fn caller_saved_locs(call_abi: X86CallAbi) -> HashSet<u8> {
    let mut locs = HashSet::new();
    let caller_saved_gprs: &[X86PReg] = match call_abi {
        X86CallAbi::SystemV => &X86_CALLER_SAVED_GPRS,
        X86CallAbi::WindowsX64 => &WINDOWS_X64_CALLER_SAVED_GPRS,
    };
    for &reg in caller_saved_gprs {
        if let Some(loc) = loc_of(reg) {
            locs.insert(loc);
        }
    }
    let caller_saved_xmm_count = match call_abi {
        X86CallAbi::SystemV => 16,
        X86CallAbi::WindowsX64 => 6,
    };
    for xmm in 0..caller_saved_xmm_count {
        if let Some(loc) = loc_of(X86PReg::new(64 + xmm)) {
            locs.insert(loc);
        }
    }
    locs
}

/// The vregs whose allocated home is a caller-saved location, with that home
/// location — the only vregs a call can sever. Sorted for determinism.
fn caller_saved_homed_vregs(
    alloc: &HashMap<VReg, X86PReg>,
    call_abi: X86CallAbi,
) -> Vec<(VReg, u8)> {
    let clobbered = caller_saved_locs(call_abi);
    let mut homed: Vec<(VReg, u8)> = alloc
        .iter()
        .filter_map(|(&vreg, &preg)| {
            let loc = loc_of(preg)?;
            clobbered.contains(&loc).then_some((vreg, loc))
        })
        .collect();
    homed.sort();
    homed
}

/// Transfer one classified instruction through the severed domain.
///
/// Defs-by-name un-sever (the vreg's home holds a fresh value OF the vreg). A
/// call severs every caller-saved-homed vreg EXCEPT those homed at a declared
/// result location: the call DEFINES those lanes, which is exactly the
/// coalesced call-result pattern (`v` allocated onto RAX with the bridge copy
/// coalesced away) — the lane taint governs those locations, same as
/// [`transfer_call_taint`]'s result-loc kill.
fn transfer_call_severed(
    severed: &mut SeveredSet,
    acc: &InstAccess,
    caller_saved_homed: &[(VReg, u8)],
) {
    for v in &acc.vreg_defs {
        severed.remove(v);
    }
    if let Some(results) = &acc.call_result_locs {
        for &(vreg, home_loc) in caller_saved_homed {
            if results.iter().any(|r| r.loc == home_loc) {
                severed.remove(&vreg);
            } else {
                severed.insert(vreg);
            }
        }
    }
}

/// Least fixed point of "this vreg's caller-saved home was clobbered by a call
/// after its last def-by-name" at every block entry. Meet is set UNION: a read
/// is unsafe if any reachable predecessor path severs it. Reachability is
/// taken from the lane-taint entries (computed first over the same CFG), so an
/// unreachable block cannot manufacture severs into live code. The EH edge
/// snapshots the post-call severed state unchanged: the unwinder's RAX/EDX
/// writes are physical-register events, never a def OF a named vreg.
fn call_severed_vregs_block_entries(
    func: &X86ISelFunction,
    alloc: &HashMap<VReg, X86PReg>,
    call_abi: X86CallAbi,
    taint_entries: &HashMap<Block, CallTaintState>,
) -> Result<HashMap<Block, SeveredSet>, Vec<String>> {
    let entry_block = func.block_order.first().copied();
    let caller_saved_homed = caller_saved_homed_vregs(alloc, call_abi);
    let protected_calls = unique_x86_eh_calls(func)?;
    let exceptional_edges: HashSet<(Block, Block)> = protected_calls
        .iter()
        .map(|(&src, &(_, dst))| (src, dst))
        .collect();
    let reachable: HashSet<Block> = func
        .block_order
        .iter()
        .copied()
        .filter(|b| {
            Some(*b) == entry_block
                || taint_entries
                    .get(b)
                    .is_some_and(|s| s[FLAGS_LOC as usize] & FLAGS_REACHABLE != 0)
        })
        .collect();

    let mut normal_edges = HashSet::new();
    let mut preds: HashMap<Block, Vec<Block>> = func
        .block_order
        .iter()
        .copied()
        .map(|block| (block, Vec::new()))
        .collect();
    for &src in &func.block_order {
        let Some(block) = func.blocks.get(&src) else {
            continue;
        };
        let explicit_normal_targets: HashSet<Block> = block
            .insts
            .iter()
            .flat_map(|inst| inst.operands.iter())
            .filter_map(|operand| match operand {
                X86ISelOperand::Block(target) => Some(*target),
                _ => None,
            })
            .collect();
        for &dst in &block.successors {
            if let Some(dst_preds) = preds.get_mut(&dst) {
                dst_preds.push(src);
            }
            let edge = (src, dst);
            if !exceptional_edges.contains(&edge) || explicit_normal_targets.contains(&dst) {
                normal_edges.insert(edge);
            }
        }
    }

    let mut outputs: HashMap<Block, SeveredSet> = func
        .block_order
        .iter()
        .copied()
        .map(|block| (block, SeveredSet::new()))
        .collect();
    let mut eh_outputs: HashMap<(Block, Block), SeveredSet> = protected_calls
        .iter()
        .map(|(&src, &(_, dst))| ((src, dst), SeveredSet::new()))
        .collect();
    loop {
        let mut changed = false;
        for &block_id in &func.block_order {
            if !reachable.contains(&block_id) {
                continue;
            }
            let mut state = SeveredSet::new();
            if let Some(block_preds) = preds.get(&block_id) {
                for &pred in block_preds {
                    if !reachable.contains(&pred) {
                        continue;
                    }
                    let edge = (pred, block_id);
                    if normal_edges.contains(&edge)
                        && let Some(edge_state) = outputs.get(&pred)
                    {
                        state.extend(edge_state.iter().copied());
                    }
                    if let Some(edge_state) = eh_outputs.get(&edge) {
                        state.extend(edge_state.iter().copied());
                    }
                }
            }
            if let Some(block) = func.blocks.get(&block_id) {
                for (inst_idx, inst) in block.insts.iter().enumerate() {
                    if let Ok(acc) = classify_x86_post_ra_inst(inst, alloc, call_abi) {
                        transfer_call_severed(&mut state, &acc, &caller_saved_homed);
                    }
                    if let Some(&(protected_idx, landing_pad)) = protected_calls.get(&block_id)
                        && inst_idx == protected_idx
                    {
                        let edge = (block_id, landing_pad);
                        if eh_outputs.get(&edge) != Some(&state) {
                            eh_outputs.insert(edge, state.clone());
                            changed = true;
                        }
                    }
                }
            }
            if outputs.get(&block_id) != Some(&state) {
                outputs.insert(block_id, state);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let mut entries = HashMap::with_capacity(func.block_order.len());
    for &block_id in &func.block_order {
        let mut state = SeveredSet::new();
        if let Some(block_preds) = preds.get(&block_id) {
            for &pred in block_preds {
                if !reachable.contains(&pred) {
                    continue;
                }
                let edge = (pred, block_id);
                if normal_edges.contains(&edge)
                    && let Some(edge_state) = outputs.get(&pred)
                {
                    state.extend(edge_state.iter().copied());
                }
                if let Some(edge_state) = eh_outputs.get(&edge) {
                    state.extend(edge_state.iter().copied());
                }
            }
        }
        entries.insert(block_id, state);
    }
    Ok(entries)
}

fn block_local_symbolic_state() -> SymbolicState {
    core::array::from_fn(|loc| {
        core::array::from_fn(|lane| Sym::BlockIn {
            loc: loc as u8,
            lane: lane as u8,
        })
    })
}

fn write_symbolic_def_lanes(state: &mut SymbolicState, def: LaneAccess, inst: u32) {
    for (lane, term) in state[def.loc as usize].iter_mut().enumerate() {
        if def.mask & (1u16 << lane) != 0 {
            *term = Sym::Def {
                inst,
                loc: def.loc,
                lane: lane as u8,
            };
        }
    }
}

fn write_symbolic_clobber_lanes(state: &mut SymbolicState, loc: u8, mask: u16, inst: u32) {
    for (lane, term) in state[loc as usize].iter_mut().enumerate() {
        if mask & (1u16 << lane) != 0 {
            *term = Sym::CallClobber {
                inst,
                loc,
                lane: lane as u8,
            };
        }
    }
}

/// Transfer one instruction through the block-local, byte-lane symbolic
/// identity domain used by tied-operand validation.
///
/// The source root is snapshotted before a copy so overlapping aliases remain
/// well-defined. `MovssRR`/`MovsdRR` replace only their low 4/8 destination
/// bytes and preserve the rest; they can therefore discharge only a scalar
/// tied use of no greater width. `MovRR32` copies four bytes and gives the
/// zero-extended upper bytes fresh definition identities, so it cannot certify
/// a 64-bit ghost unless those upper bytes are independently proven equal.
fn transfer_symbolic_state(
    state: &mut SymbolicState,
    acc: &InstAccess,
    call_abi: X86CallAbi,
    inst: u32,
) {
    if let Some(copy) = acc.lane_copy {
        let source = state[copy.src as usize];
        for lane in 0..SYMBOLIC_LANES {
            let bit = 1u16 << lane;
            if copy.write_mask & bit == 0 {
                continue;
            }
            state[copy.dst as usize][lane] = if copy.read_mask & bit != 0 {
                source[lane]
            } else {
                Sym::Def {
                    inst,
                    loc: copy.dst,
                    lane: lane as u8,
                }
            };
        }
    } else if let Some((a, b)) = acc.xchg {
        state.swap(a as usize, b as usize);
    } else {
        for &def in &acc.lane_defs {
            write_symbolic_def_lanes(state, def, inst);
        }
    }

    if let Some(results) = &acc.call_result_locs {
        let caller_saved_gprs: &[X86PReg] = match call_abi {
            X86CallAbi::SystemV => &X86_CALLER_SAVED_GPRS,
            X86CallAbi::WindowsX64 => &WINDOWS_X64_CALLER_SAVED_GPRS,
        };
        for &reg in caller_saved_gprs {
            if let Some(loc) = loc_of(reg) {
                write_symbolic_clobber_lanes(state, loc, GPR_LANE_MASK, inst);
            }
        }
        let caller_saved_xmm_count = match call_abi {
            X86CallAbi::SystemV => 16,
            X86CallAbi::WindowsX64 => 6,
        };
        for xmm in 0..caller_saved_xmm_count {
            if let Some(loc) = loc_of(X86PReg::new(64 + xmm)) {
                write_symbolic_clobber_lanes(state, loc, XMM_LANE_MASK, inst);
            }
        }
        for result in results {
            write_symbolic_def_lanes(
                state,
                LaneAccess {
                    loc: result.loc,
                    mask: low_bits_lane_mask(result.defined_bits),
                },
                inst,
            );
        }
    }
}

fn first_tied_lane_mismatch(
    state: &SymbolicState,
    dst: u8,
    ghost: u8,
    read_mask: u16,
) -> Option<(usize, Sym, Sym)> {
    (0..SYMBOLIC_LANES).find_map(|lane| {
        if read_mask & (1u16 << lane) == 0 {
            return None;
        }
        let dst_sym = state[dst as usize][lane];
        let ghost_sym = state[ghost as usize][lane];
        (dst_sym != ghost_sym).then_some((lane, dst_sym, ghost_sym))
    })
}

// ---------------------------------------------------------------------------
// Per-block symbolic copy-flow + CFG-wide call-taint driver
// ---------------------------------------------------------------------------

/// Run the symbolic copy-flow and CFG-wide lane-aware call-clobber checks over
/// one FINAL post-fixup function. Pure and side-effect-free; [`evaluate`]
/// handles mode/telemetry.
pub fn check_x86_post_ra_dataflow(
    func: &X86ISelFunction,
    alloc: &HashMap<VReg, X86PReg>,
) -> Vec<PostRaDataflowViolation> {
    check_x86_post_ra_dataflow_with_abi(func, alloc, X86CallAbi::SystemV)
}

pub fn check_x86_post_ra_dataflow_with_abi(
    func: &X86ISelFunction,
    alloc: &HashMap<VReg, X86PReg>,
    call_abi: X86CallAbi,
) -> Vec<PostRaDataflowViolation> {
    let mut violations = Vec::new();
    let taint_entries = match call_taint_block_entries(func, alloc, call_abi) {
        Ok(entries) => entries,
        Err(errors) => {
            violations.extend(errors.into_iter().map(|detail| PostRaDataflowViolation {
                kind: PostRaDataflowViolationKind::MalformedOperands,
                detail: format!(
                    "fn `{}` malformed EH call-site metadata: {detail}",
                    func.name
                ),
            }));
            return violations;
        }
    };
    // Same pure inputs as the taint fixpoint, so this cannot fail where that
    // succeeded; the arm exists only to stay fail-closed by construction.
    let severed_entries =
        match call_severed_vregs_block_entries(func, alloc, call_abi, &taint_entries) {
            Ok(entries) => entries,
            Err(errors) => {
                violations.extend(errors.into_iter().map(|detail| PostRaDataflowViolation {
                    kind: PostRaDataflowViolationKind::MalformedOperands,
                    detail: format!(
                        "fn `{}` malformed EH call-site metadata: {detail}",
                        func.name
                    ),
                }));
                return violations;
            }
        };
    let caller_saved_homed = caller_saved_homed_vregs(alloc, call_abi);

    // The exact ABI result-register lanes every `Ret` in this function
    // delivers to its caller, from the SAME return classifier the lowering
    // uses (callee-side mirror of call-site `call_result_regs`). Non-scalar
    // return shapes (sret/aggregate lanes) classify to `None` and keep the
    // previous no-read model rather than guessing.
    let ret_lane_reads: Vec<LaneAccess> =
        x86_scalar_return_result_regs(&func.sig.returns, call_abi)
            .map(|regs| {
                regs.iter()
                    .filter_map(|result| {
                        loc_of(result.reg).map(|loc| LaneAccess {
                            loc,
                            mask: low_bits_lane_mask(result.defined_bits)
                                & preg_read_mask(result.reg),
                        })
                    })
                    .collect()
            })
            .unwrap_or_default();

    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        // Opaque per-byte block-entry identities keep the tied-value proof
        // block-local (bridge copies are required to be local) while retaining
        // exact partial-register copy semantics.
        let mut state = block_local_symbolic_state();
        let mut call_taint = taint_entries
            .get(block_id)
            .copied()
            .unwrap_or([0; NUM_LOCS]);
        let mut severed = severed_entries.get(block_id).cloned().unwrap_or_default();

        for (inst_idx, inst) in block.insts.iter().enumerate() {
            let site = format!(
                "fn `{}` block {} inst #{inst_idx} ({:?})",
                func.name, block_id.0, inst.opcode
            );

            // (1) Classify; an inadmissible shape fails closed as
            // malformed-operands and contributes no transfer.
            let mut acc = match classify_x86_post_ra_inst(inst, alloc, call_abi) {
                Ok(acc) => acc,
                Err(why) => {
                    violations.push(PostRaDataflowViolation {
                        kind: PostRaDataflowViolationKind::MalformedOperands,
                        detail: format!("{site}: {why}"),
                    });
                    continue;
                }
            };
            // Ret result-register model: a `Ret` DELIVERS the function's
            // declared scalar results to the caller, so it READS exactly the
            // classified ABI result lanes (the callee-side mirror of call
            // `call_result_regs`). Without this, garbage routed into a
            // return register by an otherwise-unread path would leave the
            // function unchecked.
            if inst.opcode == X86Opcode::Ret {
                acc.lane_reads.extend(ret_lane_reads.iter().copied());
            }
            for vreg in &acc.unallocated {
                violations.push(PostRaDataflowViolation {
                    kind: PostRaDataflowViolationKind::UnallocatedVReg,
                    detail: format!(
                        "{site}: operand {vreg} has no physical register in the post-RA \
                         allocation map"
                    ),
                });
            }

            // (2) Call-clobber read checks against the PRE-transfer state.
            for read in &acc.lane_reads {
                let tainted = call_taint[read.loc as usize] & read.mask;
                if tainted != 0 {
                    // Lane-wise garbage FLOW, not a semantic use: the packed
                    // bitwise/copy op moves the tainted byte lanes verbatim
                    // into the same destination lanes, and the taint transfer
                    // keeps them tainted there. The violation fires at the
                    // first genuinely semantic consumer instead.
                    if let Some(flow) = &acc.xmm_lanewise_flow
                        && flow.covers(read.loc)
                    {
                        continue;
                    }
                    violations.push(PostRaDataflowViolation {
                        kind: PostRaDataflowViolationKind::ReadOfCallClobberedReg,
                        detail: format!(
                            "{site}: reads caller-clobbered byte lanes {tainted:#06x} of \
                             location {} on at least one CFG path",
                            read.loc,
                        ),
                    });
                }
            }
            // (2b) Call-severed vreg-named read check against the PRE-transfer
            // severed set — the launder-immune net for values living across
            // calls in caller-saved homes (bug #66's class).
            for vreg in &acc.vreg_reads {
                if severed.contains(vreg) {
                    let home = alloc.get(vreg).map_or_else(
                        || "<unallocated>".to_string(),
                        |p| x86_preg_name(*p).to_string(),
                    );
                    violations.push(PostRaDataflowViolation {
                        kind: PostRaDataflowViolationKind::CallSeveredVRegRead,
                        detail: format!(
                            "{site}: reads {vreg} whose caller-saved home {home} was \
                             clobbered by a call after the vreg's last def on at least \
                             one CFG path — the value cannot still be live in that \
                             register"
                        ),
                    });
                }
            }
            if acc.flags_use_mask != 0 {
                let flags = call_taint[FLAGS_LOC as usize];
                let clobbered = call_clobbered_flags(flags) & acc.flags_use_mask;
                let undefined = undefined_flags(flags) & acc.flags_use_mask;
                if clobbered != 0 {
                    violations.push(PostRaDataflowViolation {
                        kind: PostRaDataflowViolationKind::ReadOfClobberedFlags,
                        detail: format!(
                            "{site}: consumes {} clobbered by a call on at least one CFG path",
                            flag_mask_label(clobbered)
                        ),
                    });
                }
                if undefined != 0 {
                    violations.push(PostRaDataflowViolation {
                        kind: PostRaDataflowViolationKind::ReadOfUndefinedFlags,
                        detail: format!(
                            "{site}: consumes undefined {} on at least one CFG path",
                            flag_mask_label(undefined)
                        ),
                    });
                }
            }

            // (3) ENFORCE: the tied-ghost obligation, against the
            // PRE-transfer state.
            if let Some(tied) = acc.tied {
                // classify_tied_site guarantees both locs exist.
                let (Some(dl), Some(gl)) = (loc_of(tied.dst), loc_of(tied.ghost)) else {
                    continue;
                };
                let mismatch = (!x86_regs_overlap(tied.dst, tied.ghost))
                    .then(|| first_tied_lane_mismatch(&state, dl, gl, tied.read_mask))
                    .flatten();
                if let Some((lane, d_sym, g_sym)) = mismatch {
                    violations.push(PostRaDataflowViolation {
                        kind: PostRaDataflowViolationKind::TiedOperandValueMismatch,
                        detail: format!(
                            "{site}: tied destination {} does not overlap ghost source {} and \
                             carries a different value in required byte lane {lane} \
                             ({d_sym:?} vs {g_sym:?}) — the \
                             two-address bridge copy `mov {} <- {}` is missing, redirected, or \
                             clobbered",
                            x86_preg_name(tied.dst),
                            x86_preg_name(tied.ghost),
                            x86_preg_name(tied.dst),
                            x86_preg_name(tied.ghost),
                        ),
                    });
                }
            }

            // (4) Transfer.
            transfer_symbolic_state(&mut state, &acc, call_abi, inst_idx as u32);
            transfer_call_taint(&mut call_taint, &acc, call_abi);
            transfer_call_severed(&mut severed, &acc, &caller_saved_homed);
        }
    }

    violations
}

// ---------------------------------------------------------------------------
// Driver (mode + telemetry)
// ---------------------------------------------------------------------------

/// TV-5 driver: run the post-RA dataflow check over one FINAL post-fixup
/// function, applying the resolved [`PostRegallocRecheckMode`].
///
/// * `Off` → returns `None` immediately (zero work).
/// * Every violation is recorded (telemetry) regardless of mode.
/// * In `Enforce` mode the FIRST enforce-tier violation is returned so the
///   caller can fail the compile closed. CFG EFLAGS provenance violations are
///   enforce-tier correctness failures.
pub fn evaluate(
    func: &X86ISelFunction,
    alloc: &HashMap<VReg, X86PReg>,
    arch: &str,
    mode: PostRegallocRecheckMode,
) -> Option<PostRaDataflowViolation> {
    evaluate_with_abi(func, alloc, arch, mode, X86CallAbi::SystemV)
}

pub fn evaluate_with_abi(
    func: &X86ISelFunction,
    alloc: &HashMap<VReg, X86PReg>,
    arch: &str,
    mode: PostRegallocRecheckMode,
    call_abi: X86CallAbi,
) -> Option<PostRaDataflowViolation> {
    if mode == PostRegallocRecheckMode::Off {
        return None;
    }
    let violations = check_x86_post_ra_dataflow_with_abi(func, alloc, call_abi);
    for v in &violations {
        let failing = mode == PostRegallocRecheckMode::Enforce && v.kind.enforce_tier();
        record(arch, &func.name, v.kind.tag(), &v.detail, failing);
    }
    if mode == PostRegallocRecheckMode::Enforce {
        violations.into_iter().find(|v| v.kind.enforce_tier())
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
    use std::sync::Mutex;
    use trust_cg_ir::regs::RegClass;
    use trust_cg_ir::x86_64_ops::X86CondCode;
    use trust_cg_ir::x86_64_regs::{
        AL, EAX, EDX, ESI, R8, R9, R10, RBP, RBX, RCX, RDI, RSI, SIL, XMM2, XMM3,
    };
    use trust_cg_lower::function::{EhCallSite, EhFunctionInfo, EhLandingPad, Signature};
    use trust_cg_lower::instructions::Block;
    use trust_cg_lower::types::Type;
    use trust_cg_lower::x86_64_isel::{X86CallArgReg, X86CallResultReg};

    /// Serializes tests that assert on the process-wide DATAFLOW_HITS counter
    /// (both "increased" and "unchanged" assertions) against each other. All
    /// tests that record violations via `evaluate` take this lock.
    static COUNTER_LOCK: Mutex<()> = Mutex::new(());

    fn counter_guard() -> std::sync::MutexGuard<'static, ()> {
        COUNTER_LOCK.lock().unwrap_or_else(|e| e.into_inner())
    }

    fn v(id: u32, class: RegClass) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, class))
    }

    fn p(reg: X86PReg) -> X86ISelOperand {
        X86ISelOperand::PReg(reg)
    }

    fn call_result(reg: X86PReg, defined_bits: u16) -> X86CallResultReg {
        X86CallResultReg::new(reg, defined_bits)
    }

    fn call_arg(reg: X86PReg, read_bits: u16) -> X86CallArgReg {
        X86CallArgReg::new(reg, read_bits)
    }

    fn imm(value: i64) -> X86ISelOperand {
        X86ISelOperand::Imm(value)
    }

    fn amap(pairs: &[(u32, RegClass, X86PReg)]) -> HashMap<VReg, X86PReg> {
        pairs
            .iter()
            .map(|&(id, class, preg)| (VReg::new(id, class), preg))
            .collect()
    }

    fn slot_mem(slot: u32) -> X86ISelOperand {
        X86ISelOperand::MemAddr {
            base: Box::new(X86ISelOperand::StackSlot(slot)),
            disp: 0,
        }
    }

    fn base_mem(base: X86ISelOperand) -> X86ISelOperand {
        X86ISelOperand::MemAddr {
            base: Box::new(base),
            disp: 0,
        }
    }

    fn x86_func(name: &str, insts: Vec<X86ISelInst>) -> X86ISelFunction {
        let mut func = X86ISelFunction::new(
            name.to_string(),
            Signature {
                params: vec![Type::I64],
                returns: vec![],
            },
        );
        let block = Block(0);
        func.ensure_block(block);
        func.blocks.get_mut(&block).unwrap().insts.extend(insts);
        func
    }

    fn x86_cfg_func(name: &str, blocks: Vec<(Vec<X86ISelInst>, Vec<u32>)>) -> X86ISelFunction {
        let mut func = X86ISelFunction::new(
            name.to_string(),
            Signature {
                params: vec![],
                returns: vec![],
            },
        );
        for idx in 0..blocks.len() {
            func.ensure_block(Block(idx as u32));
        }
        for (idx, (insts, successors)) in blocks.into_iter().enumerate() {
            let block = func.blocks.get_mut(&Block(idx as u32)).unwrap();
            block.insts = insts;
            block.successors = successors.into_iter().map(Block).collect();
        }
        func
    }

    fn inst(opcode: X86Opcode, operands: Vec<X86ISelOperand>) -> X86ISelInst {
        X86ISelInst::new(opcode, operands)
    }

    fn jcc(cc: X86CondCode) -> X86ISelInst {
        inst(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(cc),
                X86ISelOperand::Block(Block(0)),
            ],
        )
    }

    fn assert_flag_violation(
        func: &X86ISelFunction,
        kind: PostRaDataflowViolationKind,
        flag_name: &str,
    ) {
        let violations = check_x86_post_ra_dataflow(func, &HashMap::new());
        assert!(
            violations
                .iter()
                .any(|violation| violation.kind == kind && violation.detail.contains(flag_name)),
            "{} must report {kind:?} for {flag_name}: {violations:?}",
            func.name
        );
    }

    /// Standard alloc for the deleted-bridge shape: v0->RAX, v1->RCX, v2->RDX.
    fn add_rr_alloc() -> HashMap<VReg, X86PReg> {
        amap(&[
            (0, RegClass::Gpr64, RAX),
            (1, RegClass::Gpr64, RCX),
            (2, RegClass::Gpr64, RDX),
        ])
    }

    fn g64(id: u32) -> X86ISelOperand {
        v(id, RegClass::Gpr64)
    }

    // ===================================================================
    // RED: refutation shapes (assert the first violation kind + detail)
    // ===================================================================

    /// THE acceptance test: a tied 3-op AddRR whose bridge copy is MISSING
    /// (the empirically proven silent-miscompile shape) fails closed under
    /// ENFORCE and is telemetry-only under WARN.
    #[test]
    fn x86_deleted_bridge_copy_refutes_enforce() {
        let _guard = counter_guard();
        let func = x86_func(
            "bad",
            vec![
                inst(X86Opcode::AddRR, vec![g64(0), g64(1), g64(2)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let alloc = add_rr_alloc();
        let violation = evaluate(&func, &alloc, "x86_64", PostRegallocRecheckMode::Enforce)
            .expect("missing bridge copy must fail closed");
        assert_eq!(
            violation.kind,
            PostRaDataflowViolationKind::TiedOperandValueMismatch
        );
        assert!(violation.detail.contains("rax"), "{}", violation.detail);
        assert!(violation.detail.contains("rcx"), "{}", violation.detail);
        // WARN records telemetry (counter bumps) but never fails.
        let before = post_ra_dataflow_hit_count();
        assert!(evaluate(&func, &alloc, "x86_64", PostRegallocRecheckMode::Warn).is_none());
        assert!(post_ra_dataflow_hit_count() > before);
    }

    /// A bridge copy from the WRONG source does not discharge the obligation.
    #[test]
    fn x86_wrong_source_bridge_refutes() {
        let _guard = counter_guard();
        let func = x86_func(
            "bad",
            vec![
                inst(X86Opcode::MovRR, vec![p(RAX), p(RDX)]),
                inst(X86Opcode::AddRR, vec![g64(0), g64(1), g64(2)]),
            ],
        );
        let violation = evaluate(
            &func,
            &add_rr_alloc(),
            "x86_64",
            PostRegallocRecheckMode::Enforce,
        )
        .expect("wrong-source bridge must fail closed");
        assert_eq!(
            violation.kind,
            PostRaDataflowViolationKind::TiedOperandValueMismatch
        );
    }

    /// A correct bridge copy whose destination is CLOBBERED before the tied
    /// site does not discharge the obligation.
    #[test]
    fn x86_clobbered_bridge_refutes() {
        let _guard = counter_guard();
        let func = x86_func(
            "bad",
            vec![
                inst(X86Opcode::MovRR, vec![p(RAX), p(RCX)]),
                inst(X86Opcode::MovRI, vec![p(RAX), imm(0)]),
                inst(X86Opcode::AddRR, vec![g64(0), g64(1), g64(2)]),
            ],
        );
        let violation = evaluate(
            &func,
            &add_rr_alloc(),
            "x86_64",
            PostRegallocRecheckMode::Enforce,
        )
        .expect("clobbered bridge must fail closed");
        assert_eq!(
            violation.kind,
            PostRaDataflowViolationKind::TiedOperandValueMismatch
        );
    }

    /// Every tied-ghost form variant refutes when its bridge is missing.
    #[test]
    fn x86_ghost_form_variants_refute_without_bridge() {
        let _guard = counter_guard();
        let f64alloc = amap(&[
            (0, RegClass::Fpr64, XMM0),
            (1, RegClass::Fpr64, XMM1),
            (2, RegClass::Fpr64, XMM2),
        ]);
        let v128alloc = amap(&[
            (0, RegClass::Fpr128, XMM0),
            (1, RegClass::Fpr128, XMM1),
            (2, RegClass::Fpr128, XMM2),
        ]);
        let pinsr_alloc = amap(&[
            (0, RegClass::Fpr128, XMM0),
            (1, RegClass::Fpr128, XMM1),
            (2, RegClass::Gpr64, RCX),
        ]);
        let cases: Vec<(Vec<X86ISelInst>, HashMap<VReg, X86PReg>)> = vec![
            // 3-op AddRI [dst, ghost, imm].
            (
                vec![inst(X86Opcode::AddRI, vec![g64(0), g64(1), imm(7)])],
                add_rr_alloc(),
            ),
            // 3-op ShlRI [dst, ghost, imm].
            (
                vec![inst(X86Opcode::ShlRI, vec![g64(0), g64(1), imm(3)])],
                add_rr_alloc(),
            ),
            // 2-op ShlRR [dst, ghost] (with a CL setup so RCX is defined).
            (
                vec![
                    inst(X86Opcode::MovRI, vec![p(RCX), imm(3)]),
                    inst(X86Opcode::ShlRR, vec![g64(0), g64(1)]),
                ],
                amap(&[(0, RegClass::Gpr64, RAX), (1, RegClass::Gpr64, RBX)]),
            ),
            // 2-op Neg [dst, ghost].
            (
                vec![inst(X86Opcode::Neg, vec![g64(0), g64(1)])],
                add_rr_alloc(),
            ),
            // Addsd without its MovsdRR bridge.
            (
                vec![inst(
                    X86Opcode::Addsd,
                    vec![
                        v(0, RegClass::Fpr64),
                        v(1, RegClass::Fpr64),
                        v(2, RegClass::Fpr64),
                    ],
                )],
                f64alloc,
            ),
            // Paddd without its MovdqaRR bridge.
            (
                vec![inst(
                    X86Opcode::Paddd,
                    vec![
                        v(0, RegClass::Fpr128),
                        v(1, RegClass::Fpr128),
                        v(2, RegClass::Fpr128),
                    ],
                )],
                v128alloc,
            ),
            // 4-op Pinsrd [dst, ghost, scalar, imm].
            (
                vec![inst(
                    X86Opcode::Pinsrd,
                    vec![
                        v(0, RegClass::Fpr128),
                        v(1, RegClass::Fpr128),
                        v(2, RegClass::Gpr64),
                        imm(1),
                    ],
                )],
                pinsr_alloc,
            ),
        ];
        for (insts, alloc) in cases {
            let opcode = insts.last().unwrap().opcode;
            let func = x86_func("bad", insts);
            let violation = evaluate(&func, &alloc, "x86_64", PostRegallocRecheckMode::Enforce)
                .unwrap_or_else(|| panic!("{opcode:?} without a bridge must fail closed"));
            assert_eq!(
                violation.kind,
                PostRaDataflowViolationKind::TiedOperandValueMismatch,
                "{opcode:?}"
            );
        }
    }

    /// A VReg with no allocation on the final stream fails closed.
    #[test]
    fn x86_unallocated_vreg_refutes() {
        let _guard = counter_guard();
        let func = x86_func(
            "bad",
            vec![inst(X86Opcode::AddRR, vec![g64(0), g64(1), g64(2)])],
        );
        // v2 missing from the map entirely.
        let alloc = amap(&[(0, RegClass::Gpr64, RAX), (1, RegClass::Gpr64, RAX)]);
        let violation = evaluate(&func, &alloc, "x86_64", PostRegallocRecheckMode::Enforce)
            .expect("unallocated vreg must fail closed");
        assert_eq!(violation.kind, PostRaDataflowViolationKind::UnallocatedVReg);
        assert!(violation.detail.contains("v2"), "{}", violation.detail);
    }

    /// Inadmissible shapes fail closed as malformed-operands.
    #[test]
    fn x86_malformed_refutes() {
        let _guard = counter_guard();
        // A Phi surviving past regalloc.
        let func = x86_func("bad", vec![inst(X86Opcode::Phi, vec![g64(0)])]);
        let violation = evaluate(
            &func,
            &add_rr_alloc(),
            "x86_64",
            PostRegallocRecheckMode::Enforce,
        )
        .expect("post-RA Phi must fail closed");
        assert_eq!(
            violation.kind,
            PostRaDataflowViolationKind::MalformedOperands
        );

        // A flag consumer without the condition code the encoder requires.
        let func = x86_func(
            "bad",
            vec![inst(X86Opcode::Jcc, vec![X86ISelOperand::Block(Block(0))])],
        );
        let violation = evaluate(
            &func,
            &HashMap::new(),
            "x86_64",
            PostRegallocRecheckMode::Enforce,
        )
        .expect("Jcc without a condition code must fail closed");
        assert_eq!(
            violation.kind,
            PostRaDataflowViolationKind::MalformedOperands
        );

        // A tied-form site whose ghost operand is an immediate.
        let func = x86_func(
            "bad",
            vec![inst(X86Opcode::AddRR, vec![g64(0), imm(1), g64(2)])],
        );
        let violation = evaluate(
            &func,
            &add_rr_alloc(),
            "x86_64",
            PostRegallocRecheckMode::Enforce,
        )
        .expect("non-register ghost must fail closed");
        assert_eq!(
            violation.kind,
            PostRaDataflowViolationKind::MalformedOperands
        );
    }

    /// A caller-saved register read after a call fails closed under Enforce.
    #[test]
    fn x86_call_clobbered_register_read_fails_closed() {
        let _guard = counter_guard();
        let func = x86_func(
            "warns",
            vec![
                inst(X86Opcode::MovRR, vec![p(RDI), p(RAX)]),
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())])
                    .with_call_arg_regs(vec![call_arg(RDI, 64)]),
                // RCX holds only the call's clobber here.
                inst(X86Opcode::MovRR, vec![p(RBX), p(RCX)]),
            ],
        );
        let alloc = HashMap::new();
        let violations = check_x86_post_ra_dataflow(&func, &alloc);
        assert!(
            violations
                .iter()
                .any(|v| v.kind == PostRaDataflowViolationKind::ReadOfCallClobberedReg),
            "expected a read-of-call-clobbered-reg record"
        );
        let before = post_ra_dataflow_hit_count();
        assert!(evaluate(&func, &alloc, "x86_64", PostRegallocRecheckMode::Enforce).is_some());
        assert!(post_ra_dataflow_hit_count() > before);
    }

    /// Only the SAME-register zero idiom is exempt from the call-clobber read
    /// check: an `XorRR`/`Pxor` with ANY non-identical register operand still
    /// consumes its sources and must fail closed after a call. Pins that
    /// `post_ra_zero_idiom_dst` opens no discharge path for distinct
    /// registers.
    #[test]
    fn x86_xor_distinct_source_after_call_still_fails() {
        let tied_3op = x86_func(
            "bad",
            vec![
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())]),
                // dst==ghost (RBX, callee-saved) but a DISTINCT caller-saved
                // source RCX: the RCX read must still be flagged.
                inst(X86Opcode::XorRR, vec![p(RBX), p(RBX), p(RCX)]),
            ],
        );
        let in_place_2op = x86_func(
            "bad",
            vec![
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())]),
                inst(X86Opcode::XorRR, vec![p(RBX), p(RCX)]),
            ],
        );
        // Distinct-source Pxor is NOT the zero-idiom exemption: the clobber
        // garbage FLOWS through the lane-wise op (both inputs tainted, so
        // every destination lane stays tainted) and must still fail closed
        // at the first semantic consumer — here the packed store.
        let pxor_distinct = x86_func(
            "bad",
            vec![
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())]),
                inst(X86Opcode::Pxor, vec![p(XMM2), p(XMM3)]),
                inst(X86Opcode::MovdqaMR, vec![base_mem(p(RBX)), p(XMM2)]),
            ],
        );
        for func in [&tied_3op, &in_place_2op, &pxor_distinct] {
            let violations = check_x86_post_ra_dataflow(func, &HashMap::new());
            assert!(
                violations
                    .iter()
                    .any(|v| v.kind == PostRaDataflowViolationKind::ReadOfCallClobberedReg),
                "{}: expected a read-of-call-clobbered-reg record: {violations:?}",
                func.name
            );
        }
    }

    // ===================================================================
    // Call-severed vreg-named reads (the #66 fail-closed net)
    // ===================================================================

    fn severed_hits(violations: &[PostRaDataflowViolation]) -> usize {
        violations
            .iter()
            .filter(|v| v.kind == PostRaDataflowViolationKind::CallSeveredVRegRead)
            .count()
    }

    /// (a) A vreg homed in caller-saved RDX, defined before a call and read
    /// after it with no intervening def-by-name: enforce-tier violation.
    #[test]
    fn x86_call_severed_vreg_read_refutes() {
        let alloc = amap(&[(0, RegClass::Gpr64, RDX)]);
        let func = x86_func(
            "bad",
            vec![
                inst(X86Opcode::MovRI, vec![g64(0), imm(7)]),
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())]),
                inst(X86Opcode::MovRR, vec![p(RBX), g64(0)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let violations = check_x86_post_ra_dataflow(&func, &alloc);
        assert!(
            severed_hits(&violations) > 0,
            "reading a caller-saved-homed vreg across a call must be severed: {violations:?}"
        );
        assert!(PostRaDataflowViolationKind::CallSeveredVRegRead.enforce_tier());
    }

    /// (b) THE LAUNDER CASE — the reason the check is vreg-named: after the
    /// call, an unrelated instruction redefines the PHYSICAL register RDX
    /// (killing the lane taint, so the existing ReadOfCallClobberedReg check
    /// provably passes), but the named vreg's value is still gone. The severed
    /// check must still refute.
    #[test]
    fn x86_call_severed_vreg_read_survives_preg_launder() {
        let alloc = amap(&[(0, RegClass::Gpr64, RDX)]);
        let func = x86_func(
            "laundered",
            vec![
                inst(X86Opcode::MovRI, vec![g64(0), imm(7)]),
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())]),
                // Launder: a PREG-level def of RDX clears the lane taint …
                inst(X86Opcode::MovRI, vec![p(RDX), imm(1)]),
                // … so this vreg-named read passes the preg check but must
                // still be severed (v0's value did not survive the call).
                inst(X86Opcode::MovRR, vec![p(RBX), g64(0)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let violations = check_x86_post_ra_dataflow(&func, &alloc);
        assert!(
            !violations
                .iter()
                .any(|v| v.kind == PostRaDataflowViolationKind::ReadOfCallClobberedReg),
            "the preg launder must clear the lane taint (else this test is not \
             exercising the miss): {violations:?}"
        );
        assert!(
            severed_hits(&violations) > 0,
            "the vreg-named severed check must survive the preg launder: {violations:?}"
        );
    }

    /// (c) A reload INTO the vreg (a def-by-name) after the call un-severs it:
    /// the classic spill/reload pattern must stay clean.
    #[test]
    fn x86_call_severed_vreg_reload_is_clean() {
        let alloc = amap(&[(0, RegClass::Gpr64, RDX)]);
        let func = x86_func(
            "reloaded",
            vec![
                inst(X86Opcode::MovRI, vec![g64(0), imm(7)]),
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())]),
                inst(X86Opcode::MovRM, vec![g64(0), slot_mem(0)]),
                inst(X86Opcode::MovRR, vec![p(RBX), g64(0)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let violations = check_x86_post_ra_dataflow(&func, &alloc);
        assert_eq!(
            severed_hits(&violations),
            0,
            "a reload-by-name must un-sever: {violations:?}"
        );
    }

    /// (d) The call-result bridge pattern `MovRR v <- RAX` is a def-by-name:
    /// reads of v after it are clean.
    #[test]
    fn x86_call_severed_vreg_result_copy_is_clean() {
        let alloc = amap(&[(0, RegClass::Gpr64, RCX)]);
        let func = x86_func(
            "result_copy",
            vec![
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())])
                    .with_call_result_regs(vec![call_result(RAX, 64)]),
                inst(X86Opcode::MovRR, vec![g64(0), p(RAX)]),
                inst(X86Opcode::MovRR, vec![p(RBX), g64(0)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let violations = check_x86_post_ra_dataflow(&func, &alloc);
        assert_eq!(
            severed_hits(&violations),
            0,
            "the result-copy def-by-name must un-sever: {violations:?}"
        );
    }

    /// (e) ABI awareness: RSI is CALLEE-saved on Windows x64, so a vreg homed
    /// there legitimately lives across a call — no severing. Under SysV the
    /// same shape must refute (RSI is caller-saved there).
    #[test]
    fn x86_call_severed_vreg_is_abi_aware() {
        let alloc = amap(&[(0, RegClass::Gpr64, RSI)]);
        let func = x86_func(
            "windows_rsi_live_across_call",
            vec![
                inst(X86Opcode::MovRI, vec![g64(0), imm(7)]),
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())]),
                inst(X86Opcode::MovRR, vec![p(RBX), g64(0)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let windows = check_x86_post_ra_dataflow_with_abi(&func, &alloc, X86CallAbi::WindowsX64);
        assert_eq!(
            severed_hits(&windows),
            0,
            "RSI is callee-saved on Windows x64: {windows:?}"
        );
        let sysv = check_x86_post_ra_dataflow_with_abi(&func, &alloc, X86CallAbi::SystemV);
        assert!(
            severed_hits(&sysv) > 0,
            "RSI is caller-saved under SysV — the same shape must refute: {sysv:?}"
        );
    }

    /// (f) A vreg homed in CALLEE-saved RBX survives calls by definition —
    /// never severed under either ABI.
    #[test]
    fn x86_call_severed_vreg_callee_saved_home_is_clean() {
        let alloc = amap(&[(0, RegClass::Gpr64, RBX)]);
        let func = x86_func(
            "callee_saved_home",
            vec![
                inst(X86Opcode::MovRI, vec![g64(0), imm(7)]),
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())]),
                inst(X86Opcode::MovRR, vec![p(RCX), g64(0)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let violations = check_x86_post_ra_dataflow(&func, &alloc);
        assert_eq!(
            severed_hits(&violations),
            0,
            "a callee-saved home is never severed: {violations:?}"
        );
    }

    /// (g) CFG propagation: a diamond where only ONE path calls must still
    /// sever the join-block read (meet is union over reachable paths).
    #[test]
    fn x86_call_severed_vreg_propagates_across_blocks() {
        let alloc = amap(&[(0, RegClass::Gpr64, RDX)]);
        let mut func = x86_cfg_func(
            "diamond",
            vec![
                // b0: define v0, branch to b1 or b2.
                (
                    vec![
                        inst(X86Opcode::MovRI, vec![g64(0), imm(7)]),
                        inst(X86Opcode::CmpRI, vec![p(RAX), imm(0)]),
                        jcc(X86CondCode::E),
                    ],
                    vec![1, 2],
                ),
                // b1: the calling path.
                (
                    vec![inst(
                        X86Opcode::Call,
                        vec![X86ISelOperand::Symbol("f".into())],
                    )],
                    vec![3],
                ),
                // b2: the call-free path.
                (vec![], vec![3]),
                // b3: join — reads v0. One predecessor severed it.
                (
                    vec![
                        inst(X86Opcode::MovRR, vec![p(RBX), g64(0)]),
                        inst(X86Opcode::Ret, vec![]),
                    ],
                    vec![],
                ),
            ],
        );
        // Point the conditional branch at b2 (fallthrough successor b1).
        if let Some(block) = func.blocks.get_mut(&Block(0))
            && let Some(j) = block.insts.last_mut()
        {
            j.operands[1] = X86ISelOperand::Block(Block(2));
        }
        let violations = check_x86_post_ra_dataflow(&func, &alloc);
        assert!(
            severed_hits(&violations) > 0,
            "a sever on ANY reachable path must poison the join read: {violations:?}"
        );
    }

    #[test]
    fn windows_callee_saved_register_is_not_modeled_as_call_clobbered() {
        let func = x86_func(
            "windows_rsi_preserved",
            vec![
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())]),
                inst(X86Opcode::MovRR, vec![p(RBX), p(RSI)]),
            ],
        );
        let alloc = HashMap::new();
        let windows = check_x86_post_ra_dataflow_with_abi(&func, &alloc, X86CallAbi::WindowsX64);
        assert!(
            !windows
                .iter()
                .any(|v| { v.kind == PostRaDataflowViolationKind::ReadOfCallClobberedReg })
        );
        let system_v = check_x86_post_ra_dataflow_with_abi(&func, &alloc, X86CallAbi::SystemV);
        assert!(
            system_v
                .iter()
                .any(|v| { v.kind == PostRaDataflowViolationKind::ReadOfCallClobberedReg })
        );
    }

    #[test]
    fn x86_call_result_metadata_malformed_shapes_fail_closed() {
        let mut missing = inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())]);
        missing.call_result_regs = None;
        let mut non_call = inst(X86Opcode::Nop, vec![]);
        non_call.call_result_regs = Some(vec![]);
        let cases = [
            missing,
            non_call,
            inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())])
                .with_call_result_regs(vec![call_result(RCX, 64)]),
            inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())])
                .with_call_result_regs(vec![call_result(RAX, 64), call_result(RAX, 32)]),
            inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())])
                .with_call_result_regs(vec![call_result(RAX, 128)]),
            inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())])
                .with_call_result_regs(vec![call_result(XMM0, 8)]),
        ];
        for bad in cases {
            let func = x86_func("malformed_call_results", vec![bad]);
            let violations = check_x86_post_ra_dataflow(&func, &HashMap::new());
            assert!(
                violations
                    .iter()
                    .any(|v| v.kind == PostRaDataflowViolationKind::MalformedOperands),
                "malformed call-result metadata must fail closed: {violations:?}"
            );
        }
    }

    #[test]
    fn x86_void_call_clobbers_every_conventional_result_register_on_both_abis() {
        for abi in [X86CallAbi::SystemV, X86CallAbi::WindowsX64] {
            let func = x86_func(
                "void_results",
                vec![
                    inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())]),
                    inst(X86Opcode::MovRR, vec![p(RBX), p(RAX)]),
                    inst(X86Opcode::MovRR, vec![p(RBX), p(RDX)]),
                    inst(X86Opcode::MovsdRR, vec![p(XMM2), p(XMM0)]),
                    inst(X86Opcode::MovsdRR, vec![p(XMM2), p(XMM1)]),
                ],
            );
            let violations = check_x86_post_ra_dataflow_with_abi(&func, &HashMap::new(), abi);
            let clobbered_reads = violations
                .iter()
                .filter(|v| v.kind == PostRaDataflowViolationKind::ReadOfCallClobberedReg)
                .count();
            assert_eq!(clobbered_reads, 4, "{abi:?}: {violations:?}");
        }
    }

    #[test]
    fn x86_exact_scalar_and_multireg_call_results_apply_on_both_abis() {
        for abi in [X86CallAbi::SystemV, X86CallAbi::WindowsX64] {
            for (declared, readable, still_clobbered) in [
                (vec![call_result(RAX, 64)], vec![RAX], RDX),
                (vec![call_result(XMM0, 64)], vec![XMM0], XMM1),
                (
                    vec![call_result(RAX, 64), call_result(RDX, 64)],
                    vec![RAX, RDX],
                    XMM0,
                ),
                (
                    vec![call_result(XMM0, 64), call_result(XMM1, 64)],
                    vec![XMM0, XMM1],
                    RAX,
                ),
            ] {
                let mut clean_insts = vec![
                    inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())])
                        .with_call_result_regs(declared.clone()),
                ];
                for reg in readable {
                    let opcode = if reg.encoding() >= 64 {
                        X86Opcode::MovsdRR
                    } else {
                        X86Opcode::MovRR
                    };
                    let dst = if reg.encoding() >= 64 { XMM2 } else { RBX };
                    clean_insts.push(inst(opcode, vec![p(dst), p(reg)]));
                }
                let clean = x86_func("exact_results", clean_insts);
                let clean_violations =
                    check_x86_post_ra_dataflow_with_abi(&clean, &HashMap::new(), abi);
                assert!(clean_violations.is_empty(), "{abi:?}: {clean_violations:?}");

                let bad_opcode = if still_clobbered.encoding() >= 64 {
                    X86Opcode::MovsdRR
                } else {
                    X86Opcode::MovRR
                };
                let bad_dst = if still_clobbered.encoding() >= 64 {
                    XMM2
                } else {
                    RBX
                };
                let bad = x86_func(
                    "undeclared_result",
                    vec![
                        inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())])
                            .with_call_result_regs(declared),
                        inst(bad_opcode, vec![p(bad_dst), p(still_clobbered)]),
                    ],
                );
                let violations = check_x86_post_ra_dataflow_with_abi(&bad, &HashMap::new(), abi);
                assert!(
                    violations
                        .iter()
                        .any(|v| { v.kind == PostRaDataflowViolationKind::ReadOfCallClobberedReg }),
                    "{abi:?}: {violations:?}"
                );
            }
        }
    }

    #[test]
    fn x86_partial_gpr_write_cannot_launder_call_clobber() {
        for abi in [X86CallAbi::SystemV, X86CallAbi::WindowsX64] {
            let partial = x86_func(
                "partial_gpr_launder",
                vec![
                    inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())]),
                    inst(X86Opcode::MovRI, vec![p(AL), imm(1)]),
                    inst(X86Opcode::MovRR, vec![p(RBX), p(RAX)]),
                ],
            );
            let violations = check_x86_post_ra_dataflow_with_abi(&partial, &HashMap::new(), abi);
            assert!(
                violations
                    .iter()
                    .any(|v| { v.kind == PostRaDataflowViolationKind::ReadOfCallClobberedReg }),
                "{abi:?}: {violations:?}"
            );

            let zero_extended = x86_func(
                "gpr32_defines_full_root",
                vec![
                    inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())]),
                    inst(X86Opcode::MovRI, vec![p(EAX), imm(1)]),
                    inst(X86Opcode::MovRR, vec![p(RBX), p(RAX)]),
                ],
            );
            let violations =
                check_x86_post_ra_dataflow_with_abi(&zero_extended, &HashMap::new(), abi);
            assert!(violations.is_empty(), "{abi:?}: {violations:?}");
        }
    }

    #[test]
    fn x86_scalar_xmm_result_defines_only_its_declared_lane() {
        for abi in [X86CallAbi::SystemV, X86CallAbi::WindowsX64] {
            let scalar_read = x86_func(
                "scalar_xmm_read",
                vec![
                    inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())])
                        .with_call_result_regs(vec![call_result(XMM0, 64)]),
                    inst(X86Opcode::MovsdRR, vec![p(XMM2), p(XMM0)]),
                ],
            );
            let violations =
                check_x86_post_ra_dataflow_with_abi(&scalar_read, &HashMap::new(), abi);
            assert!(violations.is_empty(), "{abi:?}: {violations:?}");

            // The full-register MovdqaRR copy itself is lane-wise garbage
            // FLOW (the scalar-float blend lowerings do this by design); the
            // undefined upper lanes stay TAINTED in the copy destination and
            // the violation fires at the first semantic consumer — here the
            // full-width packed store.
            let packed_read = x86_func(
                "packed_xmm_read",
                vec![
                    inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())])
                        .with_call_result_regs(vec![call_result(XMM0, 64)]),
                    inst(X86Opcode::MovdqaRR, vec![p(XMM3), p(XMM0)]),
                    inst(X86Opcode::MovdqaMR, vec![base_mem(p(RBX)), p(XMM3)]),
                ],
            );
            let violations =
                check_x86_post_ra_dataflow_with_abi(&packed_read, &HashMap::new(), abi);
            assert!(
                violations
                    .iter()
                    .any(|v| { v.kind == PostRaDataflowViolationKind::ReadOfCallClobberedReg }),
                "{abi:?}: {violations:?}"
            );
        }
    }

    #[test]
    fn x86_call_clobbers_propagate_across_cfg_joins_and_loops() {
        for abi in [X86CallAbi::SystemV, X86CallAbi::WindowsX64] {
            let straight = x86_cfg_func(
                "cross_block",
                vec![
                    (
                        vec![inst(
                            X86Opcode::Call,
                            vec![X86ISelOperand::Symbol("f".into())],
                        )],
                        vec![1],
                    ),
                    (vec![inst(X86Opcode::MovRR, vec![p(RBX), p(RCX)])], vec![]),
                ],
            );
            let straight_violations =
                check_x86_post_ra_dataflow_with_abi(&straight, &HashMap::new(), abi);
            assert!(
                straight_violations
                    .iter()
                    .any(|v| { v.kind == PostRaDataflowViolationKind::ReadOfCallClobberedReg }),
                "{abi:?}: {straight_violations:?}"
            );

            let join = x86_cfg_func(
                "join_may_clobber",
                vec![
                    (vec![], vec![1, 2]),
                    (
                        vec![inst(
                            X86Opcode::Call,
                            vec![X86ISelOperand::Symbol("f".into())],
                        )],
                        vec![3],
                    ),
                    (vec![], vec![3]),
                    (vec![inst(X86Opcode::MovRR, vec![p(RBX), p(RCX)])], vec![]),
                ],
            );
            let join_violations = check_x86_post_ra_dataflow_with_abi(&join, &HashMap::new(), abi);
            assert!(
                join_violations
                    .iter()
                    .any(|v| { v.kind == PostRaDataflowViolationKind::ReadOfCallClobberedReg }),
                "{abi:?}: {join_violations:?}"
            );

            let looped = x86_cfg_func(
                "loop_may_clobber",
                vec![
                    (vec![inst(X86Opcode::MovRR, vec![p(RBX), p(RCX)])], vec![1]),
                    (
                        vec![inst(
                            X86Opcode::Call,
                            vec![X86ISelOperand::Symbol("f".into())],
                        )],
                        vec![0],
                    ),
                ],
            );
            let loop_violations =
                check_x86_post_ra_dataflow_with_abi(&looped, &HashMap::new(), abi);
            assert!(
                loop_violations
                    .iter()
                    .any(|v| { v.kind == PostRaDataflowViolationKind::ReadOfCallClobberedReg }),
                "{abi:?}: {loop_violations:?}"
            );
        }
    }

    #[test]
    fn x86_eh_edge_defines_only_itanium_landing_pad_registers() {
        let throwing_call = || {
            inst(
                X86Opcode::Call,
                vec![X86ISelOperand::Symbol("may_throw".into())],
            )
            .with_call_result_regs(vec![])
        };
        let pad_reads = || {
            vec![
                inst(X86Opcode::MovRR, vec![p(RBX), p(RAX)]),
                inst(X86Opcode::MovRR32, vec![p(ESI), p(EDX)]),
            ]
        };

        let mut eh_only = x86_cfg_func(
            "eh_landing_pad_live_ins",
            vec![(vec![throwing_call()], vec![1]), (pad_reads(), vec![])],
        );
        eh_only.eh_info = EhFunctionInfo {
            personality: Some("__gxx_personality_v0".into()),
            landing_pads: vec![EhLandingPad {
                block: Block(1),
                catch_type_indices: vec![],
                is_cleanup: true,
            }],
            call_sites: vec![EhCallSite {
                call_block: Block(0),
                landing_pad_block: Block(1),
            }],
        };
        let violations = check_x86_post_ra_dataflow(&eh_only, &HashMap::new());
        assert!(violations.is_empty(), "{violations:?}");

        // The same machine edge without semantic EH call-site metadata
        // remains an ordinary successor and must retain the call clobber.
        let unmarked = x86_cfg_func(
            "ordinary_edge_is_not_eh",
            vec![(vec![throwing_call()], vec![1]), (pad_reads(), vec![])],
        );
        let violations = check_x86_post_ra_dataflow(&unmarked, &HashMap::new());
        assert!(violations.iter().any(|violation| {
            violation.kind == PostRaDataflowViolationKind::ReadOfCallClobberedReg
        }));

        // Edge specificity: a normal successor of the same throwing block is
        // not allowed to inherit the landing pad's RAX/EDX definitions.
        let mut mixed = x86_cfg_func(
            "eh_and_normal_successors",
            vec![
                (vec![throwing_call()], vec![1, 2]),
                (pad_reads(), vec![]),
                (vec![inst(X86Opcode::MovRR, vec![p(RBX), p(RAX)])], vec![]),
            ],
        );
        mixed.eh_info = eh_only.eh_info;
        let violations = check_x86_post_ra_dataflow(&mixed, &HashMap::new());
        assert!(
            violations
                .iter()
                .all(|violation| violation.detail.contains("block 2")),
            "only the ordinary successor may observe the clobber: {violations:?}"
        );
        assert!(!violations.is_empty());

        // A malformed producer can collapse an Invoke's normal and unwind
        // destinations onto one block. The machine successor list is set-valued,
        // so both transfers then share the same `(source, destination)` pair.
        // Keep both edge kinds: the unwinder-defined RAX/RDX state must not
        // overwrite the normal return path's call clobber.
        let mut aliased = x86_cfg_func(
            "normal_and_exceptional_edge_identity_collision",
            vec![
                (
                    vec![
                        throwing_call(),
                        inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(1))]),
                    ],
                    vec![1],
                ),
                (pad_reads(), vec![]),
            ],
        );
        aliased.eh_info = EhFunctionInfo {
            personality: Some("__gxx_personality_v0".into()),
            landing_pads: vec![EhLandingPad {
                block: Block(1),
                catch_type_indices: vec![],
                is_cleanup: true,
            }],
            call_sites: vec![EhCallSite {
                call_block: Block(0),
                landing_pad_block: Block(1),
            }],
        };
        let violations = check_x86_post_ra_dataflow(&aliased, &HashMap::new());
        assert!(
            violations.iter().any(|violation| {
                violation.kind == PostRaDataflowViolationKind::ReadOfCallClobberedReg
                    && violation.detail.contains("block 1")
            }),
            "the normal edge's call clobber must survive the colliding exceptional edge: {violations:?}"
        );

        // Exceptional state is captured at the protected call, not at the
        // call block's ordinary exit. A definition that executes only after a
        // normal return cannot launder RCX for the exceptional successor.
        let mut post_call_definition = x86_cfg_func(
            "post_call_definition_cannot_launder_eh_state",
            vec![
                (
                    vec![
                        throwing_call(),
                        inst(X86Opcode::MovRI, vec![p(RCX), imm(0)]),
                    ],
                    vec![1],
                ),
                (vec![inst(X86Opcode::MovRR, vec![p(RBX), p(RCX)])], vec![]),
            ],
        );
        post_call_definition.eh_info = EhFunctionInfo {
            personality: Some("__gxx_personality_v0".into()),
            landing_pads: vec![EhLandingPad {
                block: Block(1),
                catch_type_indices: vec![],
                is_cleanup: true,
            }],
            call_sites: vec![EhCallSite {
                call_block: Block(0),
                landing_pad_block: Block(1),
            }],
        };
        let violations = check_x86_post_ra_dataflow(&post_call_definition, &HashMap::new());
        assert!(
            violations.iter().any(|violation| {
                violation.kind == PostRaDataflowViolationKind::ReadOfCallClobberedReg
                    && violation.detail.contains("block 1")
            }),
            "post-call RCX definition must not affect exceptional state: {violations:?}"
        );
    }

    #[test]
    fn x86_block_granular_eh_metadata_requires_exactly_one_call() {
        let call = || {
            inst(
                X86Opcode::Call,
                vec![X86ISelOperand::Symbol("may_throw".into())],
            )
            .with_call_result_regs(vec![])
        };

        for (name, insts) in [
            (
                "eh_call_block_without_call",
                vec![inst(X86Opcode::MovRI, vec![p(RCX), imm(0)])],
            ),
            ("eh_call_block_with_two_calls", vec![call(), call()]),
        ] {
            let mut func = x86_cfg_func(name, vec![(insts, vec![1]), (vec![], vec![])]);
            func.eh_info = EhFunctionInfo {
                personality: Some("__gxx_personality_v0".into()),
                landing_pads: vec![EhLandingPad {
                    block: Block(1),
                    catch_type_indices: vec![],
                    is_cleanup: true,
                }],
                call_sites: vec![EhCallSite {
                    call_block: Block(0),
                    landing_pad_block: Block(1),
                }],
            };

            let violations = check_x86_post_ra_dataflow(&func, &HashMap::new());
            assert!(
                violations.iter().any(|violation| {
                    violation.kind == PostRaDataflowViolationKind::MalformedOperands
                        && violation.detail.contains("exactly one")
                }),
                "{name} must fail closed: {violations:?}"
            );
        }
    }

    #[test]
    fn x86_flags_and_abi_preserved_registers_flow_across_blocks() {
        let flags = x86_cfg_func(
            "cross_block_flags",
            vec![
                (
                    vec![inst(
                        X86Opcode::Call,
                        vec![X86ISelOperand::Symbol("f".into())],
                    )],
                    vec![1],
                ),
                (
                    vec![inst(
                        X86Opcode::Jcc,
                        vec![
                            X86ISelOperand::CondCode(X86CondCode::E),
                            X86ISelOperand::Block(Block(1)),
                        ],
                    )],
                    vec![],
                ),
            ],
        );
        for abi in [X86CallAbi::SystemV, X86CallAbi::WindowsX64] {
            let violations = check_x86_post_ra_dataflow_with_abi(&flags, &HashMap::new(), abi);
            assert!(
                violations
                    .iter()
                    .any(|v| { v.kind == PostRaDataflowViolationKind::ReadOfClobberedFlags }),
                "{abi:?}: {violations:?}"
            );
        }

        let preserved = x86_cfg_func(
            "cross_block_windows_preserved",
            vec![
                (
                    vec![inst(
                        X86Opcode::Call,
                        vec![X86ISelOperand::Symbol("f".into())],
                    )],
                    vec![1],
                ),
                (vec![inst(X86Opcode::MovRR, vec![p(RBX), p(RSI)])], vec![]),
            ],
        );
        let windows = check_x86_post_ra_dataflow_with_abi(
            &preserved,
            &HashMap::new(),
            X86CallAbi::WindowsX64,
        );
        assert!(
            !windows
                .iter()
                .any(|v| { v.kind == PostRaDataflowViolationKind::ReadOfCallClobberedReg })
        );
        let system_v =
            check_x86_post_ra_dataflow_with_abi(&preserved, &HashMap::new(), X86CallAbi::SystemV);
        assert!(
            system_v
                .iter()
                .any(|v| { v.kind == PostRaDataflowViolationKind::ReadOfCallClobberedReg })
        );
    }

    /// EFLAGS consumed across a call fails closed under Enforce.
    #[test]
    fn x86_flags_clobbered_by_call_fail_closed() {
        let _guard = counter_guard();
        let func = x86_func(
            "warns",
            vec![
                inst(X86Opcode::CmpRR, vec![p(RAX), p(RCX)]),
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())]),
                inst(
                    X86Opcode::Jcc,
                    vec![
                        X86ISelOperand::CondCode(X86CondCode::E),
                        X86ISelOperand::Block(Block(0)),
                    ],
                ),
            ],
        );
        let alloc = HashMap::new();
        let violations = check_x86_post_ra_dataflow(&func, &alloc);
        assert!(
            violations
                .iter()
                .any(|v| v.kind == PostRaDataflowViolationKind::ReadOfClobberedFlags),
            "expected a read-of-clobbered-flags record"
        );
        assert!(evaluate(&func, &alloc, "x86_64", PostRegallocRecheckMode::Enforce).is_some());
    }

    #[test]
    fn x86_flags_join_reports_clobbered_and_undefined_provenance() {
        let func = x86_cfg_func(
            "flags_mixed_invalid_join",
            vec![
                (
                    vec![
                        inst(X86Opcode::CmpRR, vec![p(RAX), p(RCX)]),
                        inst(
                            X86Opcode::Jcc,
                            vec![
                                X86ISelOperand::CondCode(X86CondCode::E),
                                X86ISelOperand::Block(Block(1)),
                            ],
                        ),
                    ],
                    vec![1, 2],
                ),
                (
                    vec![
                        inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())]),
                        inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(3))]),
                    ],
                    vec![3],
                ),
                (
                    vec![
                        inst(X86Opcode::Div, vec![p(RBX)]),
                        inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(3))]),
                    ],
                    vec![3],
                ),
                (vec![jcc(X86CondCode::E)], vec![]),
            ],
        );
        let violations = check_x86_post_ra_dataflow(&func, &HashMap::new());
        for kind in [
            PostRaDataflowViolationKind::ReadOfClobberedFlags,
            PostRaDataflowViolationKind::ReadOfUndefinedFlags,
        ] {
            assert!(
                violations
                    .iter()
                    .any(|violation| violation.kind == kind && violation.detail.contains("ZF")),
                "mixed-provenance join must report {kind:?}: {violations:?}"
            );
        }
    }

    #[test]
    fn x86_flags_without_cfg_reaching_definition_fail_closed() {
        let _guard = counter_guard();
        for func in [
            x86_func(
                "entry_flags_undefined",
                vec![inst(
                    X86Opcode::Jcc,
                    vec![
                        X86ISelOperand::CondCode(X86CondCode::E),
                        X86ISelOperand::Block(Block(0)),
                    ],
                )],
            ),
            x86_cfg_func(
                "predecessor_flags_undefined",
                vec![
                    (
                        vec![inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(1))])],
                        vec![1],
                    ),
                    (
                        vec![inst(
                            X86Opcode::Jcc,
                            vec![
                                X86ISelOperand::CondCode(X86CondCode::E),
                                X86ISelOperand::Block(Block(1)),
                            ],
                        )],
                        vec![],
                    ),
                ],
            ),
        ] {
            let violations = check_x86_post_ra_dataflow(&func, &HashMap::new());
            assert!(
                violations.iter().any(|violation| {
                    violation.kind == PostRaDataflowViolationKind::ReadOfUndefinedFlags
                        && violation.detail.contains("undefined ZF")
                }),
                "{} must reject undefined EFLAGS: {violations:?}",
                func.name
            );
            let violation = evaluate(
                &func,
                &HashMap::new(),
                "x86_64",
                PostRegallocRecheckMode::Enforce,
            )
            .expect("undefined EFLAGS must be enforce-tier");
            assert_eq!(
                violation.kind,
                PostRaDataflowViolationKind::ReadOfUndefinedFlags
            );
        }
    }

    #[test]
    fn x86_condition_code_flag_masks_are_exact() {
        use X86CondCode::*;
        for (cc, expected) in [
            (O, FLAG_OF),
            (NO, FLAG_OF),
            (B, FLAG_CF),
            (AE, FLAG_CF),
            (E, FLAG_ZF),
            (NE, FLAG_ZF),
            (BE, FLAG_CF | FLAG_ZF),
            (A, FLAG_CF | FLAG_ZF),
            (S, FLAG_SF),
            (NS, FLAG_SF),
            (P, FLAG_PF),
            (NP, FLAG_PF),
            (L, FLAG_SF | FLAG_OF),
            (GE, FLAG_SF | FLAG_OF),
            (LE, FLAG_ZF | FLAG_SF | FLAG_OF),
            (G, FLAG_ZF | FLAG_SF | FLAG_OF),
        ] {
            assert_eq!(condition_flag_mask(cc), expected, "{cc:?}");
        }
    }

    #[test]
    fn x86_partial_flag_producer_masks_are_exact() {
        let cases = [
            (X86Opcode::Inc, vec![p(RBX)], FLAGS_ALL & !FLAG_CF, 0, 0),
            (
                X86Opcode::Mul,
                vec![p(RBX)],
                FLAGS_MUL_DEFINED,
                FLAGS_MUL_UNDEFINED,
                0,
            ),
            (X86Opcode::Idiv, vec![p(RBX)], 0, FLAGS_ALL, 0),
            (
                X86Opcode::Bsf,
                vec![p(RAX), p(RBX)],
                FLAG_ZF,
                FLAGS_ALL & !FLAG_ZF,
                0,
            ),
            (
                X86Opcode::Tzcnt,
                vec![p(RAX), p(RBX)],
                FLAG_CF | FLAG_ZF,
                FLAGS_ALL & !(FLAG_CF | FLAG_ZF),
                0,
            ),
            (
                X86Opcode::BtRI,
                vec![p(RAX), imm(7)],
                FLAG_CF,
                FLAG_PF | FLAG_AF | FLAG_SF | FLAG_OF,
                0,
            ),
            (
                X86Opcode::AndRI,
                vec![p(RAX), imm(7)],
                FLAGS_LOGIC_DEFINED,
                FLAG_AF,
                0,
            ),
            (X86Opcode::ShlRI, vec![p(RAX), imm(0)], 0, 0, 0),
            (
                X86Opcode::ShlRI,
                vec![p(RAX), imm(1)],
                FLAG_CF | FLAG_PF | FLAG_ZF | FLAG_SF | FLAG_OF,
                FLAG_AF,
                0,
            ),
            (
                X86Opcode::ShlRI,
                vec![p(RAX), imm(2)],
                FLAG_CF | FLAG_PF | FLAG_ZF | FLAG_SF,
                FLAG_AF | FLAG_OF,
                0,
            ),
            (X86Opcode::ShlRR, vec![p(RBX)], 0, 0, FLAG_AF | FLAG_OF),
        ];
        for (opcode, operands, defined, undefined, may_undefined) in cases {
            let access = classify_x86_post_ra_inst(
                &inst(opcode, operands),
                &HashMap::new(),
                X86CallAbi::SystemV,
            )
            .unwrap_or_else(|error| panic!("{opcode:?} classification failed: {error}"));
            assert_eq!(access.flags_def_mask, defined, "{opcode:?} defined");
            assert_eq!(access.flags_undef_mask, undefined, "{opcode:?} undefined");
            assert_eq!(
                access.flags_may_undef_mask, may_undefined,
                "{opcode:?} maybe undefined"
            );
        }
    }

    #[test]
    fn x86_inc_preserved_cf_cannot_launder_undefined_or_call_clobbered_flags() {
        let entry = x86_func(
            "entry_inc_preserves_undefined_cf",
            vec![inst(X86Opcode::Inc, vec![p(RBX)]), jcc(X86CondCode::B)],
        );
        assert_flag_violation(
            &entry,
            PostRaDataflowViolationKind::ReadOfUndefinedFlags,
            "CF",
        );

        let across_call = x86_func(
            "call_inc_preserves_clobbered_cf",
            vec![
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())]),
                inst(X86Opcode::Inc, vec![p(RBX)]),
                jcc(X86CondCode::B),
            ],
        );
        assert_flag_violation(
            &across_call,
            PostRaDataflowViolationKind::ReadOfClobberedFlags,
            "CF",
        );

        let adc_without_cf = x86_func(
            "adc_requires_defined_cf",
            vec![
                inst(X86Opcode::AdcRR, vec![p(RBX), p(RAX)]),
                jcc(X86CondCode::E),
            ],
        );
        assert_flag_violation(
            &adc_without_cf,
            PostRaDataflowViolationKind::ReadOfUndefinedFlags,
            "CF",
        );

        let adc_with_cf = x86_func(
            "cmp_defines_adc_cf",
            vec![
                inst(X86Opcode::CmpRR, vec![p(RAX), p(RCX)]),
                inst(X86Opcode::AdcRR, vec![p(RBX), p(RAX)]),
                jcc(X86CondCode::E),
            ],
        );
        assert_clean(&adc_with_cf, &HashMap::new());
    }

    #[test]
    fn x86_partial_and_undefined_flag_producers_fail_closed_per_consumed_flag() {
        for (name, producer, cc, flag_name) in [
            (
                "div_undefined_zf",
                inst(X86Opcode::Div, vec![p(RBX)]),
                X86CondCode::E,
                "ZF",
            ),
            (
                "mul_undefined_zf",
                inst(X86Opcode::Mul, vec![p(RBX)]),
                X86CondCode::E,
                "ZF",
            ),
            (
                "bsf_undefined_cf",
                inst(X86Opcode::Bsf, vec![p(RAX), p(RBX)]),
                X86CondCode::B,
                "CF",
            ),
            (
                "bt_preserved_undefined_zf",
                inst(X86Opcode::BtRI, vec![p(RAX), imm(1)]),
                X86CondCode::E,
                "ZF",
            ),
        ] {
            let func = x86_func(name, vec![producer, jcc(cc)]);
            assert_flag_violation(
                &func,
                PostRaDataflowViolationKind::ReadOfUndefinedFlags,
                flag_name,
            );
        }
    }

    #[test]
    fn x86_partial_flag_producers_accept_defined_and_valid_preserved_flags() {
        for (name, insts) in [
            (
                "inc_defines_zf",
                vec![inst(X86Opcode::Inc, vec![p(RBX)]), jcc(X86CondCode::E)],
            ),
            (
                "cmp_inc_preserves_cf",
                vec![
                    inst(X86Opcode::CmpRR, vec![p(RAX), p(RCX)]),
                    inst(X86Opcode::Inc, vec![p(RBX)]),
                    jcc(X86CondCode::B),
                ],
            ),
            (
                "mul_defines_of",
                vec![inst(X86Opcode::Mul, vec![p(RBX)]), jcc(X86CondCode::O)],
            ),
            (
                "bsf_defines_zf",
                vec![
                    inst(X86Opcode::Bsf, vec![p(RAX), p(RBX)]),
                    jcc(X86CondCode::E),
                ],
            ),
            (
                "bt_defines_cf",
                vec![
                    inst(X86Opcode::BtRI, vec![p(RAX), imm(1)]),
                    jcc(X86CondCode::B),
                ],
            ),
            (
                "cmp_bt_preserves_zf",
                vec![
                    inst(X86Opcode::CmpRR, vec![p(RAX), p(RCX)]),
                    inst(X86Opcode::BtRI, vec![p(RAX), imm(1)]),
                    jcc(X86CondCode::E),
                ],
            ),
        ] {
            assert_clean(&x86_func(name, insts), &HashMap::new());
        }
    }

    #[test]
    fn x86_shift_flags_handle_zero_immediates_and_variable_counts_fail_closed() {
        for (name, insts, kind, flag_name) in [
            (
                "shift_zero_preserves_undefined_zf",
                vec![
                    inst(X86Opcode::ShlRI, vec![p(RAX), imm(0)]),
                    jcc(X86CondCode::E),
                ],
                PostRaDataflowViolationKind::ReadOfUndefinedFlags,
                "ZF",
            ),
            (
                "shift_masked_zero_preserves_undefined_zf",
                vec![
                    inst(X86Opcode::ShlRI, vec![p(RAX), imm(64)]),
                    jcc(X86CondCode::E),
                ],
                PostRaDataflowViolationKind::ReadOfUndefinedFlags,
                "ZF",
            ),
            (
                "shift32_masked_zero_preserves_undefined_zf",
                vec![
                    inst(X86Opcode::ShlRI, vec![p(EAX), imm(32)]),
                    jcc(X86CondCode::E),
                ],
                PostRaDataflowViolationKind::ReadOfUndefinedFlags,
                "ZF",
            ),
            (
                "shift_two_undefines_of",
                vec![
                    inst(X86Opcode::ShrRI, vec![p(RAX), imm(2)]),
                    jcc(X86CondCode::O),
                ],
                PostRaDataflowViolationKind::ReadOfUndefinedFlags,
                "OF",
            ),
            (
                "variable_shift_may_preserve_undefined_zf",
                vec![inst(X86Opcode::ShlRR, vec![p(RBX)]), jcc(X86CondCode::E)],
                PostRaDataflowViolationKind::ReadOfUndefinedFlags,
                "ZF",
            ),
            (
                "variable_shift_may_undefine_prior_of",
                vec![
                    inst(X86Opcode::CmpRR, vec![p(RAX), p(RBX)]),
                    inst(X86Opcode::ShlRR, vec![p(RBX)]),
                    jcc(X86CondCode::O),
                ],
                PostRaDataflowViolationKind::ReadOfUndefinedFlags,
                "OF",
            ),
            (
                "variable_shift_may_preserve_call_clobbered_zf",
                vec![
                    inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())]),
                    inst(X86Opcode::MovRI, vec![p(RCX), imm(2)]),
                    inst(X86Opcode::ShlRR, vec![p(RBX)]),
                    jcc(X86CondCode::E),
                ],
                PostRaDataflowViolationKind::ReadOfClobberedFlags,
                "ZF",
            ),
        ] {
            let func = x86_func(name, insts);
            assert_flag_violation(&func, kind, flag_name);
        }

        for (name, insts) in [
            (
                "shift_one_defines_of",
                vec![
                    inst(X86Opcode::SarRI, vec![p(RAX), imm(1)]),
                    jcc(X86CondCode::O),
                ],
            ),
            (
                "cmp_shift_zero_preserves_zf",
                vec![
                    inst(X86Opcode::CmpRR, vec![p(RAX), p(RBX)]),
                    inst(X86Opcode::ShlRI, vec![p(RAX), imm(0)]),
                    jcc(X86CondCode::E),
                ],
            ),
            (
                "cmp_variable_shift_keeps_zf_valid",
                vec![
                    inst(X86Opcode::CmpRR, vec![p(RAX), p(RBX)]),
                    inst(X86Opcode::ShlRR, vec![p(RBX)]),
                    jcc(X86CondCode::E),
                ],
            ),
        ] {
            assert_clean(&x86_func(name, insts), &HashMap::new());
        }
    }

    #[test]
    fn x86_narrow_scalar_xmm_bridge_cannot_certify_wider_tied_use() {
        let cases = [
            (X86Opcode::MovssRR, X86Opcode::Addsd, 4usize),
            (X86Opcode::MovssRR, X86Opcode::Paddd, 4usize),
            (X86Opcode::MovsdRR, X86Opcode::Paddd, 8usize),
        ];
        for (copy, tied_opcode, first_missing_lane) in cases {
            let func = x86_func(
                "scalar_width_launder",
                vec![
                    inst(copy, vec![p(XMM0), p(XMM1)]),
                    inst(tied_opcode, vec![p(XMM0), p(XMM1), p(XMM2)]),
                ],
            );
            let violations = check_x86_post_ra_dataflow(&func, &HashMap::new());
            assert!(
                violations.iter().any(|violation| {
                    violation.kind == PostRaDataflowViolationKind::TiedOperandValueMismatch
                        && violation
                            .detail
                            .contains(&format!("required byte lane {first_missing_lane}"))
                }),
                "{copy:?} must not certify {tied_opcode:?}: {violations:?}"
            );
        }
    }

    // ===================================================================
    // GREEN: the false-positive gauntlet (check() returns an empty vec)
    // ===================================================================

    fn assert_clean(func: &X86ISelFunction, alloc: &HashMap<VReg, X86PReg>) {
        let violations = check_x86_post_ra_dataflow(func, alloc);
        assert!(
            violations.is_empty(),
            "expected a clean stream, got: {:?}",
            violations
                .iter()
                .map(|v| (v.kind, v.detail.clone()))
                .collect::<Vec<_>>()
        );
    }

    /// The r1 shape WITH its bridge copy passes; neither mode records a hit.
    #[test]
    fn x86_bridge_copy_present_passes() {
        let _guard = counter_guard();
        let func = x86_func(
            "good",
            vec![
                inst(X86Opcode::MovRR, vec![p(RAX), p(RCX)]),
                inst(X86Opcode::AddRR, vec![g64(0), g64(1), g64(2)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let alloc = add_rr_alloc();
        assert_clean(&func, &alloc);
        let before = post_ra_dataflow_hit_count();
        assert!(evaluate(&func, &alloc, "x86_64", PostRegallocRecheckMode::Warn).is_none());
        assert!(evaluate(&func, &alloc, "x86_64", PostRegallocRecheckMode::Enforce).is_none());
        assert_eq!(post_ra_dataflow_hit_count(), before);
    }

    /// Tied destination overlapping the ghost across widths (RAX vs EAX)
    /// discharges via the overlap arm — no copy needed.
    #[test]
    fn x86_tied_overlap_across_widths_passes() {
        let func = x86_func(
            "good",
            vec![inst(X86Opcode::AddRR, vec![g64(0), g64(1), g64(2)])],
        );
        let alloc = amap(&[
            (0, RegClass::Gpr64, RAX),
            (1, RegClass::Gpr64, EAX),
            (2, RegClass::Gpr64, RDX),
        ]);
        assert_clean(&func, &alloc);
    }

    /// The commutative-swap fixup shape: operands[1] aliases operands[0].
    #[test]
    fn x86_commutative_swap_shape_passes() {
        let func = x86_func(
            "good",
            vec![inst(X86Opcode::AddRR, vec![g64(0), g64(2), g64(1)])],
        );
        let alloc = amap(&[
            (0, RegClass::Gpr64, RAX),
            (1, RegClass::Gpr64, RCX),
            (2, RegClass::Gpr64, RAX),
        ]);
        assert_clean(&func, &alloc);
    }

    /// The non-commutative scratch-triangle fixup shape.
    #[test]
    fn x86_scratch_triangle_passes() {
        let func = x86_func(
            "good",
            vec![
                inst(X86Opcode::MovRR, vec![p(R10), p(RCX)]),
                inst(X86Opcode::SubRR, vec![p(R10), p(R10), p(RDX)]),
                inst(X86Opcode::MovRR, vec![p(RAX), p(R10)]),
            ],
        );
        assert_clean(&func, &HashMap::new());
    }

    /// A MovRR32 bridge before a Gpr32 tied site.
    #[test]
    fn x86_movrr32_bridge_passes() {
        let func = x86_func(
            "good",
            vec![
                inst(
                    X86Opcode::MovRR32,
                    vec![v(0, RegClass::Gpr32), v(1, RegClass::Gpr32)],
                ),
                inst(
                    X86Opcode::AddRR,
                    vec![
                        v(0, RegClass::Gpr32),
                        v(1, RegClass::Gpr32),
                        v(2, RegClass::Gpr32),
                    ],
                ),
            ],
        );
        let alloc = amap(&[
            (0, RegClass::Gpr32, EAX),
            (1, RegClass::Gpr32, x86_64_regs::ECX),
            (2, RegClass::Gpr32, x86_64_regs::EDX),
        ]);
        assert_clean(&func, &alloc);
    }

    /// SSE bridges: MovsdRR before Addsd, MovdqaRR before Paddd, and a
    /// bridged 4-op Pinsrd.
    #[test]
    fn x86_sse_bridges_pass() {
        let func = x86_func(
            "good",
            vec![
                inst(X86Opcode::MovsdRR, vec![p(XMM0), p(XMM1)]),
                inst(X86Opcode::Addsd, vec![p(XMM0), p(XMM1), p(XMM2)]),
                inst(X86Opcode::MovdqaRR, vec![p(XMM3), p(XMM2)]),
                inst(X86Opcode::Paddd, vec![p(XMM3), p(XMM2), p(XMM1)]),
                inst(X86Opcode::MovdqaRR, vec![p(XMM1), p(XMM3)]),
                inst(X86Opcode::Pinsrd, vec![p(XMM1), p(XMM3), p(RCX), imm(1)]),
            ],
        );
        assert_clean(&func, &HashMap::new());
    }

    #[test]
    fn x86_scalar_xmm_bridge_accepts_equal_or_narrower_tied_lane() {
        for (copy, tied_opcode) in [
            (X86Opcode::MovssRR, X86Opcode::Addss),
            (X86Opcode::MovsdRR, X86Opcode::Addss),
            (X86Opcode::MovsdRR, X86Opcode::Addsd),
        ] {
            let func = x86_func(
                "scalar_width_exact",
                vec![
                    inst(copy, vec![p(XMM0), p(XMM1)]),
                    inst(tied_opcode, vec![p(XMM0), p(XMM1), p(XMM2)]),
                ],
            );
            assert_clean(&func, &HashMap::new());
        }
    }

    #[test]
    fn x86_cfg_flags_definitions_across_joins_and_loops_pass() {
        let join = x86_cfg_func(
            "flags_join",
            vec![
                (
                    vec![
                        inst(X86Opcode::CmpRR, vec![p(RAX), p(RCX)]),
                        inst(
                            X86Opcode::Jcc,
                            vec![
                                X86ISelOperand::CondCode(X86CondCode::E),
                                X86ISelOperand::Block(Block(1)),
                            ],
                        ),
                    ],
                    vec![1, 2],
                ),
                (
                    vec![
                        inst(X86Opcode::CmpRR, vec![p(RAX), p(RDX)]),
                        inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(3))]),
                    ],
                    vec![3],
                ),
                (
                    vec![
                        inst(X86Opcode::TestRR, vec![p(RCX), p(RCX)]),
                        inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(3))]),
                    ],
                    vec![3],
                ),
                (
                    vec![inst(
                        X86Opcode::Jcc,
                        vec![
                            X86ISelOperand::CondCode(X86CondCode::NE),
                            X86ISelOperand::Block(Block(3)),
                        ],
                    )],
                    vec![],
                ),
            ],
        );
        assert_clean(&join, &HashMap::new());

        let loop_func = x86_cfg_func(
            "flags_loop",
            vec![
                (
                    vec![
                        inst(X86Opcode::CmpRR, vec![p(RAX), p(RCX)]),
                        inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(1))]),
                    ],
                    vec![1],
                ),
                (
                    vec![inst(
                        X86Opcode::Jcc,
                        vec![
                            X86ISelOperand::CondCode(X86CondCode::E),
                            X86ISelOperand::Block(Block(1)),
                        ],
                    )],
                    vec![1, 2],
                ),
                (vec![inst(X86Opcode::Ret, vec![])], vec![]),
            ],
        );
        assert_clean(&loop_func, &HashMap::new());
    }

    /// The all-spilled shape: dst and lhs share one reload scratch, so the
    /// obligation discharges via overlap.
    #[test]
    fn x86_all_spilled_shared_scratch_passes() {
        let func = x86_func(
            "good",
            vec![
                inst(X86Opcode::MovRM, vec![p(R10), slot_mem(0)]),
                inst(X86Opcode::AddRR, vec![p(R10), p(R10), p(RDX)]),
                inst(X86Opcode::MovMR, vec![slot_mem(0), p(R10)]),
            ],
        );
        assert_clean(&func, &HashMap::new());
    }

    /// A folded packed rhs (spilled XMM rhs folded to a stack MemAddr at
    /// operands[2]) recurses the memory operand without double-counting.
    #[test]
    fn x86_folded_packed_rhs_passes() {
        let func = x86_func(
            "good",
            vec![
                inst(X86Opcode::MovdqaRR, vec![p(XMM0), p(XMM1)]),
                inst(X86Opcode::Paddd, vec![p(XMM0), p(XMM1), slot_mem(0)]),
            ],
        );
        assert_clean(&func, &HashMap::new());
    }

    /// The CDQ/IDIV and CQO/IDIV implicit RAX/RDX clusters.
    #[test]
    fn x86_cdq_idiv_and_cqo_idiv_pass() {
        let func = x86_func(
            "good",
            vec![
                inst(X86Opcode::MovRI, vec![p(RAX), imm(100)]),
                inst(X86Opcode::MovRI, vec![p(RCX), imm(7)]),
                inst(X86Opcode::Cdq, vec![]),
                inst(X86Opcode::Idiv, vec![p(RCX)]),
                inst(X86Opcode::Cqo, vec![]),
                inst(X86Opcode::Idiv, vec![p(RCX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        assert_clean(&func, &HashMap::new());
    }

    /// The unsigned mirror of the CDQ/CQO cluster: the isel lowers unsigned
    /// Div/Rem as `xor rdx,rdx; div` (tied 3-op `XorRR [rdx, rdx, rdx]`,
    /// x86_64_isel's "Zero-extend by clearing RDX/EDX"). The zero idiom is a
    /// pure def — RDX's prior value (here PURE call taint) is architecturally
    /// not consumed, so the site must pass and its def must launder the taint
    /// for the DIV's implicit RDX read and the remainder read after it.
    /// Pins the acc_loop/p12 false-positive class: every unsigned `/`/`%`
    /// reached after any call without an intervening RDX def failed closed.
    #[test]
    fn x86_xor_zero_idiom_unsigned_div_after_call_passes() {
        let func = x86_func(
            "good",
            vec![
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())])
                    .with_call_result_regs(vec![call_result(RAX, 64)]),
                inst(X86Opcode::MovRI, vec![p(RCX), imm(100)]),
                inst(X86Opcode::XorRR, vec![p(RDX), p(RDX), p(RDX)]),
                inst(X86Opcode::Div, vec![p(RCX)]),
                // Remainder read: RDX is now the DIV's def, not call taint.
                inst(X86Opcode::MovRR, vec![p(RBX), p(RDX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        assert_clean(&func, &HashMap::new());
    }

    /// The XMM sibling: `Pxor [x, x]` (the in-place 2-op vector-zero shape
    /// pipeline/isel emit, same-VReg operands) is a pure 16-byte def; all 16
    /// XMM are SysV caller-saved, so after a void call the register carries
    /// pure call taint that the idiom must launder. The tied 3-op same-reg
    /// form is exempt identically.
    #[test]
    fn x86_pxor_zero_idiom_after_call_passes() {
        let xmm = |id| v(id, RegClass::Fpr128);
        let func = x86_func(
            "good",
            vec![
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())]),
                // 2-op production shape, same VReg twice (isel clones dst_op).
                inst(X86Opcode::Pxor, vec![xmm(0), xmm(0)]),
                // Tied 3-op same-reg sibling on a second tainted register.
                inst(X86Opcode::Pxor, vec![p(XMM3), p(XMM3), p(XMM3)]),
                // Both zeroes are readable: tied Paddd reads XMM2 and XMM3.
                inst(X86Opcode::Paddd, vec![p(XMM2), p(XMM2), p(XMM3)]),
            ],
        );
        let alloc = amap(&[(0, RegClass::Fpr128, XMM2)]);
        assert_clean(&func, &alloc);
    }

    /// The acc_loop O0 false-positive shape (2026-07-13), as a CFG: a
    /// black_box-call loop whose exit block computes an unsigned `% 100` via
    /// the `xor rdx,rdx; div` cluster. On the loop path nothing defines RDX
    /// between the last call and the idiom, which is exactly the stream that
    /// falsely failed closed with read-of-call-clobbered-reg on the XorRR.
    #[test]
    fn x86_acc_loop_call_then_unsigned_rem_cfg_passes() {
        let call = || {
            inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("bb".into())])
                .with_call_result_regs(vec![call_result(RAX, 64)])
        };
        let func = x86_cfg_func(
            "acc_loop",
            vec![
                // Entry: acc lives in callee-saved RBX.
                (
                    vec![call(), inst(X86Opcode::MovRR, vec![p(RBX), p(RAX)])],
                    vec![1],
                ),
                // Loop body: call + tied accumulate + latch.
                (
                    vec![
                        call(),
                        inst(X86Opcode::AddRR, vec![p(RBX), p(RBX), p(RAX)]),
                        inst(X86Opcode::CmpRI, vec![p(RBX), imm(1000)]),
                        inst(
                            X86Opcode::Jcc,
                            vec![
                                X86ISelOperand::CondCode(X86CondCode::B),
                                X86ISelOperand::Block(Block(1)),
                            ],
                        ),
                    ],
                    vec![1, 2],
                ),
                // Exit: acc % 100 — RDX carries only call taint here.
                (
                    vec![
                        inst(X86Opcode::MovRR, vec![p(RAX), p(RBX)]),
                        inst(X86Opcode::MovRI, vec![p(RCX), imm(100)]),
                        inst(X86Opcode::XorRR, vec![p(RDX), p(RDX), p(RDX)]),
                        inst(X86Opcode::Div, vec![p(RCX)]),
                        inst(X86Opcode::MovRR, vec![p(RDI), p(RDX)]),
                        inst(X86Opcode::Ret, vec![]),
                    ],
                    vec![],
                ),
            ],
        );
        assert_clean(&func, &HashMap::new());
    }

    /// A bridged shift-by-CL: MovRI CL setup + 2-op ShlRR with its bridge.
    #[test]
    fn x86_shl_by_cl_passes() {
        let func = x86_func(
            "good",
            vec![
                inst(X86Opcode::MovRI, vec![p(RCX), imm(5)]),
                inst(X86Opcode::MovRR, vec![p(RAX), p(RBX)]),
                inst(X86Opcode::ShlRR, vec![p(RAX), p(RBX)]),
            ],
        );
        assert_clean(&func, &HashMap::new());
    }

    /// Call argument/return traffic: arg setup, call, then reading the RAX
    /// return value — zero violations of ANY tier (RAX is a Def after the
    /// call, not a clobber).
    #[test]
    fn x86_call_ret_read_passes() {
        let func = x86_func(
            "good",
            vec![
                inst(X86Opcode::MovRI, vec![p(RDI), imm(1)]),
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())])
                    .with_call_arg_regs(vec![call_arg(RDI, 64)])
                    .with_call_result_regs(vec![call_result(RAX, 64)]),
                inst(X86Opcode::MovRR, vec![p(RBX), p(RAX)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        assert_clean(&func, &HashMap::new());
    }

    /// THE narrow-call-arg-after-call shape (the REGALLOC-063 abort-mode
    /// false positive, 2026-07-13): after an earlier call clobbers RSI, the
    /// next call's arg setup defines ONLY byte 0 of SIL — a 1-byte fieldless
    /// enum (`atomic::Ordering`) is passed as plain i8 with NO caller-owed
    /// zero/sign-extension (SysV + LLVM ground truth), so the callee may
    /// consume only that byte. With the call's declared 8-bit read of RSI,
    /// the stale upper lanes 0x00fe must NOT fire
    /// read-of-call-clobbered-reg. Before per-arg widths this exact stream
    /// failed closed ("reads caller-clobbered byte lanes 0x00fe"), rejecting
    /// every abort-mode program that passes a narrow enum/bool/u8 by value
    /// after another call (e.g. any O0 atomic op taking an `Ordering`).
    #[test]
    fn x86_narrow_call_arg_after_call_passes() {
        let func = x86_func(
            "good",
            vec![
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())])
                    .with_call_result_regs(vec![call_result(RAX, 64)]),
                // Arg setup: self pointer (full 64-bit) + the Ordering
                // discriminant byte-loaded into SIL (defines lane 0 only).
                inst(X86Opcode::MovRI, vec![p(RDI), imm(1)]),
                inst(X86Opcode::MovRM8, vec![p(SIL), slot_mem(0)]),
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("g".into())])
                    .with_call_arg_regs(vec![call_arg(RDI, 64), call_arg(RSI, 8)])
                    .with_call_result_regs(vec![call_result(RAX, 64)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        assert_clean(&func, &HashMap::new());
    }

    /// The genuine-detection refutation for the per-arg-width fix: the SAME
    /// stream with the argument declared WIDE (a u64 in RSI) must still fail
    /// closed — the callee is entitled to all 8 bytes and lanes 1-7 hold the
    /// earlier call's clobber. Pins that narrowing is driven ONLY by the
    /// lowering's declared width, never by what the setup happened to define.
    #[test]
    fn x86_wide_call_arg_with_tainted_upper_lanes_still_fails() {
        let func = x86_func(
            "bad",
            vec![
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())])
                    .with_call_result_regs(vec![call_result(RAX, 64)]),
                inst(X86Opcode::MovRM8, vec![p(SIL), slot_mem(0)]),
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("g".into())])
                    .with_call_arg_regs(vec![call_arg(RSI, 64)])
                    .with_call_result_regs(vec![call_result(RAX, 64)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let violations = check_x86_post_ra_dataflow(&func, &HashMap::new());
        assert!(
            violations.iter().any(|v| v.kind
                == PostRaDataflowViolationKind::ReadOfCallClobberedReg
                && v.detail.contains("0x00fe")),
            "wide arg with call-tainted upper lanes must still fail closed: {violations:?}"
        );
    }

    /// Call-ARGUMENT width metadata is schema-checked like the result side:
    /// an inadmissible width (zero, non-lane, GPR>64, XMM sub-16) is
    /// malformed-operands (fail-closed), never a silently narrowed read.
    #[test]
    fn x86_call_arg_metadata_invalid_widths_fail_closed() {
        let cases = [
            call_arg(RSI, 0),
            call_arg(RSI, 24),
            call_arg(RSI, 128),
            call_arg(XMM0, 8),
        ];
        for bad in cases {
            let func = x86_func(
                "malformed_call_args",
                vec![
                    inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("f".into())])
                        .with_call_arg_regs(vec![bad])
                        .with_call_result_regs(vec![]),
                ],
            );
            let violations = check_x86_post_ra_dataflow(&func, &HashMap::new());
            assert!(
                violations
                    .iter()
                    .any(|v| v.kind == PostRaDataflowViolationKind::MalformedOperands),
                "invalid call-arg width must fail closed: {violations:?}"
            );
        }
    }

    /// A full prologue/epilogue block (the exact shapes the frame stage
    /// emits: Push/MovRR RBP<-RSP/2-op SubRI/2-op AddRI/Pop/Ret).
    #[test]
    fn x86_prologue_epilogue_block_passes() {
        let func = x86_func(
            "good",
            vec![
                inst(X86Opcode::Push, vec![p(RBP)]),
                inst(X86Opcode::MovRR, vec![p(RBP), p(RSP)]),
                inst(X86Opcode::Push, vec![p(RBX)]),
                inst(X86Opcode::SubRI, vec![p(RSP), imm(32)]),
                inst(X86Opcode::MovRI, vec![p(RAX), imm(0)]),
                inst(X86Opcode::AddRI, vec![p(RSP), imm(32)]),
                inst(X86Opcode::Pop, vec![p(RBX)]),
                inst(X86Opcode::Pop, vec![p(RBP)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        assert_clean(&func, &HashMap::new());
    }

    /// The dynamic-alloc expansion shape (all in-place 2-op forms).
    #[test]
    fn x86_dyn_alloc_expansion_shape_passes() {
        let func = x86_func(
            "good",
            vec![
                inst(X86Opcode::MovRI, vec![p(RAX), imm(40)]),
                inst(X86Opcode::AddRI, vec![p(RAX), imm(15)]),
                inst(X86Opcode::AndRI, vec![p(RAX), imm(-16)]),
                inst(X86Opcode::SubRR, vec![p(RSP), p(RAX)]),
                inst(X86Opcode::MovRR, vec![p(RAX), p(RSP)]),
            ],
        );
        assert_clean(&func, &HashMap::new());
    }

    /// In-place forms carry no tied obligation.
    #[test]
    fn x86_in_place_forms_pass() {
        let func = x86_func(
            "good",
            vec![
                inst(X86Opcode::AddRR, vec![p(RAX), p(RCX)]),
                inst(X86Opcode::AddRI, vec![p(RAX), imm(1)]),
                inst(X86Opcode::Neg, vec![p(RAX)]),
                inst(X86Opcode::Inc, vec![p(RAX)]),
                inst(X86Opcode::Dec, vec![p(RAX)]),
                inst(X86Opcode::Bswap, vec![p(RAX)]),
                inst(X86Opcode::ShlRI, vec![p(RAX), imm(3)]),
            ],
        );
        assert_clean(&func, &HashMap::new());
    }

    /// An Xchg swap routes a value into the ghost's register: the tied
    /// obligation discharges through the swapped syms.
    #[test]
    fn x86_xchg_swap_passes() {
        let func = x86_func(
            "good",
            vec![
                // RDX := value(RCX).
                inst(X86Opcode::MovRR, vec![p(RDX), p(RCX)]),
                // Swap: RSI now holds value(RCX); RDX holds old RSI.
                inst(X86Opcode::Xchg, vec![p(RDX), p(RSI)]),
                // Bridge for the tied site (dst RBX <- lhs RSI)...
                inst(X86Opcode::MovRR, vec![p(RBX), p(RSI)]),
                // ...whose ghost RSI carries the swapped-in value.
                inst(X86Opcode::AddRR, vec![p(RBX), p(RSI), p(R8)]),
            ],
        );
        assert_clean(&func, &HashMap::new());
    }

    /// CMP + Jcc in the same block, and a SIB load with VReg base and index.
    #[test]
    fn x86_cmp_jcc_and_sib_memaddr_pass() {
        let func = x86_func(
            "good",
            vec![
                inst(X86Opcode::CmpRR, vec![p(RAX), p(RCX)]),
                inst(
                    X86Opcode::Jcc,
                    vec![
                        X86ISelOperand::CondCode(X86CondCode::E),
                        X86ISelOperand::Block(Block(0)),
                    ],
                ),
                inst(
                    X86Opcode::MovRMSib,
                    vec![
                        g64(0),
                        X86ISelOperand::SibMemAddr {
                            base: Box::new(g64(1)),
                            index: Box::new(g64(2)),
                            scale: 8,
                            disp: 0,
                        },
                    ],
                ),
            ],
        );
        let alloc = amap(&[
            (0, RegClass::Gpr64, RAX),
            (1, RegClass::Gpr64, RSI),
            (2, RegClass::Gpr64, R9),
        ]);
        assert_clean(&func, &alloc);
    }

    /// The memory-form exchange (`xchg reg, [mem]` — the ISel atomic-swap
    /// bridge): register read+freshly-defined, address registers read.
    #[test]
    fn x86_xchg_memory_form_passes() {
        let func = x86_func(
            "good",
            vec![
                inst(X86Opcode::Xchg, vec![p(RAX), base_mem(p(RBX))]),
                // The freshly-defined register is immediately usable.
                inst(X86Opcode::MovRR, vec![p(RCX), p(RAX)]),
            ],
        );
        assert_clean(&func, &HashMap::new());
    }

    /// An atomic CAS-loop pseudo with a memory operand.
    #[test]
    fn x86_cas_loop_passes() {
        let func = x86_func(
            "good",
            vec![inst(
                X86Opcode::AtomicRmwCasLoop8,
                vec![
                    p(x86_64_regs::ECX),
                    p(x86_64_regs::EDI),
                    base_mem(p(RBX)),
                    imm(0),
                ],
            )],
        );
        assert_clean(&func, &HashMap::new());
    }

    // ===================================================================
    // Mode + mirror pins
    // ===================================================================

    /// Off mode skips entirely: no verdict, no counter bump.
    #[test]
    fn x86_off_mode_skips() {
        let _guard = counter_guard();
        let func = x86_func(
            "bad",
            vec![
                inst(X86Opcode::AddRR, vec![g64(0), g64(1), g64(2)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let before = post_ra_dataflow_hit_count();
        assert!(
            evaluate(
                &func,
                &add_rr_alloc(),
                "x86_64",
                PostRegallocRecheckMode::Off
            )
            .is_none()
        );
        assert_eq!(post_ra_dataflow_hit_count(), before);
    }

    /// Pin the verify-owned tied-index mirror to codegen's
    /// `x86_two_address_lhs_operand_index` semantics.
    #[test]
    fn x86_tied_index_mirror_pinned() {
        let some1 = Some(1);
        // Two-address RR: tied at 3 operands, in-place at 2.
        assert_eq!(
            post_ra_tied_lhs_index(&inst(X86Opcode::AddRR, vec![g64(0), g64(1), g64(2)])),
            some1
        );
        assert_eq!(
            post_ra_tied_lhs_index(&inst(X86Opcode::AddRR, vec![g64(0), g64(1)])),
            None
        );
        // ALU reg-imm: tied at 3 operands, in-place at 2.
        assert_eq!(
            post_ra_tied_lhs_index(&inst(X86Opcode::AddRI, vec![g64(0), g64(1), imm(1)])),
            some1
        );
        assert_eq!(
            post_ra_tied_lhs_index(&inst(X86Opcode::AddRI, vec![g64(0), imm(1)])),
            None
        );
        // Shift-by-imm: tied at 3 operands, in-place at 2.
        assert_eq!(
            post_ra_tied_lhs_index(&inst(X86Opcode::ShlRI, vec![g64(0), g64(1), imm(1)])),
            some1
        );
        assert_eq!(
            post_ra_tied_lhs_index(&inst(X86Opcode::ShlRI, vec![g64(0), imm(1)])),
            None
        );
        // Shift-by-CL: tied at 2 operands, in-place at 1.
        assert_eq!(
            post_ra_tied_lhs_index(&inst(X86Opcode::ShlRR, vec![g64(0), g64(1)])),
            some1
        );
        assert_eq!(
            post_ra_tied_lhs_index(&inst(X86Opcode::ShlRR, vec![g64(0)])),
            None
        );
        // Explicit-source unary: tied at 2 operands, in-place at 1.
        assert_eq!(
            post_ra_tied_lhs_index(&inst(X86Opcode::Neg, vec![g64(0), g64(1)])),
            some1
        );
        assert_eq!(
            post_ra_tied_lhs_index(&inst(X86Opcode::Neg, vec![g64(0)])),
            None
        );
        // Pinsr: tied at 4 operands, in-place at 3.
        assert_eq!(
            post_ra_tied_lhs_index(&inst(
                X86Opcode::Pinsrd,
                vec![g64(0), g64(1), g64(2), imm(0)]
            )),
            some1
        );
        assert_eq!(
            post_ra_tied_lhs_index(&inst(X86Opcode::Pinsrd, vec![g64(0), g64(1), imm(0)])),
            None
        );
        // Non-tied opcodes never report a ghost.
        assert_eq!(
            post_ra_tied_lhs_index(&inst(X86Opcode::Lea, vec![g64(0), base_mem(p(RBP))])),
            None
        );
        assert_eq!(
            post_ra_tied_lhs_index(&inst(X86Opcode::ImulRRI, vec![g64(0), g64(1), imm(4)])),
            None
        );
    }

    /// The compiled-in default is ENFORCE (no env mutation in tests).
    #[test]
    fn x86_default_mode_is_enforce() {
        assert_eq!(
            X86_POST_RA_DATAFLOW_DEFAULT,
            PostRegallocRecheckMode::Enforce
        );
    }

    // ===================================================================
    // XMM lane-wise garbage flow (the scalar-float-across-libcall class)
    // + the Ret result-register read model
    // ===================================================================

    /// Build a single-block function with an explicit scalar return
    /// signature, for the `Ret` result-register read model.
    fn x86_ret_func(name: &str, returns: Vec<Type>, insts: Vec<X86ISelInst>) -> X86ISelFunction {
        let mut func = X86ISelFunction::new(
            name.to_string(),
            Signature {
                params: vec![],
                returns,
            },
        );
        let block = Block(0);
        func.ensure_block(block);
        func.blocks.get_mut(&block).unwrap().insts.extend(insts);
        func
    }

    /// THE acceptance shape (probe `p9_f32` O2, previously fail-closed): a
    /// libcall returns a 32-bit scalar in XMM0 — upper lanes are
    /// call-clobbered garbage — and the min/max/clamp lowering routes the
    /// FULL register through MovdqaRR + packed bitwise blend ops before
    /// consuming only the scalar lane. The garbage flows lane-wise and is
    /// never semantically read, so the function must be CLEAN.
    #[test]
    fn x86_packed_bitwise_blend_after_scalar_xmm_call_result_passes() {
        let func = x86_func(
            "f32_blend",
            vec![
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("fmaf".into())])
                    .with_call_result_regs(vec![call_result(XMM0, 32)]),
                // Blend mask defined AFTER the call (zero idiom): fully clean.
                inst(X86Opcode::Pxor, vec![p(XMM2), p(XMM2)]),
                inst(X86Opcode::MovdqaRR, vec![p(XMM1), p(XMM0)]),
                inst(X86Opcode::Pand, vec![p(XMM1), p(XMM2)]),
                inst(X86Opcode::Por, vec![p(XMM1), p(XMM2)]),
                // Semantic consumer reads ONLY the defined scalar lane.
                inst(X86Opcode::MovssMR, vec![base_mem(p(RBX)), p(XMM1)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        );
        let violations = check_x86_post_ra_dataflow(&func, &HashMap::new());
        assert!(violations.is_empty(), "{violations:?}");
    }

    /// Same routing, but the flowed garbage reaches a packed op that is NOT
    /// lane-wise-exempt (Paddd reads all 16 bytes semantically): the taint
    /// must still fail closed at that consumer.
    #[test]
    fn x86_packed_garbage_reaching_non_lanewise_op_still_fails() {
        let func = x86_func(
            "packed_semantic_use",
            vec![
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("fmaf".into())])
                    .with_call_result_regs(vec![call_result(XMM0, 32)]),
                inst(X86Opcode::MovdqaRR, vec![p(XMM1), p(XMM0)]),
                inst(X86Opcode::Paddd, vec![p(XMM1), p(XMM1)]),
            ],
        );
        let violations = check_x86_post_ra_dataflow(&func, &HashMap::new());
        assert!(
            violations.iter().any(|v| v.kind
                == PostRaDataflowViolationKind::ReadOfCallClobberedReg
                && v.detail.contains("Paddd")),
            "{violations:?}"
        );
    }

    /// The packed bitwise def must NOT launder taint clean: garbage in the
    /// SCALAR lane (a void call clobbers all of XMM0) flows through the
    /// blend ops and must still fail closed when the scalar lane is finally
    /// consumed.
    #[test]
    fn x86_packed_bitwise_cannot_launder_scalar_lane_garbage() {
        let func = x86_func(
            "launder_attempt",
            vec![
                inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("g".into())]),
                inst(X86Opcode::Pxor, vec![p(XMM2), p(XMM2)]),
                inst(X86Opcode::MovdqaRR, vec![p(XMM1), p(XMM0)]),
                inst(X86Opcode::Pand, vec![p(XMM1), p(XMM2)]),
                inst(X86Opcode::MovssMR, vec![base_mem(p(RBX)), p(XMM1)]),
            ],
        );
        let violations = check_x86_post_ra_dataflow(&func, &HashMap::new());
        assert!(
            violations.iter().any(|v| v.kind
                == PostRaDataflowViolationKind::ReadOfCallClobberedReg
                && v.detail.contains("MovssMR")),
            "{violations:?}"
        );
    }

    /// `Ret` reads the function's declared scalar result lanes (the closed
    /// "Ret v1 miss"): a return register holding only call-clobber garbage
    /// at `Ret` fails closed, and a call result legitimately routed to `Ret`
    /// stays clean — for both the XMM and the GPR return channels.
    #[test]
    fn x86_ret_reads_declared_scalar_return_lanes() {
        for (returns, result, name) in [
            (vec![Type::F64], call_result(XMM0, 64), "ret_f64"),
            (vec![Type::I64], call_result(RAX, 64), "ret_i64"),
        ] {
            let garbage = x86_ret_func(
                &format!("{name}_garbage"),
                returns.clone(),
                vec![
                    // Void call: clobbers every conventional result register.
                    inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("g".into())]),
                    inst(X86Opcode::Ret, vec![]),
                ],
            );
            let violations = check_x86_post_ra_dataflow(&garbage, &HashMap::new());
            assert!(
                violations.iter().any(|v| v.kind
                    == PostRaDataflowViolationKind::ReadOfCallClobberedReg
                    && v.detail.contains("Ret")),
                "{name}: {violations:?}"
            );

            let clean = x86_ret_func(
                &format!("{name}_clean"),
                returns,
                vec![
                    inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("g".into())])
                        .with_call_result_regs(vec![result]),
                    inst(X86Opcode::Ret, vec![]),
                ],
            );
            let violations = check_x86_post_ra_dataflow(&clean, &HashMap::new());
            assert!(violations.is_empty(), "{name}: {violations:?}");
        }
    }
}
