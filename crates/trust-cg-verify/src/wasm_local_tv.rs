// trust-cg-verify/wasm_local_tv.rs - translation validation of wasm local emission
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Translation validation of the wasm32 lane's LOCAL emission pass
//! (`trust-cg-codegen` `wasm/opt.rs`): local colouring, self-copy deletion,
//! local reordering, constant rematerialization, single-use stackification
//! (`local.tee`, dead-definition `drop` and vacuum), memarg offset folding,
//! narrow-canonicalization elimination and the load/store expansion of small
//! `memory.copy`s.
//!
//! [`validate`] is given two bodies of ONE function — the lane's own lowering
//! output (PRE) and the rewritten body (POST) — the IMAGE the rewrite claims
//! for every pre local (the post local that holds its value, a constant it
//! always equals, or nothing) and, optionally, a FACT claimed for every pre
//! local (an unsigned upper bound and a sign-extension width, see
//! [`LocalFacts`]). It decodes both bodies independently with
//! [`crate::wasm_cfg_proofs::decode_body`] and accepts only when:
//!
//! 1. **Control is structurally identical.** The two bodies have the same
//!    sequence of control instructions (`block`, `loop`, `if`, `else`, `end`,
//!    `br`, `br_if`, `br_table`, `return`, `unreachable`) with equal
//!    immediates. The runs of other instructions between them are the
//!    SEGMENTS; segment `k` of one body corresponds to segment `k` of the
//!    other, and both bodies have the same segment successor relation.
//! 2. **Every segment is equivalent** under the boundary invariant below. Both
//!    segments are executed symbolically over hash-consed terms (pure
//!    operations build terms; every other instruction is an EFFECT whose
//!    results are opaque symbols named by its position in the trace; a float
//!    operation whose NaN result is nondeterministic builds one term per
//!    EVALUATION, the `k`-th on given operands matching only the other
//!    side's `k`-th, so a rewrite that evaluates it twice where the pre body
//!    evaluated it once does not compare equal), and the segment is accepted
//!    when
//!    - the ordered effect traces are equal: the same loads, stores, calls,
//!      `call_indirect`s, `global.get`/`global.set`s, `memory.size`/`grow`,
//!      `memory.copy`/`fill`, and trapping arithmetic (integer division and
//!      remainder, trapping float-to-int truncation), with equal immediates
//!      and equal operand terms;
//!    - the end operand stacks are equal (the same number of values taken
//!      from below the segment's start, and equal pushed terms);
//!    - every pre local live out of the segment equals its image in the post
//!      state, and satisfies its claimed fact (below).
//!
//!    Two terms are equal when they are the same hash-consed node. Integer
//!    residuals that are not syntactically equal go to the `ay` solver under
//!    [`ResidualPolicy::Solver`]; only an independently certified `unsat`
//!    ([`crate::ay_bridge::AYResult::Verified`]) accepts one, and every other
//!    answer, a float or untyped residual, or [`ResidualPolicy::Refuse`]
//!    rejects the function.
//!
//! **The boundary invariant.** At the start of every segment the two operand
//! stacks are equal, and every pre local live into the segment equals its
//! image. The first segment starts from the function entry state itself
//! (parameters and zero-initialized declared locals on both sides), so it
//! assumes nothing. Every other segment ASSUMES the invariant — a live pre
//! local reads the shared symbol of its image, an untracked local reads a
//! symbol private to its side — and the invariant is CHECKED at the end of
//! every predecessor for the union of its successors' live-in sets. Control
//! instructions are identical and see equal stacks, so they take the same
//! edge on both sides. By induction over the executed segments the two bodies
//! perform the same effects and return the same values.
//!
//! **Stack heights.** Values a segment takes from below its start are
//! symbols shared by both sides, equal by the boundary invariant only where
//! the stack really holds them. The validator therefore re-checks its own
//! stack accounting against WebAssembly's typing (function entry and every
//! `block`, `loop`, `if` and `else` arm start with an empty frame; `end`
//! leaves the frame's results): a reachable segment that takes more values
//! than its frame holds, or a reachable frame that ends with another count
//! than its results, means a symbolic rule dropped or invented a value, and
//! the function is refused. `global.get` pushes its result, typed by
//! [`TvTypes::global`]. Only memory 0 is modelled: a memarg with a memory
//! index or a bulk or `memory.size`/`grow` operation on another memory is
//! refused.
//!
//! The liveness sets only make the check complete, not sound: a local the
//! liveness under-approximates reads a side-private symbol, so any use of it
//! fails the comparison instead of being assumed equal. The liveness used is
//! STRONG liveness of the pre body: a local is live into a segment only when
//! its value there can reach an effect operand, a segment's end stack, or a
//! live local — so a pre local read only by code the rewrite deleted as dead
//! need not survive in its image.
//!
//! **Known bits and canonical terms.** Every integer term carries a FACT
//! derived from its own structure only: an unsigned upper bound and the
//! smallest width it is the sign extension of (a constant by its value, a
//! narrow load by its width, a comparison as 0 or 1, a mask, an extension,
//! and so on through `and`/`or`/`xor`/`select`/shifts/wrap/extend). Three
//! identities are applied when a term is built, on both sides alike, so an
//! eliminated instruction leaves the same node behind: `x & (2^k - 1)` is `x`
//! when the fact bounds `x` by `2^k - 1`; `extendN_s(x)` is `x` when `x` is
//! already the sign extension of its low `N` bits; `x + 0` is `x`.
//!
//! **Facts across boundaries.** A claimed fact of a pre local is ASSUMED of
//! the shared symbol at the start of every segment the local is live into,
//! and CHECKED, from the pre term's own fact, at the end of every segment the
//! local is live out of — the same induction as the boundary invariant, so a
//! claim that does not hold rejects the function. At the end of a segment
//! that ends in `if` whose `then` arm is an immediate `unreachable` (the
//! lane's stack-pointer guard), the check may use the guard's condition being
//! zero: `x >u y` false gives `x <=u y`, and a frame base `x = y - k` (or that
//! value realigned down by a power-of-two mask, when `2k + align <= 2^32`)
//! with `x <=u y` did not wrap, so `x <= 2^32 - 1 - k`.
//!
//! **Addresses.** A load's or store's effective address is compared as a
//! base term plus a static offset: an address `b + c` (an `i32.add` of a
//! constant) contributes `c` to the offset when the fact of `b` bounds `b + c`
//! below `2^32` — the `i32.add` cannot wrap, so the 33-bit effective address
//! `b + c + offset` the access computes is the same either way. That is the
//! no-wrap side condition of memarg offset folding
//! (`wasm_memarg_offset_proofs::memarg_fold_obligation` states it as an
//! obligation). `memory.copy` and `memory.fill` addresses are compared the
//! same way with offset 0; a relocated memarg is compared as written.
//!
//! **No-wrap premises.** [`validate_with_premises`] also takes premises
//! [`crate::wasm_nowrap_premise::check_nowrap_premises`] re-derived from the
//! trust-ir function: pre local `V` is written by `B + I` (or `B + I * s`)
//! lowering a GEP, an addition that does not wrap in any execution in which
//! the GEP is defined. A premise is active only for the function and pre
//! body it is bound to (the body it was derived on, or that body's control
//! cleanup when [`validate_control_with_premises`] carried it there), and
//! only when the pre body writes `V` exactly once. When the pre body writes `V` there, with a value that IS
//! the sum of the values `B` and `I` hold at that point (the same
//! hash-consed node), that sum is marked as not wrapping, from the pre
//! segment's current effect count on: the `k`-th effect of either side may
//! absorb a marked `x + c` into its static offset when the mark was made
//! before the pre body's `k`-th effect, whatever bounds `x`. Effects before
//! the mark are compared without it, so a fold never moves an access ahead
//! of the GEP that licenses it. With premises the relation is conditional:
//! the bodies agree on every execution in which the premised GEPs are
//! defined (`wasm_nowrap_premise` says what that rests on).
//!
//! **Small copies.** Where the pre body performs `memory.copy(d, s, n)` with a
//! constant `1 <= n <= 32` ([`MAX_EXPANDED_COPY`]), the post body may perform
//! instead a run of loads followed by a run of stores, nothing else effectful
//! between them, such that every load reads `s` and every store writes `d`
//! (as base plus offset), each store writes exactly the value of one distinct
//! load of the same width (`i64`, `i32`, 16 or 8 bits, zero-extending) at the
//! same relative offset, the loads tile `[0, n)` exactly, and the FIRST store
//! is the chunk that ends at `n`. All loads precede all stores, so the copy
//! reads the source as it was even when the ranges overlap; the source end is
//! read before any store and the destination end is the first byte written,
//! so the run traps exactly when `memory.copy` traps (`s + n` or `d + n` past
//! the memory) and then writes nothing. Such a run is compared as that one
//! `memory.copy`; the loaded values are symbols private to the post side.
//!
//! **Control cleanup.** [`validate_control`] checks the pass's other kind of
//! rewrite, which changes the control skeleton and leaves every other
//! instruction alone (removed branches, returns, dead code, unnamed blocks,
//! empty `else` arms, `if` arms turned into `br_if`): a lockstep simulation
//! of the two bodies over pairs of program points, described in
//! `wasm_local_tv_control.rs`. The pass runs it before the rewrites above,
//! so the PRE body [`validate`] compares against is the cleaned body.
//!
//! **What this does not claim.** The relation is between the lane's PRE body
//! and its POST body: an emission-level equivalence of one function, given
//! the function and type signatures the caller supplies for its calls. It says
//! nothing about whether the pre body computes what the trust-ir function
//! computes, and nothing about any other function.

use std::collections::{BTreeMap, HashMap};
use std::fmt;

use crate::smt::SmtExpr;
use crate::wasm_cfg_proofs::{DecodedInst, FuncSig, Imm, ValKind, decode_body};
use crate::wasm_nowrap_premise::NoWrapPremise;
use crate::wasm_semantics as sem;

#[path = "wasm_local_tv_control.rs"]
mod control;

pub use control::{ControlTvReport, ControlTvRequest, validate_control};

/// [`validate_control`], carrying the no-wrap `premises` bound to the
/// cleanup's pre body over to its post body when the cleanup is accepted.
/// A premise bound to another body is dropped.
///
/// **Why a premise carries over.** The lockstep simulation pairs every real
/// instruction POST executes with a byte-identical PRE instruction executed
/// on equal locals, stack, memory and globals, and the cleanup keeps the
/// declared locals. So every execution of POST's write of the premise's
/// local `V` is an execution of a PRE write of `V`, the only one (the
/// checker counted it), in an equal state: the value written, and the
/// values `B` and `I` hold, are those of the PRE write whose addition the
/// premise says does not wrap in an execution in which the GEP is defined.
/// The cleanup only deletes control, unreached code and `else` arms and
/// turns `if; br; end` into `br_if`, so it never writes `V` where PRE does
/// not; [`validate_with_premises`] still re-checks, on the cleaned body,
/// that `V` is written once and that the value written is `B + I`.
pub fn validate_control_with_premises(
    req: &ControlTvRequest<'_>,
    premises: &[NoWrapPremise],
) -> Result<(ControlTvReport, Vec<NoWrapPremise>), TvFailure> {
    let report = validate_control(req)?;
    let (from, to) = (
        crate::wasm_nowrap_premise::digest(req.pre.code),
        crate::wasm_nowrap_premise::digest(req.post.code),
    );
    let carried = premises
        .iter()
        .filter_map(|p| p.carried(from, to))
        .collect();
    Ok((report, carried))
}

/// One relocation of a body, as an opaque identity: the linker rewrites the
/// field at `offset` from `(kind, target, addend)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TvReloc {
    /// Byte offset of the relocated field within the body's code.
    pub offset: u32,
    /// The relocation kind.
    pub kind: u8,
    /// The relocation target, encoded by the caller (class and index).
    pub target: u64,
    /// The addend.
    pub addend: i32,
}

/// One function body: its declared (non-parameter) locals, code without the
/// trailing `end`, and relocations.
#[derive(Debug, Clone, Copy)]
pub struct TvBody<'a> {
    /// Declared locals in index order (parameters excluded).
    pub locals: &'a [ValKind],
    /// The instruction bytes, without the function's final `end`.
    pub code: &'a [u8],
    /// Relocations against `code`.
    pub relocs: &'a [TvReloc],
}

/// Where a pre local's value lives in the post body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LocalImage {
    /// Post local (parameters included in the index space).
    Local(u32),
    /// The local always equals this constant: the bytes of one `i32.const`,
    /// `i64.const`, `f32.const` or `f64.const` instruction.
    Const(Vec<u8>),
    /// The post body has no counterpart: the local may never be live at a
    /// segment boundary.
    Unused,
}

/// A fact about an integer value: an unsigned upper bound of its bits, and
/// the smallest width `s` such that the value equals the sign extension of
/// its low `s` bits. As a claim about a pre local ([`TvRequest::facts`]) it
/// is assumed where the local is live into a segment and checked where it is
/// live out of one (module docs).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LocalFacts {
    /// An unsigned upper bound of the value's bits.
    pub max: u64,
    /// The value is the sign extension of its low `sext` bits.
    pub sext: u8,
}

impl LocalFacts {
    /// No claim.
    pub const NONE: LocalFacts = LocalFacts {
        max: u64::MAX,
        sext: 64,
    };

    /// Whether every value satisfying `self` satisfies `other`.
    pub fn implies(self, other: LocalFacts) -> bool {
        self.max <= other.max && self.sext <= other.sext
    }

    /// Both facts at once.
    pub fn meet(self, other: LocalFacts) -> LocalFacts {
        LocalFacts {
            max: self.max.min(other.max),
            sext: self.sext.min(other.sext),
        }
    }

    /// Either fact (the weakest fact both imply).
    pub fn join(self, other: LocalFacts) -> LocalFacts {
        LocalFacts {
            max: self.max.max(other.max),
            sext: self.sext.max(other.sext),
        }
    }
}

/// The most bytes a `memory.copy` may move and still be validated against a
/// run of loads and stores (module docs).
pub const MAX_EXPANDED_COPY: u64 = 32;

/// Function, type and global signatures the body refers to.
pub trait TvTypes {
    /// The type of function `index` (imports and definitions).
    fn func(&self, index: u32) -> Option<FuncSig>;
    /// The type at type-section index `index` (`call_indirect`).
    fn type_at(&self, index: u32) -> Option<FuncSig>;
    /// The value type of global `index` (imports and definitions).
    fn global(&self, index: u32) -> Option<ValKind>;
}

/// What a residual (syntactically unequal) term equality does.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResidualPolicy {
    /// Reject the function on the first residual.
    Refuse,
    /// Ask `ay` for a certified proof of each integer residual, at most
    /// `max_queries` per function, each within `timeout_ms`.
    Solver {
        /// Per-query solver timeout.
        timeout_ms: u64,
        /// Queries allowed per function before it is rejected.
        max_queries: usize,
    },
}

/// One validation request.
pub struct TvRequest<'a> {
    /// The function's parameter types (never part of either body's locals).
    pub params: &'a [ValKind],
    /// The lane's own body.
    pub pre: TvBody<'a>,
    /// The rewritten body.
    pub post: TvBody<'a>,
    /// The image of every pre local, parameters first.
    pub image: &'a [LocalImage],
    /// The claimed fact of every pre local, parameters first; empty claims
    /// nothing. A float local's claim must be [`LocalFacts::NONE`].
    pub facts: &'a [LocalFacts],
    /// Signatures for `call` / `call_indirect`.
    pub types: &'a dyn TvTypes,
    /// What a residual equality does.
    pub residual: ResidualPolicy,
    /// Work budget (instructions stepped, liveness words, boundary checks).
    pub max_work: usize,
}

/// What an accepted validation checked.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct TvReport {
    /// Segments compared.
    pub segments: usize,
    /// Effects compared across all segments.
    pub effects: usize,
    /// Live-out locals compared at segment ends.
    pub live_out_checks: usize,
    /// Residual equalities the solver certified.
    pub residuals_proven: usize,
    /// Claimed local facts checked at segment ends.
    pub facts_checked: usize,
    /// Loads and stores whose post memarg offset differs from the pre one
    /// while the effective addresses are equal (a folded offset).
    pub offsets_folded: usize,
    /// Of those, the ones whose address comparison used a no-wrap premise
    /// ([`validate_with_premises`]).
    pub premised_folds: usize,
    /// `memory.copy`s matched by a run of loads and stores.
    pub copies_expanded: usize,
}

/// Why a function was not validated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TvFailureKind {
    /// A body the independent decoder cannot read.
    Undecodable,
    /// The image is malformed (length, index or type).
    ImageInvalid,
    /// The control skeletons differ.
    StructureMismatch,
    /// A relocation sits where the model cannot attach it.
    RelocUnsupported,
    /// An instruction the model has no rule for (or a call with no signature).
    Unsupported,
    /// The effect traces differ.
    EffectMismatch,
    /// The end operand stacks differ.
    StackMismatch,
    /// A live-out local differs from its image.
    LiveOutMismatch,
    /// A live-out local's claimed fact does not follow from its value.
    FactUnproven,
    /// A residual equality the solver did not certify (or policy refused).
    ResidualUnproven,
    /// The work budget ran out.
    Budget,
}

impl TvFailureKind {
    /// Stable short name, for evidence and fallback counts.
    pub fn as_str(self) -> &'static str {
        match self {
            TvFailureKind::Undecodable => "undecodable",
            TvFailureKind::ImageInvalid => "image_invalid",
            TvFailureKind::StructureMismatch => "structure_mismatch",
            TvFailureKind::RelocUnsupported => "reloc_unsupported",
            TvFailureKind::Unsupported => "unsupported",
            TvFailureKind::EffectMismatch => "effect_mismatch",
            TvFailureKind::StackMismatch => "stack_mismatch",
            TvFailureKind::LiveOutMismatch => "live_out_mismatch",
            TvFailureKind::FactUnproven => "fact_unproven",
            TvFailureKind::ResidualUnproven => "residual_unproven",
            TvFailureKind::Budget => "budget",
        }
    }
}

/// A rejected validation: the class and where.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TvFailure {
    /// The failure class.
    pub kind: TvFailureKind,
    /// The segment, when the failure belongs to one.
    pub segment: Option<usize>,
    /// What differed.
    pub detail: String,
}

impl fmt::Display for TvFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.segment {
            Some(s) => write!(f, "{} in segment {s}: {}", self.kind.as_str(), self.detail),
            None => write!(f, "{}: {}", self.kind.as_str(), self.detail),
        }
    }
}

fn fail(kind: TvFailureKind, segment: Option<usize>, detail: impl Into<String>) -> TvFailure {
    TvFailure {
        kind,
        segment,
        detail: detail.into(),
    }
}

// ---------------------------------------------------------------------------
// Instruction classes
// ---------------------------------------------------------------------------

fn is_control(op: u8) -> bool {
    matches!(
        op,
        0x00 | 0x02 | 0x03 | 0x04 | 0x05 | 0x0b | 0x0c | 0x0d | 0x0e | 0x0f
    )
}

/// The result type of a PURE numeric opcode (no trap, no state), with its
/// operand count. `None` for every other opcode.
fn pure_numeric(op: u8, sub: Option<u32>) -> Option<(usize, ValKind)> {
    use ValKind::*;
    if op == 0xfc {
        // Saturating truncation never traps.
        return match sub? {
            0..=3 => Some((1, I32)),
            4..=7 => Some((1, I64)),
            _ => None,
        };
    }
    Some(match op {
        0x45 => (1, I32),
        0x46..=0x4f => (2, I32),
        0x50 => (1, I32),
        0x51..=0x66 => (2, I32),
        0x67..=0x69 => (1, I32),
        0x6a..=0x6c | 0x71..=0x78 => (2, I32),
        0x79..=0x7b => (1, I64),
        0x7c..=0x7e | 0x83..=0x8a => (2, I64),
        0x8b..=0x91 => (1, F32),
        0x92..=0x98 => (2, F32),
        0x99..=0x9f => (1, F64),
        0xa0..=0xa6 => (2, F64),
        0xa7 => (1, I32),
        0xac | 0xad => (1, I64),
        0xb2..=0xb6 => (1, F32),
        0xb7..=0xbb => (1, F64),
        0xbc => (1, I32),
        0xbd => (1, I64),
        0xbe => (1, F32),
        0xbf => (1, F64),
        0xc0 | 0xc1 => (1, I32),
        0xc2..=0xc4 => (1, I64),
        _ => return None,
    })
}

/// A float operation whose NaN result has a nondeterministic sign and
/// payload: every float arithmetic, rounding, `min`/`max`, `sqrt`, `demote`
/// and `promote` opcode. `abs`, `neg`, `copysign`, the reinterpretations and
/// the conversions from integers are bitwise or never produce a NaN.
///
/// Two evaluations of such an operation on equal operands may return
/// different bits, so a rewrite that evaluates one of them where the pre
/// body evaluated it once is not a refinement. Each evaluation is therefore
/// a distinct term: the `k`-th evaluation of `(op, args)` on one side is
/// matched only with the `k`-th on the other (a bijection between the two
/// sides' choices), never with an earlier or later one.
fn nan_nondeterministic(op: u8) -> bool {
    matches!(op, 0x8d..=0x97 | 0x9b..=0xa5 | 0xb6 | 0xbb)
}

/// Arithmetic that can TRAP: an ordered effect, with its operand count and
/// result type.
fn trapping_numeric(op: u8) -> Option<(usize, ValKind)> {
    use ValKind::*;
    Some(match op {
        0x6d..=0x70 => (2, I32),
        0x7f..=0x82 => (2, I64),
        0xa8..=0xab => (1, I32),
        0xae..=0xb1 => (1, I64),
        _ => return None,
    })
}

/// The result type of a load opcode.
fn load_type(op: u8) -> Option<ValKind> {
    use ValKind::*;
    Some(match op {
        0x28 | 0x2c..=0x2f => I32,
        0x29 | 0x30..=0x35 => I64,
        0x2a => F32,
        0x2b => F64,
        _ => return None,
    })
}

/// Bytes moved by a load a small-copy run may use (zero-extending forms).
fn copy_load_width(op: u8) -> Option<u64> {
    match op {
        0x29 => Some(8),
        0x28 => Some(4),
        0x2f => Some(2),
        0x2d => Some(1),
        _ => None,
    }
}

/// Bytes moved by a store a small-copy run may use.
fn copy_store_width(op: u8) -> Option<u64> {
    match op {
        0x37 => Some(8),
        0x36 => Some(4),
        0x3b => Some(2),
        0x3a => Some(1),
        _ => None,
    }
}

/// Whether [`Validator::step`] records `x` as an ordered effect.
fn is_effect(x: &DecodedInst) -> bool {
    matches!(x.opcode, 0x10 | 0x11 | 0x23 | 0x24 | 0x28..=0x40)
        || (x.opcode == 0xfc && matches!(x.sub, Some(10) | Some(11)))
        || trapping_numeric(x.opcode).is_some()
}

// ---------------------------------------------------------------------------
// Known bits
// ---------------------------------------------------------------------------

/// All ones at `w` bits.
pub fn ones(w: u32) -> u64 {
    if w >= 64 { u64::MAX } else { (1u64 << w) - 1 }
}

fn bit_len(v: u64) -> u32 {
    64 - v.leading_zeros()
}

/// The `w`-bit value whose low `s` bits are those of `v`, sign-extended.
fn sign_extend(v: u64, s: u32, w: u32) -> u64 {
    let shift = 64 - s;
    ((((v << shift) as i64) >> shift) as u64) & ones(w)
}

/// No fact at width `w`.
pub fn top(w: u32) -> LocalFacts {
    LocalFacts {
        max: ones(w),
        sext: w as u8,
    }
}

/// `f` at width `w`, with the sign-extension width a small bound implies.
pub fn tighten(f: LocalFacts, w: u32) -> LocalFacts {
    let max = f.max.min(ones(w));
    let mut sext = u32::from(f.sext).min(w);
    if w > 0 && max < (1u64 << (w - 1)) {
        sext = sext.min(bit_len(max) + 1);
    }
    LocalFacts {
        max,
        sext: sext.max(1) as u8,
    }
}

/// The fact of the `w`-bit constant `v`.
pub fn const_facts(v: u64, w: u32) -> LocalFacts {
    let v = v & ones(w);
    let sext = (1..=w).find(|&s| sign_extend(v, s, w) == v).unwrap_or(w);
    LocalFacts {
        max: v,
        sext: sext as u8,
    }
}

/// The fact of a load's result, by its opcode.
pub fn load_facts(op: u8) -> Option<LocalFacts> {
    let zext = |bits: u32| LocalFacts {
        max: ones(bits),
        sext: (bits + 1) as u8,
    };
    let sext = |bits: u32| LocalFacts {
        max: u64::MAX,
        sext: bits as u8,
    };
    Some(match op {
        0x2d | 0x31 => zext(8),
        0x2f | 0x33 => zext(16),
        0x35 => zext(32),
        0x2c | 0x30 => sext(8),
        0x2e | 0x32 => sext(16),
        0x34 => sext(32),
        _ => return None,
    })
}

/// The fact of the width-`w` result of the pure operation `op` from its
/// operands' facts and, where an operand is a constant, its value (module
/// docs). The rules hold for every operand value the facts admit.
pub fn pure_op_facts(op: u8, facts: &[LocalFacts], consts: &[Option<u64>], w: u32) -> LocalFacts {
    tighten(op_rule(op, facts, consts, w), w)
}

fn op_rule(op: u8, facts: &[LocalFacts], consts: &[Option<u64>], w: u32) -> LocalFacts {
    let fa = |i: usize| facts.get(i).copied().unwrap_or(LocalFacts::NONE);
    let shift = |i: usize| -> Option<u32> {
        consts
            .get(i)
            .copied()
            .flatten()
            .map(|v| (v % u64::from(w)) as u32)
    };
    let max_sext = |a: LocalFacts, b: LocalFacts| a.sext.max(b.sext);
    match op {
        // Comparisons and `eqz`: 0 or 1.
        0x45..=0x66 => LocalFacts { max: 1, sext: 2 },
        // clz / ctz / popcnt: at most the width.
        0x67..=0x69 | 0x79..=0x7b => LocalFacts {
            max: u64::from(w),
            sext: w as u8,
        },
        // and
        0x71 | 0x83 => {
            let (a, b) = (fa(0), fa(1));
            LocalFacts {
                max: a.max.min(b.max),
                sext: max_sext(a, b),
            }
        }
        // or, xor
        0x72 | 0x84 | 0x73 | 0x85 => {
            let (a, b) = (fa(0), fa(1));
            LocalFacts {
                max: ones(bit_len(a.max.max(b.max))),
                sext: max_sext(a, b),
            }
        }
        // shr_u
        0x76 | 0x88 => match shift(1) {
            Some(0) => fa(0),
            Some(k) => LocalFacts {
                max: fa(0).max >> k,
                sext: w as u8,
            },
            None => LocalFacts {
                max: fa(0).max,
                sext: w as u8,
            },
        },
        // shr_s
        0x75 | 0x87 => match shift(1) {
            Some(k) => {
                let a = fa(0);
                let nonneg = a.max < (1u64 << (w - 1));
                LocalFacts {
                    max: if nonneg { a.max >> k } else { ones(w) },
                    sext: u32::from(a.sext).saturating_sub(k).max(1) as u8,
                }
            }
            None => top(w),
        },
        // add, sub: one more sign bit; add's bound when it cannot wrap.
        0x6a | 0x7c | 0x6b | 0x7d => {
            let (a, b) = (fa(0), fa(1));
            let max = if matches!(op, 0x6a | 0x7c) {
                a.max.checked_add(b.max).filter(|m| *m <= ones(w))
            } else {
                None
            };
            LocalFacts {
                max: max.unwrap_or(ones(w)),
                sext: (u32::from(max_sext(a, b)) + 1).min(w) as u8,
            }
        }
        0xc0 | 0xc2 => LocalFacts {
            max: ones(w),
            sext: 8,
        },
        0xc1 | 0xc3 => LocalFacts {
            max: ones(w),
            sext: 16,
        },
        0xc4 => LocalFacts {
            max: ones(w),
            sext: 32,
        },
        // i64.extend_i32_s: the sign bits extend; a non-negative bound stays.
        0xac => {
            let a = fa(0);
            LocalFacts {
                max: if a.max < (1u64 << 31) { a.max } else { ones(w) },
                sext: a.sext,
            }
        }
        // i64.extend_i32_u
        0xad => LocalFacts {
            max: fa(0).max,
            sext: w as u8,
        },
        // i32.wrap_i64
        0xa7 => {
            let a = fa(0);
            LocalFacts {
                max: a.max.min(ones(32)),
                sext: a.sext.min(32),
            }
        }
        // select: either value.
        0x1b => fa(0).join(fa(1)),
        _ => top(w),
    }
}

fn const_term(inst: &DecodedInst) -> Option<(ValKind, u64)> {
    match (inst.opcode, &inst.imm) {
        (0x41, Imm::Int(v)) => Some((ValKind::I32, u64::from(*v as i32 as u32))),
        (0x42, Imm::Int(v)) => Some((ValKind::I64, *v as u64)),
        (0x43, Imm::Float(b)) if b.len() == 4 => Some((
            ValKind::F32,
            u64::from(u32::from_le_bytes([b[0], b[1], b[2], b[3]])),
        )),
        (0x44, Imm::Float(b)) if b.len() == 8 => {
            let mut a = [0u8; 8];
            a.copy_from_slice(b);
            Some((ValKind::F64, u64::from_le_bytes(a)))
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Terms
// ---------------------------------------------------------------------------

/// A relocation attached to an instruction, relative to its first byte.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct RelocTag {
    rel: u32,
    kind: u8,
    target: u64,
    addend: i32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Term {
    /// Parameter `p` at function entry (the first segment only).
    Param(u32),
    /// A constant of a type, by its bits.
    Const(ValKind, u64),
    /// A relocated constant: its identity is its bytes and relocations.
    RelocConst(Vec<u8>, Vec<RelocTag>),
    /// The shared value of post local `c` at segment start, which every live
    /// pre local imaged to `c` also holds.
    LiveIn(u32),
    /// A pre local the liveness does not track at segment start.
    PreUnk(u32),
    /// A post local no live pre local is imaged to at segment start.
    PostUnk(u32),
    /// The `k`-th value below the segment's starting stack top.
    StackIn(u32),
    /// Result `index` of the `effect`-th effect of the segment, whose opcode
    /// is `op` (`sub`).
    Result {
        effect: u32,
        index: u32,
        op: u8,
        sub: Option<u32>,
    },
    /// The value the `index`-th load of a small-copy run read (post side
    /// only; the run is compared as the segment's `effect`-th effect).
    CopyTmp { effect: u32, index: u32 },
    /// A pure operation. `occ` is 0 for a deterministic operation; for one
    /// whose NaN result is nondeterministic ([`nan_nondeterministic`]) it
    /// counts this side's earlier evaluations of the same operation on the
    /// same arguments in the segment, so each evaluation is its own value.
    Op {
        op: u8,
        sub: Option<u32>,
        args: Vec<u32>,
        occ: u32,
    },
}

#[derive(Default)]
struct Arena {
    terms: Vec<Term>,
    ty: Vec<Option<ValKind>>,
    /// The structural fact of every integer term ([`LocalFacts::NONE`] for
    /// floats and untyped stack inputs).
    facts: Vec<LocalFacts>,
    index: HashMap<Term, u32>,
}

impl Arena {
    fn clear(&mut self) {
        self.terms.clear();
        self.ty.clear();
        self.facts.clear();
        self.index.clear();
    }

    fn lookup(&self, t: &Term) -> Option<u32> {
        self.index.get(t).copied()
    }

    fn insert(&mut self, t: Term, ty: Option<ValKind>, facts: LocalFacts) -> u32 {
        let id = self.terms.len() as u32;
        self.terms.push(t.clone());
        self.ty.push(ty);
        self.facts.push(facts);
        self.index.insert(t, id);
        id
    }

    fn constant(&self, t: u32) -> Option<(ValKind, u64)> {
        match self.terms[t as usize] {
            Term::Const(k, v) => Some((k, v)),
            _ => None,
        }
    }
}

/// The width of an integer type.
fn int_width(ty: Option<ValKind>) -> Option<u32> {
    match ty? {
        ValKind::I32 => Some(32),
        ValKind::I64 => Some(64),
        _ => None,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Effect {
    op: u8,
    sub: Option<u32>,
    /// The immediate; a memarg's offset is moved into `addrs`.
    imm: Imm,
    /// Bytes and relocations of a relocated instruction.
    raw: Option<(Vec<u8>, Vec<RelocTag>)>,
    /// Operands other than addresses.
    args: Vec<u32>,
    /// Each address operand as a base term plus a static offset.
    addrs: Vec<(u32, u64)>,
    /// The memarg offset as written (0 without a memarg).
    memarg_offset: u64,
    /// Whether normalizing an address absorbed a premised addition.
    premised: bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Side {
    Pre,
    Post,
}

#[derive(Default, Clone)]
struct SideState {
    stack: Vec<u32>,
    base_pops: u32,
    effects: Vec<Effect>,
    locals: HashMap<u32, u32>,
    written: Vec<u32>,
    /// Evaluations so far of each NaN-nondeterministic `(op, args)`.
    nan_evals: HashMap<(u8, Vec<u32>), u32>,
}

/// A decoded body with its relocations attached to instructions.
struct Decoded {
    insts: Vec<DecodedInst>,
    tags: HashMap<usize, Vec<RelocTag>>,
    /// Index of every control instruction, in order.
    controls: Vec<usize>,
}

fn decode(body: &TvBody<'_>, which: &str) -> Result<Decoded, TvFailure> {
    let insts = decode_body(body.code, 0).map_err(|e| {
        fail(
            TvFailureKind::Undecodable,
            None,
            format!("{which} body: {e}"),
        )
    })?;
    let mut tags: HashMap<usize, Vec<RelocTag>> = HashMap::new();
    for r in body.relocs {
        let at = r.offset as usize;
        let k = insts
            .partition_point(|x| x.offset <= at)
            .checked_sub(1)
            .ok_or_else(|| {
                fail(
                    TvFailureKind::RelocUnsupported,
                    None,
                    format!("{which} relocation at {at} precedes the code"),
                )
            })?;
        let x = &insts[k];
        if at == x.offset || at >= x.offset + x.size {
            return Err(fail(
                TvFailureKind::RelocUnsupported,
                None,
                format!("{which} relocation at {at} is not inside an immediate"),
            ));
        }
        if is_control(x.opcode) || matches!(x.opcode, 0x20..=0x22) {
            return Err(fail(
                TvFailureKind::RelocUnsupported,
                None,
                format!(
                    "{which} relocation at {at} patches opcode 0x{:02x}, which this model \
                     does not relocate",
                    x.opcode
                ),
            ));
        }
        tags.entry(k).or_default().push(RelocTag {
            rel: (at - x.offset) as u32,
            kind: r.kind,
            target: r.target,
            addend: r.addend,
        });
    }
    for v in tags.values_mut() {
        v.sort_by_key(|t| (t.rel, t.kind, t.target, t.addend));
    }
    let controls = insts
        .iter()
        .enumerate()
        .filter(|(_, x)| is_control(x.opcode))
        .map(|(i, _)| i)
        .collect();
    Ok(Decoded {
        insts,
        tags,
        controls,
    })
}

/// The successor segments of every segment, from the control skeleton.
fn successors(insts: &[DecodedInst], controls: &[usize]) -> Result<Vec<Vec<usize>>, TvFailure> {
    let k = controls.len();
    let bad = |d: &str| fail(TvFailureKind::Unsupported, None, d.to_string());
    let mut end_of = vec![usize::MAX; k];
    let mut else_of = vec![usize::MAX; k];
    let mut if_of_else = vec![usize::MAX; k];
    let mut stack: Vec<usize> = Vec::new();
    // (control, label openers) resolved once every `end` is known.
    let mut pending: Vec<(usize, Vec<Option<usize>>)> = Vec::new();
    let label = |stack: &[usize], d: u32| -> Result<Option<usize>, TvFailure> {
        let d = d as usize;
        match d.cmp(&stack.len()) {
            std::cmp::Ordering::Less => Ok(Some(stack[stack.len() - 1 - d])),
            std::cmp::Ordering::Equal => Ok(None),
            std::cmp::Ordering::Greater => Err(bad("branch depth beyond the function label")),
        }
    };
    for (c, &i) in controls.iter().enumerate() {
        let x = &insts[i];
        match x.opcode {
            0x02..=0x04 => stack.push(c),
            0x05 => {
                let o = *stack.last().ok_or_else(|| bad("`else` outside a scope"))?;
                if insts[controls[o]].opcode != 0x04 || else_of[o] != usize::MAX {
                    return Err(bad("`else` without its `if`"));
                }
                else_of[o] = c;
                if_of_else[c] = o;
            }
            0x0b => {
                let o = stack.pop().ok_or_else(|| bad("unbalanced `end`"))?;
                end_of[o] = c;
            }
            0x0c | 0x0d => {
                let Imm::Depth(d) = x.imm else {
                    return Err(bad("branch without a depth"));
                };
                pending.push((c, vec![label(&stack, d)?]));
            }
            0x0e => {
                let Imm::Table { targets, default } = &x.imm else {
                    return Err(bad("br_table without a table"));
                };
                let mut ls = Vec::with_capacity(targets.len() + 1);
                for &d in targets.iter().chain(std::iter::once(default)) {
                    ls.push(label(&stack, d)?);
                }
                pending.push((c, ls));
            }
            _ => {}
        }
    }
    if !stack.is_empty() {
        return Err(bad("unclosed scope"));
    }
    let target_seg = |o: usize| -> usize {
        if insts[controls[o]].opcode == 0x03 {
            o + 1
        } else {
            end_of[o] + 1
        }
    };
    let mut succ: Vec<Vec<usize>> = vec![Vec::new(); k + 1];
    for (c, &i) in controls.iter().enumerate() {
        let s = &mut succ[c];
        match insts[i].opcode {
            0x02 | 0x03 | 0x0b => s.push(c + 1),
            0x04 => {
                s.push(c + 1);
                s.push(if else_of[c] != usize::MAX {
                    else_of[c] + 1
                } else {
                    end_of[c] + 1
                });
            }
            0x05 => s.push(end_of[if_of_else[c]] + 1),
            0x0d => s.push(c + 1),
            _ => {}
        }
    }
    for (c, labels) in pending {
        for o in labels.into_iter().flatten() {
            let t = target_seg(o);
            succ[c].push(t);
        }
    }
    for s in &mut succ {
        s.sort_unstable();
        s.dedup();
    }
    Ok(succ)
}

/// Segment `s` covers the instructions strictly between control `s - 1` (or
/// the start) and control `s` (or the end).
fn segment_range(controls: &[usize], n: usize, s: usize) -> std::ops::Range<usize> {
    let lo = if s == 0 { 0 } else { controls[s - 1] + 1 };
    let hi = if s < controls.len() { controls[s] } else { n };
    lo..hi
}

struct Validator<'a> {
    req: &'a TvRequest<'a>,
    pre: Decoded,
    post: Decoded,
    n_params: u32,
    /// Pre local -> its liveness bit, for locals with an upward-exposed read.
    gbit: Vec<u32>,
    /// Liveness bit -> pre local.
    glocal: Vec<u32>,
    words: usize,
    live_in: Vec<u64>,
    succ: Vec<Vec<usize>>,
    /// Post local -> pre locals imaged to it.
    inverse: Vec<Vec<u32>>,
    /// The claimed fact of every pre local ([`LocalFacts::NONE`] unclaimed).
    claims: Vec<LocalFacts>,
    work: usize,
    queries: usize,
    report: TvReport,
    arena: Arena,
    seg: usize,
    /// The active no-wrap premises, by the pre local they write.
    premises: HashMap<u32, NoWrapPremise>,
    /// Sums marked as not wrapping in the current segment, with the pre
    /// effect count at the mark.
    nowrap: HashMap<u32, usize>,
}

impl<'a> Validator<'a> {
    /// The hash-consed node of `t`, with its structural fact.
    fn intern(&mut self, t: Term, ty: Option<ValKind>) -> u32 {
        if let Some(id) = self.arena.lookup(&t) {
            return id;
        }
        let facts = self.facts_of(&t, ty);
        self.arena.insert(t, ty, facts)
    }

    /// The fact of a term, from its own structure (module docs). A live-in
    /// symbol has the claims of the live pre locals it stands for.
    fn facts_of(&self, t: &Term, ty: Option<ValKind>) -> LocalFacts {
        let Some(w) = int_width(ty) else {
            return LocalFacts::NONE;
        };
        match t {
            Term::Const(_, v) => const_facts(*v, w),
            Term::LiveIn(c) => {
                let mut f = top(w);
                if let Some(ls) = self.inverse.get(*c as usize) {
                    for &l in ls {
                        if self.live_in_bit(self.seg, l) {
                            f = f.meet(self.claims[l as usize]);
                        }
                    }
                }
                tighten(f, w)
            }
            Term::Result { op, .. } => load_facts(*op).map_or(top(w), |f| tighten(f, w)),
            Term::Op { op, args, .. } => self.op_facts(*op, args, w),
            _ => top(w),
        }
    }

    /// The fact of a pure operation's result of width `w` from its operands'.
    fn op_facts(&self, op: u8, args: &[u32], w: u32) -> LocalFacts {
        let facts: Vec<LocalFacts> = args.iter().map(|&a| self.arena.facts[a as usize]).collect();
        let consts: Vec<Option<u64>> = args
            .iter()
            .map(|&a| self.arena.constant(a).map(|(_, v)| v))
            .collect();
        pure_op_facts(op, &facts, &consts, w)
    }

    /// The node of a pure operation, after the identities of the module docs
    /// (`x & (2^k - 1)`, `extendN_s(x)` and `x + 0` are `x` when the operand's
    /// fact makes them so).
    fn op_term(
        &mut self,
        op: u8,
        sub: Option<u32>,
        args: Vec<u32>,
        ty: Option<ValKind>,
        occ: u32,
    ) -> u32 {
        if sub.is_none() && occ == 0 {
            let facts = |t: u32| self.arena.facts[t as usize];
            match (op, args.as_slice()) {
                (0x71 | 0x83, &[a, b]) => {
                    for (x, m) in [(a, b), (b, a)] {
                        if let Some((_, mv)) = self.arena.constant(m)
                            && mv & mv.wrapping_add(1) == 0
                            && facts(x).max <= mv
                        {
                            return x;
                        }
                    }
                }
                (0xc0 | 0xc2, &[x]) if facts(x).sext <= 8 => return x,
                (0xc1 | 0xc3, &[x]) if facts(x).sext <= 16 => return x,
                (0xc4, &[x]) if facts(x).sext <= 32 => return x,
                (0x6a | 0x7c, &[a, b]) => {
                    if matches!(self.arena.constant(b), Some((_, 0))) {
                        return a;
                    }
                    if matches!(self.arena.constant(a), Some((_, 0))) {
                        return b;
                    }
                }
                _ => {}
            }
        }
        self.intern(Term::Op { op, sub, args, occ }, ty)
    }

    /// An address as a base term plus a static offset: `b + c` (an `i32.add`
    /// of a constant) moves `c` into the offset when `b`'s fact bounds the sum
    /// below `2^32`, or when the sum was marked as not wrapping before the
    /// pre body's `at`-th effect (module docs). Returns how many additions
    /// were absorbed, and whether one of them needed a mark.
    fn norm_addr(&self, t: u32, offset: u64, at: usize) -> (u32, u64, usize, bool) {
        let (mut t, mut offset, mut absorbed, mut premised) = (t, offset, 0usize, false);
        while let Term::Op {
            op: 0x6a,
            args,
            occ: 0,
            sub: None,
        } = &self.arena.terms[t as usize]
        {
            let (x, c) = match (self.arena.constant(args[0]), self.arena.constant(args[1])) {
                (_, Some((ValKind::I32, c))) => (args[0], c),
                (Some((ValKind::I32, c)), _) => (args[1], c),
                _ => break,
            };
            if self.arena.ty[x as usize] != Some(ValKind::I32) {
                break;
            }
            let bounded = self.arena.facts[x as usize].max.saturating_add(c) <= u64::from(u32::MAX);
            if !bounded {
                if !self.nowrap.get(&t).is_some_and(|&e| e <= at) {
                    break;
                }
                premised = true;
            }
            t = x;
            offset += c;
            absorbed += 1;
        }
        (t, offset, absorbed, premised)
    }

    /// The value pre local `l` holds now, without recording a read.
    fn peek_local(&mut self, st: &SideState, l: u32) -> Option<u32> {
        match st.locals.get(&l) {
            Some(&t) => Some(t),
            None => self.initial(Side::Pre, l).ok(),
        }
    }

    /// The pre body writes `t` to local `l`: when `l` carries an active
    /// premise and `t` is the premised sum of the values its base and index
    /// locals hold now, mark `t` as not wrapping from the current effect on.
    fn mark_nowrap(&mut self, st: &SideState, l: u32, t: u32) {
        let Some(p) = self.premises.get(&l).copied() else {
            return;
        };
        let (Some(b), Some(i)) = (
            self.peek_local(st, p.base()),
            self.peek_local(st, p.index()),
        ) else {
            return;
        };
        let addend = if p.multiplied() {
            let Some(s) = self
                .arena
                .lookup(&Term::Const(ValKind::I32, u64::from(p.scale())))
            else {
                return;
            };
            match self.arena.lookup(&Term::Op {
                op: 0x6c,
                sub: None,
                args: vec![i, s],
                occ: 0,
            }) {
                Some(m) => m,
                None => return,
            }
        } else {
            i
        };
        let sum = Term::Op {
            op: 0x6a,
            sub: None,
            args: vec![b, addend],
            occ: 0,
        };
        if self.arena.lookup(&sum) == Some(t) {
            self.nowrap.entry(t).or_insert(st.effects.len());
        }
    }

    fn spend(&mut self, n: usize) -> Result<(), TvFailure> {
        self.work = self.work.saturating_add(n);
        if self.work > self.req.max_work {
            return Err(fail(
                TvFailureKind::Budget,
                Some(self.seg),
                format!("work budget of {} exhausted", self.req.max_work),
            ));
        }
        Ok(())
    }

    fn pre_type(&self, l: u32) -> Option<ValKind> {
        let l = l as usize;
        let p = self.req.params.len();
        if l < p {
            Some(self.req.params[l])
        } else {
            self.req.pre.locals.get(l - p).copied()
        }
    }

    fn post_type(&self, c: u32) -> Option<ValKind> {
        let c = c as usize;
        let p = self.req.params.len();
        if c < p {
            Some(self.req.params[c])
        } else {
            self.req.post.locals.get(c - p).copied()
        }
    }

    fn live_in_bit(&self, seg: usize, l: u32) -> bool {
        match self.gbit.get(l as usize) {
            Some(&g) if g != u32::MAX => {
                let g = g as usize;
                self.live_in[seg * self.words + g / 64] >> (g % 64) & 1 == 1
            }
            _ => false,
        }
    }

    fn image_const(&mut self, bytes: &[u8]) -> Result<u32, TvFailure> {
        let insts = decode_body(bytes, 0).map_err(|e| {
            fail(
                TvFailureKind::ImageInvalid,
                None,
                format!("constant image: {e}"),
            )
        })?;
        match insts.as_slice() {
            [x] => {
                let (ty, bits) = const_term(x).ok_or_else(|| {
                    fail(
                        TvFailureKind::ImageInvalid,
                        None,
                        "constant image is not a constant",
                    )
                })?;
                Ok(self.intern(Term::Const(ty, bits), Some(ty)))
            }
            _ => Err(fail(
                TvFailureKind::ImageInvalid,
                None,
                "constant image is not one instruction",
            )),
        }
    }

    /// The value local `l` holds at the start of the current segment.
    fn initial(&mut self, side: Side, l: u32) -> Result<u32, TvFailure> {
        let seg = self.seg;
        let ty = match side {
            Side::Pre => self.pre_type(l),
            Side::Post => self.post_type(l),
        }
        .ok_or_else(|| {
            fail(
                TvFailureKind::Unsupported,
                Some(seg),
                format!("local {l} is outside the function's locals"),
            )
        })?;
        if seg == 0 {
            return Ok(if l < self.n_params {
                self.intern(Term::Param(l), Some(ty))
            } else {
                self.intern(Term::Const(ty, 0), Some(ty))
            });
        }
        match side {
            Side::Pre => {
                if !self.live_in_bit(seg, l) {
                    return Ok(self.intern(Term::PreUnk(l), Some(ty)));
                }
                match &self.req.image[l as usize] {
                    LocalImage::Local(c) => {
                        let c = *c;
                        Ok(self.intern(Term::LiveIn(c), self.post_type(c)))
                    }
                    LocalImage::Const(bytes) => {
                        let bytes = bytes.clone();
                        self.image_const(&bytes)
                    }
                    LocalImage::Unused => Err(fail(
                        TvFailureKind::LiveOutMismatch,
                        Some(seg),
                        format!("pre local {l} is live in but has no image"),
                    )),
                }
            }
            Side::Post => {
                let tracked = self
                    .inverse
                    .get(l as usize)
                    .is_some_and(|ls| ls.iter().any(|&p| self.live_in_bit(seg, p)));
                Ok(if tracked {
                    self.intern(Term::LiveIn(l), Some(ty))
                } else {
                    self.intern(Term::PostUnk(l), Some(ty))
                })
            }
        }
    }

    fn read_local(&mut self, side: Side, st: &mut SideState, l: u32) -> Result<u32, TvFailure> {
        if let Some(&t) = st.locals.get(&l) {
            return Ok(t);
        }
        let t = self.initial(side, l)?;
        st.locals.insert(l, t);
        Ok(t)
    }

    fn pop(&mut self, st: &mut SideState) -> u32 {
        match st.stack.pop() {
            Some(t) => t,
            None => {
                let k = st.base_pops;
                st.base_pops += 1;
                self.intern(Term::StackIn(k), None)
            }
        }
    }

    fn pop_n(&mut self, st: &mut SideState, n: usize) -> Vec<u32> {
        let mut v: Vec<u32> = (0..n).map(|_| self.pop(st)).collect();
        v.reverse();
        v
    }

    fn effect(
        &mut self,
        st: &mut SideState,
        x: &DecodedInst,
        raw: Option<(Vec<u8>, Vec<RelocTag>)>,
        pops: usize,
        results: &[ValKind],
    ) {
        let mut args = self.pop_n(st, pops);
        let k = st.effects.len() as u32;
        let mut imm = x.imm.clone();
        let mut addrs = Vec::new();
        let mut memarg_offset = 0u64;
        let mut premised = false;
        // A relocated instruction is compared as written (its bytes and
        // relocations), so its address is not normalized.
        let normalize = raw.is_none();
        let at = k as usize;
        let mut addr = |v: &Self, t: u32, offset: u64| -> (u32, u64) {
            if normalize {
                let (b, o, _, p) = v.norm_addr(t, offset, at);
                premised |= p;
                (b, o)
            } else {
                (t, offset)
            }
        };
        match (x.opcode, x.sub, &x.imm) {
            (0x28..=0x3e, _, &Imm::MemArg { align, offset }) if !args.is_empty() => {
                let a = args.remove(0);
                memarg_offset = u64::from(offset);
                addrs.push(addr(self, a, memarg_offset));
                imm = Imm::MemArg { align, offset: 0 };
            }
            (0xfc, Some(10), _) if args.len() == 3 => {
                let d = args.remove(0);
                let s = args.remove(0);
                addrs.push(addr(self, d, 0));
                addrs.push(addr(self, s, 0));
            }
            (0xfc, Some(11), _) if args.len() == 3 => {
                let d = args.remove(0);
                addrs.push(addr(self, d, 0));
            }
            _ => {}
        }
        st.effects.push(Effect {
            op: x.opcode,
            sub: x.sub,
            imm,
            raw,
            args,
            addrs,
            memarg_offset,
            premised,
        });
        for (i, ty) in results.iter().enumerate() {
            let t = self.intern(
                Term::Result {
                    effect: k,
                    index: i as u32,
                    op: x.opcode,
                    sub: x.sub,
                },
                Some(*ty),
            );
            st.stack.push(t);
        }
    }

    fn sig(&self, x: &DecodedInst) -> Result<FuncSig, TvFailure> {
        let found = match x.imm {
            Imm::Index(f) if x.opcode == 0x10 => self.req.types.func(f),
            Imm::CallIndirect { type_idx, .. } if x.opcode == 0x11 => {
                self.req.types.type_at(type_idx)
            }
            _ => None,
        };
        found.ok_or_else(|| {
            fail(
                TvFailureKind::Unsupported,
                Some(self.seg),
                format!("call at {} has no known signature", x.offset),
            )
        })
    }

    fn step(&mut self, side: Side, st: &mut SideState, idx: usize) -> Result<(), TvFailure> {
        let body = match side {
            Side::Pre => &self.pre,
            Side::Post => &self.post,
        };
        let x = body.insts[idx].clone();
        let tags = body.tags.get(&idx).cloned();
        let code = match side {
            Side::Pre => self.req.pre.code,
            Side::Post => self.req.post.code,
        };
        let raw = tags.map(|t| (code[x.offset..x.offset + x.size].to_vec(), t));
        let seg = self.seg;
        let unsupported = |what: &str| {
            fail(
                TvFailureKind::Unsupported,
                Some(seg),
                format!("opcode 0x{:02x} at {}: {what}", x.opcode, x.offset),
            )
        };
        match x.opcode {
            0x01 => {}
            0x1a => {
                self.pop(st);
            }
            0x1b => {
                let args = self.pop_n(st, 3);
                let ty = self.arena.ty[args[0] as usize];
                let t = self.intern(
                    Term::Op {
                        op: 0x1b,
                        sub: None,
                        args,
                        occ: 0,
                    },
                    ty,
                );
                st.stack.push(t);
            }
            0x20..=0x22 => {
                let Imm::Index(l) = x.imm else {
                    return Err(unsupported("local access without an index"));
                };
                if x.opcode == 0x20 {
                    let t = self.read_local(side, st, l)?;
                    st.stack.push(t);
                } else {
                    // Check the index exists on this side.
                    let exists = match side {
                        Side::Pre => self.pre_type(l).is_some(),
                        Side::Post => self.post_type(l).is_some(),
                    };
                    if !exists {
                        return Err(unsupported("local index outside the function's locals"));
                    }
                    let t = self.pop(st);
                    if side == Side::Pre {
                        self.mark_nowrap(st, l, t);
                    }
                    st.locals.insert(l, t);
                    st.written.push(l);
                    if x.opcode == 0x22 {
                        st.stack.push(t);
                    }
                }
            }
            0x23 => {
                // `global.get` pushes the global's value: the effect's result,
                // so where it flows is compared like any other term.
                let Imm::Index(g) = x.imm else {
                    return Err(unsupported("global access without an index"));
                };
                let ty = self
                    .req
                    .types
                    .global(g)
                    .ok_or_else(|| unsupported("global with no known type"))?;
                self.effect(st, &x, raw, 0, &[ty]);
            }
            0x24 => self.effect(st, &x, raw, 1, &[]),
            0x3f | 0x40 if x.imm != Imm::MemIdx(0) => {
                return Err(unsupported("memory.size/grow on a memory other than 0"));
            }
            0x28..=0x3e if !matches!(x.imm, Imm::MemArg { align, .. } if align < 0x40) => {
                // Bit 6 of the alignment field selects a memory index
                // (multi-memory), which the decoder does not read.
                return Err(unsupported("memarg naming a memory index"));
            }
            0x28..=0x35 => {
                let ty = load_type(x.opcode).ok_or_else(|| unsupported("load type"))?;
                self.effect(st, &x, raw, 1, &[ty]);
            }
            0x36..=0x3e => self.effect(st, &x, raw, 2, &[]),
            0x3f => self.effect(st, &x, raw, 0, &[ValKind::I32]),
            0x40 => self.effect(st, &x, raw, 1, &[ValKind::I32]),
            0x41..=0x44 => {
                let t = match raw {
                    Some((bytes, tags)) => {
                        self.intern(Term::RelocConst(bytes, tags), Some(ValKind::I32))
                    }
                    None => {
                        let (ty, bits) = const_term(&x).ok_or_else(|| unsupported("constant"))?;
                        self.intern(Term::Const(ty, bits), Some(ty))
                    }
                };
                st.stack.push(t);
            }
            0x10 | 0x11 => {
                let sig = self.sig(&x)?;
                let pops = sig.params.len() + usize::from(x.opcode == 0x11);
                self.effect(st, &x, raw, pops, &sig.results);
            }
            0xfc if matches!(x.sub, Some(10) | Some(11)) => {
                // The decoder skips the memory-index bytes (two for `copy`,
                // one for `fill`) and records no immediate, so only memory 0
                // is admitted: every compared bulk operation names it.
                let n = if x.sub == Some(10) { 2 } else { 1 };
                let ix = x.offset + x.size;
                if x.size < 2 + n || code[ix - n..ix].iter().any(|&b| b != 0) {
                    return Err(unsupported(
                        "bulk-memory operation on a memory other than 0",
                    ));
                }
                self.effect(st, &x, raw, 3, &[]);
            }
            op => {
                if let Some((n, ty)) = trapping_numeric(op) {
                    self.effect(st, &x, raw, n, &[ty]);
                } else if let Some((n, ty)) = pure_numeric(op, x.sub) {
                    if raw.is_some() {
                        return Err(unsupported("relocated numeric instruction"));
                    }
                    let args = self.pop_n(st, n);
                    let occ = if nan_nondeterministic(op) {
                        let k = st.nan_evals.entry((op, args.clone())).or_default();
                        *k += 1;
                        *k - 1
                    } else {
                        0
                    };
                    let t = self.op_term(op, x.sub, args, Some(ty), occ);
                    st.stack.push(t);
                } else {
                    return Err(unsupported("no symbolic rule"));
                }
            }
        }
        Ok(())
    }

    /// The byte count `n` when post instruction `i` may start a small-copy
    /// run: it is a load a run may use, and the pre effect it would be
    /// compared with is `memory.copy` of a constant `1 <= n <= 32`.
    fn small_copy_at(&self, pre: &SideState, post: &SideState, i: usize) -> Option<u64> {
        copy_load_width(self.post.insts[i].opcode)?;
        if self.post.tags.contains_key(&i) {
            return None;
        }
        let e = pre.effects.get(post.effects.len())?;
        if e.op != 0xfc || e.sub != Some(10) || e.args.len() != 1 {
            return None;
        }
        match self.arena.constant(e.args[0]) {
            Some((ValKind::I32, n)) if (1..=MAX_EXPANDED_COPY).contains(&n) => Some(n),
            _ => None,
        }
    }

    /// Execute the post instructions from `from` as a small-copy run of `n`
    /// bytes (module docs). On success the state after the run, in which the
    /// run is ONE `memory.copy` effect and each loaded value is a private
    /// symbol, and the index after its last store; `None` when the
    /// instructions are not such a run (the caller then executes them as
    /// written, and the effect comparison reports the difference).
    fn copy_expansion(
        &mut self,
        st: &SideState,
        from: usize,
        end: usize,
        n: u64,
    ) -> Option<(SideState, usize)> {
        let mut t = st.clone();
        let k = t.effects.len() as u32;
        // (base, offset, width, value) of each load and store, in order.
        let mut loads: Vec<(u32, u64, u64, u32)> = Vec::new();
        let mut stores: Vec<(u32, u64, u64, u32)> = Vec::new();
        let mut idx = from;
        while idx < end {
            if self.post.tags.contains_key(&idx) {
                return None;
            }
            let x = self.post.insts[idx].clone();
            let offset = match x.imm {
                // A memory index (alignment bit 6) is refused by `step`.
                Imm::MemArg { align, .. } if align >= 0x40 => return None,
                Imm::MemArg { offset, .. } => u64::from(offset),
                _ => 0,
            };
            if let Some(w) = copy_load_width(x.opcode) {
                // Every load precedes every store.
                if !stores.is_empty() {
                    return None;
                }
                let a = self.pop(&mut t);
                let (b, o, _, _) = self.norm_addr(a, offset, k as usize);
                let ty = if w == 8 { ValKind::I64 } else { ValKind::I32 };
                let tmp = self.intern(
                    Term::CopyTmp {
                        effect: k,
                        index: loads.len() as u32,
                    },
                    Some(ty),
                );
                t.stack.push(tmp);
                loads.push((b, o, w, tmp));
            } else if let Some(w) = copy_store_width(x.opcode) {
                let v = self.pop(&mut t);
                let a = self.pop(&mut t);
                let (b, o, _, _) = self.norm_addr(a, offset, k as usize);
                stores.push((b, o, w, v));
                if stores.len() >= loads.len() {
                    idx += 1;
                    break;
                }
            } else if is_control(x.opcode)
                || is_effect(&x)
                || self.step(Side::Post, &mut t, idx).is_err()
            {
                return None;
            }
            idx += 1;
        }
        let m = loads.len();
        if m == 0 || stores.len() != m {
            return None;
        }
        let (bs, bd) = (loads[0].0, stores[0].0);
        if loads.iter().any(|l| l.0 != bs) || stores.iter().any(|s| s.0 != bd) {
            return None;
        }
        let ks = loads.iter().map(|l| l.1).min()?;
        let kd = stores.iter().map(|s| s.1).min()?;
        // Each store writes one distinct load's value, of its width, at its
        // relative offset.
        let mut used = vec![false; m];
        for s in &stores {
            let j = loads.iter().position(|l| l.3 == s.3)?;
            if used[j] || loads[j].2 != s.2 || loads[j].1 - ks != s.1 - kd {
                return None;
            }
            used[j] = true;
        }
        // The chunks tile [0, n) exactly.
        let mut chunks: Vec<(u64, u64)> = loads.iter().map(|l| (l.1 - ks, l.2)).collect();
        chunks.sort_unstable();
        let mut at = 0u64;
        for (o, w) in chunks {
            if o != at {
                return None;
            }
            at += w;
        }
        // The first store is the one that reaches the destination's end.
        if at != n || stores[0].1 - kd + stores[0].2 != n {
            return None;
        }
        let len = self.intern(Term::Const(ValKind::I32, n), Some(ValKind::I32));
        t.effects.push(Effect {
            op: 0xfc,
            sub: Some(10),
            imm: Imm::None,
            raw: None,
            args: vec![len],
            addrs: vec![(bd, kd), (bs, ks)],
            memarg_offset: 0,
            premised: false,
        });
        self.report.copies_expanded += 1;
        Some((t, idx))
    }

    /// Are two terms equal on every input? Syntactically, or by a certified
    /// solver proof of an integer residual.
    fn equal(&mut self, a: u32, b: u32, what: TvFailureKind, ctx: &str) -> Result<(), TvFailure> {
        if a == b {
            return Ok(());
        }
        let seg = self.seg;
        let ResidualPolicy::Solver {
            timeout_ms,
            max_queries,
        } = self.req.residual
        else {
            return Err(fail(what, Some(seg), format!("{ctx}: terms differ")));
        };
        if self.queries >= max_queries {
            return Err(fail(
                TvFailureKind::ResidualUnproven,
                Some(seg),
                format!("{ctx}: residual query limit {max_queries} reached"),
            ));
        }
        self.queries += 1;
        let mut vars = BTreeMap::new();
        let (Some(ea), Some(eb)) = (self.smt(a, &mut vars, 0), self.smt(b, &mut vars, 0)) else {
            return Err(fail(
                TvFailureKind::ResidualUnproven,
                Some(seg),
                format!("{ctx}: residual outside the integer fragment"),
            ));
        };
        if ea.bv_width() != eb.bv_width() {
            return Err(fail(what, Some(seg), format!("{ctx}: widths differ")));
        }
        let ob = crate::lowering_proof::ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: format!("wasm_local_tv residual ({ctx})"),
            trust_ir_expr: ea,
            aarch64_expr: eb,
            inputs: vars.into_iter().collect(),
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
        };
        let config = crate::ay_bridge::AYConfig::default().with_timeout(timeout_ms);
        match crate::ay_bridge::verify_with_ay(&ob, &config) {
            crate::ay_bridge::AYResult::Verified => {
                self.report.residuals_proven += 1;
                Ok(())
            }
            // A counterexample is a difference, reported as one.
            crate::ay_bridge::AYResult::CounterExample(cex) => Err(fail(
                what,
                Some(seg),
                format!("{ctx}: the solver found inputs where the terms differ ({cex:?})"),
            )),
            other => Err(fail(
                TvFailureKind::ResidualUnproven,
                Some(seg),
                format!("{ctx}: solver did not certify the residual ({other})"),
            )),
        }
    }

    /// The integer SMT term of `t`; leaves become variables. `None` outside
    /// the integer fragment (floats, untyped stack inputs, unmodelled ops).
    fn smt(&self, t: u32, vars: &mut BTreeMap<String, u32>, depth: usize) -> Option<SmtExpr> {
        if depth > 256 {
            return None;
        }
        let width = |ty: Option<ValKind>| match ty? {
            ValKind::I32 => Some(32u32),
            ValKind::I64 => Some(64u32),
            _ => None,
        };
        let ty = self.arena.ty[t as usize];
        let leaf = |vars: &mut BTreeMap<String, u32>| {
            let w = width(ty)?;
            let name = format!("t{t}");
            vars.insert(name.clone(), w);
            Some(SmtExpr::var(name, w))
        };
        match &self.arena.terms[t as usize] {
            Term::Const(_, bits) => Some(SmtExpr::bv_const(*bits, width(ty)?)),
            Term::StackIn(_) => None,
            Term::Param(_)
            | Term::RelocConst(..)
            | Term::LiveIn(_)
            | Term::PreUnk(_)
            | Term::PostUnk(_)
            | Term::Result { .. }
            | Term::CopyTmp { .. } => leaf(vars),
            Term::Op { op, args, .. } => {
                let mut a = Vec::with_capacity(args.len());
                for &x in args {
                    a.push(self.smt(x, vars, depth + 1)?);
                }
                let w = |e: &SmtExpr| e.bv_width();
                let e = match (*op, a.as_slice()) {
                    (0x45 | 0x50, [x]) => sem::encode_eqz(x.clone()),
                    (0x46 | 0x51, [x, y]) => sem::encode_eq(x.clone(), y.clone()),
                    (0x47 | 0x52, [x, y]) => sem::encode_ne(x.clone(), y.clone()),
                    (0x48 | 0x53, [x, y]) => sem::encode_lt_s(x.clone(), y.clone()),
                    (0x49 | 0x54, [x, y]) => sem::encode_lt_u(x.clone(), y.clone()),
                    (0x4a | 0x55, [x, y]) => sem::encode_gt_s(x.clone(), y.clone()),
                    (0x4b | 0x56, [x, y]) => sem::encode_gt_u(x.clone(), y.clone()),
                    (0x4c | 0x57, [x, y]) => sem::encode_le_s(x.clone(), y.clone()),
                    (0x4d | 0x58, [x, y]) => sem::encode_le_u(x.clone(), y.clone()),
                    (0x4e | 0x59, [x, y]) => sem::encode_ge_s(x.clone(), y.clone()),
                    (0x4f | 0x5a, [x, y]) => sem::encode_ge_u(x.clone(), y.clone()),
                    (0x67 | 0x79, [x]) => sem::encode_clz(x.clone()),
                    (0x68 | 0x7a, [x]) => sem::encode_ctz(x.clone()),
                    (0x69 | 0x7b, [x]) => sem::encode_popcnt(x.clone()),
                    (0x6a | 0x7c, [x, y]) => sem::encode_add(x.clone(), y.clone()),
                    (0x6b | 0x7d, [x, y]) => sem::encode_sub(x.clone(), y.clone()),
                    (0x6c | 0x7e, [x, y]) => sem::encode_mul(x.clone(), y.clone()),
                    (0x71 | 0x83, [x, y]) => sem::encode_and(x.clone(), y.clone()),
                    (0x72 | 0x84, [x, y]) => sem::encode_or(x.clone(), y.clone()),
                    (0x73 | 0x85, [x, y]) => sem::encode_xor(x.clone(), y.clone()),
                    (0x74 | 0x86, [x, y]) => sem::encode_shl(x.clone(), y.clone(), w(x)),
                    (0x75 | 0x87, [x, y]) => sem::encode_shr_s(x.clone(), y.clone(), w(x)),
                    (0x76 | 0x88, [x, y]) => sem::encode_shr_u(x.clone(), y.clone(), w(x)),
                    (0x77 | 0x89, [x, y]) => sem::encode_rotl(x.clone(), y.clone(), w(x)),
                    (0x78 | 0x8a, [x, y]) => sem::encode_rotr(x.clone(), y.clone(), w(x)),
                    (0xa7, [x]) if w(x) == 64 => sem::encode_wrap(x.clone()),
                    (0xac, [x]) if w(x) == 32 => sem::encode_sext_i32_i64(x.clone()),
                    (0xad, [x]) if w(x) == 32 => sem::encode_zext_i32_i64(x.clone()),
                    (0xc0 | 0xc2, [x]) => sem::encode_sign_extend_in_place(x.clone(), 8),
                    (0xc1 | 0xc3, [x]) => sem::encode_sign_extend_in_place(x.clone(), 16),
                    (0xc4, [x]) if w(x) == 64 => sem::encode_sign_extend_in_place(x.clone(), 32),
                    (0x1b, [v1, v2, c]) if w(c) == 32 && w(v1) == w(v2) => {
                        sem::encode_select(v1.clone(), v2.clone(), c.clone())
                    }
                    _ => return None,
                };
                Some(e)
            }
        }
    }

    fn compare_segment(&mut self, pre: &SideState, post: &SideState) -> Result<(), TvFailure> {
        let seg = self.seg;
        if pre.effects.len() != post.effects.len() {
            return Err(fail(
                TvFailureKind::EffectMismatch,
                Some(seg),
                format!(
                    "{} effects before, {} after",
                    pre.effects.len(),
                    post.effects.len()
                ),
            ));
        }
        for (k, (a, b)) in pre.effects.iter().zip(&post.effects).enumerate() {
            if a.op != b.op
                || a.sub != b.sub
                || a.imm != b.imm
                || a.raw != b.raw
                || a.args.len() != b.args.len()
                || a.addrs.len() != b.addrs.len()
            {
                return Err(fail(
                    TvFailureKind::EffectMismatch,
                    Some(seg),
                    format!(
                        "effect {k}: opcode 0x{:02x} before, 0x{:02x} after (or immediates differ)",
                        a.op, b.op
                    ),
                ));
            }
            for (j, (&(x, xo), &(y, yo))) in a.addrs.iter().zip(&b.addrs).enumerate() {
                if xo != yo {
                    return Err(fail(
                        TvFailureKind::EffectMismatch,
                        Some(seg),
                        format!(
                            "effect {k} (opcode 0x{:02x}) address {j}: static offset {xo} \
                             before, {yo} after",
                            a.op
                        ),
                    ));
                }
                self.equal(
                    x,
                    y,
                    TvFailureKind::EffectMismatch,
                    &format!("effect {k} (opcode 0x{:02x}) address {j}", a.op),
                )?;
            }
            if a.memarg_offset != b.memarg_offset {
                self.report.offsets_folded += 1;
                if a.premised || b.premised {
                    self.report.premised_folds += 1;
                }
            }
            for (j, (&x, &y)) in a.args.iter().zip(&b.args).enumerate() {
                self.equal(
                    x,
                    y,
                    TvFailureKind::EffectMismatch,
                    &format!("effect {k} (opcode 0x{:02x}) operand {j}", a.op),
                )?;
            }
        }
        self.report.effects += pre.effects.len();
        if pre.base_pops != post.base_pops || pre.stack.len() != post.stack.len() {
            return Err(fail(
                TvFailureKind::StackMismatch,
                Some(seg),
                format!(
                    "stack takes {} and leaves {} before, takes {} and leaves {} after",
                    pre.base_pops,
                    pre.stack.len(),
                    post.base_pops,
                    post.stack.len()
                ),
            ));
        }
        for (j, (&x, &y)) in pre.stack.iter().zip(&post.stack).enumerate() {
            self.equal(
                x,
                y,
                TvFailureKind::StackMismatch,
                &format!("stack slot {j}"),
            )?;
        }
        Ok(())
    }

    /// What the current segment's exit may assume for fact checks: when the
    /// pre segment ends in `if` whose `then` arm is an empty segment ending in
    /// `unreachable`, every live-out local is live only on the `if`'s false
    /// edge, where the condition is zero. Returns the pairs `(x, y)` with
    /// `x <=u y` that follow from that (`x >u y` or `y <u x` zero, through
    /// `i32.or`).
    fn guard_assumptions(&self, pre: &SideState) -> Vec<(u32, u32)> {
        let s = self.seg;
        let c = &self.pre.controls;
        if s + 1 >= c.len()
            || self.pre.insts[c[s]].opcode != 0x04
            || self.pre.insts[c[s + 1]].opcode != 0x00
            || c[s + 1] != c[s] + 1
        {
            return Vec::new();
        }
        let Some(&cond) = pre.stack.last() else {
            return Vec::new();
        };
        let mut out = Vec::new();
        let mut work = vec![cond];
        while let Some(t) = work.pop() {
            if let Term::Op { op, args, .. } = &self.arena.terms[t as usize]
                && args.len() == 2
                && self.arena.ty[args[0] as usize] == Some(ValKind::I32)
            {
                match op {
                    // A zero `or` has both operands zero.
                    0x72 => work.extend_from_slice(args),
                    // `x >u y` is zero: x <=u y.
                    0x4b => out.push((args[0], args[1])),
                    // `y <u x` is zero: x <=u y.
                    0x49 => out.push((args[1], args[0])),
                    _ => {}
                }
            }
        }
        out
    }

    /// An upper bound of the frame base `t` under `guard`: `t = y - k`, or
    /// `(y - k) & -align` for a power-of-two `align` with `2k + align <=
    /// 2^32`, together with `t <=u y`, means the subtraction did not wrap
    /// (module docs), so `t <= 2^32 - 1 - k`.
    fn guarded_max(&self, t: u32, guard: &[(u32, u32)]) -> Option<u64> {
        let sub_of = |s: u32| -> Option<(u32, u64)> {
            match &self.arena.terms[s as usize] {
                Term::Op { op: 0x6b, args, .. } => match self.arena.constant(args[1]) {
                    Some((ValKind::I32, k)) => Some((args[0], k)),
                    _ => None,
                },
                _ => None,
            }
        };
        let (y, k) = match &self.arena.terms[t as usize] {
            Term::Op { op: 0x71, args, .. } => {
                let (Some((ValKind::I32, m)), Some((y, k))) =
                    (self.arena.constant(args[1]), sub_of(args[0]))
                else {
                    return None;
                };
                let align = (!m & u64::from(u32::MAX)) + 1;
                if !align.is_power_of_two() || 2 * k + align > 1u64 << 32 {
                    return None;
                }
                (y, k)
            }
            _ => sub_of(t)?,
        };
        guard.contains(&(t, y)).then(|| u64::from(u32::MAX) - k)
    }

    fn check_live_out(
        &mut self,
        pre: &mut SideState,
        post: &mut SideState,
    ) -> Result<(), TvFailure> {
        let seg = self.seg;
        let w = self.words;
        if w == 0 || self.succ[seg].is_empty() {
            return Ok(());
        }
        let mut out = vec![0u64; w];
        let succs = self.succ[seg].clone();
        for &s in &succs {
            for (o, x) in out.iter_mut().zip(&self.live_in[s * w..(s + 1) * w]) {
                *o |= *x;
            }
        }
        self.spend(w * (succs.len() + 1))?;
        // Locals whose boundary value may differ from what the start assumed:
        // all of them in the entry segment (which assumed nothing), otherwise
        // those not assumed live in, and those either side wrote.
        let mut cand: Vec<u32> = Vec::new();
        let in_out = |l: u32, out: &[u64], gbit: &[u32]| -> bool {
            match gbit.get(l as usize) {
                Some(&g) if g != u32::MAX => out[g as usize / 64] >> (g % 64) & 1 == 1,
                _ => false,
            }
        };
        for (i, &word) in out.iter().enumerate() {
            let fresh = if seg == 0 {
                word
            } else {
                word & !self.live_in[seg * w + i]
            };
            let mut bits = fresh;
            while bits != 0 {
                let b = bits.trailing_zeros() as usize;
                bits &= bits - 1;
                cand.push(self.glocal[i * 64 + b]);
            }
        }
        for &l in &pre.written {
            if in_out(l, &out, &self.gbit) {
                cand.push(l);
            }
        }
        for &c in &post.written {
            if let Some(ls) = self.inverse.get(c as usize) {
                for &l in ls {
                    if in_out(l, &out, &self.gbit) {
                        cand.push(l);
                    }
                }
            }
        }
        cand.sort_unstable();
        cand.dedup();
        self.spend(cand.len())?;
        let guard = self.guard_assumptions(pre);
        for l in cand {
            let a = self.read_local(Side::Pre, pre, l)?;
            let claim = self.claims[l as usize];
            if claim != LocalFacts::NONE {
                let mut f = self.arena.facts[a as usize];
                if !f.implies(claim)
                    && let Some(max) = self.guarded_max(a, &guard)
                {
                    f = tighten(LocalFacts { max, ..f }, 32);
                }
                if !f.implies(claim) {
                    return Err(fail(
                        TvFailureKind::FactUnproven,
                        Some(seg),
                        format!(
                            "live-out pre local {l}: claimed bound {} / sign width {}, \
                             derived {} / {}",
                            claim.max, claim.sext, f.max, f.sext
                        ),
                    ));
                }
                self.report.facts_checked += 1;
            }
            let b = match self.req.image[l as usize].clone() {
                LocalImage::Local(c) => self.read_local(Side::Post, post, c)?,
                LocalImage::Const(bytes) => self.image_const(&bytes)?,
                LocalImage::Unused => {
                    return Err(fail(
                        TvFailureKind::LiveOutMismatch,
                        Some(seg),
                        format!("pre local {l} is live out but has no image"),
                    ));
                }
            };
            self.equal(
                a,
                b,
                TvFailureKind::LiveOutMismatch,
                &format!("live-out pre local {l}"),
            )?;
            self.report.live_out_checks += 1;
        }
        Ok(())
    }
}

/// The dependencies of one pre segment for STRONG liveness: the locals whose
/// value at the segment start reaches an effect operand or the segment's end
/// stack, and for each local the segment writes, the locals its final value
/// is computed from. A local read only into values that are dropped, or into
/// locals that are dead, is not strongly live.
///
/// Any liveness keeps the validation sound (module docs: an untracked local
/// reads a private symbol, so an observable use of it fails the comparison);
/// strong liveness only spares the comparison of values the pre body never
/// observes, such as those the emission pass deletes as dead.
struct SegmentDeps {
    base: Vec<u64>,
    writes: Vec<(u32, Vec<u64>)>,
}

type LocalDependencies = (Vec<u32>, Vec<(u32, Vec<u32>)>);

impl SegmentDeps {
    /// As bitsets over the liveness bits; `None` (a segment the dependency
    /// scan does not read) depends on every local it reads, which is plain
    /// liveness.
    fn bits(
        deps: Option<LocalDependencies>,
        uses: &[u32],
        defs: &[u32],
        gbit: &[u32],
        words: usize,
    ) -> SegmentDeps {
        let set = |ls: &[u32]| -> Vec<u64> {
            let mut v = vec![0u64; words];
            for &l in ls {
                if let Some(&g) = gbit.get(l as usize)
                    && g != u32::MAX
                {
                    v[g as usize / 64] |= 1u64 << (g % 64);
                }
            }
            v
        };
        match deps {
            Some((base, writes)) => SegmentDeps {
                base: set(&base),
                writes: writes.iter().map(|(l, d)| (*l, set(d))).collect(),
            },
            None => SegmentDeps {
                base: set(uses),
                writes: defs.iter().map(|&l| (l, set(uses))).collect(),
            },
        }
    }
}

/// Most locals one value's dependency set may name before the segment is
/// treated as depending on everything it reads.
const MAX_DEPS: usize = 256;

fn union(a: &[u32], b: &[u32]) -> Option<Vec<u32>> {
    let mut v: Vec<u32> = a.iter().chain(b).copied().collect();
    v.sort_unstable();
    v.dedup();
    (v.len() <= MAX_DEPS).then_some(v)
}

/// The dependency scan of [`SegmentDeps`] over one pre segment's
/// instructions: `(base, writes)` with local indices, or `None` for an
/// instruction it has no rule for (or a set past [`MAX_DEPS`]).
fn segment_deps(insts: &[DecodedInst], types: &dyn TvTypes) -> Option<LocalDependencies> {
    let mut stack: Vec<Vec<u32>> = Vec::new();
    let mut cur: HashMap<u32, Vec<u32>> = HashMap::new();
    let mut base: Vec<u32> = Vec::new();
    let pop = |s: &mut Vec<Vec<u32>>| s.pop().unwrap_or_default();
    for x in insts {
        let used = |n: usize, stack: &mut Vec<Vec<u32>>, base: &mut Vec<u32>| -> Option<()> {
            for _ in 0..n {
                let v = pop(stack);
                *base = union(base, &v)?;
            }
            Some(())
        };
        match x.opcode {
            0x01 => {}
            0x1a => {
                pop(&mut stack);
            }
            0x1b => {
                let mut v = Vec::new();
                for _ in 0..3 {
                    v = union(&v, &pop(&mut stack))?;
                }
                stack.push(v);
            }
            0x20..=0x22 => {
                let Imm::Index(l) = x.imm else { return None };
                if x.opcode == 0x20 {
                    stack.push(cur.get(&l).cloned().unwrap_or_else(|| vec![l]));
                } else {
                    let v = pop(&mut stack);
                    if x.opcode == 0x22 {
                        stack.push(v.clone());
                    }
                    cur.insert(l, v);
                }
            }
            0x23 | 0x3f => stack.push(Vec::new()),
            0x24 => used(1, &mut stack, &mut base)?,
            0x28..=0x35 | 0x40 => {
                used(1, &mut stack, &mut base)?;
                stack.push(Vec::new());
            }
            0x36..=0x3e => used(2, &mut stack, &mut base)?,
            0x41..=0x44 => stack.push(Vec::new()),
            0x10 | 0x11 => {
                let sig = match x.imm {
                    Imm::Index(f) if x.opcode == 0x10 => types.func(f)?,
                    Imm::CallIndirect { type_idx, .. } if x.opcode == 0x11 => {
                        types.type_at(type_idx)?
                    }
                    _ => return None,
                };
                used(
                    sig.params.len() + usize::from(x.opcode == 0x11),
                    &mut stack,
                    &mut base,
                )?;
                for _ in &sig.results {
                    stack.push(Vec::new());
                }
            }
            0xfc if matches!(x.sub, Some(10) | Some(11)) => used(3, &mut stack, &mut base)?,
            op => {
                if let Some((n, _)) = trapping_numeric(op) {
                    used(n, &mut stack, &mut base)?;
                    stack.push(Vec::new());
                } else if let Some((n, _)) = pure_numeric(op, x.sub) {
                    let mut v = Vec::new();
                    for _ in 0..n {
                        v = union(&v, &pop(&mut stack))?;
                    }
                    stack.push(v);
                } else {
                    return None;
                }
            }
        }
    }
    for v in &stack {
        base = union(&base, v)?;
    }
    let mut writes: Vec<(u32, Vec<u32>)> = cur.into_iter().collect();
    writes.sort_unstable();
    Some((base, writes))
}

/// Validate one rewritten function body against the lane's own body (module
/// docs). `Ok` carries what was compared; `Err` names the first difference or
/// the reason the model could not decide.
pub fn validate(req: &TvRequest<'_>) -> Result<TvReport, TvFailure> {
    validate_with_premises(req, "", &[])
}

/// [`validate`] under the no-wrap `premises` of the function named
/// `function` (module docs): each is active only when it is bound to that
/// function name and to the pre body's code (derived for it by
/// `wasm_nowrap_premise::check_nowrap_premises`, or carried to it by
/// [`validate_control_with_premises`]), the pre body writes its local
/// exactly once, and its local, base and index locals are `i32` pre locals.
pub fn validate_with_premises(
    req: &TvRequest<'_>,
    function: &str,
    premises: &[NoWrapPremise],
) -> Result<TvReport, TvFailure> {
    let n_pre = req.params.len() + req.pre.locals.len();
    if req.image.len() != n_pre {
        return Err(fail(
            TvFailureKind::ImageInvalid,
            None,
            format!(
                "image has {} entries for {n_pre} pre locals",
                req.image.len()
            ),
        ));
    }
    let pre = decode(&req.pre, "pre")?;
    let post = decode(&req.post, "post")?;
    if pre.controls.len() != post.controls.len() {
        return Err(fail(
            TvFailureKind::StructureMismatch,
            None,
            format!(
                "{} control instructions before, {} after",
                pre.controls.len(),
                post.controls.len()
            ),
        ));
    }
    for (k, (&a, &b)) in pre.controls.iter().zip(&post.controls).enumerate() {
        let (x, y) = (&pre.insts[a], &post.insts[b]);
        if x.opcode != y.opcode || x.imm != y.imm {
            return Err(fail(
                TvFailureKind::StructureMismatch,
                Some(k),
                format!(
                    "control {k}: opcode 0x{:02x} before, 0x{:02x} after (or immediates differ)",
                    x.opcode, y.opcode
                ),
            ));
        }
    }
    let succ = successors(&pre.insts, &pre.controls)?;
    let nseg = pre.controls.len() + 1;

    let n_params = req.params.len() as u32;
    let n_post = req.params.len() + req.post.locals.len();
    let post_ty = |c: usize| {
        if c < req.params.len() {
            req.params[c]
        } else {
            req.post.locals[c - req.params.len()]
        }
    };
    let pre_ty = |l: usize| {
        if l < req.params.len() {
            req.params[l]
        } else {
            req.pre.locals[l - req.params.len()]
        }
    };
    let mut inverse: Vec<Vec<u32>> = vec![Vec::new(); n_post];
    for (l, im) in req.image.iter().enumerate() {
        match im {
            LocalImage::Local(c) => {
                let c = *c as usize;
                if c >= n_post || post_ty(c) != pre_ty(l) {
                    return Err(fail(
                        TvFailureKind::ImageInvalid,
                        None,
                        format!("pre local {l} is imaged to post local {c} of another type"),
                    ));
                }
                inverse[c].push(l as u32);
            }
            LocalImage::Const(bytes) => {
                let ok = decode_body(bytes, 0).ok().is_some_and(|v| {
                    v.len() == 1 && const_term(&v[0]).is_some_and(|(ty, _)| ty == pre_ty(l))
                });
                if !ok {
                    return Err(fail(
                        TvFailureKind::ImageInvalid,
                        None,
                        format!("pre local {l} is imaged to a constant of another type"),
                    ));
                }
            }
            LocalImage::Unused => {}
        }
    }
    let claims: Vec<LocalFacts> = if req.facts.is_empty() {
        vec![LocalFacts::NONE; n_pre]
    } else if req.facts.len() != n_pre {
        return Err(fail(
            TvFailureKind::ImageInvalid,
            None,
            format!("{} facts claimed for {n_pre} pre locals", req.facts.len()),
        ));
    } else {
        for (l, f) in req.facts.iter().enumerate() {
            if *f != LocalFacts::NONE && int_width(Some(pre_ty(l))).is_none() {
                return Err(fail(
                    TvFailureKind::ImageInvalid,
                    None,
                    format!("a fact is claimed for the float pre local {l}"),
                ));
            }
        }
        req.facts.to_vec()
    };

    // Liveness over segments of the PRE body, for locals with an upward-
    // exposed read somewhere (no other local is live into any segment).
    let mut uses: Vec<Vec<u32>> = vec![Vec::new(); nseg];
    let mut defs: Vec<Vec<u32>> = vec![Vec::new(); nseg];
    let mut gbit = vec![u32::MAX; n_pre];
    let mut ng = 0u32;
    {
        let mut written_at = vec![usize::MAX; n_pre];
        let mut read_at = vec![usize::MAX; n_pre];
        for s in 0..nseg {
            for i in segment_range(&pre.controls, pre.insts.len(), s) {
                let x = &pre.insts[i];
                let Imm::Index(l) = x.imm else { continue };
                if !matches!(x.opcode, 0x20..=0x22) {
                    continue;
                }
                let li = l as usize;
                if li >= n_pre {
                    return Err(fail(
                        TvFailureKind::Unsupported,
                        Some(s),
                        format!("pre local {l} is outside the function's locals"),
                    ));
                }
                if x.opcode == 0x20 {
                    if written_at[li] != s && read_at[li] != s {
                        read_at[li] = s;
                        if gbit[li] == u32::MAX {
                            gbit[li] = ng;
                            ng += 1;
                        }
                        uses[s].push(l);
                    }
                } else if written_at[li] != s {
                    written_at[li] = s;
                    defs[s].push(l);
                }
            }
        }
    }
    let words = (ng as usize).div_ceil(64);
    let mut glocal = vec![u32::MAX; words * 64];
    for (l, &g) in gbit.iter().enumerate() {
        if g != u32::MAX {
            glocal[g as usize] = l as u32;
        }
    }
    let mut v = Validator {
        req,
        pre,
        post,
        n_params,
        gbit,
        glocal,
        words,
        live_in: Vec::new(),
        succ,
        inverse,
        claims,
        work: 0,
        queries: 0,
        report: TvReport::default(),
        arena: Arena::default(),
        seg: 0,
        premises: HashMap::new(),
        nowrap: HashMap::new(),
    };
    if !premises.is_empty() {
        let mut writes: HashMap<u32, usize> = HashMap::new();
        for x in &v.pre.insts {
            if let (0x21 | 0x22, Imm::Index(l)) = (x.opcode, &x.imm) {
                *writes.entry(*l).or_default() += 1;
            }
        }
        for p in premises {
            let i32_local = |l: u32| (l as usize) < n_pre && pre_ty(l as usize) == ValKind::I32;
            if p.binds(function, req.pre.code)
                && writes.get(&p.result()) == Some(&1)
                && i32_local(p.result())
                && i32_local(p.base())
                && i32_local(p.index())
            {
                v.premises.insert(p.result(), *p);
            }
        }
    }
    v.spend(nseg.saturating_mul(words.max(1)))?;
    v.live_in = vec![0u64; nseg * words];
    let mut strong: Vec<SegmentDeps> = Vec::with_capacity(nseg);
    for (s, seg_uses) in uses.iter().enumerate() {
        let range = segment_range(&v.pre.controls, v.pre.insts.len(), s);
        v.spend(range.len())?;
        let deps = segment_deps(&v.pre.insts[range], req.types);
        strong.push(SegmentDeps::bits(deps, seg_uses, &defs[s], &v.gbit, words));
    }
    if words > 0 {
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); nseg];
        for (s, ss) in v.succ.iter().enumerate() {
            for &t in ss {
                preds[t].push(s);
            }
        }
        let mut queued = vec![true; nseg];
        let mut work: Vec<usize> = (0..nseg).collect();
        let mut out = vec![0u64; words];
        while let Some(s) = work.pop() {
            queued[s] = false;
            out.iter_mut().for_each(|w| *w = 0);
            for &t in &v.succ[s] {
                for (o, x) in out.iter_mut().zip(&v.live_in[t * words..(t + 1) * words]) {
                    *o |= *x;
                }
            }
            // A written local's value at the segment end depends on the
            // locals its final term reads; only a live one's do.
            let mut add: Vec<u64> = vec![0u64; words];
            for (l, deps) in &strong[s].writes {
                let g = v.gbit[*l as usize];
                if g != u32::MAX && out[g as usize / 64] >> (g % 64) & 1 == 1 {
                    for (a, d) in add.iter_mut().zip(deps) {
                        *a |= *d;
                    }
                }
            }
            for &l in &defs[s] {
                let g = v.gbit[l as usize];
                if g != u32::MAX {
                    out[g as usize / 64] &= !(1u64 << (g % 64));
                }
            }
            for (o, (a, b)) in out.iter_mut().zip(add.iter().zip(&strong[s].base)) {
                *o |= *a | *b;
            }
            v.spend(words * (v.succ[s].len() + 2 + strong[s].writes.len()))?;
            if out[..] != v.live_in[s * words..(s + 1) * words] {
                v.live_in[s * words..(s + 1) * words].copy_from_slice(&out);
                for &p in &preds[s] {
                    if !queued[p] {
                        queued[p] = true;
                        work.push(p);
                    }
                }
            }
        }
    }

    let mut frames = vec![Frame::default()];
    for s in 0..nseg {
        v.seg = s;
        v.arena.clear();
        v.nowrap.clear();
        let mut a = SideState::default();
        let mut b = SideState::default();
        let r_pre = segment_range(&v.pre.controls, v.pre.insts.len(), s);
        let r_post = segment_range(&v.post.controls, v.post.insts.len(), s);
        v.spend(r_pre.len() + r_post.len())?;
        for i in r_pre {
            v.step(Side::Pre, &mut a, i)?;
        }
        let mut i = r_post.start;
        while i < r_post.end {
            if let Some(n) = v.small_copy_at(&a, &b, i)
                && let Some((expanded, next)) = v.copy_expansion(&b, i, r_post.end, n)
            {
                b = expanded;
                i = next;
                continue;
            }
            v.step(Side::Post, &mut b, i)?;
            i += 1;
        }
        check_heights(&mut frames, s, &a, &b)?;
        v.compare_segment(&a, &b)?;
        v.check_live_out(&mut a, &mut b)?;
        v.report.segments += 1;
        if let Some(&c) = v.pre.controls.get(s) {
            control_heights(&mut frames, s, &v.pre.insts[c])?;
        }
    }
    Ok(v.report)
}

/// One open control frame of the stack-height model: the operand-stack
/// height above the frame's base, its result count, and whether the rest of
/// the frame is unreachable (the stack is then polymorphic).
#[derive(Default)]
struct Frame {
    height: usize,
    results: usize,
    unreachable: bool,
}

/// The validator's own stack accounting, re-checked against WebAssembly's
/// typing. A segment's operands from below its start are the shared
/// [`Term::StackIn`] symbols, which stand for equal values only when they
/// exist: a reachable segment may take at most the values its frame holds
/// (none at function entry or at the start of a `block`, `loop`, `if` or
/// `else` arm), and a reachable `end` or `else` must see exactly the frame's
/// results. A symbolic rule that drops or invents a result value breaks one
/// of these, so the function is refused instead of being compared over
/// symbols that stand for nothing.
fn check_heights(
    frames: &mut [Frame],
    s: usize,
    pre: &SideState,
    post: &SideState,
) -> Result<(), TvFailure> {
    let Some(top) = frames.last_mut() else {
        return Err(fail(TvFailureKind::Unsupported, Some(s), "no open frame"));
    };
    for st in [pre, post] {
        let taken = st.base_pops as usize;
        if !top.unreachable && taken > top.height {
            return Err(fail(
                TvFailureKind::Unsupported,
                Some(s),
                format!(
                    "the stack model takes {taken} values from below the segment, where the \
                     frame holds {}",
                    top.height
                ),
            ));
        }
    }
    top.height = top.height.saturating_sub(pre.base_pops as usize) + pre.stack.len();
    Ok(())
}

/// Apply control instruction `x` (after segment `s`) to the height model.
fn control_heights(frames: &mut Vec<Frame>, s: usize, x: &DecodedInst) -> Result<(), TvFailure> {
    let bad = |what: &str| {
        fail(
            TvFailureKind::Unsupported,
            Some(s),
            format!("stack model at control 0x{:02x}: {what}", x.opcode),
        )
    };
    let results = |x: &DecodedInst| match x.imm {
        Imm::Block(bt) => Ok(bt.results().len()),
        _ => Err(bad("block without a block type")),
    };
    let take = |frames: &mut Vec<Frame>, n: usize| -> Result<(), TvFailure> {
        let top = frames.last_mut().ok_or_else(|| bad("no open frame"))?;
        if top.unreachable {
            top.height = top.height.saturating_sub(n);
        } else {
            top.height = top
                .height
                .checked_sub(n)
                .ok_or_else(|| bad("operand missing"))?;
        }
        Ok(())
    };
    let close = |f: &Frame| {
        if f.unreachable || f.height == f.results {
            Ok(())
        } else {
            Err(bad(&format!(
                "{} values at the end of a frame with {} results",
                f.height, f.results
            )))
        }
    };
    match x.opcode {
        0x02 | 0x03 => frames.push(Frame {
            results: results(x)?,
            ..Frame::default()
        }),
        0x04 => {
            take(frames, 1)?;
            frames.push(Frame {
                results: results(x)?,
                ..Frame::default()
            });
        }
        0x05 => {
            let top = frames.last_mut().ok_or_else(|| bad("no open frame"))?;
            close(top)?;
            top.height = 0;
            top.unreachable = false;
        }
        0x0b => {
            if frames.len() < 2 {
                return Err(bad("`end` closes the function body"));
            }
            let f = frames.pop().ok_or_else(|| bad("no open frame"))?;
            close(&f)?;
            let top = frames.last_mut().ok_or_else(|| bad("no open frame"))?;
            top.height += f.results;
        }
        0x0d => take(frames, 1)?,
        0x0e => {
            take(frames, 1)?;
            if let Some(top) = frames.last_mut() {
                top.unreachable = true;
            }
        }
        0x00 | 0x0c | 0x0f => {
            if let Some(top) = frames.last_mut() {
                top.unreachable = true;
            }
        }
        _ => return Err(bad("not a control instruction")),
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Whether the `w`-bit value `v` satisfies `f`.
    fn holds(v: u64, f: LocalFacts, w: u32) -> bool {
        v <= f.max && sign_extend(v, u32::from(f.sext).clamp(1, w), w) == v
    }

    fn sx(v: u64, w: u32) -> i64 {
        sign_extend(v, w, 64) as i64
    }

    /// The `(result, result width)` of `op` on `args` of width `w`.
    fn eval(op: u8, args: &[u64], w: u32) -> Option<(u64, u32)> {
        let m = ones(w);
        let a = args.first().copied().unwrap_or(0) & m;
        let b = args.get(1).copied().unwrap_or(0) & m;
        let k = (b % u64::from(w)) as u32;
        let cmp = |c: bool| Some((u64::from(c), 32));
        let (sa, sb) = (sx(a, w), sx(b, w));
        Some(match op {
            0x45 | 0x50 => return cmp(a == 0),
            0x46 | 0x51 => return cmp(a == b),
            0x47 | 0x52 => return cmp(a != b),
            0x48 | 0x53 => return cmp(sa < sb),
            0x49 | 0x54 => return cmp(a < b),
            0x4a | 0x55 => return cmp(sa > sb),
            0x4b | 0x56 => return cmp(a > b),
            0x4c | 0x57 => return cmp(sa <= sb),
            0x4d | 0x58 => return cmp(a <= b),
            0x4e | 0x59 => return cmp(sa >= sb),
            0x4f | 0x5a => return cmp(a >= b),
            0x67 | 0x79 => (u64::from(a.leading_zeros() - (64 - w)), w),
            0x68 | 0x7a => (u64::from(a.trailing_zeros().min(w)), w),
            0x69 | 0x7b => (u64::from(a.count_ones()), w),
            0x6a | 0x7c => (a.wrapping_add(b) & m, w),
            0x6b | 0x7d => (a.wrapping_sub(b) & m, w),
            0x71 | 0x83 => (a & b, w),
            0x72 | 0x84 => (a | b, w),
            0x73 | 0x85 => (a ^ b, w),
            0x75 | 0x87 => ((sa >> k) as u64 & m, w),
            0x76 | 0x88 => (a >> k, w),
            0xc0 | 0xc2 => (sign_extend(a, 8, w), w),
            0xc1 | 0xc3 => (sign_extend(a, 16, w), w),
            0xc4 => (sign_extend(a, 32, w), w),
            0xa7 => (a & ones(32), 32),
            0xac => (sign_extend(a, 32, 64), 64),
            0xad => (a & ones(32), 64),
            0x1b => (if args[2] != 0 { a } else { b }, w),
            _ => return None,
        })
    }

    const OPS: &[(u8, u32, usize)] = &[
        (0x45, 32, 1),
        (0x50, 64, 1),
        (0x46, 32, 2),
        (0x49, 32, 2),
        (0x4b, 32, 2),
        (0x48, 32, 2),
        (0x57, 64, 2),
        (0x67, 32, 1),
        (0x68, 32, 1),
        (0x69, 32, 1),
        (0x7a, 64, 1),
        (0x6a, 32, 2),
        (0x6b, 32, 2),
        (0x7c, 64, 2),
        (0x7d, 64, 2),
        (0x71, 32, 2),
        (0x72, 32, 2),
        (0x73, 32, 2),
        (0x83, 64, 2),
        (0x84, 64, 2),
        (0x85, 64, 2),
        (0x75, 32, 2),
        (0x76, 32, 2),
        (0x87, 64, 2),
        (0x88, 64, 2),
        (0xc0, 32, 1),
        (0xc1, 32, 1),
        (0xc2, 64, 1),
        (0xc3, 64, 1),
        (0xc4, 64, 1),
        (0xa7, 64, 1),
        (0xac, 32, 1),
        (0xad, 32, 1),
        (0x1b, 32, 3),
    ];

    const VALUES: &[u64] = &[
        0,
        1,
        2,
        3,
        7,
        8,
        31,
        32,
        33,
        0x7f,
        0x80,
        0xff,
        0x100,
        0x7fff,
        0x8000,
        0xffff,
        0x1_0000,
        0x7fff_ffff,
        0x8000_0000,
        0xffff_ff80,
        0xffff_fff0,
        0xffff_ffff,
        0xdead_beef,
        0x1_0000_0000,
        0x7fff_ffff_ffff_ffff,
        0x8000_0000_0000_0000,
        0xffff_ffff_ffff_ff80,
        u64::MAX,
    ];

    /// Every fact rule holds of the concrete result on every operand value the
    /// operand facts admit: the exact facts of each value, and facts weakened
    /// by joining with another value's.
    #[test]
    fn every_fact_rule_holds_on_concrete_values() {
        let mut checked = 0usize;
        for &(op, w, arity) in OPS {
            let vals: Vec<u64> = VALUES.iter().map(|v| v & ones(w)).collect();
            let pick = |i: usize, j: usize| (vals[i % vals.len()], vals[j % vals.len()]);
            for i in 0..vals.len() {
                for j in 0..vals.len() {
                    for weak in 0..vals.len() {
                        let (a, b) = pick(i, j);
                        let c = vals[(i + j) % vals.len()] & 1;
                        let args: Vec<u64> = match arity {
                            1 => vec![a],
                            2 => vec![a, b],
                            _ => vec![a, b, c],
                        };
                        let Some((r, rw)) = eval(op, &args, w) else {
                            continue;
                        };
                        let other = vals[weak];
                        for exact in [true, false] {
                            let facts: Vec<LocalFacts> = args
                                .iter()
                                .take(arity.min(2))
                                .map(|&v| {
                                    let f = const_facts(v, w);
                                    if exact {
                                        f
                                    } else {
                                        tighten(f.join(const_facts(other, w)), w)
                                    }
                                })
                                .collect();
                            let mut facts = facts;
                            if arity == 3 {
                                facts.push(const_facts(c, 32));
                            }
                            for consts in [true, false] {
                                let cs: Vec<Option<u64>> =
                                    args.iter().map(|&v| consts.then_some(v)).collect();
                                let f = pure_op_facts(op, &facts, &cs, rw);
                                assert!(
                                    holds(r, f, rw),
                                    "op 0x{op:02x} on {args:x?} (exact {exact}, consts \
                                     {consts}) = 0x{r:x}, facts {f:?}"
                                );
                                checked += 1;
                            }
                        }
                    }
                }
            }
        }
        assert!(checked > 100_000, "{checked}");
    }

    /// A constant's fact is exact, a narrow load's covers every byte it can
    /// return, and the identities the validator builds terms with hold
    /// whenever their fact condition does.
    #[test]
    fn load_facts_and_term_identities_hold() {
        for &v in VALUES {
            for w in [32, 64] {
                let v = v & ones(w);
                assert!(holds(v, const_facts(v, w), w));
                let f = const_facts(v, w);
                for mask_bits in 1..w {
                    let m = ones(mask_bits);
                    if f.max <= m {
                        assert_eq!(v & m, v);
                    }
                }
                for bits in [8, 16, 32] {
                    if u32::from(f.sext) <= bits && bits <= w {
                        assert_eq!(sign_extend(v, bits, w), v);
                    }
                }
            }
        }
        for raw in 0..=0xffffu64 {
            for (op, w) in [
                (0x2d, 32),
                (0x2c, 32),
                (0x2f, 32),
                (0x2e, 32),
                (0x31, 64),
                (0x30, 64),
                (0x33, 64),
                (0x32, 64),
            ] {
                let bits = if matches!(op, 0x2d | 0x2c | 0x31 | 0x30) {
                    8
                } else {
                    16
                };
                let byte = raw & ones(bits);
                let v = if matches!(op, 0x2c | 0x2e | 0x30 | 0x32) {
                    sign_extend(byte, bits, w)
                } else {
                    byte
                };
                let f = tighten(load_facts(op).expect("a narrow load"), w);
                assert!(holds(v, f, w), "0x{op:02x} 0x{v:x} {f:?}");
            }
        }
    }

    // ---- The body-side re-check of a no-wrap premise ----
    //
    // A premise bound to the body it is applied to is only constructed by
    // `check_nowrap_premises`, which refuses the bodies below; these tests
    // reach the validator's own re-check (the second line of defence) with
    // the test constructor.

    struct NoCalls;

    impl TvTypes for NoCalls {
        fn func(&self, _: u32) -> Option<FuncSig> {
            None
        }
        fn type_at(&self, _: u32) -> Option<FuncSig> {
            None
        }
        fn global(&self, _: u32) -> Option<ValKind> {
            None
        }
    }

    const GET: u8 = 0x20;
    const SET: u8 = 0x21;
    const C: u8 = 0x41;
    const ADD: u8 = 0x6a;
    const LOAD: u8 = 0x28;
    /// `x + 8` written to `V` (local 2) as a one-byte GEP's addition, then
    /// `i32.load (V)`.
    const GOOD: &[u8] = &[
        C, 8, SET, 1, GET, 0, GET, 1, ADD, SET, 2, GET, 2, LOAD, 2, 0, SET, 3, GET, 3,
    ];
    /// The premise shape of [`GOOD`]: `V = 2`, `B = 0`, `I = 1`, unscaled.
    const SHAPE: (u32, u32, u32, u32, bool) = (2, 0, 1, 1, false);

    /// `pre` (locals 1-3 `i32`) against `post` under `premises` applied as
    /// function `function`.
    fn premised(
        pre: &[u8],
        post: &[u8],
        function: &str,
        premises: &[NoWrapPremise],
    ) -> Result<TvReport, TvFailure> {
        validate_with_premises(
            &TvRequest {
                params: &[ValKind::I32],
                pre: TvBody {
                    locals: &[ValKind::I32; 3],
                    code: pre,
                    relocs: &[],
                },
                post: TvBody {
                    locals: &[],
                    code: post,
                    relocs: &[],
                },
                image: &[
                    LocalImage::Local(0),
                    LocalImage::Unused,
                    LocalImage::Unused,
                    LocalImage::Unused,
                ],
                facts: &[],
                types: &NoCalls,
                residual: ResidualPolicy::Refuse,
                max_work: 1 << 20,
            },
            function,
            premises,
        )
    }

    /// The body's own shape gates a bound premise: the sum written must be
    /// `B + I` of the values the locals hold (here `x + 12` while `I` holds
    /// 8), and `V` must be written once.
    #[test]
    fn a_bound_premise_is_rechecked_on_the_body() {
        let p = NoWrapPremise::for_test(SHAPE, "f", GOOD);
        let r = premised(GOOD, &[GET, 0, LOAD, 2, 8], "f", &[p]).expect("accepted");
        assert_eq!(r.premised_folds, 1);
        let other_sum = [
            C, 8, SET, 1, GET, 0, C, 12, ADD, SET, 2, GET, 2, LOAD, 2, 0, SET, 3, GET, 3,
        ];
        let p = NoWrapPremise::for_test(SHAPE, "f", &other_sum);
        let e = premised(&other_sum, &[GET, 0, LOAD, 2, 12], "f", &[p]).expect_err("refused");
        assert_eq!(e.kind, TvFailureKind::EffectMismatch, "{e}");
        let twice = [
            C, 8, SET, 1, GET, 0, GET, 1, ADD, SET, 2, GET, 2, SET, 2, GET, 2, LOAD, 2, 0, SET, 3,
            GET, 3,
        ];
        let p = NoWrapPremise::for_test(SHAPE, "f", &twice);
        let e = premised(&twice, &[GET, 0, LOAD, 2, 8], "f", &[p]).expect_err("refused");
        assert_eq!(e.kind, TvFailureKind::EffectMismatch, "{e}");
    }

    /// A premise licenses nothing for another function name or another
    /// body, and an accepted control cleanup carries it to the cleaned body
    /// only.
    #[test]
    fn a_premise_binds_its_function_and_body() {
        let folded: &[u8] = &[GET, 0, LOAD, 2, 8];
        let p = NoWrapPremise::for_test(SHAPE, "f", GOOD);
        for (name, premise) in [
            ("g", p),
            ("f", NoWrapPremise::for_test(SHAPE, "f", &[0x01])),
        ] {
            let e = premised(GOOD, folded, name, &[premise]).expect_err("refused");
            assert_eq!(e.kind, TvFailureKind::EffectMismatch, "{e}");
        }
        // `block; i32.const 8; local.set 1; end; ...` cleaned to GOOD: the
        // premise is carried to the cleaned body, which it then binds; a
        // premise of another body is dropped.
        let mut wrapped = vec![0x02, 0x40];
        wrapped.extend(&GOOD[..4]);
        wrapped.push(0x0b);
        wrapped.extend(&GOOD[4..]);
        let p_wrapped = NoWrapPremise::for_test(SHAPE, "f", &wrapped);
        let req = ControlTvRequest {
            results: 1,
            pre: TvBody {
                locals: &[ValKind::I32; 3],
                code: &wrapped,
                relocs: &[],
            },
            post: TvBody {
                locals: &[ValKind::I32; 3],
                code: GOOD,
                relocs: &[],
            },
            types: &NoCalls,
            max_work: 1 << 20,
        };
        let stale = NoWrapPremise::for_test(SHAPE, "f", &[0x01]);
        let (_, carried) =
            validate_control_with_premises(&req, &[p_wrapped, stale]).expect("accepted");
        assert_eq!(carried, vec![p]);
        let r = premised(GOOD, folded, "f", &carried).expect("accepted");
        assert_eq!(r.premised_folds, 1);
        // Uncarried, the wrapped body's premise licenses nothing on GOOD.
        assert!(premised(GOOD, folded, "f", &[p_wrapped]).is_err());
        // A refused cleanup carries nothing.
        let bad = [
            C, 9, SET, 1, GET, 0, GET, 1, ADD, SET, 2, GET, 2, LOAD, 2, 0, SET, 3, GET, 3,
        ];
        let req = ControlTvRequest {
            post: TvBody {
                locals: &[ValKind::I32; 3],
                code: &bad,
                relocs: &[],
            },
            ..req
        };
        assert!(validate_control_with_premises(&req, &[p_wrapped]).is_err());
    }
}
