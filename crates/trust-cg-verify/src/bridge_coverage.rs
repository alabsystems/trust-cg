// trust-cg-verify/bridge_coverage.rs — P0 bridge refinement-coverage manifest
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// CONTEXT: the bridge (`rustc_codegen_trust_cg`) lowers rustc MIR to trust-ir per
// compile. A per-compile MIR->trust-ir REFINEMENT lane already exists
// (`mir_semantics::{check_rvalue_lowering, ..}`, driven by the bridge's
// `refine_push_*` helpers + the `mir_to_trust_ir` drain): for each SCALAR rvalue
// it lowers, the bridge encodes the Rust-defined meaning (the MIR spec) and the
// trust-ir op it chose, and asks the verifier whether they can ever disagree. A
// `Refuted` verdict fails the compile CLOSED.
//
// But that lane refines ONLY scalar rvalue OP-SELECTION (which trust-ir op / cc /
// cast the bridge picked for a scalar value). EVERYTHING ELSE is still TRUSTED and
// — crucially — that trusted surface was IMPLICIT: a MIR rvalue / place / control
// shape that the bridge lowers without any refinement simply produced no
// obligation, and nothing recorded that it had been skipped. That is the same
// silent-coverage-hole class that `coverage_gate.rs` fixed on the OPCODE side
// (the #68-fneg bug: an emittable opcode with no proof obligation at all, never
// noticed).
//
// This module is the MIR->trust-ir analogue of `coverage_gate.rs`. It makes the
// trusted-vs-proven MIR surface VISIBLE and LOUD:
//
//   * Every MIR rvalue / place-projection / terminator SHAPE the bridge emits is
//     classified by an EXHAUSTIVE, wildcard-free `match` into exactly one of:
//       - `RefinableScalarOpSelection` — the scalar-rvalue refinement lane builds
//         and discharges an op-selection obligation for it (the EXISTING lane).
//       - `TrustedAllowlisted { reason, phase }` — currently unproven, but on an
//         EXPLICIT, named allowlist with a reason and the phase that will prove it
//         (e.g. "memory projection — P1", "terminator switch — P3"). This is the
//         key deliverable: the trusted surface becomes an enumerated, reviewable
//         list, not an implicit silence.
//       - `Unmodeled` — neither refined nor allowlisted; no coverage decision has
//         been made. LOUD by default; fails the compile CLOSED under STRICT.
//
//   * A per-function "refinement coverage manifest" is debug-loggable behind
//     `TCG_BRIDGE_COVERAGE`, and `TCG_BRIDGE_COVERAGE_STRICT` fails the compile on
//     any `Unmodeled` shape.
//
// The EXHAUSTIVENESS is load-bearing exactly as in `coverage_gate.rs`: the
// classifier `match`es over the local mirror enums (`RvalueKind` /
// `TerminatorShape` / `ProjectionKind`) are wildcard-free, AND the bridge-side
// adapters that map the real rustc enums onto these mirrors are wildcard-free too
// (`bridge_coverage_rvalue_kind` etc. in the bridge `lib.rs`). So a NEW rustc MIR
// rvalue / terminator / projection variant will NOT COMPILE until a human (a) adds
// the mirror variant and (b) classifies it here — which forces the
// refined/trusted/unmodeled decision exactly when the shape is introduced, not
// after it ships an unrefined lowering.
//
// HONESTY (return item f): "Refined" in the manifest reflects REALITY, not
// optimism. A shape's row is reported `REFINED` ONLY when a refinement obligation
// was actually PUSHED for it AND the drain reported it `Refined` (recorded in the
// refinement ledger via `note_refinement_*`). An obligation that was pushed but
// the active lane abstained on (e.g. a > 8-bit width with no solver present, which
// the fast lane skips) is reported honestly as TRUSTED-with-attempt, never as
// proven. And "Refined" only ever means OP-SELECTION (which op was chosen) — not
// operand wiring, not memory, not control flow.
//
// Reference: crates/trust-cg-verify/src/coverage_gate.rs   (the opcode-side gate)
//            crates/trust-cg-verify/src/mir_semantics.rs    (the refinement lane)
//            crates/rustc-codegen-trust-cg/src/lib.rs       (refine_push_*, drain)

//! Per-compile bridge refinement-coverage manifest (Phase P0).
//!
//! [`CoverageRecorder`] records every MIR shape a function's lowering emits,
//! classifies it ([`classify_rvalue`] / [`classify_terminator`] /
//! [`classify_projection`]), cross-references the refinement ledger, and renders a
//! per-function manifest. It is the build-time, MIR-shape-complete complement to
//! the per-instruction refinement lane, which only ever sees the scalar rvalues a
//! given function happens to contain.

use std::collections::BTreeMap;
use std::fmt::Write as _;

// ---------------------------------------------------------------------------
// Phase — which verification phase will (eventually) discharge a trusted shape
// ---------------------------------------------------------------------------

/// The verification phase that is expected to replace a `TrustedAllowlisted`
/// shape's trust with a real proof. Recorded so the trusted surface is not just
/// enumerated but ROADMAPPED — every trusted shape names who will prove it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Phase {
    /// P1 — memory & places: loads/stores, address-of, field/index/deref
    /// projections, discriminant tag reads.
    P1MemoryAndPlaces,
    /// P2 — per-instruction operand wiring: value identity of moves/copies,
    /// aggregate construction / scalarization, array repeat.
    P2OperandWiring,
    /// P3 — control flow & terminators: branches, switches, asserts, drops.
    P3ControlFlow,
    /// Covered by an EXISTING non-MIR-refinement proof family (per-instruction
    /// opcode proofs, frame/ABI proofs, call-lowering proofs, EH proofs, reloc
    /// proofs) rather than by a MIR->trust-ir refinement. Listed so the manifest
    /// does not imply a future MIR-refinement obligation where one is unwarranted.
    CoveredElsewhere,
}

impl std::fmt::Display for Phase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Phase::P1MemoryAndPlaces => "P1 (memory/places)",
            Phase::P2OperandWiring => "P2 (operand wiring)",
            Phase::P3ControlFlow => "P3 (control flow)",
            Phase::CoveredElsewhere => "covered-elsewhere",
        })
    }
}

// ---------------------------------------------------------------------------
// Shape classification — the load-bearing taxonomy
// ---------------------------------------------------------------------------

/// How a MIR shape relates to the bridge's MIR->trust-ir refinement requirement.
///
/// Every MIR rvalue / place-projection / terminator shape is mapped to exactly
/// one of these by an exhaustive (wildcard-free) `match`, so the classification
/// can never silently fall through for a newly added MIR shape.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShapeClass {
    /// The scalar-rvalue refinement lane (`refine_push_*` -> the `mir_to_trust_ir`
    /// drain) builds and discharges a per-OP-SELECTION obligation for this shape.
    ///
    /// IMPORTANT (honesty): this covers OP-SELECTION ONLY — *which* trust-ir
    /// op/cc/cast the bridge chose for a scalar rvalue — not operand wiring,
    /// memory, or control flow. Whether a given INSTANCE actually discharged
    /// `Refined` (vs the active lane abstaining at that width) is determined at
    /// render time from the refinement ledger, so a `RefinableScalarOpSelection`
    /// row is reported `REFINED` only when an obligation truly discharged.
    RefinableScalarOpSelection,

    /// Currently TRUSTED (no MIR->trust-ir refinement yet), but on the EXPLICIT,
    /// named allowlist with a reason and the phase that will prove it. This is the
    /// enumerated, reviewable trusted surface — never an implicit silence.
    TrustedAllowlisted {
        /// Why this shape is allowed to be lowered without a refinement today.
        reason: &'static str,
        /// The phase expected to discharge it (or `CoveredElsewhere`).
        phase: Phase,
    },

    /// Neither refined nor allowlisted: no coverage decision exists for this
    /// shape. Surfaced LOUDLY (a warning on every compile that emits it), and
    /// fails the compile CLOSED under `TCG_BRIDGE_COVERAGE_STRICT`.
    Unmodeled,
}

/// The three MIR dimensions a shape can come from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ShapeCategory {
    /// An `Rvalue` (the value side of an assignment).
    Rvalue,
    /// A `ProjectionElem` of a `Place` (the memory/place side).
    Place,
    /// A `TerminatorKind` (the control-flow side).
    Terminator,
}

impl std::fmt::Display for ShapeCategory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            ShapeCategory::Rvalue => "rvalue",
            ShapeCategory::Place => "place",
            ShapeCategory::Terminator => "terminator",
        })
    }
}

// ---------------------------------------------------------------------------
// Local mirror enums of the rustc MIR shape kinds (testable, no rustc dep)
// ---------------------------------------------------------------------------
//
// These mirror `rustc_middle::mir::{Rvalue, TerminatorKind, ProjectionElem}`
// variant-for-variant. They exist so (a) the classifier can be unit-tested
// WITHOUT a `TyCtxt` (constructing real `Rvalue`s needs a compiler context), and
// (b) the rustc<->mirror boundary lives in ONE wildcard-free adapter per kind (in
// the bridge), giving the same "new rustc variant fails to compile" guarantee the
// classifier match gives.

/// Mirror of `rustc_middle::mir::Rvalue`'s discriminant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RvalueKind {
    Use,
    Repeat,
    Ref,
    ThreadLocalRef,
    RawPtr,
    Cast,
    BinaryOp,
    UnaryOp,
    Discriminant,
    Aggregate,
    CopyForDeref,
    WrapUnsafeBinder,
}

impl RvalueKind {
    /// Stable display name (matches the rustc variant name).
    pub fn name(self) -> &'static str {
        match self {
            RvalueKind::Use => "Use",
            RvalueKind::Repeat => "Repeat",
            RvalueKind::Ref => "Ref",
            RvalueKind::ThreadLocalRef => "ThreadLocalRef",
            RvalueKind::RawPtr => "RawPtr",
            RvalueKind::Cast => "Cast",
            RvalueKind::BinaryOp => "BinaryOp",
            RvalueKind::UnaryOp => "UnaryOp",
            RvalueKind::Discriminant => "Discriminant",
            RvalueKind::Aggregate => "Aggregate",
            RvalueKind::CopyForDeref => "CopyForDeref",
            RvalueKind::WrapUnsafeBinder => "WrapUnsafeBinder",
        }
    }
}

/// Mirror of `rustc_middle::mir::TerminatorKind`'s discriminant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TerminatorShape {
    Goto,
    SwitchInt,
    UnwindResume,
    UnwindTerminate,
    Return,
    Unreachable,
    Drop,
    Call,
    TailCall,
    Assert,
    Yield,
    CoroutineDrop,
    FalseEdge,
    FalseUnwind,
    InlineAsm,
}

impl TerminatorShape {
    /// Stable display name (matches the rustc variant name).
    pub fn name(self) -> &'static str {
        match self {
            TerminatorShape::Goto => "Goto",
            TerminatorShape::SwitchInt => "SwitchInt",
            TerminatorShape::UnwindResume => "UnwindResume",
            TerminatorShape::UnwindTerminate => "UnwindTerminate",
            TerminatorShape::Return => "Return",
            TerminatorShape::Unreachable => "Unreachable",
            TerminatorShape::Drop => "Drop",
            TerminatorShape::Call => "Call",
            TerminatorShape::TailCall => "TailCall",
            TerminatorShape::Assert => "Assert",
            TerminatorShape::Yield => "Yield",
            TerminatorShape::CoroutineDrop => "CoroutineDrop",
            TerminatorShape::FalseEdge => "FalseEdge",
            TerminatorShape::FalseUnwind => "FalseUnwind",
            TerminatorShape::InlineAsm => "InlineAsm",
        }
    }
}

/// Mirror of `rustc_middle::mir::ProjectionElem`'s discriminant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProjectionKind {
    Deref,
    Field,
    Index,
    ConstantIndex,
    Subslice,
    Downcast,
    OpaqueCast,
    UnwrapUnsafeBinder,
}

impl ProjectionKind {
    /// Stable display name (matches the rustc variant name).
    pub fn name(self) -> &'static str {
        match self {
            ProjectionKind::Deref => "Deref",
            ProjectionKind::Field => "Field",
            ProjectionKind::Index => "Index",
            ProjectionKind::ConstantIndex => "ConstantIndex",
            ProjectionKind::Subslice => "Subslice",
            ProjectionKind::Downcast => "Downcast",
            ProjectionKind::OpaqueCast => "OpaqueCast",
            ProjectionKind::UnwrapUnsafeBinder => "UnwrapUnsafeBinder",
        }
    }
}

/// Which Phase P1 MEMORY-refinement lowering an obligation discharged. Recorded
/// per (place-anchor, kind) so the manifest can report — HONESTLY, only after a
/// real `check_memory_sequence` discharge — exactly which memory lowerings were
/// proven (a field LOAD, a field STORE, a whole-aggregate COPY), never claiming
/// `REFINED (memory)` on the mere presence of a trusted shape.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum MemRefineKind {
    /// `dst = o.b.x` — a fixed-offset scalar field LOAD.
    FieldLoad,
    /// `o.b.x = v` — a fixed-offset scalar field STORE (incl. sibling isolation).
    FieldStore,
    /// `dst = src` — a multi-lane whole-aggregate COPY.
    AggregateCopy,
    /// `(*r).field = v` / `*r = v` — a scalar STORE THROUGH A REFERENCE, at
    /// `r_ptr + layout_offset` (incl. sibling isolation off the SAME `r_ptr`). The
    /// distinguishing property from `FieldStore` is that the base is a RUNTIME
    /// pointer value bound to the reference `r`, not a stack-slot pointer.
    DerefStore,
    /// `let (a, b) = s.split_at(mid)` — the intercepted `<[T]>::split_at` /
    /// `str::split_at` lowering. A VALUE-level refinement (not a memory-op
    /// sequence): the reconstructed trap predicate + the two `{data,len}` halves
    /// are checked against `mir_semantics::split_at_spec` (trap iff `mid >u len`;
    /// `fst = {ptr, mid}`; `snd = {ptr + mid*elem_size, len - mid}`). Has no place
    /// projection, so it surfaces only in the dedicated `[memory refinements]`
    /// manifest section, exactly like `AggregateCopy`.
    SplitAt,
    /// `for c in v.chunks(n)` (and `windows`/`chunks_exact`/`rchunks`/
    /// `rchunks_exact`) — the intercepted slice STRIDE-ITERATOR constructor
    /// lowering. A VALUE-level refinement (not a memory-op sequence): the
    /// reconstructed trap predicate + the three `{ ptr, end, n }` cursor fields are
    /// checked against `mir_semantics::stride_iter_ctor_spec` (trap iff `n == 0`;
    /// `ptr == data`; `end == data + len*elem_size`; `n == n`). Like `SplitAt` it
    /// has no place projection, so it surfaces only in the dedicated
    /// `[memory refinements]` manifest section.
    StrideIterCtor,
    /// `v[i]` / `&v[i]` / `&mut v[i]` — the intercepted CHECKED slice/Vec index
    /// (`<Vec<T> as Index>::index` / `index_mut` and `<[T]>::index`; NOT the
    /// `unsafe` `get_unchecked*`, which is intentionally unchecked and never
    /// refined against a trap). A VALUE-level refinement (not a memory-op
    /// sequence): the reconstructed bounds "continue" predicate + the element
    /// address are checked against `mir_semantics::vec_index_spec` (trap iff
    /// `i >=u len`; `elem_addr == data + i*elem_size`) — the class of the real O0
    /// soundness bug (a `v[oob]` that silently read out of bounds instead of
    /// panicking). Like `SplitAt` it has no place projection, so it surfaces only
    /// in the dedicated `[memory refinements]` manifest section.
    VecIndex,
    /// `&v[a..b]` / `&v[a..]` / `&v[..b]` — the intercepted CHECKED Vec range
    /// subslice (`<Vec<T> as Index<Range|RangeFrom|RangeTo>>::index` / `index_mut`).
    /// A VALUE-level refinement (not a memory-op sequence): the reconstructed
    /// combined bounds "continue" predicate + the subslice `{ ptr, len }` are checked
    /// against `mir_semantics::vec_range_subslice_spec` (trap iff
    /// `NOT((start <=u end) AND (end <=u len))`; `ptr == data + start*elem_size`;
    /// `len == end - start`). Like `SplitAt` it has no place projection, so it
    /// surfaces only in the dedicated `[memory refinements]` manifest section.
    VecRangeSubslice,
    /// `<[T]>::first(&self)` / `last(&self)` -> `Option<&T>` — the intercepted
    /// niche-encoded Option slice accessor (`lower_slice_first_last_call`). A
    /// VALUE-level refinement over the SINGLE niche field the `Option<&T>` occupies:
    /// the reconstructed `Select`-chosen value written to the field is checked
    /// against `mir_semantics::slice_first_last_spec`
    /// (`niche == (len != 0) ? elem_ptr : 0`, with `elem_ptr = data` for `first` /
    /// `data + (len-1)*elem_size` for `last`). Like `SplitAt` it has no place
    /// projection, so it surfaces only in the dedicated `[memory refinements]`
    /// manifest section.
    SliceFirstLast,
    /// `<Range<T> as Iterator>::next(&mut self)` -> `Option<T>` — the intercepted
    /// branchless Range iterator step (`lower_range_next`). The FIRST
    /// STATE-TRANSITION refinement: a VALUE-level check over the three cells the
    /// lowering writes — the `self.start` write-back plus the `Option<T>` tag and
    /// payload — reconstructed from the emitted pre-state `Load`s / `ICmp` /
    /// `Select`s / `Store`s and checked against `mir_semantics::range_next_spec`
    /// (`new_start == ITE(start < end, start+1, start)`;
    /// `tag == ITE(start < end, some_discr, none_discr)`; `payload == start`, the
    /// PRE-state start). Like `SplitAt` it has no place projection, so it surfaces
    /// only in the dedicated `[memory refinements]` manifest section.
    RangeNext,
    /// `<[T]>::split_first(&self)` / `split_last(&self)` -> `Option<(&T, &[T])>` —
    /// the intercepted niche-encoded split accessor
    /// (`lower_slice_split_first_last`). A VALUE-level refinement over the THREE
    /// 8-byte cells the lowering writes — the `&T` head pointer (`f0`), the tail
    /// data pointer (`f1`), and the tail length (`f1+8`) — reconstructed from the
    /// emitted `ICmp`/`Sub`/address arithmetic/`Select`/`Store`s and checked
    /// against `mir_semantics::split_first_last_spec`. The LAYOUT-designated
    /// niche cell (never the emission) selects which pointer cell carries the
    /// `ITE(len != 0, ptr, 0)` discriminant formula. Like `SplitAt` it has no
    /// place projection, so it surfaces only in the dedicated
    /// `[memory refinements]` manifest section.
    SplitEnds,
    /// `<slice::Iter<T> as Iterator>::next(&mut self)` -> `Option<&T>` — the
    /// intercepted branchless slice-iterator step (`lower_slice_iter_next`, the
    /// `for x in slice` workhorse). A STATE-TRANSITION VALUE-level check over
    /// the two 8-byte cells the lowering writes — the `self.ptr` write-back
    /// plus the niche-encoded `Option<&T>` — reconstructed from the emitted
    /// pre-state `Load`s / `ICmp Ne` / `Select`s / `Store`s and checked against
    /// `mir_semantics::slice_iter_next_spec`
    /// (`new_ptr == ITE(ptr != end, ptr + elem_size, ptr)`;
    /// `niche == ITE(ptr != end, ptr, 0)` — the yielded reference is the
    /// PRE-advance `ptr`, `None` is the null niche). Like `SplitAt` it has no
    /// place projection, so it surfaces only in the dedicated
    /// `[memory refinements]` manifest section.
    SliceIterNext,
    /// `<StepBy<Range<i64>> as Iterator>::next(&mut self)` -> `Option<i64>` —
    /// the intercepted branchless StepBy step (`lower_step_by_next`, the
    /// SIGNED-Range std-layout path; the historical-P0 iterator adapter). A
    /// STATE-TRANSITION VALUE-level check over the FOUR cells the lowering
    /// writes — the `range.start` write-back, the 1-BYTE `first_take`
    /// write-back, and the `Option<i64>` tag and payload — reconstructed from
    /// the emitted pre-state `Load`s (incl. the WIDTH-FAITHFUL 1-byte
    /// `first_take` load, modeled as an explicitly masked 64-bit formula) /
    /// `ZExt`/`Trunc` masking casts / `ICmp`s / Bool `And` / `Select`s /
    /// `Store`s and checked against `mir_semantics::step_by_next_spec`
    /// (`countdown = ITE(ft != 0, 0, sm)`; `y = start + countdown`;
    /// `cond = (y >=s start) AND (y <s end)`;
    /// `new_start == ITE(cond, y+1, start)`;
    /// `new_ft == ITE(cond, 0, ft) & 0xff` — compared at the store's 1-byte
    /// width; `tag == ITE(cond, some, none)`; `payload == y`). Like `SplitAt`
    /// it has no place projection, so it surfaces only in the dedicated
    /// `[memory refinements]` manifest section.
    StepByNext,
    /// `<StepBy<Range<u64|usize>> as Iterator>::next(&mut self)` ->
    /// `Option<u64|usize>` — the intercepted branchless StepBy step
    /// (`lower_step_by_next`, the PACKED-UNSIGNED Range path: the step state is
    /// ONE I64 word `(k-1) << 32 | countdown`, NO `first_take` cell). A
    /// STATE-TRANSITION VALUE-level check over the FOUR cells the lowering
    /// writes — the `range.start` write-back, the packed-state write-back, and
    /// the `Option` tag and payload — reconstructed from the emitted pre-state
    /// `Load`s / the `And`/`LShr`/`Shl`/`Or` packed prelude / `ICmp`s / Bool
    /// `And` / `Select`s / `Store`s and checked against
    /// `mir_semantics::step_by_next_packed_spec`
    /// (`countdown = state & 0xFFFF_FFFF`; `reset = state >> 32`;
    /// `y = start + countdown`; `cond = (y >=u start) AND (y <u end)`;
    /// `new_start == ITE(cond, y+1, start)`;
    /// `new_state == ITE(cond, (reset<<32)|reset, state)`;
    /// `tag == ITE(cond, some, none)`; `payload == y`). Like `SplitAt` it has
    /// no place projection, so it surfaces only in the dedicated
    /// `[memory refinements]` manifest section.
    StepByNextPacked,
    /// `<StepBy<slice::Iter<T>> as Iterator>::next(&mut self)` -> `Option<&T>`
    /// — the intercepted branchless StepBy step (`lower_step_by_next`, the
    /// STD-LAYOUT SLICE-source path: a `{ptr, end}` cursor + the std
    /// `{step_minus_one, first_take}` cells; the dest is the niche-encoded
    /// `Option<&T>`). A STATE-TRANSITION VALUE-level check over the THREE
    /// cells the lowering writes — the `self.ptr` write-back, the 1-BYTE
    /// `first_take` write-back, and the single niche cell — reconstructed from
    /// the emitted pre-state `Load`s (incl. the WIDTH-FAITHFUL 1-byte
    /// `first_take` load) / `ZExt`/`Trunc` masking casts / the
    /// `emit_element_addr` stride arithmetic / `ICmp`s / Bool `And` /
    /// `Select`s / `Store`s and checked against
    /// `mir_semantics::step_by_next_slice_spec`
    /// (`countdown = ITE(ft != 0, 0, sm)`;
    /// `y_ptr = ptr + countdown*elem_size`;
    /// `cond = (y_ptr >=u ptr) AND (y_ptr <u end)`;
    /// `new_ptr == ITE(cond, y_ptr + elem_size, ptr)`;
    /// `new_ft == ITE(cond, 0, ft) & 0xff` — compared at the store's 1-byte
    /// width; `niche == ITE(cond, y_ptr, 0)`). Like `SplitAt` it has no place
    /// projection, so it surfaces only in the dedicated `[memory refinements]`
    /// manifest section.
    StepByNextSlice,
    /// `s.to_vec()` / `s.to_owned()` / `v.clone()` — the `{ptr, cap, len}` Vec
    /// HEADER the bridge builds before the copy loop runs. A VALUE-level
    /// refinement (no place projection, like `SplitAt`): the emitted capacity,
    /// requested byte count, recorded length, and requested alignment are
    /// checked against `mir_semantics::slice_to_vec_header_spec`
    /// (`cap == max(n,1)`; `alloc_bytes == cap*elem_size`; `len == n`;
    /// `len <=u cap`), with `elem_size`/`elem_align` RE-QUERIED from the layout
    /// oracle rather than read back out of the emitted constants.
    ///
    /// SCOPE — read this before trusting the manifest line. The lane certifies
    /// the ALLOCATION IDENTITY of the header only. It does not cover the
    /// fill/copy loop (that is `check_memory_sequence`'s territory), and it does
    /// NOT prove the returned buffer is fresh or non-aliasing: allocator
    /// freshness is a TRUSTED-MODEL BOUNDARY here, recorded the way lane 9
    /// records its cursor model. An earlier draft "proved" freshness with an
    /// assumption identical to the goal (`P ⊢ P`); that is why it is stated as a
    /// boundary instead.
    SliceToVecHeader,
}

impl MemRefineKind {
    /// Stable manifest label for this memory-refinement kind.
    pub fn label(self) -> &'static str {
        match self {
            MemRefineKind::FieldLoad => "field-LOAD",
            MemRefineKind::FieldStore => "field-STORE",
            MemRefineKind::AggregateCopy => "aggregate-COPY",
            MemRefineKind::DerefStore => "deref-STORE",
            MemRefineKind::SplitAt => "split-AT",
            MemRefineKind::StrideIterCtor => "stride-iter-CTOR",
            MemRefineKind::VecIndex => "vec-INDEX",
            MemRefineKind::VecRangeSubslice => "vec-SUBSLICE",
            MemRefineKind::SliceFirstLast => "slice-FIRST-LAST",
            MemRefineKind::RangeNext => "range-NEXT",
            MemRefineKind::SplitEnds => "split-ENDS",
            MemRefineKind::SliceIterNext => "slice-iter-NEXT",
            MemRefineKind::StepByNext => "stepby-NEXT",
            MemRefineKind::StepByNextPacked => "stepby-next-PACKED",
            MemRefineKind::StepByNextSlice => "stepby-next-SLICE",
            MemRefineKind::SliceToVecHeader => "to-vec-HEADER",
        }
    }
}

// ---------------------------------------------------------------------------
// The exhaustive classifiers (the load-bearing taxonomy + allowlist)
// ---------------------------------------------------------------------------
//
// WILDCARD-FREE on purpose. The allowlist IS these matches: a shape is
// `TrustedAllowlisted` only because a human wrote it down here with a reason and a
// phase. Adding a mirror variant (which a new rustc variant forces) will not
// compile until it is classified.

/// Classify an `Rvalue` shape. WILDCARD-FREE — see module note.
///
/// `BinaryOp` / `UnaryOp` / `Cast` are the SCALAR families the existing
/// `refine_push_*` lane covers (op-selection). Non-scalar instances of those
/// kinds (pointer-offset `BinaryOp`, ptr<->int `Cast`, …) push no obligation;
/// the manifest reflects that honestly from the ledger rather than claiming them.
pub fn classify_rvalue(kind: RvalueKind) -> ShapeClass {
    use ShapeClass::*;
    match kind {
        // The scalar op-selection refinement lane (refine_push_binop / _icmp /
        // _fcmp / _overflow / _unop / _int_cast / _int_to_float / _float_to_int).
        RvalueKind::BinaryOp | RvalueKind::UnaryOp | RvalueKind::Cast => RefinableScalarOpSelection,

        // Operand wiring: value identity of a move/copy of a place or constant.
        // No op is selected; the bound trust-ir value IS the source value.
        RvalueKind::Use => TrustedAllowlisted {
            reason: "operand wiring — move/copy of a value or place; no op selected, \
                     SSA value identity is trusted",
            phase: Phase::P2OperandWiring,
        },
        // Aggregate construction (tuple/array/adt/closure): field placement /
        // scalarization wiring — no scalar op selected.
        RvalueKind::Aggregate => TrustedAllowlisted {
            reason: "aggregate construction (tuple/array/adt/closure) — field placement / \
                     scalarization wiring",
            phase: Phase::P2OperandWiring,
        },
        // `[v; N]` array repeat: element wiring into a slot.
        RvalueKind::Repeat => TrustedAllowlisted {
            reason: "array repeat [v; N] — element wiring",
            phase: Phase::P2OperandWiring,
        },
        // `CopyForDeref`: a place copy feeding a deref — operand wiring.
        RvalueKind::CopyForDeref => TrustedAllowlisted {
            reason: "copy-for-deref (place copy feeding a deref) — operand wiring",
            phase: Phase::P2OperandWiring,
        },

        // `&place` / `&raw place`: produce a pointer to a place — the memory/place
        // address surface (the address arithmetic is what P1 will prove).
        RvalueKind::Ref => TrustedAllowlisted {
            reason: "address-of a place (&place) — produces a pointer; place address arithmetic",
            phase: Phase::P1MemoryAndPlaces,
        },
        RvalueKind::RawPtr => TrustedAllowlisted {
            reason: "raw address-of (&raw const/mut place) — pointer to a place",
            phase: Phase::P1MemoryAndPlaces,
        },
        // Enum discriminant read: a layout-derived tag load.
        RvalueKind::Discriminant => TrustedAllowlisted {
            reason: "enum discriminant read — layout-derived tag load",
            phase: Phase::P1MemoryAndPlaces,
        },

        // Thread-local address: a TLV descriptor access — its correctness is the
        // relocation/global proof family, not a MIR-level refinement.
        RvalueKind::ThreadLocalRef => TrustedAllowlisted {
            reason: "thread-local address — TLV descriptor access; covered by reloc/global proofs",
            phase: Phase::CoveredElsewhere,
        },

        // `WrapUnsafeBinder`: the bridge does not lower it (fails closed). No
        // coverage decision — keep it visible as Unmodeled rather than pretend.
        RvalueKind::WrapUnsafeBinder => Unmodeled,
    }
}

/// Classify a `TerminatorKind` shape. WILDCARD-FREE — see module note.
pub fn classify_terminator(kind: TerminatorShape) -> ShapeClass {
    use ShapeClass::*;
    match kind {
        TerminatorShape::Goto => TrustedAllowlisted {
            reason: "unconditional branch — CFG edge",
            phase: Phase::P3ControlFlow,
        },
        TerminatorShape::SwitchInt => TrustedAllowlisted {
            reason: "integer/bool switch — CFG edge selection on a discriminant",
            phase: Phase::P3ControlFlow,
        },
        TerminatorShape::Assert => TrustedAllowlisted {
            reason: "bounds/overflow/divzero assert — conditional trap edge",
            phase: Phase::P3ControlFlow,
        },
        TerminatorShape::Drop => TrustedAllowlisted {
            reason: "drop terminator — drop-glue branch",
            phase: Phase::P3ControlFlow,
        },
        TerminatorShape::Unreachable => TrustedAllowlisted {
            reason: "unreachable — hard trap; CFG terminator",
            phase: Phase::P3ControlFlow,
        },

        TerminatorShape::Return => TrustedAllowlisted {
            reason: "return edge — ABI return; covered by frame/call-lowering proofs",
            phase: Phase::CoveredElsewhere,
        },
        TerminatorShape::Call => TrustedAllowlisted {
            reason: "function call — argument/return ABI; covered by call-lowering proofs",
            phase: Phase::CoveredElsewhere,
        },
        TerminatorShape::UnwindResume => TrustedAllowlisted {
            reason: "unwind resume — exception re-raise; covered by EH proofs",
            phase: Phase::CoveredElsewhere,
        },
        TerminatorShape::UnwindTerminate => TrustedAllowlisted {
            reason: "unwind terminate — abort at a nounwind boundary; covered by EH proofs",
            phase: Phase::CoveredElsewhere,
        },

        // The bridge does not lower these (fails closed). No coverage decision —
        // keep them visible as Unmodeled.
        TerminatorShape::TailCall
        | TerminatorShape::Yield
        | TerminatorShape::CoroutineDrop
        | TerminatorShape::FalseEdge
        | TerminatorShape::FalseUnwind
        | TerminatorShape::InlineAsm => Unmodeled,
    }
}

/// Classify a place `ProjectionElem` shape. WILDCARD-FREE — see module note.
///
/// Every projection is part of an effective-address computation; the whole family
/// is the P1 memory/places surface (no MIR refinement yet). `OpaqueCast` /
/// `UnwrapUnsafeBinder` are pure type-changes with no runtime effect.
pub fn classify_projection(kind: ProjectionKind) -> ShapeClass {
    use ShapeClass::*;
    match kind {
        ProjectionKind::Deref => TrustedAllowlisted {
            reason: "deref projection (*p) — load/store address",
            phase: Phase::P1MemoryAndPlaces,
        },
        ProjectionKind::Field => TrustedAllowlisted {
            reason: "field projection (.f) — layout offset address",
            phase: Phase::P1MemoryAndPlaces,
        },
        ProjectionKind::Index => TrustedAllowlisted {
            reason: "dynamic index projection ([i]) — element address (base + i*stride)",
            phase: Phase::P1MemoryAndPlaces,
        },
        ProjectionKind::ConstantIndex => TrustedAllowlisted {
            reason: "constant index projection — element address at a fixed offset",
            phase: Phase::P1MemoryAndPlaces,
        },
        ProjectionKind::Subslice => TrustedAllowlisted {
            reason: "subslice projection — slice sub-range address + length",
            phase: Phase::P1MemoryAndPlaces,
        },
        ProjectionKind::Downcast => TrustedAllowlisted {
            reason: "enum-variant downcast projection — re-types a place to a variant payload",
            phase: Phase::P1MemoryAndPlaces,
        },
        ProjectionKind::OpaqueCast => TrustedAllowlisted {
            reason: "opaque-type cast projection — pure type change, no runtime effect",
            phase: Phase::CoveredElsewhere,
        },
        ProjectionKind::UnwrapUnsafeBinder => TrustedAllowlisted {
            reason: "unsafe-binder unwrap projection — pure type change, no runtime effect",
            phase: Phase::CoveredElsewhere,
        },
    }
}

// ---------------------------------------------------------------------------
// Refinement ledger — the reality check
// ---------------------------------------------------------------------------

/// The outcome of a refinement obligation the bridge pushed for a scalar rvalue.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RefineOutcome {
    /// Queued by a `refine_push_*` helper; the drain has not reported on it yet.
    /// (Left at this value if the function errored before the drain ran.)
    Pushed,
    /// The drain discharged it `Refined` — a genuine, verified op-selection proof.
    Refined,
    /// The drain SKIPPED it: the active lane could not decide it (out of the
    /// encodable slice, or > 8-bit with no solver so the fast lane abstains, or a
    /// solver-timeout `Inconclusive` in the default-solver lane). A SOUND skip,
    /// NOT a proof — reported honestly, never counted as `Refined`.
    Skipped,
}

/// Map a refinement job KEY (built by the bridge's `refine_push_*` helpers) back
/// to the originating rvalue kind, for display attribution in the manifest. The
/// key prefixes are stable and defined in the same repository
/// (`crates/rustc-codegen-trust-cg/src/lib.rs`). Display-only: no gate decision
/// depends on this mapping.
pub fn rvalue_kind_of_refine_key(key: &str) -> Option<RvalueKind> {
    let prefix = key.split(':').next().unwrap_or("");
    Some(match prefix {
        "binop" | "icmp" | "fcmp" | "overflow" => RvalueKind::BinaryOp,
        "unop" => RvalueKind::UnaryOp,
        "intcast" | "inttofloat" | "floattoint" => RvalueKind::Cast,
        _ => return None,
    })
}

// ---------------------------------------------------------------------------
// The per-function recorder
// ---------------------------------------------------------------------------

/// Aggregated record for one (category, shape-name) pair within a function.
#[derive(Debug, Clone)]
struct ShapeRecord {
    class: ShapeClass,
    count: usize,
}

/// Records the MIR shapes a single function's lowering emits, cross-references the
/// refinement ledger, and renders the per-function coverage manifest.
///
/// Created once per function (in `MirLoweringCtx::new`). The `record_*` methods
/// are invoked from the bridge's lowering dispatch; `note_refinement_*` from the
/// `refine_push_*` helpers and the `mir_to_trust_ir` drain; `finish` once at the
/// end of a successful lowering.
#[derive(Debug, Clone)]
pub struct CoverageRecorder {
    /// `TCG_BRIDGE_COVERAGE`: print the manifest at function end.
    manifest: bool,
    /// `TCG_BRIDGE_COVERAGE_STRICT`: fail the compile CLOSED on any `Unmodeled`
    /// shape (and still print the manifest).
    strict: bool,
    /// Observed shapes, keyed by (category, stable name).
    shapes: BTreeMap<(ShapeCategory, &'static str), ShapeRecord>,
    /// Refinement obligations pushed this function, keyed by job name, with their
    /// drain outcome. The ground truth behind a `REFINED` headline.
    ledger: BTreeMap<String, RefineOutcome>,
    /// Phase P1 MEMORY-refinement ground truth: per (PLACE-anchor name, kind),
    /// the number of fixed-offset memory obligations the `mir_to_trust_ir` drain
    /// discharged `Refined` through `check_memory_sequence`. An anchor is reported
    /// `REFINED (memory)` ONLY when its count is > 0 — never on the mere existence
    /// of the trusted shape (the same honesty discipline as the op-selection
    /// ledger). Distinct from `ledger`, which is op-selection only.
    mem_refined: BTreeMap<(&'static str, MemRefineKind), usize>,
}

impl CoverageRecorder {
    /// Construct a recorder with explicit flags (used by unit tests).
    pub fn new(manifest: bool, strict: bool) -> Self {
        Self {
            manifest,
            strict,
            shapes: BTreeMap::new(),
            ledger: BTreeMap::new(),
            mem_refined: BTreeMap::new(),
        }
    }

    /// Construct a recorder from the environment:
    /// `TCG_BRIDGE_COVERAGE` enables the per-function manifest; STRICT mode is
    /// `TCG_BRIDGE_COVERAGE_STRICT` (fail-closed on any `Unmodeled` shape).
    pub fn from_env() -> Self {
        Self::new(
            std::env::var_os("TCG_BRIDGE_COVERAGE").is_some(),
            std::env::var_os("TCG_BRIDGE_COVERAGE_STRICT").is_some(),
        )
    }

    /// Whether anything observable should happen for this recorder. When neither
    /// the manifest nor strict mode is on, recording is still cheap, but a caller
    /// can use this to skip incidental work.
    pub fn is_active(&self) -> bool {
        self.manifest || self.strict
    }

    /// True when STRICT mode is on.
    pub fn is_strict(&self) -> bool {
        self.strict
    }

    /// Core observe: record one occurrence of a shape, warn (always, deduped per
    /// shape) on `Unmodeled`, and — under STRICT — fail closed with a clear
    /// message naming the shape. In DEFAULT mode this NEVER returns `Err`, so the
    /// bridge's behavior is unchanged (the warning is additive stderr output).
    fn observe(
        &mut self,
        category: ShapeCategory,
        name: &'static str,
        class: ShapeClass,
    ) -> Result<(), String> {
        let entry = self
            .shapes
            .entry((category, name))
            .or_insert(ShapeRecord { class, count: 0 });
        let first_occurrence = entry.count == 0;
        entry.count += 1;

        if matches!(class, ShapeClass::Unmodeled) {
            if self.strict {
                return Err(format!(
                    "trust-cg bridge coverage [STRICT]: UNMODELED MIR {category} shape `{name}` \
                     — it has NO MIR->trust-ir refinement and is NOT on the trusted allowlist, so \
                     it would be lowered without any formal coverage decision. Fail-closed under \
                     TCG_BRIDGE_COVERAGE_STRICT. Resolve it in \
                     crates/trust-cg-verify/src/bridge_coverage.rs: either refine it, or add it to \
                     the trusted allowlist with a reason + phase."
                ));
            }
            if first_occurrence {
                eprintln!(
                    "warning: trust-cg bridge coverage: UNMODELED MIR {category} shape `{name}` \
                     has no MIR->trust-ir refinement and is not on the trusted allowlist — it may \
                     be lowered without any formal coverage decision. Classify it in \
                     crates/trust-cg-verify/src/bridge_coverage.rs (refine it, or allowlist it \
                     with a reason + phase). Set TCG_BRIDGE_COVERAGE_STRICT=1 to fail closed."
                );
            }
        }
        Ok(())
    }

    /// Record one emitted rvalue shape.
    pub fn record_rvalue(&mut self, kind: RvalueKind) -> Result<(), String> {
        self.observe(ShapeCategory::Rvalue, kind.name(), classify_rvalue(kind))
    }

    /// Record one emitted terminator shape.
    pub fn record_terminator(&mut self, kind: TerminatorShape) -> Result<(), String> {
        self.observe(
            ShapeCategory::Terminator,
            kind.name(),
            classify_terminator(kind),
        )
    }

    /// Record one emitted place-projection shape.
    pub fn record_projection(&mut self, kind: ProjectionKind) -> Result<(), String> {
        self.observe(ShapeCategory::Place, kind.name(), classify_projection(kind))
    }

    /// Note that a refinement obligation `key` was PUSHED by a `refine_push_*`
    /// helper. Idempotent (deduped by key, matching the bridge's `refine_seen`).
    pub fn note_refinement_pushed(&mut self, key: &str) {
        self.ledger
            .entry(key.to_string())
            .or_insert(RefineOutcome::Pushed);
    }

    /// Note the drain's OUTCOME for a refinement obligation `key`. Called from the
    /// `mir_to_trust_ir` drain with `Refined` or `Skipped`. (A `Refuted` verdict
    /// fails the compile before this is reached, so it never appears here.)
    pub fn note_refinement_outcome(&mut self, key: &str, outcome: RefineOutcome) {
        self.ledger.insert(key.to_string(), outcome);
    }

    /// Note that a Phase P1 MEMORY refinement obligation of `kind` for the place
    /// anchor `place_name` (e.g. `"Field"`) discharged `Refined` through
    /// `check_memory_sequence`. Called from the `mir_to_trust_ir` drain ONLY on a
    /// genuine `Refined` verdict, so the manifest's `REFINED (memory)` headline is
    /// backed by a real discharge — never by the mere presence of the shape.
    pub fn note_memory_refined(&mut self, place_name: &'static str, kind: MemRefineKind) {
        *self.mem_refined.entry((place_name, kind)).or_insert(0) += 1;
    }

    /// Total Phase P1 MEMORY obligations discharged `Refined` for the place anchor
    /// `name` this function (summed across kinds; 0 if none).
    fn memory_refined_count(&self, name: &str) -> usize {
        self.mem_refined
            .iter()
            .filter(|((k, _), _)| *k == name)
            .map(|(_, n)| *n)
            .sum()
    }

    /// Per-kind breakdown label for the place anchor `name`, e.g.
    /// `"2 field-LOAD, 1 field-STORE"` — the GROUND TRUTH behind a
    /// `REFINED (memory)` headline (empty when nothing discharged for `name`).
    fn memory_refined_labels(&self, name: &str) -> String {
        self.mem_refined
            .iter()
            .filter(|((k, _), n)| *k == name && **n > 0)
            .map(|((_, kind), n)| format!("{n} {}", kind.label()))
            .collect::<Vec<_>>()
            .join(", ")
    }

    /// Aggregate ledger stats (refined, skipped, total pushed) for the obligations
    /// attributed to a given rvalue shape name.
    fn refine_stats_for(&self, rvalue_name: &str) -> (usize, usize, usize) {
        let mut refined = 0;
        let mut skipped = 0;
        let mut total = 0;
        for (key, outcome) in &self.ledger {
            let Some(kind) = rvalue_kind_of_refine_key(key) else {
                continue;
            };
            if kind.name() != rvalue_name {
                continue;
            }
            total += 1;
            match outcome {
                RefineOutcome::Refined => refined += 1,
                RefineOutcome::Skipped | RefineOutcome::Pushed => skipped += 1,
            }
        }
        (refined, skipped, total)
    }

    /// The headline status string for one shape row (reflecting REALITY for
    /// refinable rows: `REFINED` only when an obligation truly discharged).
    fn status_for(&self, category: ShapeCategory, name: &str, class: ShapeClass) -> String {
        // Phase P1: a PLACE shape with one or more discharged MEMORY obligations
        // is reported `REFINED (memory)` with a per-kind breakdown (the rest of
        // that shape's instances remain trusted — the proof covers the
        // fixed-offset scalar field LOAD/STORE lowerings only). Backed by
        // `note_memory_refined`, so it is never claimed without a real discharge.
        if category == ShapeCategory::Place {
            let mem_refined = self.memory_refined_count(name);
            if mem_refined > 0 {
                let trusted_note = match class {
                    ShapeClass::TrustedAllowlisted { phase, .. } => {
                        format!("other {name} projections still TRUSTED [{phase}]")
                    }
                    _ => format!("other {name} projections still trusted"),
                };
                return format!(
                    "REFINED (memory) {} fixed-offset obligation(s) discharged Refined \
                     via check_memory_sequence; {trusted_note}",
                    self.memory_refined_labels(name)
                );
            }
        }
        match class {
            ShapeClass::RefinableScalarOpSelection => {
                // Refinable rows live only in the rvalue category, and only the
                // ledger can say whether any instance actually discharged.
                let (refined, skipped, total) = if category == ShapeCategory::Rvalue {
                    self.refine_stats_for(name)
                } else {
                    (0, 0, 0)
                };
                if refined > 0 {
                    format!(
                        "REFINED   op-selection only: {refined} obligation(s) discharged Refined, \
                         {skipped} skipped, of {total} pushed"
                    )
                } else if total > 0 {
                    format!(
                        "TRUSTED   op-selection obligations pushed ({total}) but the active lane \
                         ABSTAINED on all (e.g. > 8-bit width with no solver) — attempted, not proven"
                    )
                } else {
                    "TRUSTED   no scalar op-selection obligation fired for these instances \
                     (non-scalar/pointer operands, unsupported width/shape, or refinement lanes off) \
                     — operand wiring [P2/P1]"
                        .to_string()
                }
            }
            ShapeClass::TrustedAllowlisted { reason, phase } => {
                format!("TRUSTED   [{phase}] {reason}")
            }
            ShapeClass::Unmodeled => {
                "UNMODELED no refinement and not allowlisted — LOUD; fail-closed under STRICT"
                    .to_string()
            }
        }
    }

    /// Number of distinct shapes classified `Unmodeled`.
    pub fn unmodeled_count(&self) -> usize {
        self.shapes
            .values()
            .filter(|r| matches!(r.class, ShapeClass::Unmodeled))
            .count()
    }

    /// Render the per-function manifest (every observed shape + the refinement
    /// ledger). Public so tests and the bridge can format it identically.
    pub fn manifest(&self, symbol: &str) -> String {
        let mut out = String::new();
        let total_shapes: usize = self.shapes.values().map(|r| r.count).sum();
        let distinct = self.shapes.len();
        let _ = writeln!(
            out,
            "=== trust-cg bridge refinement-coverage manifest: {symbol} ===",
        );
        let _ = writeln!(
            out,
            "  {distinct} distinct MIR shapes ({total_shapes} occurrences); \
             {} pushed refinement obligation(s); {} unmodeled shape(s)",
            self.ledger.len(),
            self.unmodeled_count(),
        );
        let _ = writeln!(
            out,
            "  NOTE: \"REFINED\" means the SCALAR OP-SELECTION lane discharged an obligation \
             (which trust-ir op was chosen) — NOT operand wiring, memory, or control flow."
        );

        let mut last_category: Option<ShapeCategory> = None;
        for ((category, name), record) in &self.shapes {
            if last_category != Some(*category) {
                let _ = writeln!(out, "  [{category}]");
                last_category = Some(*category);
            }
            let status = self.status_for(*category, name, record.class);
            let _ = writeln!(out, "    {:<18} x{:<4} {}", name, record.count, status);
        }

        if !self.ledger.is_empty() {
            let _ = writeln!(
                out,
                "  [refinement ledger] (op-selection obligations, ground truth)"
            );
            for (key, outcome) in &self.ledger {
                let tag = match outcome {
                    RefineOutcome::Refined => "REFINED ",
                    RefineOutcome::Skipped => "skipped ",
                    RefineOutcome::Pushed => "pushed  ",
                };
                let _ = writeln!(out, "    [{tag}] {key}");
            }
        }
        // Phase P1 MEMORY refinements (ground truth, INCLUDING anchors with no
        // place row — e.g. the whole-aggregate COPY). Each line is backed by a
        // real `check_memory_sequence` discharge (`note_memory_refined`), never
        // by the mere presence of a shape.
        if !self.mem_refined.is_empty() {
            let _ = writeln!(
                out,
                "  [memory refinements] (check_memory_sequence discharges, ground truth)"
            );
            for ((anchor, kind), n) in &self.mem_refined {
                let _ = writeln!(
                    out,
                    "    [REFINED ] {} x{n} @ {anchor} (REFINED memory via check_memory_sequence)",
                    kind.label()
                );
            }
        }
        out
    }

    /// Finish recording for a function: print the manifest (if enabled). Called at
    /// the end of a SUCCESSFUL lowering. STRICT-mode fail-closing happens eagerly
    /// in `observe` (so it fires even if a later lowering step errors), so this is
    /// infallible — it only emits output.
    pub fn finish(&self, symbol: &str) {
        if self.manifest || self.strict {
            eprint!("{}", self.manifest(symbol));
        }
    }
}

impl Default for CoverageRecorder {
    fn default() -> Self {
        Self::from_env()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- A known scalar rvalue -> RefinableScalarOpSelection -----------------

    #[test]
    fn scalar_binop_unop_cast_are_refinable() {
        assert_eq!(
            classify_rvalue(RvalueKind::BinaryOp),
            ShapeClass::RefinableScalarOpSelection
        );
        assert_eq!(
            classify_rvalue(RvalueKind::UnaryOp),
            ShapeClass::RefinableScalarOpSelection
        );
        assert_eq!(
            classify_rvalue(RvalueKind::Cast),
            ShapeClass::RefinableScalarOpSelection
        );
    }

    // -- A memory projection -> Trusted with the P1 reason -------------------

    #[test]
    fn memory_projections_are_trusted_p1() {
        for k in [
            ProjectionKind::Deref,
            ProjectionKind::Field,
            ProjectionKind::Index,
            ProjectionKind::ConstantIndex,
            ProjectionKind::Subslice,
            ProjectionKind::Downcast,
        ] {
            match classify_projection(k) {
                ShapeClass::TrustedAllowlisted { phase, reason } => {
                    assert_eq!(phase, Phase::P1MemoryAndPlaces, "{k:?} should be P1");
                    assert!(!reason.is_empty(), "{k:?} must carry a reason");
                }
                other => panic!("{k:?} should be Trusted-allowlisted P1, got {other:?}"),
            }
        }
    }

    #[test]
    fn rvalue_memory_and_wiring_are_trusted_with_named_reasons() {
        // The enumerated trusted surface: each names a reason + phase.
        let cases = [
            (RvalueKind::Use, Phase::P2OperandWiring),
            (RvalueKind::Aggregate, Phase::P2OperandWiring),
            (RvalueKind::Repeat, Phase::P2OperandWiring),
            (RvalueKind::CopyForDeref, Phase::P2OperandWiring),
            (RvalueKind::Ref, Phase::P1MemoryAndPlaces),
            (RvalueKind::RawPtr, Phase::P1MemoryAndPlaces),
            (RvalueKind::Discriminant, Phase::P1MemoryAndPlaces),
            (RvalueKind::ThreadLocalRef, Phase::CoveredElsewhere),
        ];
        for (k, expected_phase) in cases {
            match classify_rvalue(k) {
                ShapeClass::TrustedAllowlisted { phase, reason } => {
                    assert_eq!(phase, expected_phase, "{k:?} phase");
                    assert!(!reason.is_empty());
                }
                other => panic!("{k:?} should be Trusted-allowlisted, got {other:?}"),
            }
        }
    }

    #[test]
    fn terminators_are_trusted_or_unmodeled() {
        // Lowered control flow is trusted (named); the rest is honestly Unmodeled.
        for k in [
            TerminatorShape::Goto,
            TerminatorShape::SwitchInt,
            TerminatorShape::Assert,
            TerminatorShape::Drop,
            TerminatorShape::Unreachable,
            TerminatorShape::Return,
            TerminatorShape::Call,
            TerminatorShape::UnwindResume,
            TerminatorShape::UnwindTerminate,
        ] {
            assert!(
                matches!(
                    classify_terminator(k),
                    ShapeClass::TrustedAllowlisted { .. }
                ),
                "{k:?} should be Trusted-allowlisted"
            );
        }
        for k in [
            TerminatorShape::TailCall,
            TerminatorShape::Yield,
            TerminatorShape::CoroutineDrop,
            TerminatorShape::FalseEdge,
            TerminatorShape::FalseUnwind,
            TerminatorShape::InlineAsm,
        ] {
            assert_eq!(
                classify_terminator(k),
                ShapeClass::Unmodeled,
                "{k:?} should be Unmodeled"
            );
        }
    }

    // -- A hypothetical NEW shape -> Unmodeled / forces classification -------

    #[test]
    fn unmodeled_rvalue_and_terminator_exist_and_are_loud() {
        // `WrapUnsafeBinder` stands in for "a shape with no coverage decision".
        assert_eq!(
            classify_rvalue(RvalueKind::WrapUnsafeBinder),
            ShapeClass::Unmodeled
        );
        assert_eq!(
            classify_terminator(TerminatorShape::InlineAsm),
            ShapeClass::Unmodeled
        );
    }

    // -- The recorder: Refined only when an obligation truly discharged ------

    #[test]
    fn refined_status_requires_a_discharged_obligation() {
        // A BinaryOp observed, with a pushed obligation that discharged Refined.
        let mut rec = CoverageRecorder::new(true, false);
        rec.record_rvalue(RvalueKind::BinaryOp).unwrap();
        rec.note_refinement_pushed("binop:Add:Add:U8");
        rec.note_refinement_outcome("binop:Add:Add:U8", RefineOutcome::Refined);
        let m = rec.manifest("test::refined");
        assert!(m.contains("BinaryOp"));
        assert!(m.contains("REFINED"), "manifest:\n{m}");

        // A BinaryOp whose only obligation was SKIPPED must NOT read REFINED.
        let mut rec = CoverageRecorder::new(true, false);
        rec.record_rvalue(RvalueKind::BinaryOp).unwrap();
        rec.note_refinement_pushed("binop:Add:Add:I64");
        rec.note_refinement_outcome("binop:Add:Add:I64", RefineOutcome::Skipped);
        let m = rec.manifest("test::skipped");
        let binop_line = m
            .lines()
            .find(|l| l.contains("BinaryOp"))
            .expect("BinaryOp row present");
        assert!(
            !binop_line.contains("REFINED"),
            "a skipped-only BinaryOp must not claim REFINED: {binop_line}"
        );
        assert!(binop_line.contains("TRUSTED"), "{binop_line}");
    }

    #[test]
    fn field_place_reads_refined_memory_only_after_a_discharge() {
        // A Field projection observed, but NO memory obligation discharged yet:
        // the row must still read TRUSTED [P1], never REFINED.
        let mut rec = CoverageRecorder::new(true, false);
        rec.record_projection(ProjectionKind::Field).unwrap();
        let m = rec.manifest("test::field_trusted");
        let field_line = m
            .lines()
            .find(|l| l.trim_start().starts_with("Field"))
            .expect("Field row present");
        assert!(
            field_line.contains("TRUSTED") && !field_line.contains("REFINED"),
            "without a discharge the Field place must read TRUSTED, not REFINED: {field_line}"
        );

        // After a genuine Phase P1 memory field-LOAD discharge, the Field row
        // reads REFINED (memory) — backed by the discharge, not the shape.
        let mut rec = CoverageRecorder::new(true, false);
        rec.record_projection(ProjectionKind::Field).unwrap();
        rec.note_memory_refined(ProjectionKind::Field.name(), MemRefineKind::FieldLoad);
        let m = rec.manifest("test::field_refined");
        let field_line = m
            .lines()
            .find(|l| l.trim_start().starts_with("Field"))
            .expect("Field row present");
        assert!(
            field_line.contains("REFINED (memory)") && field_line.contains("field-LOAD"),
            "a discharged field-load must read REFINED (memory) field-LOAD: {field_line}"
        );
        assert!(
            field_line.contains("check_memory_sequence"),
            "the REFINED (memory) row should name its discharge path: {field_line}"
        );
    }

    #[test]
    fn field_store_and_copy_read_refined_memory_only_after_a_discharge() {
        // A Field projection observed but NO store discharge: TRUSTED, not REFINED.
        let mut rec = CoverageRecorder::new(true, false);
        rec.record_projection(ProjectionKind::Field).unwrap();
        let m = rec.manifest("test::store_trusted");
        let field_line = m
            .lines()
            .find(|l| l.trim_start().starts_with("Field"))
            .expect("Field row present");
        assert!(
            !field_line.contains("field-STORE"),
            "without a discharge the Field place must not claim field-STORE: {field_line}"
        );

        // A genuine field-STORE discharge: the Field row reports field-STORE.
        let mut rec = CoverageRecorder::new(true, false);
        rec.record_projection(ProjectionKind::Field).unwrap();
        rec.note_memory_refined(ProjectionKind::Field.name(), MemRefineKind::FieldStore);
        let m = rec.manifest("test::store_refined");
        let field_line = m
            .lines()
            .find(|l| l.trim_start().starts_with("Field"))
            .expect("Field row present");
        assert!(
            field_line.contains("REFINED (memory)") && field_line.contains("field-STORE"),
            "a discharged field-store must read REFINED (memory) field-STORE: {field_line}"
        );

        // A whole-aggregate COPY has no place row; it surfaces ONLY in the
        // dedicated [memory refinements] section, and ONLY after a discharge.
        let rec = CoverageRecorder::new(true, false);
        let m = rec.manifest("test::no_copy");
        assert!(
            !m.contains("aggregate-COPY"),
            "without a discharge no aggregate-COPY may appear: {m}"
        );
        let mut rec = CoverageRecorder::new(true, false);
        rec.note_memory_refined("<whole-aggregate>", MemRefineKind::AggregateCopy);
        let m = rec.manifest("test::copy_refined");
        assert!(
            m.contains("[memory refinements]") && m.contains("aggregate-COPY"),
            "a discharged copy must surface in the memory-refinements section: {m}"
        );
        assert!(
            m.contains("check_memory_sequence"),
            "the copy memory line should name its discharge path: {m}"
        );

        // A genuine `(*r).field = v` deref-STORE discharge surfaces in the
        // memory-refinements section under the Deref anchor, only after a real
        // discharge — never on the mere presence of a Deref place.
        let rec = CoverageRecorder::new(true, false);
        let m = rec.manifest("test::no_deref_store");
        assert!(
            !m.contains("deref-STORE"),
            "without a discharge no deref-STORE may appear: {m}"
        );
        let mut rec = CoverageRecorder::new(true, false);
        rec.note_memory_refined(ProjectionKind::Deref.name(), MemRefineKind::DerefStore);
        let m = rec.manifest("test::deref_store_refined");
        assert!(
            m.contains("[memory refinements]") && m.contains("deref-STORE") && m.contains("Deref"),
            "a discharged deref store must surface as deref-STORE @ Deref: {m}"
        );
        assert!(
            m.contains("check_memory_sequence"),
            "the deref-store memory line should name its discharge path: {m}"
        );
    }

    #[test]
    fn split_at_surfaces_in_memory_refinements_only_after_a_discharge() {
        // Like the whole-aggregate COPY, `split_at` has no place row: it must NOT
        // appear until a real discharge notes it.
        let rec = CoverageRecorder::new(true, false);
        let m = rec.manifest("test::no_split_at");
        assert!(
            !m.contains("split-AT"),
            "without a discharge no split-AT may appear: {m}"
        );
        let mut rec = CoverageRecorder::new(true, false);
        rec.note_memory_refined("<slice::split_at>", MemRefineKind::SplitAt);
        let m = rec.manifest("test::split_at_refined");
        assert!(
            m.contains("[memory refinements]")
                && m.contains("split-AT")
                && m.contains("slice::split_at"),
            "a discharged split_at must surface as split-AT @ the split anchor: {m}"
        );
        assert_eq!(MemRefineKind::SplitAt.label(), "split-AT");
    }

    #[test]
    fn stride_iter_ctor_surfaces_in_memory_refinements_only_after_a_discharge() {
        // Like `split_at`, the stride-iterator constructor has no place row: it must
        // NOT appear until a real discharge notes it.
        let rec = CoverageRecorder::new(true, false);
        let m = rec.manifest("test::no_stride_iter");
        assert!(
            !m.contains("stride-iter-CTOR"),
            "without a discharge no stride-iter-CTOR may appear: {m}"
        );
        let mut rec = CoverageRecorder::new(true, false);
        rec.note_memory_refined("<slice::stride_iter_ctor>", MemRefineKind::StrideIterCtor);
        let m = rec.manifest("test::stride_iter_refined");
        assert!(
            m.contains("[memory refinements]")
                && m.contains("stride-iter-CTOR")
                && m.contains("slice::stride_iter_ctor"),
            "a discharged stride-iter ctor must surface as stride-iter-CTOR @ the ctor anchor: {m}"
        );
        assert_eq!(MemRefineKind::StrideIterCtor.label(), "stride-iter-CTOR");
    }

    #[test]
    fn vec_index_surfaces_in_memory_refinements_only_after_a_discharge() {
        // Like `split_at`, the checked index has no place row: it must NOT appear
        // until a real discharge notes it.
        let rec = CoverageRecorder::new(true, false);
        let m = rec.manifest("test::no_vec_index");
        assert!(
            !m.contains("vec-INDEX"),
            "without a discharge no vec-INDEX may appear: {m}"
        );
        let mut rec = CoverageRecorder::new(true, false);
        rec.note_memory_refined("<slice::index>", MemRefineKind::VecIndex);
        let m = rec.manifest("test::vec_index_refined");
        assert!(
            m.contains("[memory refinements]")
                && m.contains("vec-INDEX")
                && m.contains("slice::index"),
            "a discharged checked index must surface as vec-INDEX @ the index anchor: {m}"
        );
        assert_eq!(MemRefineKind::VecIndex.label(), "vec-INDEX");
    }

    #[test]
    fn vec_range_subslice_surfaces_in_memory_refinements_only_after_a_discharge() {
        // Like `split_at`, the checked range subslice has no place row: it must NOT
        // appear until a real discharge notes it.
        let rec = CoverageRecorder::new(true, false);
        let m = rec.manifest("test::no_vec_subslice");
        assert!(
            !m.contains("vec-SUBSLICE"),
            "without a discharge no vec-SUBSLICE may appear: {m}"
        );
        let mut rec = CoverageRecorder::new(true, false);
        rec.note_memory_refined("<slice::index>", MemRefineKind::VecRangeSubslice);
        let m = rec.manifest("test::vec_subslice_refined");
        assert!(
            m.contains("[memory refinements]")
                && m.contains("vec-SUBSLICE")
                && m.contains("slice::index"),
            "a discharged range subslice must surface as vec-SUBSLICE @ the index anchor: {m}"
        );
        assert_eq!(MemRefineKind::VecRangeSubslice.label(), "vec-SUBSLICE");
    }

    #[test]
    fn slice_first_last_surfaces_in_memory_refinements_only_after_a_discharge() {
        // Like `split_at`, the niche `Option<&T>` first/last accessor has no place
        // row: it must NOT appear until a real discharge notes it.
        let rec = CoverageRecorder::new(true, false);
        let m = rec.manifest("test::no_slice_first_last");
        assert!(
            !m.contains("slice-FIRST-LAST"),
            "without a discharge no slice-FIRST-LAST may appear: {m}"
        );
        let mut rec = CoverageRecorder::new(true, false);
        rec.note_memory_refined("<slice::first_last>", MemRefineKind::SliceFirstLast);
        let m = rec.manifest("test::slice_first_last_refined");
        assert!(
            m.contains("[memory refinements]")
                && m.contains("slice-FIRST-LAST")
                && m.contains("slice::first_last"),
            "a discharged first/last must surface as slice-FIRST-LAST @ the anchor: {m}"
        );
        assert_eq!(MemRefineKind::SliceFirstLast.label(), "slice-FIRST-LAST");
    }

    #[test]
    fn range_next_surfaces_in_memory_refinements_only_after_a_discharge() {
        // Like `split_at`, the Range::next state transition has no place row: it
        // must NOT appear until a real discharge notes it.
        let rec = CoverageRecorder::new(true, false);
        let m = rec.manifest("test::no_range_next");
        assert!(
            !m.contains("range-NEXT"),
            "without a discharge no range-NEXT may appear: {m}"
        );
        let mut rec = CoverageRecorder::new(true, false);
        rec.note_memory_refined("<range::next>", MemRefineKind::RangeNext);
        let m = rec.manifest("test::range_next_refined");
        assert!(
            m.contains("[memory refinements]")
                && m.contains("range-NEXT")
                && m.contains("range::next"),
            "a discharged Range::next must surface as range-NEXT @ the anchor: {m}"
        );
        assert_eq!(MemRefineKind::RangeNext.label(), "range-NEXT");
    }

    #[test]
    fn split_ends_surfaces_in_memory_refinements_only_after_a_discharge() {
        // Like `split_at`, the split_first/split_last accessor has no place row:
        // it must NOT appear until a real discharge notes it.
        let rec = CoverageRecorder::new(true, false);
        let m = rec.manifest("test::no_split_ends");
        assert!(
            !m.contains("split-ENDS"),
            "without a discharge no split-ENDS may appear: {m}"
        );
        let mut rec = CoverageRecorder::new(true, false);
        rec.note_memory_refined("<slice::split_ends>", MemRefineKind::SplitEnds);
        let m = rec.manifest("test::split_ends_refined");
        assert!(
            m.contains("[memory refinements]")
                && m.contains("split-ENDS")
                && m.contains("slice::split_ends"),
            "a discharged split_first/split_last must surface as split-ENDS @ the anchor: {m}"
        );
        assert_eq!(MemRefineKind::SplitEnds.label(), "split-ENDS");
    }

    #[test]
    fn slice_iter_next_surfaces_in_memory_refinements_only_after_a_discharge() {
        // Like `split_at`, the slice Iter::next state transition has no place
        // row: it must NOT appear until a real discharge notes it.
        let rec = CoverageRecorder::new(true, false);
        let m = rec.manifest("test::no_slice_iter_next");
        assert!(
            !m.contains("slice-iter-NEXT"),
            "without a discharge no slice-iter-NEXT may appear: {m}"
        );
        let mut rec = CoverageRecorder::new(true, false);
        rec.note_memory_refined("<slice::iter_next>", MemRefineKind::SliceIterNext);
        let m = rec.manifest("test::slice_iter_next_refined");
        assert!(
            m.contains("[memory refinements]")
                && m.contains("slice-iter-NEXT")
                && m.contains("slice::iter_next"),
            "a discharged slice Iter::next must surface as slice-iter-NEXT @ the anchor: {m}"
        );
        assert_eq!(MemRefineKind::SliceIterNext.label(), "slice-iter-NEXT");
    }

    #[test]
    fn step_by_next_surfaces_in_memory_refinements_only_after_a_discharge() {
        // Like `split_at`, the StepBy::next state transition has no place row:
        // it must NOT appear until a real discharge notes it.
        let rec = CoverageRecorder::new(true, false);
        let m = rec.manifest("test::no_step_by_next");
        assert!(
            !m.contains("stepby-NEXT"),
            "without a discharge no stepby-NEXT may appear: {m}"
        );
        let mut rec = CoverageRecorder::new(true, false);
        rec.note_memory_refined("<stepby::next>", MemRefineKind::StepByNext);
        let m = rec.manifest("test::step_by_next_refined");
        assert!(
            m.contains("[memory refinements]")
                && m.contains("stepby-NEXT")
                && m.contains("stepby::next"),
            "a discharged StepBy::next must surface as stepby-NEXT @ the anchor: {m}"
        );
        assert_eq!(MemRefineKind::StepByNext.label(), "stepby-NEXT");
    }

    #[test]
    fn step_by_next_packed_surfaces_in_memory_refinements_only_after_a_discharge() {
        // Like `split_at`, the packed-unsigned StepBy::next state transition
        // has no place row: it must NOT appear until a real discharge notes it.
        let rec = CoverageRecorder::new(true, false);
        let m = rec.manifest("test::no_step_by_next_packed");
        assert!(
            !m.contains("stepby-next-PACKED"),
            "without a discharge no stepby-next-PACKED may appear: {m}"
        );
        let mut rec = CoverageRecorder::new(true, false);
        rec.note_memory_refined("<stepby::next_packed>", MemRefineKind::StepByNextPacked);
        let m = rec.manifest("test::step_by_next_packed_refined");
        assert!(
            m.contains("[memory refinements]")
                && m.contains("stepby-next-PACKED")
                && m.contains("stepby::next_packed"),
            "a discharged packed StepBy::next must surface as stepby-next-PACKED @ the anchor: {m}"
        );
        assert_eq!(
            MemRefineKind::StepByNextPacked.label(),
            "stepby-next-PACKED"
        );
    }

    #[test]
    fn step_by_next_slice_surfaces_in_memory_refinements_only_after_a_discharge() {
        // Like `split_at`, the slice-source StepBy::next state transition has
        // no place row: it must NOT appear until a real discharge notes it.
        let rec = CoverageRecorder::new(true, false);
        let m = rec.manifest("test::no_step_by_next_slice");
        assert!(
            !m.contains("stepby-next-SLICE"),
            "without a discharge no stepby-next-SLICE may appear: {m}"
        );
        let mut rec = CoverageRecorder::new(true, false);
        rec.note_memory_refined("<stepby::next_slice>", MemRefineKind::StepByNextSlice);
        let m = rec.manifest("test::step_by_next_slice_refined");
        assert!(
            m.contains("[memory refinements]")
                && m.contains("stepby-next-SLICE")
                && m.contains("stepby::next_slice"),
            "a discharged slice StepBy::next must surface as stepby-next-SLICE @ the anchor: {m}"
        );
        assert_eq!(MemRefineKind::StepByNextSlice.label(), "stepby-next-SLICE");
    }

    #[test]
    fn icmp_overflow_keys_attribute_to_binaryop() {
        assert_eq!(
            rvalue_kind_of_refine_key("icmp:Lt:SignedLessThan:I32"),
            Some(RvalueKind::BinaryOp)
        );
        assert_eq!(
            rvalue_kind_of_refine_key("overflow:AddOverflow:I32"),
            Some(RvalueKind::BinaryOp)
        );
        assert_eq!(
            rvalue_kind_of_refine_key("unop:Neg:I64"),
            Some(RvalueKind::UnaryOp)
        );
        assert_eq!(
            rvalue_kind_of_refine_key("intcast:SExt:I32->I64:signed=true"),
            Some(RvalueKind::Cast)
        );
        assert_eq!(rvalue_kind_of_refine_key("mystery:foo"), None);
    }

    #[test]
    fn strict_mode_fails_closed_on_unmodeled_shape() {
        let mut rec = CoverageRecorder::new(false, true);
        // Allowlisted/refinable shapes are fine under strict.
        assert!(rec.record_rvalue(RvalueKind::BinaryOp).is_ok());
        assert!(rec.record_terminator(TerminatorShape::SwitchInt).is_ok());
        assert!(rec.record_projection(ProjectionKind::Field).is_ok());
        // An Unmodeled shape fails closed with a clear, shape-naming message.
        let err = rec
            .record_terminator(TerminatorShape::InlineAsm)
            .expect_err("InlineAsm must fail closed under strict");
        assert!(err.contains("UNMODELED"), "{err}");
        assert!(err.contains("InlineAsm"), "{err}");
        assert!(err.contains("STRICT"), "{err}");
    }

    #[test]
    fn default_mode_never_errs_even_on_unmodeled() {
        // Behavior-identity: in default mode, recording NEVER returns Err, so the
        // bridge's lowering control flow is unchanged (warning is additive only).
        let mut rec = CoverageRecorder::new(false, false);
        assert!(rec.record_rvalue(RvalueKind::WrapUnsafeBinder).is_ok());
        assert!(rec.record_terminator(TerminatorShape::Yield).is_ok());
        assert!(rec.record_terminator(TerminatorShape::InlineAsm).is_ok());
        assert_eq!(rec.unmodeled_count(), 3); // WrapUnsafeBinder rvalue + Yield + InlineAsm terms
    }

    #[test]
    fn manifest_lists_all_three_dimensions() {
        let mut rec = CoverageRecorder::new(true, false);
        rec.record_rvalue(RvalueKind::BinaryOp).unwrap();
        rec.record_projection(ProjectionKind::Field).unwrap();
        rec.record_projection(ProjectionKind::Deref).unwrap();
        rec.record_terminator(TerminatorShape::SwitchInt).unwrap();
        rec.record_terminator(TerminatorShape::Return).unwrap();
        let m = rec.manifest("test::all_dims");
        assert!(m.contains("[rvalue]"));
        assert!(m.contains("[place]"));
        assert!(m.contains("[terminator]"));
        assert!(m.contains("Field"));
        assert!(m.contains("SwitchInt"));
    }
}
